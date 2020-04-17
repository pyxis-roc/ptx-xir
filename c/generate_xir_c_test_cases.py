#!/usr/bin/env python3
#
# generate_test_cases.py
#
# Generate test cases for native inline assembly PTX
#
# Authors:
#  - Benjamin Valpey
#  - Sreepathi Pai

import json
import re
import pathlib
import subprocess
import argparse
import yaml
import pycparser
from pycparser import c_ast, c_generator
import shutil
from gpusemtest.isa import ptx
from gpusemtest.utils.testinfo import InstructionTest, write_all_tests

PROLOGUE = """
/* -*- mode: c++ -*- */
#include <stdio.h>
#include <assert.h>
#include <string.h>
#include <stdlib.h>
#include <errno.h>
#include <stdint.h>
#include "testutils.h"
#include "{header}"

"""

EPILOGUE = """
int main(int argc, char *argv[]) {{
   if(argc < 3) {{
      printf("Usage: %s <input_file> <output_file>\\n", argv[0]);
      return 1;
   }}

   const char *input = argv[1];
   const char *output = argv[2];

   {input_type} *args;
   {output_type} *results;
   size_t nargs;

   nargs = {read_fn}(input, &args);
   printf("Read %ld tuples of arguments\\n", nargs);
   if(nargs == 0)
	 return 1;

   results = ({output_type} *) calloc(nargs, sizeof({output_type}));
   if(!results) {{
	 fprintf(stderr, "ERROR: Failed to allocate memory for results: %s\\n", strerror(errno));
	 return 1;
   }}

   int i;
   for(i = 0; i < nargs; i++)
       {test_call};

   if({write_fn}(output, results, nargs))
	 return 0;

   return 1;
}}
"""

def write_ptx_harness(insn: str, decl: str, ret_type: str):
    """
    Constructs a harness for a C driver program.

    :param ptx_instruction: The name of the ptx instruction; e.g. add_s32
    :param decl: The C AST declaration


    """
    funcname = insn

    # Extract the number of arguments, excluding the destination register
    nargs = len(decl.type.args.params)

    # Grab the name of the ptx inline function as well as the argument type
    ptx_funcname = decl.name

    # Now, build the driver function

    g = c_generator.CGenerator()
    arglist = [g.visit(p) for p in decl.type.args.params]

    driver_func_defn = [f"void test_{funcname}({ret_type} * result, {', '.join(arglist)}) {{"]

    # for all arguments that are pointers, perform a cudaMalloc
    device_allocs = {}

    callargs = [d.name if d.name not in device_allocs else device_allocs[d.name][0] for d in decl.type.args.params]

    # TODO: this only supports scalar!
    driver_func_defn.append(f"\t*result = {ptx_funcname}({', '.join(callargs)});")

    # THIS MUST AGREE WITH EPILOGUE
    testcall_args = ["&results[i]"] + [f"args[i*{nargs}+{i}]" for i in range(nargs)]
    call = f"test_{funcname}({', '.join(testcall_args)})"

    return call, "\n".join(driver_func_defn) + "\n}\n"


def load_declarations(srcfile, headers):
    src = pycparser.parse_file(srcfile, use_cpp=True, cpp_args=[f"-I{headers}"])
    out = {}

    for d in src.ext: # should work in pycparse < 2.19
        if isinstance(d, c_ast.FuncDef) and d.decl.name.startswith("execute_"):
            n = d.decl.name[len("execute_"):]
            out[n] = d.decl

    return out

def gen_test_case(insn, fdecl):
    ty = ptx.get_insn_types(insn)
    inputargs = len(fdecl.type.args.params)

    template = {'insn': insn}

    if len(ty) == 1:
        ty = ty[0]
        template = {'input_type': ptx.PTX_TO_CUDA_TYPES[ty],
                    'output_type': ptx.PTX_TO_CUDA_TYPES[ty],
                    'read_fn': f'read_{ty}_{inputargs}',
                    'write_fn': f'write_{ty}',
                    'header': args.header} # global!

        call, harness = write_ptx_harness(insn, fdecl, ret_type = template['output_type'])

        template['test_call'] = call

        output = PROLOGUE.format(**template) + harness + EPILOGUE.format(**template)
    else:
        raise NotImplementedError(f"Multiple types in {insn} not supported yet")

    return output

def gen_all_tests(fdecls):
    out = {}
    total = 0
    for f in fdecls:
        total += 1
        try:
            test = gen_test_case(f, fdecls[f])
            assert f not in out, f"Duplicate instruction semantics {f}"
            out[f] = InstructionTest(insn=f, testfile=f"{f}.c",
                                     contents=test,
                                     compile_cmd=f'make {f}', executable=f)
        except NotImplementedError as e:
            print(f"{f} test case generation support not yet implemented ({e})")

    return total, out

def write_tests(tests, outputdir, srcpath, sources, supportfiles):
    dst = pathlib.Path(outputdir)

    # create tests.yaml
    write_all_tests(tests, dst, write_contents=True)

    # generate a makefile
    with open(dst / 'Makefile', 'w') as f:
        f.write(f"all: {' '.join(tests.keys())}\n\n")
        #f.write(f'testutils.o: testutils.c testutils.h\n\tgcc -std=c99 -c -g $< -o $@\n\n')
        f.write("include Makefile.testutils\n")
        f.write(f'ptxc.o: ptxc.c\n\tgcc -c -O3 -g $< -o $@\n\n')

        #TODO:
        sources = [x for x in sources if x != 'ptxc.c']

        for t in tests:
            f.write(f"{t}: {t}.c ptxc.o testutils.o {' '.join(sources)}\n\tgcc -g -O3 $^ -lm -o $@\n\n")

    # copy files
    for support in sources + supportfiles:
        print(f"Copying {srcpath / support} to {dst / support}")
        shutil.copyfile(srcpath / support, dst / support)

    # copy common support files
    # TODO: make this configurable?
    common_support_dir = dst / '..' / '..' / 'support' / 'common-c'
    for commsupport in ['testutils.c', 'testutils.h', 'Makefile.testutils']:
        print(f"Copying {common_support_dir / commsupport} to {dst / commsupport}")
        shutil.copyfile(common_support_dir / commsupport, dst / commsupport)


def main(args):
    decls = load_declarations(args.source, args.fakecheaders)
    total, tests = gen_all_tests(decls)
    print(f"Generated {total} tests. Writing ...")
    write_tests(tests, args.testcasedir, pathlib.Path(__file__).parent,
                [args.source, args.header], [])

if __name__ == '__main__':
    p = argparse.ArgumentParser(description='Create test cases for PTX instructions semantics compiled to C')
    p.add_argument("testcasedir", help="Directory for test cases")
    p.add_argument("--header", help="Header file containing declarations", default="ptxc.h")
    p.add_argument("--source", help="Source file containing definitions", default="ptxc.c")
    p.add_argument('--fakecheaders', help="Fake C headers for pycparser", default="/usr/share/python-pycparser/fake_libc_include") # this assumes that a pycparser package is installed
    args = p.parse_args()

    main(args)


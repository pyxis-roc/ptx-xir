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
from gpusemtest.utils.ctestutils import *

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

PROLOGUE_CUSTOM_RD = "{arg_struct_defn}\n{custom_reader_defn}\n"
PROLOGUE_CUSTOM_WR = "{out_struct_defn}\n{custom_writer_defn}\n"

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

   nargs = {read_fn}({read_fn_args});
   printf("Read %ld tuples of arguments\\n", nargs);
   if(nargs == 0)
	 return 1;

   results = ({output_type} *) calloc(nargs, sizeof({output_type}));
   if(!results) {{
	 fprintf(stderr, "ERROR: Failed to allocate memory for results: %s\\n", strerror(errno));
	 return 1;
   }}

   results = ({output_type} *) memset(results, 0x65, nargs * sizeof({output_type}));

   int i;
   for(i = 0; i < nargs; i++)
       {test_call};

   if({write_fn}{write_fn_args})
	 return 0;

   return 1;
}}
"""

def write_ptx_harness(pii, insn: str, decl, ret_type: str):
    """
    Constructs a harness for a C driver program.

    :param ptx_instruction: The name of the ptx instruction; e.g. add_s32
    :param decl: The C AST declaration


    """
    funcname = insn

    nargs = len(pii.arg_types)

    # Grab the name of the ptx inline function as well as the argument type
    ptx_funcname = decl.name

    # Now, build the driver function

    g = c_generator.CGenerator()
    arglist = [g.visit(p) for p in decl.type.args.params if p.name != 'cc_reg']

    driver_func_defn = [f"void test_{funcname}({ret_type} * result, {', '.join(arglist)}) {{"]

    callargs = [d.name for d in decl.type.args.params]

    needs_cc = 'cc_reg' in set([a.name for a in decl.type.args.params])
    if needs_cc:
        driver_func_defn.append(g.visit(decl.type.args.params[-1]) + ";")
        driver_func_defn.append("cc_reg.cf = 0;")

    driver_func_defn.append(f"\t*result = {ptx_funcname}({', '.join(callargs)});")

    # THIS MUST AGREE WITH EPILOGUE
    if len(pii.output_types) == 1:
        testcall_args = ["&results[i]"]
    else:
        testcall_args = [f"&results[i].out{k}" for k in range(len(pii.output_types))]

    if pii.is_homogeneous():
        testcall_args.extend([f"args[i*{pii.nargs}+{i}]" for i in range(pii.nargs)])
    else:
        testcall_args.extend([f"args[i].arg{i}" for i in range(pii.nargs)])

    #testcall_args = ["&results[i]"] + [f"args[i*{nargs}+{i}]" for i in range(nargs)]
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

def gen_test_case(dpii, insn, fdecl):
    if insn not in dpii:
        raise NotImplementedError(f"Instruction {insn} not in PTX Instruction database")

    pii = dpii[insn]
    template = {'insn': insn}

    template = gen_io_template(pii, insn, ptx.PTX_TO_C_TYPES,
                               ptx.PTX_TO_SCANF_FORMAT_STRING,
                               ptx.PTX_TO_PRINTF_FORMAT_STRING)

    call, harness = write_ptx_harness(pii, insn, fdecl, template['output_type'])
    template['test_call'] = call
    template['header'] = args.header # GLOBAL!

    output = []

    output.append(PROLOGUE.format(**template))
    if 'arg_struct_defn' in template: output.append(PROLOGUE_CUSTOM_RD.format(**template))
    if 'out_struct_defn' in template: output.append(PROLOGUE_CUSTOM_WR.format(**template))

    output.append(harness)
    output.append(EPILOGUE.format(**template))

    output = "\n".join(output)

    return output

def gen_all_tests(dpii, fdecls):
    out = {}
    total = 0
    for f in fdecls:
        print(f)
        total += 1
        if f in dpii:
            if ptx.PII_FLAG_ABSTRACT in dpii[f].flags:
                #total += gen_abstract_tests(dpii, insn, semantics[f], out)
                continue

        try:
            test = gen_test_case(dpii, f, fdecls[f])
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
    for support in ['ptxc.c'] + sources + supportfiles:
        print(f"Copying {srcpath / support} to {dst / support}")
        shutil.copyfile(srcpath / support, dst / support)

    # copy common support files
    # TODO: make this configurable?
    common_support_dir = dst / '..' / '..' / 'support' / 'common-c'
    for commsupport in ['testutils.c', 'testutils.h', 'Makefile.testutils']:
        print(f"Copying {common_support_dir / commsupport} to {dst / commsupport}")
        shutil.copyfile(common_support_dir / commsupport, dst / commsupport)


def main(args):
    pii = ptx.PTXInstructionInfo.load(v=65)
    decls = load_declarations(args.source, args.fakecheaders)
    total, tests = gen_all_tests(pii, decls)
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


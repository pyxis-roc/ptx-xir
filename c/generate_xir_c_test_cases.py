#!/usr/bin/env python3
#
# generate_test_cases.py
#
# Generate test cases for C translations of XIR
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
from gpusemtest.utils.metadata import write_static_metadata

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

def write_ptx_harness(pii, insn: str, decl, ret_type: str, base_pii = None):
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

    if not pii.base_instruction:
        arglist = [g.visit(p) for p in decl.type.args.params if p.name != 'cc_reg']
        callargs = [d.name for d in decl.type.args.params]
    else:
        arglist = [g.visit(p) for p in decl.type.args.params[:pii.nargs] if p.name != 'cc_reg']
        callargs = [d.name for d in decl.type.args.params[:pii.nargs]]

        if base_pii is None:
            import pdb
            pdb.set_trace()

        for p in base_pii.abstract_params:
            callargs.append(str(pii.abstract_args[p]))

    if len(pii.output_types) == 1 or (len(pii.output_types) == 2 and pii.output_types[1] == 'cc_reg'):
        ret_args = f"{ret_type} * result"
    else:
        ret_args = [f"{ptx.PTX_TO_C_TYPES[a]} * result{k}" for k, a in enumerate(pii.output_types)]
        ret_args = ", ".join(ret_args)

    driver_func_defn = [f"void test_{funcname}({ret_args}, {', '.join(arglist)}) {{"]



    needs_cc = 'cc_reg' in set(pii.arg_types) or 'cc_reg' in set(pii.output_types)
    if needs_cc:
        driver_func_defn.append(g.visit(decl.type.args.params[-1]) + ";")
        driver_func_defn.append("cc_reg.cf = 0;")

    if len(pii.output_types) == 1 or (len(pii.output_types) == 2 and pii.output_types[1] == 'cc_reg'):
        driver_func_defn.append(f"\t*result = {ptx_funcname}({', '.join(callargs)});")
    else:
        # TODO
        driver_func_defn.append(f"struct retval_{insn} result;")
        driver_func_defn.append(f"\tresult = {ptx_funcname}({', '.join(callargs)});")
        for k in range(len(pii.output_types)):
            driver_func_defn.append(f"\t*result{k} = result.out{k};")

    # THIS MUST AGREE WITH EPILOGUE
    if len(pii.output_types) == 1 or (len(pii.output_types) == 2 and pii.output_types[1] == 'cc_reg'):
        testcall_args = ["&results[i]"]
    else:
        testcall_args = [f"&results[i].out{k}" for k in range(len(pii.output_types))]

    cpii = pii.copy()
    cpii.arg_types = [x for x in cpii.arg_types if x != 'cc_reg']

    if cpii.is_homogeneous(): # TODO: handle cc_regq
        testcall_args.extend([f"args[i*{pii.nargs}+{i}]" for i in range(cpii.nargs)])
    else:
        testcall_args.extend([f"args[i].arg{i}" for i in range(cpii.nargs)])

    #testcall_args = ["&results[i]"] + [f"args[i*{nargs}+{i}]" for i in range(nargs)]
    call = f"test_{funcname}({', '.join(testcall_args)})"

    return call, "\n".join(driver_func_defn) + "\n}\n"

def load_declarations(srcfile, headers):
    src = pycparser.parse_file(srcfile, use_cpp=True, cpp_args=[f"-I{headers}", "-DPYCPARSER", "-D__STDC_VERSION__=199901L"])
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

    if pii.base_instruction:
        base_pii = dpii[pii.base_instruction]
    else:
        base_pii = None

    call, harness = write_ptx_harness(pii, insn, fdecl, template['output_type'], base_pii)
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

def gen_abstract_tests(dpii, base, abs_fdecl, out):
    derivatives = [k for k in dpii if dpii[k].base_instruction == base]

    for insn in derivatives:
        try:
            assert insn not in out, f"Duplicate instruction semantics {insn} ({f})"
            test = gen_test_case(dpii, insn, abs_fdecl)

            out[insn] = InstructionTest(insn=insn, testfile=f"{insn}.c",
                                        contents=test,
                                        compile_cmd=f'make {insn}', executable=insn)
        except NotImplementedError as e:
            print(f"{f} test case generation support not yet implemented ({e})")

    return len(derivatives)

def gen_all_tests(dpii, fdecls):
    out = {}
    total = 0
    for f in fdecls:
        total += 1
        if f in dpii:
            if ptx.PII_FLAG_ABSTRACT in dpii[f].flags:
                total += gen_abstract_tests(dpii, f, fdecls[f], out)
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
    write_static_metadata(dst, 'git', ignore_spec='ignore_spec_c.txt')

    # generate a makefile
    with open(dst / 'Makefile', 'w') as f:
        f.write(f"all: libptxc.so {' '.join(tests.keys())}\n\n") #TODO: libptxc.so
        #f.write(f'testutils.o: testutils.c testutils.h\n\tgcc -std=c99 -c -g $< -o $@\n\n')
        f.write("include Makefile.testutils\n")
        f.write(f'libptxc.so: ptxc.c lop3_lut.h\n\tgcc -shared -fPIC -O3 -g $< -lm -o $@\n\n')

        src = [x for x in sources if x != 'ptxc.c']

        for t in tests:
            f.write(f"{t}: {t}.c testutils.o {' '.join(src)}\n\tgcc -g -O3 -L. -Wl,-rpath,'$$ORIGIN' $^ -lptxc -lm -o $@\n\n")

    # copy files
    for support in ['ptxc.c'] + sources + supportfiles + ['ignore_spec_c.txt']:
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
    #decls = {'setp_q_eq_ftz_f32': decls['setp_q_eq_ftz_f32']}

    total, tests = gen_all_tests(pii, decls)
    print(f"Generated {total} tests. Writing ...")
    write_tests(tests, args.testcasedir, pathlib.Path(__file__).parent,
                [args.source], [args.header, 'ptxc_utils.h', 'lop3_lut.h', 'ptxc_utils_template.h'])

if __name__ == '__main__':
    p = argparse.ArgumentParser(description='Create test cases for PTX instructions semantics compiled to C')
    p.add_argument("testcasedir", help="Directory for test cases")
    p.add_argument("--header", help="Header file containing declarations", default="ptxc.h")
    p.add_argument("--source", help="Source file containing definitions", default="ptxc.c")
    p.add_argument('--fakecheaders', help="Fake C headers for pycparser", default="/usr/share/python-pycparser/fake_libc_include") # this assumes that a pycparser package is installed
    args = p.parse_args()

    main(args)


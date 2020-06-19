#!/usr/bin/env python3
#
# generate_test_cases.py
#
# Generate test cases for SMT2 translations of XIR

import argparse
import sys
import extract_ex_semantics
import re
import shutil
import pathlib
import yaml
from gpusemtest.isa import ptx
from gpusemtest.utils.testinfo import InstructionTest, write_all_tests
from gpusemtest.utils.metadata import write_static_metadata
import smt2ast

PROLOGUE = """#!/usr/bin/env python3
from smt2ast import *
import testutils
import testutils_smt2
import sys

SMT2STR = {smt2str}
"""

X_TEST_HARNESS = """
NARGS = {nargs}

def test_{insn}(testcases):
    smt2_testcases = testutils.encode_test_cases({fmt_str}, testcases, smt2_literal)

    scr = []
    for tc in smt2_testcases:
        scr.append(SExprList(Symbol("get-value"), SExprList(SExprList(Symbol("execute_{insn}"), *tc))))

    return testutils_smt2.get_output(SMT2STR, scr, "z3", {ptx_output_type})
"""

EPILOGUE = """
if __name__ == "__main__":
    import testutils
    import argparse

    p = argparse.ArgumentParser(description="Run test cases for {insn}")
    p.add_argument("input", help="Input file containing test cases")
    p.add_argument("output", help="Output file containing test cases")

    args = p.parse_args()

    testcases = testutils.{reader}{reader_args}
    results = test_{insn}(testcases)
    testutils.{writer}{writer_args}

"""

def load_execute_functions(semfile):
    status = 0
    block = None

    gl = None
    out = {}
    contents = []

    with open(semfile, "r") as f:
        for l in f:
            if l[0] == ";":
                if ":begin" in l:
                    assert status == 0, f"begin encountered when status={status} on line {l}"
                    block = l.split()[2].strip()
                    status = 1 # in block
                elif ":end" in l:
                    assert status == 1, f"end encountered when status={status} on line {l}"
                    block2 = l.split()[2].strip()
                    assert block == block2, f"end encountered for block {block2}, but in block {block}"

                    if block == "global":
                        gl = contents
                    else:
                        assert block not in out, f"Duplicate block {block}"
                        out[block] = contents

                    contents = []
                    block = None
                    status = 0
                else:
                    if status == 1: contents.append(l)
            else:
                if status == 1:
                    contents.append(l)

    return gl, out

def gen_test_case(dpii, insn, fdef, deriv_pii = None):
    if insn not in dpii:
        raise NotImplementedError(f"Instruction {insn} not found in PTX instruction database")

    pii = dpii[insn]

    template = {'insn': insn}

    nargs = pii.nargs
    needs_cc = 'cc_reg' in pii.arg_types or 'cc_reg' in pii.output_types

    if needs_cc:
        th = X_TEST_HARNESS
        #nargs -= 1
    else:
        th = X_TEST_HARNESS

    # template['iter_arg_list'] = [f"src{i}" for i in range(nargs)]
    # if nargs == 1:
    #     template["arg_list"] = ["src0[0]"] don't ask ...
    # else:
    #     template["arg_list"] = list(template['iter_arg_list'])

    if deriv_pii is not None:
        # TODO: locate abstract argument position in instruction semantics, and place it there
        # right now, there is an assumption that all arguments occur at end of instruction
        ast = smt2ast.SMT2Parser.parse("\n".join(fdef))[0]

        # name
        ast.v[1] = smt2ast.Symbol("execute_" + insn)
        # args
        ast.v[2].v = [x for x in ast.v[2].v if x.v[0].v not in pii.abstract_args]
        # original function
        # TODO: ordering of abstract args!
        abstract_args_ty = list(zip(pii.abstract_args.values(), deriv_pii.arg_types[nargs:]))

        orig_args = [x.v[0] for x in ast.v[2].v] + [smt2ast.smt2_literal(x, ty) for x, ty in abstract_args_ty]
        ast.v[4] = smt2ast.SExprList(smt2ast.Symbol("execute_" + pii.base_instruction), *orig_args)

        new_fn = str(ast)
        template['smt2str'] = '"""\\\n' + "".join(gl) + "".join(fdef) + '\n\n' + new_fn + '\n"""'
    else:
        template['smt2str'] = '"""\\\n' + "".join(gl) + "".join(fdef) + '\n"""'

    # template["iter_arg_list"] = ", ".join(template["iter_arg_list"])
    # template["arg_list"] = ", ".join(template["arg_list"])
    template['nargs'] = nargs

    #TODO: needs to be in PTX Instruction Info

    # note: cc_reg flag is not really observable, so don't output it?
    if len(pii.output_types) == 1: # or (len(pii.output_types) == 2 and needs_cc):
        # homogeneous output
        template['writer'] = f"write_{pii.output_types[0]}_test_cases"
        template['writer_args'] = "(args.output, results)"
        template['ptx_output_type'] = repr(pii.output_types[0])
    else:
        out_fmt_str = str(tuple(pii.output_types))
        template['writer'] = f"write_custom_test_cases"
        template['writer_args'] = f"({out_fmt_str}, args.output, results)"
        template['ptx_output_type'] = out_fmt_str

    # cc_reg workaround
    cpii = pii.copy()
    #cpii.arg_types = [x for x in cpii.arg_types[:nargs] if x != 'cc_reg']

    fmt_str = str(tuple(cpii.arg_types))
    template['fmt_str'] = fmt_str

    if cpii.is_homogeneous():
        input_ty = cpii.arg_types[0]
        template['reader'] = f"read_{input_ty}_test_cases"
        template['reader_args'] = f"(args.input, NARGS)"
    else:
        template['reader'] = f"read_custom_test_cases"
        template['reader_args'] = f"({fmt_str}, args.input, NARGS)"

    output = PROLOGUE.format(**template) + th.format(**template) + EPILOGUE.format(**template)

    return insn, output

def gen_abstract_tests(dpii, base, abs_semantics, out):
    derivatives = [k for k in dpii if dpii[k].base_instruction == base]

    for insn in derivatives:
        try:
            assert insn not in out, f"Duplicate instruction semantics {insn} ({f})"
            _, test = gen_test_case(dpii, insn, abs_semantics, dpii[base])
            out[insn] = InstructionTest(insn, f"{insn}.py", test, '')
        except NotImplementedError as e:
            print(f"{f} test case generation support not yet implemented ({e})")

    return len(derivatives)

def gen_all_tests(dpii, semantics):
    out = {}
    total = 0
    for f in semantics:
        if f[:8] == "execute_":
            insn = f[len("execute_"):]
            total += 1

            if insn in dpii:
                if ptx.PII_FLAG_ABSTRACT in dpii[insn].flags:
                    total += gen_abstract_tests(dpii, insn, semantics[f], out)
                    continue

                try:
                    insn, test = gen_test_case(dpii, insn, semantics[f])
                    assert insn not in out, f"Duplicate instruction semantics {insn} ({f})"
                    out[insn] = InstructionTest(insn, f"{insn}.py", test, '')
                except NotImplementedError as e:
                    print(f"{f} test case generation support not yet implemented ({e})")
            else:
                print(f"Instruction {insn} not found in PTX instruction database")

    return total, out

def write_tests(tests, outputdir, srcpath, semantics):
    dst = pathlib.Path(outputdir)

    write_all_tests(tests, dst, write_contents = True, mark_executable = True)
    write_static_metadata(dst, 'git', ignore_spec='ignore_spec_smt2.txt',
                          ptx_semantics = ptx.__file__,
                          filter_cc_reg = True)

    for support in ['smt2ast.py', 'testutils.py', 'testutils_smt2.py', 'ignore_spec_smt2.txt']:
        print(f"Copying {srcpath / support} to {dst / support}")
        shutil.copyfile(srcpath / support, dst / support)

if __name__ == "__main__":
    p = argparse.ArgumentParser(description="Generate test cases for SMT2 semantics")
    p.add_argument("testcasedir", help="Directory for test cases")
    p.add_argument("-s", "--semantics", help="Executable semantics file", default="ptx_executable_semantics.smt2")

    args = p.parse_args()

    pii = ptx.PTXInstructionInfo.load(v=65)
    gl, semantics = load_execute_functions(args.semantics)
    #semantics = {'setp_eq_or_b16': semantics['setp_eq_or_b16']}
    total, tests = gen_all_tests(pii, semantics)
    print(f"Using ptx information from {ptx.__file__}")
    print(f"Generated {len(tests)} tests. Writing ...")

    write_tests(tests, args.testcasedir, pathlib.Path(__file__).parent, args.semantics)
    print(f"{len(tests)} tests generated of total {total} semantics {len(tests)/total*100:0.2f}%")

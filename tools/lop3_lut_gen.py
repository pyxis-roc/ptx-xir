#!/usr/bin/env python3

# SPDX-FileCopyrightText: 2020 University of Rochester
#
# SPDX-License-Identifier: LGPL-3.0-or-later

from quine_mccluskey.qm import QuineMcCluskey
import ast
import argparse
import sys
import functools

def gen_lop3(n, fgen, varnames="abc", use_xor = False, hexfn = hex):
    if n == 0:
        return hexfn(0)

    ones = []
    for i in range(8):
        if n & (1 << i):
            ones.append(i)

    #print(ones)

    s = QuineMcCluskey(use_xor = use_xor)

    x = s.simplify(ones, num_bits = 3)

    if len(x) == 1 and x == set(['---']):
        return hexfn(2**32-1)

    #print(x)
    minterms = []

    for term in x:
        terms = []
        all_xor = []
        all_xnor = []

        for bit, v in enumerate(term):
            if v == "^":
                all_xor.append(bit)
            elif v == "~":
                all_xnor.append(bit)
            elif v == "0":
                terms.append(-(bit+1))
            elif v == "1":
                terms.append(bit+1)

        minterms.append((terms, all_xor, all_xnor))

    return fgen(minterms, varnames)

def gen_formula_debug(mt, varnames="ABC"):
    print(mt)
    print(gen_formula_py(mt, varnames))
    return ""

def gen_formula_smt2(mt, varnames="ABC"):
    mts = []
    for p, xort, xnort in mt:
        ps = []
        if len(p):
            ps.extend([varnames[b-1] if b > 0 else f"(bvnot {varnames[-b-1]})" for b in sorted(set(p))])

        if len(xort):
            vn = [varnames[b] for b in sorted(set(xort))]
            ps.append(functools.reduce(lambda x, y: f"(bvxor {x} {y})", vn))

        if len(xnort):
            vn = [varnames[b] for b in sorted(set(xnort))]
            ps.append("(bvnot " + functools.reduce(lambda x, y: f"(bvxor {x} {y})", vn) + ")")

        mts.append(functools.reduce(lambda x, y: f"(bvand {x} {y})", ps))

    sop = functools.reduce(lambda x, y: f"(bvor {x} {y})", mts)
    return sop

def gen_formula_py(mt, varnames="ABC"):
    mts = []
    for p, xort, xnort in mt:
        ps = []
        if len(p):
            ps.extend([varnames[b-1] if b > 0 else f"~{varnames[-b-1]}" for b in sorted(set(p))])

        if len(xort):
            ps.append("(" + " ^ ".join([varnames[b] for b in sorted(set(xort))]) + ")")

        if len(xnort):
            ps.append("~(" + " ^ ".join([varnames[b] for b in sorted(set(xnort))]) + ")")

        mts.append(" & ".join(sorted(ps)))

    sop = "(" + ") | (".join(sorted(mts)) + ")"
    return sop

def generate_c_lop3_table():
    s = ["#pragma once",
         "#include <stdint.h>",
         "static inline uint32_t logical_op3(uint32_t a, uint32_t b, uint32_t c, uint8_t immLut) {",
         "    switch(immLut) {"]

    for i in range(256):
        fn = gen_lop3(i, gen_formula_py, use_xor=args.use_xor)
        s.append(f"        case 0x{i:02x}: return {fn};")

    s.extend(["    }", "}\n"])

    return "\n".join(s)

def generate_smt2chk_lop3_table():
    s = ["(set-logic QF_BV)",
         "(declare-fun a () (_ BitVec 32))",
         "(declare-fun b () (_ BitVec 32))",
         "(declare-fun c () (_ BitVec 32))",]

    for i in range(256):
        fn1 = gen_lop3(i, gen_formula_smt2, use_xor=True)
        fn2 = gen_lop3(i, gen_formula_smt2, use_xor=False)
        if i == 0:
            fn1 = "#x" + fn1
            fn2 = "#x" + fn2
        elif i == 255:
            fn1 = "#x" + fn1[2:]
            fn2 = "#x" + fn2[2:]

        s.append(f"(assert (not (= {fn1} {fn2})))")
        s.append("(check-sat)")

    return "\n".join(s)

def generate_smt2_lop3_table():
    def recgen(p):
        if p == len(out) - 1:
            return f"\n    {out[p]}"
        else:
            return f"\n    (ite (= immLut #x{p:02x}) {out[p]}{recgen(p+1)})"

    out = []
    for i in range(256):
        fn1 = gen_lop3(i, gen_formula_smt2, use_xor=True, hexfn=lambda x: f"#x{x:08x}")
        out.append(fn1)

    assert len(out) > 0
    fn = f"(define-fun logical_op3 ((a b32) (b b32) (c b32) (immLut u8)) b32{recgen(0)})"

    return fn

def test_gen_lop3():
    # the result is non-deterministic?
    gen_lop3(0x15, gen_formula_debug, use_xor = True)
    gen_lop3(0x15, gen_formula_debug)

#test_gen_lop3()
#sys.exit(0)

if __name__ == "__main__":
    p = argparse.ArgumentParser(description="Generate a LOP3 function table")
    p.add_argument("language", choices=["c", "smt2chk", "smt2"])
    p.add_argument("output", nargs="?")
    p.add_argument("-x", dest="use_xor", action="store_true")

    args = p.parse_args()

    if args.language == "c":
        if args.output:
            f = open(args.output, "w")
        else:
            f = sys.stdout

        f.write(generate_c_lop3_table())

        f.close()
    elif args.language == "smt2chk":
        if args.output:
            f = open(args.output, "w")
        else:
            f = sys.stdout

        f.write(generate_smt2chk_lop3_table())

        f.close()
    elif args.language == "smt2":
        if args.output:
            f = open(args.output, "w")
        else:
            f = sys.stdout

        f.write(generate_smt2_lop3_table())

        f.close()
    else:
        raise NotImplementedError(f"Don't support language {args.language}")

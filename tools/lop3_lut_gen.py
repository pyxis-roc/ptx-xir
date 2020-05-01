#!/usr/bin/env python3

from quine_mccluskey.qm import QuineMcCluskey
import ast
import argparse
import sys

def gen_lop3(n, fgen, varnames="abc"):
    if n == 0:
        return "0"

    ones = []
    for i in range(8):
        if n & (1 << i):
            ones.append(i)

    s = QuineMcCluskey(use_xor = args.use_xor)

    x = s.simplify(ones, num_bits = 3)

    if len(x) == 1 and x == set(['---']):
        return hex(2**32-1)

    minterms = []
    all_xor = []
    all_xnor = []

    for term in x:
        terms = []

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
        fn = gen_lop3(i, gen_formula_py)
        s.append(f"        case 0x{i:02x}: return {fn};")

    s.extend(["    }", "}\n"])

    return "\n".join(s)

if __name__ == "__main__":
    p = argparse.ArgumentParser(description="Generate a LOP3 function table")
    p.add_argument("language", choices=["c"])
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
    else:
        raise NotImplementedError(f"Don't support language {args.language}")

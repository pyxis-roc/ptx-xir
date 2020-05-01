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

    s = QuineMcCluskey(use_xor = True)

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

        minterms.append(terms)

    return fgen(minterms, all_xor, all_xnor, varnames)

def gen_formula_py(mt, all_xor, all_xnor, varnames="ABC"):
    xor_term = " ^ ".join([varnames[b] for b in all_xor])
    xnor_term = " ^ ".join([varnames[b] for b in all_xnor])

    mts = []
    for p in mt:
        if len(p):
            ps = " & ".join([varnames[b-1] if b > 0 else f"~{varnames[-b-1]}" for b in p])
            mts.append(ps)

    if xor_term: mts.append(xor_term)
    if xnor_term: mts.append(xnor_term)

    sop ="(" + ") | (".join(mts) + ")"
    return sop

def generate_c_lop3_table():
    s = ["#pragma once",
         "#include <stdint.h>",
         "static inline uint32_t logical_op3(uint32_t a, uint32_t b, uint32_t c, uint8_t immLut) {",
         "    switch(immLut) {"]

    for i in range(256):
        fn = gen_lop3(i, gen_formula_py)
        s.append(f"        case {i}: return {fn};")

    s.extend(["    }", "}\n"])

    return "\n".join(s)

if __name__ == "__main__":
    p = argparse.ArgumentParser(description="Generate a LOP3 function table")
    p.add_argument("language", choices=["c"])
    p.add_argument("output", nargs="?")

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

#!/usr/bin/env python3

# SPDX-FileCopyrightText: 2020 University of Rochester
#
# SPDX-License-Identifier: LGPL-3.0-or-later

def f4e(c):
    "Starting at c, extract next 4 bytes"
    for i in range(c, c + 4):
        yield i % 8

def b4e(c):
    "Starting at c, extract previous 4 bytes, wrapping around"
    for i in range(4):
        yield c
        c = c - 1
        if c < 0: c = 7

def rc8(c):
    "Replicate the byte at c"
    for i in range(4):
        yield c

def ecl(c):
    "Start at c, clamp to c until i reaches c, after which increase normally"

    for i in range(4):
        yield c
        if c == i:
            c = c + 1

def ecr(c):
    "Start from 0, and yield increasing indices until reaching c, after which clamp to c"

    for i in range(4):
        if c > i:
            yield i
        else:
            yield c

def rc16(c):
    "Replicate halfwords, weirdly both c==0/1 and c==0/3 seem to do the same thing"

    s = (c * 2) & 3
    for i in range(4):
        yield s + (i & 1)

MODES = {'f4e': f4e, 'b4e': b4e, 'rc8': rc8, 'ecl': ecl, 'ecr': ecr, 'rc16': rc16}

def get_modes():
    for m in MODES:
        f = MODES[m]
        for c in range(4):
            pos = list(f(c))
            yield (m, c, pos)

def generate_c():
    print("#pragma once")
    print("#include <stdint.h>")

    lastmode = None
    for mode, control, positions in get_modes():
        if lastmode != mode:
            print(f"static inline uint8_t ReadByte_{mode}(uint8_t control, uint64_t value, uint8_t pos) {{")
            print("uint8_t byte = 0;")
            lastmode = mode

        print(f"  if(control == {control}) {{")
        print("     switch(pos) {")
        for i, x in enumerate(positions):
             print(f"       case {i}: byte = {x}; break;")
        print("     }")
        print("   }")

        if control == 3:
            print("  return (value >> (byte * 8)) & 0xff;")
            print("}")

def generate_smt2():
    def itechain(values, offset):
        if len(values) == 1:
            return "\n" + " "*(offset+4) + f"{values[0][1]}"

        return "\n" + " "*offset + f"(ite {values[0][0]} {values[0][1]}{itechain(values[1:], offset)})"

    lastmode = None
    for mode, control, positions in get_modes():
        if lastmode != mode:
            #TODO: this uses u32 for control and pos, but should really be u8?
            print(f"(define-fun ReadByte_{mode}((control u32) (value u64) (pos u32)) u32", end='')
            lastmode = mode
            control_ite = []

        values = []
        for i, x in enumerate(positions):
            shiftpos = x*8
            shiftpos_end = shiftpos + 8 - 1
            ext = f"((_ zero_extend 24) ((_ extract {shiftpos_end} {shiftpos}) value))"
            values.append((f"(= pos #x{i:08x})", ext))

        control_ite.append((f"(= control #x{control:08x})", itechain(values, 8)))

        if control == 3:
            print(itechain(control_ite, 4) + ")")

if __name__ == "__main__":
    import argparse
    p = argparse.ArgumentParser(description="Generate the ReadByte functions for prmt")
    p.add_argument("language", choices=["c", "smt2"])

    args = p.parse_args()

    if args.language == 'c':
        generate_c()
    elif args.language == 'smt2':
        generate_smt2()
    else:
        raise NotImplementedError(f"Unknown language {args.language}")

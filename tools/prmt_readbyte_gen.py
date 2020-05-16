#!/usr/bin/env python3

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

if __name__ == "__main__":
    import argparse
    p = argparse.ArgumentParser(description="Generate the ReadByte functions for prmt")
    p.add_argument("language", choices=["c"])

    args = p.parse_args()

    if args.language == 'c':
        generate_c()
    else:
        raise NotImplementedError(f"Unknown language {args.language}")

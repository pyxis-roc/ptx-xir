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

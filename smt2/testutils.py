#!/usr/bin/env python3

def read_integer_test_cases(tcfile, nargs):
    out = []
    with open(tcfile, "r") as f:
        for l in f:
            ls = l.strip().split()

            ls = ls[:nargs]
            out.append([int(x) for x in ls])

    return out

def write_integer_test_cases(outfile, results):
    with open(outfile, "w") as f:
        for r in results:
            l = f"{r}\n"
            f.write(l)

READERS = {'u16': int,
           'u32': int,
           'u64': int,
           's16': int,
           's32': int,
           's64': int,
           'b16': int,
           'b32': int,
           'b64': int,
           'f32': lambda x: float.fromhex(x),
           'f64': lambda x: float.fromhex(x)}

def read_custom_test_cases(fmt, tcfile, nargs):
    out = []
    with open(tcfile, "r") as f:
        for l in f:
            ls = l.strip().split()

            ls = ls[:nargs]
            out.append([READERS[fmt](x) for x, fmt in zip(ls, fmt)])

    return out

def read_float_test_cases(tcfile, nargs):
    out = []
    with open(tcfile, "r") as f:
        for l in f:
            ls = l.strip().split()

            ls = ls[:nargs]

            # note: fromhex doesn't distinguish -nan and +nan
            out.append([float.fromhex(x) for x in ls])

    return out

def conform_c(x):
    """Conform to C's %0.13a"""

    if x == "0x0.0p+0":
        return "0x0.0000000000000p+0"
    elif x == "-0x0.0p+0":
        return "-0x0.0000000000000p+0"
    else:
        return x

def write_float_test_cases(outfile, results):
    with open(outfile, "w") as f:
        for r in results:
            # note: we always write doubles, because that's what %a also does in printf
            l = f"{conform_c(r.hex())}\n"
            f.write(l)

#read_u8_test_cases = read_integer_test_cases
read_u16_test_cases = read_integer_test_cases
read_u32_test_cases = read_integer_test_cases
read_u64_test_cases = read_integer_test_cases

#read_u8_test_cases = read_integer_test_cases
read_b16_test_cases = read_integer_test_cases
read_b32_test_cases = read_integer_test_cases
read_b64_test_cases = read_integer_test_cases

#read_s8_test_cases = read_integer_test_cases
read_s16_test_cases = read_integer_test_cases
read_s32_test_cases = read_integer_test_cases
read_s64_test_cases = read_integer_test_cases

#write_u8_test_cases = write_integer_test_cases
write_u16_test_cases = write_integer_test_cases
write_u32_test_cases = write_integer_test_cases
write_u64_test_cases = write_integer_test_cases

#write_u8_test_cases = write_integer_test_cases
write_b16_test_cases = write_integer_test_cases
write_b32_test_cases = write_integer_test_cases
write_b64_test_cases = write_integer_test_cases

#write_s8_test_cases = write_integer_test_cases
write_s16_test_cases = write_integer_test_cases
write_s32_test_cases = write_integer_test_cases
write_s64_test_cases = write_integer_test_cases

read_f32_test_cases = read_float_test_cases
read_f64_test_cases = read_float_test_cases
write_f32_test_cases = write_float_test_cases
write_f64_test_cases = write_float_test_cases

write_pred_test_cases = write_u32_test_cases
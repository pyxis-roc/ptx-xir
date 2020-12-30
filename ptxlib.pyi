#!/usr/bin/env python3

from typing import TypeVar

T = TypeVar('T')
T1 = TypeVar('T1')
T2 = TypeVar('T2')

Tf = TypeVar('Tf') # intended to be restricted to floats

RM = str # round mode, needs to be a literal string

# ROUND_SAT_ARITH_FNS
# the RewritePythonisms pass moves round mode in the front
def ADD_ROUND(a: T, b: T, m: RM) -> T: ...
def SUB_ROUND(a: T, b: T, m: RM) -> T: ...
def MUL_ROUND(a: T, b: T, m: RM) -> T: ...
def DIV_ROUND(a: T, b: T, m: RM) -> T: ...
def FMA_ROUND(a: T, b: T, c: T, m: RM) -> T: ...
def SQRT_ROUND(a: T, m: RM) -> T: ...
def RCP_ROUND(a: T, m: RM) -> T: ...

def ADD_ROUND_SATURATE(a: T, b: T, m: RM) -> T: ...
def SUB_ROUND_SATURATE(a: T, b: T, m: RM) -> T: ...
def MUL_ROUND_SATURATE(a: T, b: T, m: RM) -> T: ...
def FMA_ROUND_SATURATE(a: T, b: T, c: T, m: RM) -> T: ...

# SAT_ARITH_FNS
def ADD_SATURATE(a: T, b: T) -> T: ...
def SUB_SATURATE(a: T, b: T) -> T: ...
def MUL_SATURATE(a: T, b: T) -> T: ...
def DIV_SATURATE(a: T, b: T) -> T: ...

# CARRY_ARITH_FNS
def ADD_CARRY(a: T, b: T, c: carryflag) -> (T, carryflag): ...
def SUB_CARRY(a: T, b: T, c: carryflag) -> (T, carryflag): ...

# MACHINE_SPECIFIC_FNS
def MACHINE_SPECIFIC_execute_rem_divide_by_zero_unsigned(a: T) -> T: ...
def MACHINE_SPECIFIC_execute_div_divide_by_zero_integer(a: T) -> T: ...
def MACHINE_SPECIFIC_execute_rem_divide_by_neg(a: T, b: T) -> T: ...

# ARITH_FNS (excluding built-ins)
def DIV_FULL(a: Tf, b: Tf) -> Tf: ...
def DIV_APPROX(a: Tf, b: Tf) -> Tf: ...
#def POW(a: T, b: T) -> T: ... # part of built-ins
def REM(a: T, b: T) -> T: ...
def FMA(a: T, b: T, c: T) -> T: ...
def MUL24(a: T, b: T) -> u64: ...
def MULWIDE(a: T1, b: T1) -> T2: ...

def LOG2(a: Tf) -> Tf: ...
def EXP2(a: Tf) -> Tf: ...
def RCP(a: Tf) -> Tf: ...
def RSQRT(a: Tf) -> Tf: ...
def SINE(a: Tf) -> Tf: ...
def COSINE(a: Tf) -> Tf: ...
def COPYSIGN(x: Tf, y: Tf) -> Tf: ...

# FLOAT_FNS, some of these are not used
def ROUND(a: Tf) -> Tf: ...
def FTZ(a: Tf) -> Tf: ...
def SATURATE(a: T) -> T: ...
def ABSOLUTE(a: T) -> T: ...
def ISNAN(a: Tf) -> bool: ...
def SQRT(a: Tf) -> Tf: ...

def SAR(a: T1, b: T2) -> T1: ...
def SHL_LIT(a: T, b: T) -> T: ...
def SHR_LIT(a: T, b: T) -> T: ...
def SAR_LIT(a: T, b: T) -> T: ...

# COMPARE_PTX
def compare_eq(a: T, b: T) -> bool: ...
def compare_equ(a: T, b: T) -> bool: ...
def compare_ge(a: T, b: T) -> bool: ...
def compare_geu(a: T, b: T) -> bool: ...
def compare_gt(a: T, b: T) -> bool: ...
def compare_gtu(a: T, b: T) -> bool: ...
def compare_hi(a: T, b: T) -> bool: ...
def compare_hs(a: T, b: T) -> bool: ...
def compare_le(a: T, b: T) -> bool: ...
def compare_leu(a: T, b: T) -> bool: ...
def compare_lo(a: T, b: T) -> bool: ...
def compare_ls(a: T, b: T) -> bool: ...
def compare_lt(a: T, b: T) -> bool: ...
def compare_ltu(a: T, b: T) -> bool: ...
def compare_nan(a: T, b: T) -> bool: ...
def compare_ne(a: T, b: T) -> bool: ...
def compare_neu(a: T, b: T) -> bool: ...
def compare_num(a: T, b: T) -> bool: ...

# BOOLEAN_OP_PTX (not used since these are rewritten by RewritePythonisms)
#Tb = TypeVar('Tb') #TODO: this is bool in the original type translation, but should be pred?
#def booleanOp_and(a: bool, b: bool) -> bool: ...
#def booleanOp_or(a: bool, b: bool) -> bool: ...
def booleanOp_xor(a: bool, b: bool) -> bool: ... # used by smt2

# miscellaneous functions
def subnormal_check(f: Tf) -> bool: ...
def logical_op3(a: b32, b: b32, c: b32, f: u8) -> b32: ...

# designed to handle EQ(x, float(literal)), by RewritePythonisms
def FLOAT_COMPARE_EQ(a: Tf, b: Tf) -> bool: ...
def FLOAT_COMPARE_NOTEQ(a: Tf, b: Tf) -> bool: ...

# typecast-ing functions
def sext_16(v: T) -> s16: ...
def sext_32(v: T) -> s32: ...
def sext_64(v: T) -> s64: ...

def truncate_16(v: T) -> u16: ...
def truncate_32(v: T) -> u32: ...
def truncate_64(v: T) -> u64: ...

def zext_16(v: T) -> u16: ...
def zext_32(v: T) -> u32: ...
def zext_64(v: T) -> u64: ...

# ReadByte
# return value should be u8
def ReadByte(a: b32, b: b64, c: b32) -> u32: ...
def ReadByte_b4e(a: b32, b: b64, c: b32) -> u32: ...
def ReadByte_ecl(a: b32, b: b64, c: b32) -> u32: ...
def ReadByte_ecr(a: b32, b: b64, c: b32) -> u32: ...
def ReadByte_rc16(a: b32, b: b64, c: b32) -> u32: ...
def ReadByte_rc8(a: b32, b: b64, c: b32) -> u32: ...
def ReadByte_f4e(a: b32, b: b64, c: b32) -> u32: ...

# extractAndZeroExt
# note: non-standard (i.e non-mypy) syntax for array type, also None maps to void internally
def extractAndSignExt_2(a: u32, b: u32[2]) -> None: ...
def extractAndSignExt_4(a: u32, b: u32[4]) -> None: ...
def extractAndZeroExt_2(a: u32, b: u32[2]) -> None: ...
def extractAndZeroExt_4(a: u32, b: u32[4]) -> None: ...

# na_extractAndZeroExt? versions of above
def na_extractAndSignExt_2(a: u32, b: u8) -> u32: ...
def na_extractAndSignExt_4(a: u32, b: u8) -> u32: ...
def na_extractAndZeroExt_2(a: u32, b: u8) -> u32: ...
def na_extractAndZeroExt_4(a: u32, b: u8) -> u32: ...


# note: there are additional syntactic constraints not captured in the type here
def range(a: s32, b: s32) -> s32: ...

# float value constructor for -inf, +inf, nan, etc.
def float(a: T) -> Tf: ...

# BITSTRING
def BITSTRING_32(a: b32) -> b1[32]: ...
def BITSTRING_64(a: b64) -> b1[64]: ...

# FROM_BITSTRING
def FROM_BITSTRING_32(a: b1[32]) -> b32: ...
def FROM_BITSTRING_64(a: b1[64]) -> b64: ...

# TODO:
# set_value, set_memory, get_value, get_memory

def min(a: T, b: T) -> T: ... # TODO: move to builtins
def MIN(a: T, b: T) -> T: ... # TODO: get rid of this? probably put in for floats?
def MAX(a: T, b: T) -> T: ... # TODO: get rid of this?

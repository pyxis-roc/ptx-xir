try:
    from functools import singledispatchmethod # 3.8+
except ImportError:
    from singledispatchmethod import singledispatchmethod

from xlatir.xir.xirlib import XIRLib
from xlatir.xir.xirlibc import CBasicType, c_float, SINGLETONS, CSigned, CUnsigned, CInteger, uint64_t, uint32_t, uint16_t, uint8_t, double, CFP, int32_t, int64_t, int16_t, BinOpInfix, UnOpPrefix, FnCall, CastOp
from ptxlib import PTXLib

ROUND_MODES = {'rp': 'FE_UPWARD',  # to positive infinity
               'rn': 'FE_TONEAREST', # towards nearest even
               'rz': 'FE_TOWARDZERO', # towards zero
               'rm': 'FE_DOWNWARD'} # to negative infinity

def RoundedFnCall(fn, nargs):
    fnc = FnCall(fn, nargs)

    def rfc(*args):
        args = list(args)
        args[-1] = ROUND_MODES[args[-1][1:-1]] # 'strconst'
        return fnc(*args)

    return rfc

class PTXLibC(PTXLib):
    type_dict = dict(SINGLETONS)

    def __init__(self):
        self.type_dict['str'] = str

    def get_dispatch_types(self, fnty, xirty):
        return [fnty[0]] + [self.type_dict[x] for x in fnty[1:]]

    @singledispatchmethod
    def MIN(self, aty, bty):
        raise NotImplementedError(f"MIN({aty}, {bty}) not implemented.")

    @MIN.register(c_float)
    def _(self, aty: c_float, bty: c_float):
        return FnCall("fminf_ptx", 2)

    @MIN.register(double)
    def _(self, aty: double, bty: double):
        return FnCall("fmin_ptx", 2)

    @MIN.register(CBasicType)
    def _(self, aty: CBasicType, bty: CBasicType):
        return FnCall("MIN", 2)

    # TODO: get rid of this and replace it with MIN
    @singledispatchmethod
    def min(self, aty, bty):
        raise NotImplementedError(f"min({aty}, {bty}) not implemented.")

    @min.register(CBasicType)
    def _(self, aty: CBasicType, bty: CBasicType):
        return FnCall("MIN", 2)

    @singledispatchmethod
    def MAX(self, aty, bty):
        raise NotImplementedError(f"MAX({aty}, {bty}) not implemented.")

    @MAX.register(c_float)
    def _(self, aty: c_float, bty: c_float):
        return FnCall("fmaxf_ptx", 2)

    @MAX.register(double)
    def _(self, aty: double, bty: double):
        return FnCall("fmax_ptx", 2)

    @MAX.register(CBasicType)
    def _(self, aty: CBasicType, bty: CBasicType):
        return FnCall("MAX", 2)

    @singledispatchmethod
    def SAR(self, aty, bty):
        raise NotImplementedError(f"SAR({aty}, {bty}) not implemented.")

    @SAR.register(CSigned)
    def _(self, aty: CSigned, bty: uint32_t):
        # dispatch on second argument doesn't quite mimic '*', '*'
        # TODO: eliminate >>?
        if isinstance(bty, uint32_t):
            return FnCall("SHR", 2)
        else:
            return BinOpInfix(">>")

    # this mimics the original dictionary, but makes little sense?
    @SAR.register(CBasicType)
    def _(self, aty: CBasicType, bty: CBasicType):
        return BinOpInfix(">>")

    SAR_LIT = SAR

    @singledispatchmethod
    def SHR_LIT(self, aty, bty):
        raise NotImplementedError(f"SHR_LIT({aty}, {bty}) not implemented.")

    @SHR_LIT.register(CUnsigned)
    def _(self, aty: CUnsigned, bty: uint32_t):
        # does the same as SHR, though why?
        if isinstance(bty, uint32_t):
            return FnCall("SHR", 2)
        else:
            return BinOpInfix(">>")

    @SHR_LIT.register(CBasicType)
    def _(self, aty: CBasicType, bty: CBasicType):
        return BinOpInfix(">>")

    @singledispatchmethod
    def SHL_LIT(self, aty, bty):
        raise NotImplementedError(f"SHL_LIT({aty}, {bty}) not implemented.")

    @SHL_LIT.register(CUnsigned)
    def _(self, aty: CUnsigned, bty: uint32_t):
        # dispatch on second argument doesn't quite mimic '*', '*'
        # TODO: eliminate >>?
        if isinstance(bty, uint32_t):
            return FnCall("SHL", 2)
        else:
            return BinOpInfix("<<")

    @SHL_LIT.register(CBasicType)
    def _(self, aty: CBasicType, bty: CBasicType):
        return BinOpInfix("<<")

    @singledispatchmethod
    def LOG2(self, aty):
        raise NotImplementedError(f"LOG2({aty}) not implemented.")

    # use CFP since C files use _Generic to dispatch
    @LOG2.register(CFP)
    def _(self, aty: CFP):
        return FnCall("LOG2", 1)

    @singledispatchmethod
    def FTZ(self, aty):
        raise NotImplementedError(f"FTZ({aty}) not implemented.")

    # use CFP since C files use _Generic to dispatch
    @FTZ.register(CFP)
    def _(self, aty: CFP):
        return FnCall("FTZ", 1)

    @singledispatchmethod
    def SINE(self, aty):
        raise NotImplementedError(f"SINE({aty}) not implemented.")

    # use CFP since C files use _Generic to dispatch
    @SINE.register(CFP)
    def _(self, aty: CFP):
        return FnCall("SINE", 1)

    @singledispatchmethod
    def COSINE(self, aty):
        raise NotImplementedError(f"COSINE({aty}) not implemented.")

    # use CFP since C files use _Generic to dispatch
    @COSINE.register(CFP)
    def _(self, aty: CFP):
        return FnCall("COSINE", 1)

    @singledispatchmethod
    def COPYSIGN(self, aty):
        raise NotImplementedError(f"COPYSIGN({aty}) not implemented.")

    # use CFP since C files use _Generic to dispatch
    @COPYSIGN.register(CFP)
    def _(self, aty: CFP):
        return FnCall("COPYSIGN", 1)

    @singledispatchmethod
    def SQRT(self, aty):
        raise NotImplementedError(f"SQRT({aty}) not implemented.")

    @SQRT.register(c_float)
    def _(self, aty: c_float):
        return FnCall("sqrtf", 1)

    @SQRT.register(double)
    def _(self, aty: double):
        return FnCall("sqrt", 1)

    @singledispatchmethod
    def ABSOLUTE(self, aty):
        raise NotImplementedError(f"ABSOLUTE({aty}) not implemented.")

    @ABSOLUTE.register(c_float)
    def _(self, aty: c_float):
        return FnCall("fabsf", 1)

    @ABSOLUTE.register(double)
    def _(self, aty: double):
        return FnCall("fabs", 1)

    @ABSOLUTE.register(int32_t)
    def _(self, aty: int32_t):
        return FnCall("abs", 1)

    @ABSOLUTE.register(int64_t)
    def _(self, aty: int64_t):
        return FnCall("labs", 1) # depends on 64-bit model!

    @ABSOLUTE.register(int16_t)
    def _(self, aty: int16_t):
        return FnCall("abs", 1)

    @singledispatchmethod
    def POW(self, aty, bty):
        raise NotImplementedError(f"POW({aty}, {bty}) not implemented.")

    @POW.register(c_float)
    def _(self, aty: c_float, bty: c_float):
        return FnCall("powf", 2)

    @POW.register(double)
    def _(self, aty: double, bty: double):
        return FnCall("pow", 2)

    @singledispatchmethod
    def FMA(self, aty, bty, cty):
        raise NotImplementedError(f"FMA({aty}, {bty}, {cty}) not implemented.")

    @FMA.register(CFP)
    def _(self, aty: CFP, bty: CFP, cty: CFP):
        return FnCall("FMA", 3)

    @singledispatchmethod
    def ADD_ROUND(self, aty, bty, rty):
        raise NotImplementedError(f"ADD_ROUND({aty}, {bty}, {rty}) not implemented.")

    @ADD_ROUND.register(CFP)
    def _(self, aty: CFP, bty: CFP, rty: str):
        return RoundedFnCall("ADD_ROUND", 3)

    @singledispatchmethod
    def MUL_ROUND(self, aty, bty, rty):
        raise NotImplementedError(f"MUL_ROUND({aty}, {bty}, {rty}) not implemented.")

    @MUL_ROUND.register(CFP)
    def _(self, aty: CFP, bty: CFP, rty: str):
        return RoundedFnCall("MUL_ROUND", 3)

    @singledispatchmethod
    def SUB_ROUND(self, aty, bty, rty):
        raise NotImplementedError(f"SUB_ROUND({aty}, {bty}, {rty}) not implemented.")

    @SUB_ROUND.register(CFP)
    def _(self, aty: CFP, bty: CFP, rty: str):
        return RoundedFnCall("SUB_ROUND", 3)

    @singledispatchmethod
    def DIV_ROUND(self, aty, bty, rty):
        raise NotImplementedError(f"DIV_ROUND({aty}, {bty}, {rty}) not implemented.")

    @DIV_ROUND.register(CFP)
    def _(self, aty: CFP, bty: CFP, rty: str):
        return RoundedFnCall("DIV_ROUND", 3)

    @singledispatchmethod
    def FMA_ROUND(self, aty, bty, cty, rty):
        raise NotImplementedError(f"FMA_ROUND({aty}, {bty}, {cty}, {rty}) not implemented.")

    @FMA_ROUND.register(CFP)
    def _(self, aty: CFP, bty: CFP, cty: CFP, rty: str):
        return RoundedFnCall("FMA_ROUND", 4)

    @singledispatchmethod
    def RCP_ROUND(self, aty, rty):
        raise NotImplementedError(f"RCP_ROUND({aty}, {rty}) not implemented.")

    @RCP_ROUND.register(CFP)
    def _(self, aty: CFP, rty: str):
        return RoundedFnCall("RCP_ROUND", 2)

    @singledispatchmethod
    def SQRT_ROUND(self, aty, rty):
        raise NotImplementedError(f"SQRT_ROUND({aty}, {rty}) not implemented.")

    @SQRT_ROUND.register(CFP)
    def _(self, aty: CFP, rty: str):
        return RoundedFnCall("SQRT_ROUND", 2)

    @singledispatchmethod
    def MACHINE_SPECIFIC_execute_rem_divide_by_zero_unsigned(self, aty):
        raise NotImplementedError(f"MACHINE_SPECIFIC_execute_rem_divide_by_zero_unsigned({aty}) not implemented")

    @MACHINE_SPECIFIC_execute_rem_divide_by_zero_unsigned.register(CUnsigned)
    def _(self, aty: CUnsigned):
        return FnCall('', 1)

    @singledispatchmethod
    def MACHINE_SPECIFIC_execute_rem_divide_by_neg(self, aty, bty):
        raise NotImplementedError(f"MACHINE_SPECIFIC_execute_rem_divide_by_neg({aty}, {bty}) not implemented")

    # should be CInteger?/CSigned?
    @MACHINE_SPECIFIC_execute_rem_divide_by_neg.register(CBasicType)
    def _(self, aty: CBasicType, bty: CBasicType):
        return FnCall('MACHINE_SPECIFIC_execute_rem_divide_by_neg', 2)

    @singledispatchmethod
    def MACHINE_SPECIFIC_execute_div_divide_by_zero_integer(self, aty):
        raise NotImplementedError(f"MACHINE_SPECIFIC_execute_div_divide_by_zero_integer({aty}) not implemented")

    @MACHINE_SPECIFIC_execute_div_divide_by_zero_integer.register(CInteger)
    def _(self, aty: CInteger):
        atyn = aty.__class__.__name__

        # returned the negated unsigned 0
        if isinstance(aty, CUnsigned):
            return lambda _: f"~(({atyn}) 0)"
        else:
            return lambda _: f"~((u{atyn}) 0)"

    @singledispatchmethod
    def zext_64(self, aty):
        raise NotImplementedError(f"zext_64({aty}) not implemented.")

    @zext_64.register(CInteger)
    def _(self, aty: uint64_t):
        return CastOp('uint64_t')

    @singledispatchmethod
    def sext_64(self, aty):
        raise NotImplementedError(f"sext_64({aty}) not implemented.")

    @sext_64.register(CInteger)
    def _(self, aty: CInteger):
        return CastOp('int64_t')

    @singledispatchmethod
    def sext_32(self, aty):
        raise NotImplementedError(f"sext_32({aty}) not implemented.")

    @sext_32.register(CInteger)
    def _(self, aty: CInteger):
        return CastOp('int32_t')

    @singledispatchmethod
    def sext_16(self, aty):
        raise NotImplementedError(f"sext_16({aty}) not implemented.")

    @sext_16.register(CInteger)
    def _(self, aty: CInteger):
        return CastOp('int16_t')

    @singledispatchmethod
    def truncate_64(self, aty):
        raise NotImplementedError(f"truncate_64({aty}) not implemented.")

    @truncate_64.register(CInteger)
    def _(self, aty: CInteger):
        return CastOp('uint64_t')

    @singledispatchmethod
    def truncate_32(self, aty):
        raise NotImplementedError(f"truncate_32({aty}) not implemented.")

    @truncate_32.register(CInteger)
    def _(self, aty: CInteger):
        return CastOp('uint32_t')

    @singledispatchmethod
    def truncate_16(self, aty):
        raise NotImplementedError(f"truncate_16({aty}) not implemented.")

    @truncate_16.register(CInteger)
    def _(self, aty: CInteger):
        return CastOp('uint16_t')

    def _float_cmp(self, fn):
        tmp = fn(CBasicType(), CBasicType())
        # TODO: paren
        return lambda x, y: f"(!(isnan({x}) || isnan({y}))) && {tmp(x, y)}"

    def _float_cmp_unordered(self, fn):
        tmp = fn(CBasicType(), CBasicType())
        return lambda x, y: f"isnan({x}) || isnan({y}) || {tmp(x, y)}"

    @singledispatchmethod
    def compare_eq(self, aty, bty):
        raise NotImplementedError(f"compare_eq({aty}, {bty}) not implemented.")

    @compare_eq.register(CFP)
    def _(self, aty: CFP, bty: CFP):
        return self._float_cmp(self.compare_eq)

    @compare_eq.register(CBasicType)
    def _(self, aty: CBasicType, bty: CBasicType):
        return BinOpInfix('==')

    @singledispatchmethod
    def compare_equ(self, aty, bty):
        raise NotImplementedError(f"compare_equ({aty}, {bty}) not implemented.")

    @compare_equ.register(CFP)
    def _(self, aty: CFP, bty: CFP):
        return self._float_cmp_unordered(self.compare_eq)

    @singledispatchmethod
    def compare_ne(self, aty, bty):
        raise NotImplementedError(f"compare_ne({aty}, {bty}) not implemented.")

    @compare_ne.register(CFP)
    def _(self, aty: CFP, bty: CFP):
        return self._float_cmp(self.compare_ne)

    @compare_ne.register(CBasicType)
    def _(self, aty: CBasicType, bty: CBasicType):
        return BinOpInfix('!=')

    @singledispatchmethod
    def compare_neu(self, aty, bty):
        raise NotImplementedError(f"compare_neu({aty}, {bty}) not implemented.")

    @compare_neu.register(CFP)
    def _(self, aty: CFP, bty: CFP):
        return self._float_cmp_unordered(self.compare_ne)

    @singledispatchmethod
    def compare_lt(self, aty, bty):
        raise NotImplementedError(f"compare_lt({aty}, {bty}) not implemented.")

    @compare_lt.register(CFP)
    def _(self, aty: CFP, bty: CFP):
        return self._float_cmp(self.compare_lt)

    @compare_lt.register(CBasicType)
    def _(self, aty: CBasicType, bty: CBasicType):
        return BinOpInfix('<')

    @singledispatchmethod
    def compare_ltu(self, aty, bty):
        raise NotImplementedError(f"compare_ltu({aty}, {bty}) not implemented.")

    @compare_ltu.register(CFP)
    def _(self, aty: CFP, bty: CFP):
        return self._float_cmp_unordered(self.compare_lt)

    @singledispatchmethod
    def compare_le(self, aty, bty):
        raise NotImplementedError(f"compare_le({aty}, {bty}) not implemented.")

    @compare_le.register(CFP)
    def _(self, aty: CFP, bty: CFP):
        return self._float_cmp(self.compare_le)

    @compare_le.register(CBasicType)
    def _(self, aty: CBasicType, bty: CBasicType):
        return BinOpInfix('<=')

    @singledispatchmethod
    def compare_leu(self, aty, bty):
        raise NotImplementedError(f"compare_leu({aty}, {bty}) not implemented.")

    @compare_leu.register(CFP)
    def _(self, aty: CFP, bty: CFP):
        return self._float_cmp_unordered(self.compare_le)

    @singledispatchmethod
    def compare_gt(self, aty, bty):
        raise NotImplementedError(f"compare_gt({aty}, {bty}) not implemented.")

    @compare_gt.register(CFP)
    def _(self, aty: CFP, bty: CFP):
        return self._float_cmp(self.compare_gt)

    @compare_gt.register(CBasicType)
    def _(self, aty: CBasicType, bty: CBasicType):
        return BinOpInfix('>')

    @singledispatchmethod
    def compare_gtu(self, aty, bty):
        raise NotImplementedError(f"compare_gtu({aty}, {bty}) not implemented.")

    @compare_gtu.register(CFP)
    def _(self, aty: CFP, bty: CFP):
        return self._float_cmp_unordered(self.compare_gt)

    @singledispatchmethod
    def compare_ge(self, aty, bty):
        raise NotImplementedError(f"compare_ge({aty}, {bty}) not implemented.")

    @compare_ge.register(CFP)
    def _(self, aty: CFP, bty: CFP):
        return self._float_cmp(self.compare_ge)

    @compare_ge.register(CBasicType)
    def _(self, aty: CBasicType, bty: CBasicType):
        return BinOpInfix('>=')

    @singledispatchmethod
    def compare_geu(self, aty, bty):
        raise NotImplementedError(f"compare_geu({aty}, {bty}) not implemented.")

    @compare_geu.register(CFP)
    def _(self, aty: CFP, bty: CFP):
        return self._float_cmp_unordered(self.compare_ge)

    @singledispatchmethod
    def compare_lo(self, aty, bty):
        raise NotImplementedError(f"compare_lo({aty}, {bty}) not implemented.")

    @compare_lo.register(CUnsigned)
    def _(self, aty: CUnsigned, bty: CUnsigned):
        return BinOpInfix('<')

    @singledispatchmethod
    def compare_ls(self, aty, bty):
        raise NotImplementedError(f"compare_ls({aty}, {bty}) not implemented.")

    @compare_ls.register(CUnsigned)
    def _(self, aty: CUnsigned, bty: CUnsigned):
        return BinOpInfix('<=')

    @singledispatchmethod
    def compare_hi(self, aty, bty):
        raise NotImplementedError(f"compare_hi({aty}, {bty}) not implemented.")

    @compare_hi.register(CUnsigned)
    def _(self, aty: CUnsigned, bty: CUnsigned):
        return BinOpInfix('>')

    @singledispatchmethod
    def compare_hs(self, aty, bty):
        raise NotImplementedError(f"compare_hs({aty}, {bty}) not implemented.")

    @compare_hs.register(CUnsigned)
    def _(self, aty: CUnsigned, bty: CUnsigned):
        return BinOpInfix('>=')

    @singledispatchmethod
    def compare_num(self, aty, bty):
        raise NotImplementedError(f"compare_num({aty}, {bty}) not implemented.")

    @compare_num.register(CFP)
    def _(self, aty: CFP, bty: CFP):
        return lambda x, y: f"!(isnan({x}) || isnan({y}))"

    @singledispatchmethod
    def compare_nan(self, aty, bty):
        raise NotImplementedError(f"compare_nan({aty}, {bty}) not implemented.")

    @compare_nan.register(CFP)
    def _(self, aty: CFP, bty: CFP):
        return lambda x, y: f"(isnan({x}) || isnan({y}))"

    def _fp_sat(self, fn):
        return lambda *args: f"SATURATE({fn(*args)})"

    @singledispatchmethod
    def ADD_SATURATE(self, aty, bty):
        raise NotImplementedError(f'ADD_SATURATE({aty}, {bty}) not implemented.')

    @ADD_SATURATE.register(CFP)
    def _(self, aty: CFP, bty: CFP):
        return self._fp_sat(BinOpInfix("+"))

    @ADD_SATURATE.register(int32_t)
    def _(self, aty: int32_t, bty: int32_t):
        return FnCall('ADD_SATURATE_s32', 2)

    @singledispatchmethod
    def SUB_SATURATE(self, aty, bty):
        raise NotImplementedError(f'SUB_SATURATE({aty}, {bty}) not implemented.')

    @SUB_SATURATE.register(CFP)
    def _(self, aty: CFP, bty: CFP):
        return self._fp_sat(BinOpInfix("-"))

    @SUB_SATURATE.register(int32_t)
    def _(self, aty: int32_t, bty: int32_t):
        return FnCall('SUB_SATURATE_s32', 2)

    @singledispatchmethod
    def MUL_SATURATE(self, aty, bty):
        raise NotImplementedError(f'MUL_SATURATE({aty}, {bty}) not implemented.')

    @MUL_SATURATE.register(CFP)
    def _(self, aty: CFP, bty: CFP):
        return self._fp_sat(BinOpInfix("*"))

    # there is no integer version of mul saturate

    @singledispatchmethod
    def ADD_ROUND_SATURATE(self, aty, bty, rty):
        raise NotImplementedError(f'ADD_ROUND_SATURATE({aty}, {bty}, {rty}) not implemented.')

    @ADD_ROUND_SATURATE.register(CFP)
    def _(self, aty: CFP, bty: CFP, rty: str):
        return self._fp_sat(self.ADD_ROUND(aty, bty, rty))

    @singledispatchmethod
    def SUB_ROUND_SATURATE(self, aty, bty, rty):
        raise NotImplementedError(f'SUB_ROUND_SATURATE({aty}, {bty}, {rty}) not implemented.')

    @SUB_ROUND_SATURATE.register(CFP)
    def _(self, aty: CFP, bty: CFP, rty: str):
        return self._fp_sat(self.SUB_ROUND(aty, bty, rty))

    @singledispatchmethod
    def MUL_ROUND_SATURATE(self, aty, bty, rty):
        raise NotImplementedError(f'MUL_ROUND_SATURATE({aty}, {bty}, {rty}) not implemented.')

    @MUL_ROUND_SATURATE.register(CFP)
    def _(self, aty: CFP, bty: CFP, rty: str):
        return self._fp_sat(self.MUL_ROUND(aty, bty, rty))

    @singledispatchmethod
    def FMA_ROUND_SATURATE(self, aty, bty, cty, rty):
        raise NotImplementedError(f'FMA_ROUND_SATURATE({aty}, {bty}, {cty}, {rty}) not implemented.')

    @FMA_ROUND_SATURATE.register(CFP)
    def _(self, aty: CFP, bty: CFP, cty: CFP, rty: str):
        return self._fp_sat(self.FMA_ROUND(aty, bty, cty, rty))

    @singledispatchmethod
    def logical_op3(self, aty, bty, cty, imm):
        raise NotImplementedError(f'logical_op3({aty}, {bty}, {cty}, {imm}) not implemented.')

    @logical_op3.register(uint32_t)
    def _(self, aty: uint32_t, bty: uint32_t, cty: uint32_t, imm: uint8_t):
        return FnCall('logical_op3', 4)

    @singledispatchmethod
    def ISNAN(self, aty):
        raise NotImplementedError(f'ISNAN({aty}) not implemented.')

    @ISNAN.register(CFP)
    def _(self, aty: CFP):
        return FnCall('isnan', 1)

    @singledispatchmethod
    def subnormal_check(self, aty):
        raise NotImplementedError(f'subnormal_check({aty}) not implemented.')

    @subnormal_check.register(CFP)
    def _(self, aty: CFP):
        return lambda a: f"(fpclassify({a}) == FP_SUBNORMAL)"

def get_libs(backend):
    assert backend == "c", f"Don't support backend {backend} for ptxlibc"

    return [PTXLibC()]

try:
    from functools import singledispatchmethod # 3.8+
except ImportError:
    from singledispatchmethod import singledispatchmethod

from xlatir.xir.xirlib import XIRLib
from xlatir.xir.xirlibsmt2 import SMT2BasicType, SMT2Float, SINGLETONS, Signed, Unsigned, BV, u64, u32, u16, u8, f64, f32, s32, s64, s16, BinOp, UnOp, bool_to_pred, pred_to_bool, b1, do_SHIFT, BoolBinOp, FPBinOp
from xlatir.smt2ast import *

from ptxlib import PTXLib

carryflag = b1

ROUND_MODES_SMT2 = {'rp': 'RTP', # positive inf
                    'rm': 'RTN', # negative inf
                    'rz': 'RTZ', # zero
                    'rn': 'RNE'} # nearest even, no support in PTX for RNA


def extract_cf(x):
    # actually do a proper type check on x?
    return SExprList(SExprList(Symbol("_"), Symbol("extract"), Decimal(0), Decimal(0)), x)

def RCP(ty, x, rm = Symbol('rn')):
    if isinstance(ty, f32):
        exp = 8
        signi = 24
    elif isinstance(ty, f64):
        exp = 11
        signi = 53
    else:
        raise NotImplementedError(f"Unknown type for rcp {ty}")

    return SExprList(Symbol("fp.div"),
                     Symbol(ROUND_MODES_SMT2[rm.v]),
                     SExprList(SExprList(Symbol("_"), Symbol("to_fp"), Decimal(exp), Decimal(signi)),
                               Symbol(ROUND_MODES_SMT2['rn']),
                               Hexadecimal(1, width=(exp+signi)//4)),
                     x)

def generic_round(fn, nargs):
    if nargs == 1:
        return lambda x, m: SExprList(Symbol(fn), Symbol(ROUND_MODES_SMT2[m.v]), x)
    elif nargs == 2:
        return lambda x, y, m: SExprList(Symbol(fn), Symbol(ROUND_MODES_SMT2[m.v]), x, y)
    elif nargs == 3:
        return lambda x, y, z, m: SExprList(Symbol(fn), Symbol(ROUND_MODES_SMT2[m.v]), x, y, z)
    else:
        raise NotImplementedError(f"nargs={nargs} not implemented")

class PTXLibSMT2(PTXLib):
    type_dict = dict(SINGLETONS)

    def __init__(self):
        self.type_dict['carryflag'] = self.type_dict['b1'] # used for carryflag
        self.type_dict['str'] = str # used for rounding mode

    def get_dispatch_types(self, fnty, xirty):
        return [fnty[0]] + [self.type_dict[str(x)] for x in fnty[1:]]

    @singledispatchmethod
    def MIN(self, aty, bty):
        raise NotImplementedError(f"MIN({aty}, {bty}) not implemented.")

    @MIN.register(f32)
    def _(self, aty: f32, bty: f32):
        return BinOp("MIN_f32")

    @MIN.register(f64)
    def _(self, aty: f64, bty: f64):
        return BinOp("MIN_f64")

    @MIN.register(Unsigned)
    def _(self, aty: Unsigned, bty: Unsigned):
        return lambda x, y: SExprList(Symbol("ite"), SExprList(Symbol("bvult"), x, y), x, y)

    @MIN.register(Signed)
    def _(self, aty: Signed, bty: Signed):
        return lambda x, y: SExprList(Symbol("ite"), SExprList(Symbol("bvslt"), x, y), x, y)

    def min(self, aty, bty):
        return self.MIN(aty, bty)


    @singledispatchmethod
    def MAX(self, aty, bty):
        raise NotImplementedError(f"MAX({aty}, {bty}) not implemented.")

    @MAX.register(f32)
    def _(self, aty: f32, bty: f32):
        return BinOp("MAX_f32")

    @MAX.register(f64)
    def _(self, aty: f64, bty: f64):
        return BinOp("MAX_f64")

    @MAX.register(Signed)
    def _(self, aty: Signed, bty: Signed):
        return lambda x, y: SExprList(Symbol("ite"), SExprList(Symbol("bvslt"), x, y), y, x)

    @MAX.register(Unsigned)
    def _(self, aty: Unsigned, bty: Unsigned):
        return lambda x, y: SExprList(Symbol("ite"), SExprList(Symbol("bvult"), x, y), y, x)

    @singledispatchmethod
    def SAR(self, aty, bty):
        raise NotImplementedError(f"SAR({aty}, {bty}) not implemented.")

    @SAR.register(BV)
    def _(self, aty: BV, bty: BV):
        return do_SHIFT(aty, bty, BinOp("bvashr"))

    SAR_LIT = SAR

    @singledispatchmethod
    def SHR_LIT(self, aty, bty):
        raise NotImplementedError(f"SHR_LIT({aty}, {bty}) not implemented.")

    @SHR_LIT.register(Unsigned)
    def _(self, aty: Unsigned, bty: BV):
        return do_SHIFT(aty, bty, BinOp("bvlshr"))

    @SHR_LIT.register(Signed)
    def _(self, aty: Signed, bty: BV):
        return do_SHIFT(aty, bty, BinOp("bvashr"))

    @singledispatchmethod
    def SHL_LIT(self, aty, bty):
        raise NotImplementedError(f"SHL_LIT({aty}, {bty}) not implemented.")

    @SHL_LIT.register(BV)
    def _(self, aty: BV, bty: BV):
        return do_SHIFT(aty, bty, BinOp("bvshl"))


    @singledispatchmethod
    def LOG2(self, aty):
        raise NotImplementedError(f"LOG2({aty}) not implemented.")

    # use SMT2Float since C files use _Generic to dispatch
    @LOG2.register(SMT2Float)
    def _(self, aty: SMT2Float):
        return FnCall(f"log2_f{aty.w}", 1)

    @singledispatchmethod
    def FTZ(self, aty):
        raise NotImplementedError(f"FTZ({aty}) not implemented.")

    # use SMT2Float since C files use _Generic to dispatch
    @FTZ.register(SMT2Float)
    def _(self, aty: SMT2Float):
        return FnCall("FTZ", 1)

    @singledispatchmethod
    def SINE(self, aty):
        raise NotImplementedError(f"SINE({aty}) not implemented.")

    # use SMT2Float since C files use _Generic to dispatch
    @SINE.register(SMT2Float)
    def _(self, aty: SMT2Float):
        return UnOp(f"sin_f{aty.w}")

    @singledispatchmethod
    def COSINE(self, aty):
        raise NotImplementedError(f"COSINE({aty}) not implemented.")

    # use SMT2Float since C files use _Generic to dispatch
    @COSINE.register(SMT2Float)
    def _(self, aty: SMT2Float):
        return UnOp(f"cos_f{aty.w}")

    @singledispatchmethod
    def COPYSIGN(self, aty, bty):
        raise NotImplementedError(f"COPYSIGN({aty}, {bty}) not implemented.")

    # use SMT2Float since C files use _Generic to dispatch
    @COPYSIGN.register(SMT2Float)
    def _(self, aty: SMT2Float, bty: SMT2Float):
        return BinOp(f"copysign_f{aty.w}")

    @singledispatchmethod
    def SQRT(self, aty):
        raise NotImplementedError(f"SQRT({aty}) not implemented.")

    @SQRT.register(f32)
    def _(self, aty: f32):
        return UnOp(f"sqrt_f32")

    @SQRT.register(f64)
    def _(self, aty: f64):
        return UnOp("sqrt_f64")

    @singledispatchmethod
    def ABSOLUTE(self, aty):
        raise NotImplementedError(f"ABSOLUTE({aty}) not implemented.")

    @ABSOLUTE.register(SMT2Float)
    def _(self, aty: SMT2Float):
        return UnOp("fp.abs")

    @ABSOLUTE.register(Signed)
    def _(self, aty: Signed):
        return UnOp(f"abs_s{aty.w}")

    @singledispatchmethod
    def POW(self, aty, bty):
        raise NotImplementedError(f"POW({aty}, {bty}) not implemented.")

    @POW.register(f32)
    def _(self, aty: f32, bty: f32):
        return FnCall("powf", 2)

    @POW.register(f64)
    def _(self, aty: f64, bty: f64):
        return FnCall("pow", 2)

    @singledispatchmethod
    def FMA(self, aty, bty, cty):
        raise NotImplementedError(f"FMA({aty}, {bty}, {cty}) not implemented.")

    @FMA.register(SMT2Float)
    def _(self, aty: SMT2Float, bty: SMT2Float, cty: SMT2Float):
        return FnCall("FMA", 3)

    @singledispatchmethod
    def ADD_ROUND(self, aty, bty, rty):
        raise NotImplementedError(f"ADD_ROUND({aty}, {bty}, {rty}) not implemented.")

    @ADD_ROUND.register(SMT2Float)
    def _(self, aty: SMT2Float, bty: SMT2Float, rty: str):
        return generic_round("fp.add", 2)

    @singledispatchmethod
    def MUL_ROUND(self, aty, bty, rty):
        raise NotImplementedError(f"MUL_ROUND({aty}, {bty}, {rty}) not implemented.")

    @MUL_ROUND.register(SMT2Float)
    def _(self, aty: SMT2Float, bty: SMT2Float, rty: str):
        return generic_round("fp.mul", 2)

    @singledispatchmethod
    def SUB_ROUND(self, aty, bty, rty):
        raise NotImplementedError(f"SUB_ROUND({aty}, {bty}, {rty}) not implemented.")

    @SUB_ROUND.register(SMT2Float)
    def _(self, aty: SMT2Float, bty: SMT2Float, rty: str):
        return generic_round("fp.sub", 2)

    @singledispatchmethod
    def DIV_ROUND(self, aty, bty, rty):
        raise NotImplementedError(f"DIV_ROUND({aty}, {bty}, {rty}) not implemented.")

    @DIV_ROUND.register(SMT2Float)
    def _(self, aty: SMT2Float, bty: SMT2Float, rty: str):
        return generic_round("fp.div", 2)

    @singledispatchmethod
    def FMA_ROUND(self, aty, bty, cty, rty):
        raise NotImplementedError(f"FMA_ROUND({aty}, {bty}, {cty}, {rty}) not implemented.")

    @FMA_ROUND.register(SMT2Float)
    def _(self, aty: SMT2Float, bty: SMT2Float, cty: SMT2Float, rty: str):
        return generic_round("fp.fma", 3)

    @singledispatchmethod
    def RCP_ROUND(self, aty, rty):
        raise NotImplementedError(f"RCP_ROUND({aty}, {rty}) not implemented.")

    @RCP_ROUND.register(SMT2Float)
    def _(self, aty: SMT2Float, rty: str):
        return lambda x, m: RCP(aty, x, m)

    @singledispatchmethod
    def SQRT_ROUND(self, aty, rty):
        raise NotImplementedError(f"SQRT_ROUND({aty}, {rty}) not implemented.")

    @SQRT_ROUND.register(SMT2Float)
    def _(self, aty: SMT2Float, rty: str):
        return generic_round(f"sqrt_round_f{aty.w}", 1)

    @singledispatchmethod
    def MACHINE_SPECIFIC_execute_rem_divide_by_zero_unsigned(self, aty):
        raise NotImplementedError(f"MACHINE_SPECIFIC_execute_rem_divide_by_zero_unsigned({aty}) not implemented")

    @MACHINE_SPECIFIC_execute_rem_divide_by_zero_unsigned.register(Unsigned)
    def _(self, aty: Unsigned):
        return lambda x: x

    @singledispatchmethod
    def MACHINE_SPECIFIC_execute_rem_divide_by_neg(self, aty, bty):
        raise NotImplementedError(f"MACHINE_SPECIFIC_execute_rem_divide_by_neg({aty}, {bty}) not implemented")

    @MACHINE_SPECIFIC_execute_rem_divide_by_neg.register(Signed)
    def _(self, aty: Signed, bty: Signed):
        return lambda x, y: SExprList(Symbol("bvsrem"), x, SExprList(Symbol("bvneg"), y))

    @singledispatchmethod
    def MACHINE_SPECIFIC_execute_div_divide_by_zero_integer(self, aty):
        raise NotImplementedError(f"MACHINE_SPECIFIC_execute_div_divide_by_zero_integer({aty}) not implemented")

    @MACHINE_SPECIFIC_execute_div_divide_by_zero_integer.register(BV)
    def _(self, aty: BV):
        # note, despite _uX, this is used for signed as well (for convenience)
        return lambda _: Symbol(f"MACHINE_SPECIFIC_execute_div_divide_by_zero_integer_u{aty.w}")

    @singledispatchmethod
    def zext_64(self, aty):
        raise NotImplementedError(f"zext_64({aty}) not implemented.")

    @zext_64.register(BV)
    def _(self, aty: BV):
        return lambda x: SExprList(SExprList(Symbol('_'),
                                             Symbol('zero_extend'),
                                             Decimal(64 - aty.w)), x)

    @singledispatchmethod
    def sext_64(self, aty):
        raise NotImplementedError(f"sext_64({aty}) not implemented.")

    @sext_64.register(BV)
    def _(self, aty: BV):
        return CastOp('s64')

    @singledispatchmethod
    def sext_32(self, aty):
        raise NotImplementedError(f"sext_32({aty}) not implemented.")

    @sext_32.register(BV)
    def _(self, aty: BV):
        return CastOp('s32')

    @singledispatchmethod
    def sext_16(self, aty):
        raise NotImplementedError(f"sext_16({aty}) not implemented.")

    @sext_16.register(BV)
    def _(self, aty: BV):
        return CastOp('s16')

    @singledispatchmethod
    def truncate_64(self, aty):
        raise NotImplementedError(f"truncate_64({aty}) not implemented.")

    @truncate_64.register(BV)
    def _(self, aty: BV):
        return CastOp('u64')

    @singledispatchmethod
    def truncate_32(self, aty):
        raise NotImplementedError(f"truncate_32({aty}) not implemented.")

    @truncate_32.register(BV)
    def _(self, aty: BV):
        return CastOp('u32')

    @singledispatchmethod
    def truncate_16(self, aty):
        raise NotImplementedError(f"truncate_16({aty}) not implemented.")

    @truncate_16.register(BV)
    def _(self, aty: BV):
        return CastOp('u16')

    def _do_compare_2(self, op, aty, bty):
        if op in ('lt', 'le', 'gt', 'ge'):
            assert type(aty) == type(bty), f"Incorrect type signature for compare {op}({aty},{bty})"
            if isinstance(aty, Unsigned):
                op = "bvu" + op
            elif isinstance(aty, Signed):
                op = "bvs" + op
            elif isinstance(aty, SMT2Float):
                op = "fp." + op
                if op in ("fp.le", "fp.ge"): op += "q" # le -> leq, ge -> geq
        elif op in ('lo', 'ls', 'hi', 'hs'):
            #TODO: type check?
            xlat = {'lo': 'lt', 'ls': 'le', 'hi': 'gt', 'hs': 'ge'}
            op = "bvu" + xlat[op]
        else:
            raise NotImplementedError(f"Unknown comparison operator {op}")

        # this is a bool binop
        return lambda x, y: bool_to_pred(SExprList(Symbol(op), x, y))

    def _do_compare_unordered(self, op, aty, bty, ofn):
        assert op[-1] == 'u' # unordered

        orig_fn = ofn(aty, bty)
        opfn = lambda x, y: orig_fn(x, y).v[1] # strip the bool_to_pred

        return lambda x, y: bool_to_pred(SExprList(Symbol("or"),
                                                   SExprList(Symbol("fp.isNaN"), x),
                                                   SExprList(Symbol("fp.isNaN"), y),
                                                   opfn(x, y)))

    @singledispatchmethod
    def compare_eq(self, aty, bty):
        raise NotImplementedError(f"compare_eq({aty}, {bty}) not implemented.")

    @compare_eq.register(SMT2Float)
    def _(self, aty: SMT2Float, bty: SMT2Float):
        return BoolBinOp('fp.eq')

    @compare_eq.register(SMT2BasicType)
    def _(self, aty: SMT2BasicType, bty: SMT2BasicType):
        return BoolBinOp('=')

    @singledispatchmethod
    def compare_equ(self, aty, bty):
        raise NotImplementedError(f"compare_equ({aty}, {bty}) not implemented.")

    @compare_equ.register(SMT2Float)
    def _(self, aty: SMT2Float, bty: SMT2Float):
        return self._do_compare_unordered('equ', aty, bty, self.compare_eq)

    @singledispatchmethod
    def compare_ne(self, aty, bty):
        raise NotImplementedError(f"compare_ne({aty}, {bty}) not implemented.")

    @compare_ne.register(SMT2Float)
    def _(self, aty: SMT2Float, bty: SMT2Float):
        return lambda x, y: bool_to_pred(SExprList(Symbol("and"),
                                                   SExprList(Symbol("not"),
                                                             SExprList(Symbol("or"),
                                                                       SExprList(Symbol("fp.isNaN"), x),
                                                                       SExprList(Symbol("fp.isNaN"), y))), SExprList(Symbol("not"), SExprList(Symbol('fp.eq'), x, y))))


    @compare_ne.register(SMT2BasicType)
    def _(self, aty: SMT2BasicType, bty: SMT2BasicType):
        return lambda x, y: bool_to_pred(SExprList(Symbol("not"), SExprList(Symbol('='), x, y)))

    @singledispatchmethod
    def compare_neu(self, aty, bty):
        raise NotImplementedError(f"compare_neu({aty}, {bty}) not implemented.")

    @compare_neu.register(SMT2Float)
    def _(self, aty: SMT2Float, bty: SMT2Float):
        return self._do_compare_unordered('neu', aty, bty, self.compare_ne)

    def compare_lt(self, aty, bty):
        return self._do_compare_2('lt', aty, bty)

    @singledispatchmethod
    def compare_ltu(self, aty, bty):
        raise NotImplementedError(f"compare_ltu({aty}, {bty}) not implemented.")

    @compare_ltu.register(SMT2Float)
    def _(self, aty: SMT2Float, bty: SMT2Float):
        return self._do_compare_unordered('ltu', aty, bty, self.compare_lt)

    def compare_le(self, aty, bty):
        return self._do_compare_2('le', aty, bty)

    @singledispatchmethod
    def compare_leu(self, aty, bty):
        raise NotImplementedError(f"compare_leu({aty}, {bty}) not implemented.")

    @compare_leu.register(SMT2Float)
    def _(self, aty: SMT2Float, bty: SMT2Float):
        return self._do_compare_unordered('leu', aty, bty, self.compare_le)

    def compare_gt(self, aty, bty):
        return self._do_compare_2('gt', aty, bty)

    @singledispatchmethod
    def compare_gtu(self, aty, bty):
        raise NotImplementedError(f"compare_gtu({aty}, {bty}) not implemented.")

    @compare_gtu.register(SMT2Float)
    def _(self, aty: SMT2Float, bty: SMT2Float):
        return self._do_compare_unordered('gtu', aty, bty, self.compare_gt)

    def compare_ge(self, aty, bty):
        return self._do_compare_2('ge', aty, bty)

    @singledispatchmethod
    def compare_geu(self, aty, bty):
        raise NotImplementedError(f"compare_geu({aty}, {bty}) not implemented.")

    @compare_geu.register(SMT2Float)
    def _(self, aty: SMT2Float, bty: SMT2Float):
        return self._do_compare_unordered('geu', aty, bty, self.compare_ge)


    def compare_lo(self, aty, bty):
        return self._do_compare_2('lo', aty, bty)

    def compare_ls(self, aty, bty):
        return self._do_compare_2('ls', aty, bty)

    def compare_hi(self, aty, bty):
        return self._do_compare_2('hi', aty, bty)

    def compare_hs(self, aty, bty):
        return self._do_compare_2('hs', aty, bty)

    @singledispatchmethod
    def compare_num(self, aty, bty):
        raise NotImplementedError(f"compare_num({aty}, {bty}) not implemented.")

    @compare_num.register(SMT2Float)
    def _(self, aty: SMT2Float, bty: SMT2Float):
        return lambda x, y: bool_to_pred(SExprList(Symbol("not"),
                                                   SExprList(Symbol("or"),
                                                             SExprList(Symbol("fp.isNaN"), x),
                                                             SExprList(Symbol("fp.isNaN"), y))))


    @singledispatchmethod
    def compare_nan(self, aty, bty):
        raise NotImplementedError(f"compare_nan({aty}, {bty}) not implemented.")

    @compare_nan.register(SMT2Float)
    def _(self, aty: SMT2Float, bty: SMT2Float):
        return lambda x, y: bool_to_pred(SExprList(Symbol("or"),
                                                   SExprList(Symbol("fp.isNaN"), x),
                                                   SExprList(Symbol("fp.isNaN"), y)))

    def _fp_sat(self, aty, fn):
        assert isinstance(aty, SMT2Float)
        sfn = f"SATURATE_f{aty.w}"
        return lambda *args: SExprList(Symbol(sfn), fn(*args))

    @singledispatchmethod
    def ADD_SATURATE(self, aty, bty):
        raise NotImplementedError(f'ADD_SATURATE({aty}, {bty}) not implemented.')

    @ADD_SATURATE.register(SMT2Float)
    def _(self, aty: SMT2Float, bty: SMT2Float):
        return self._fp_sat(aty, FPBinOp("fp.add", "roundNearestTiesToEven"))

    @ADD_SATURATE.register(s32)
    def _(self, aty: s32, bty: s32):
        return lambda x, y: SExprList(Symbol('ADD_SATURATE_s32'), x, y)

    @singledispatchmethod
    def SUB_SATURATE(self, aty, bty):
        raise NotImplementedError(f'SUB_SATURATE({aty}, {bty}) not implemented.')

    @SUB_SATURATE.register(SMT2Float)
    def _(self, aty: SMT2Float, bty: SMT2Float):
        return self._fp_sat(aty, FPBinOp("fp.sub", "roundNearestTiesToEven"))

    @SUB_SATURATE.register(s32)
    def _(self, aty: s32, bty: s32):
        return lambda x, y: SExprList(Symbol('SUB_SATURATE_s32'), x, y)

    @singledispatchmethod
    def MUL_SATURATE(self, aty, bty):
        raise NotImplementedError(f'MUL_SATURATE({aty}, {bty}) not implemented.')

    @MUL_SATURATE.register(SMT2Float)
    def _(self, aty: SMT2Float, bty: SMT2Float):
        return self._fp_sat(aty, FPBinOp("fp.mul", "roundNearestTiesToEven"))

    # there is no integer version of mul saturate

    @singledispatchmethod
    def ADD_ROUND_SATURATE(self, aty, bty, rty):
        raise NotImplementedError(f'ADD_ROUND_SATURATE({aty}, {bty}, {rty}) not implemented.')

    @ADD_ROUND_SATURATE.register(SMT2Float)
    def _(self, aty: SMT2Float, bty: SMT2Float, rty: str):
        return self._fp_sat(aty, self.ADD_ROUND(aty, bty, rty))

    @singledispatchmethod
    def SUB_ROUND_SATURATE(self, aty, bty, rty):
        raise NotImplementedError(f'SUB_ROUND_SATURATE({aty}, {bty}, {rty}) not implemented.')

    @SUB_ROUND_SATURATE.register(SMT2Float)
    def _(self, aty: SMT2Float, bty: SMT2Float, rty: str):
        return self._fp_sat(aty, self.SUB_ROUND(aty, bty, rty))

    @singledispatchmethod
    def MUL_ROUND_SATURATE(self, aty, bty, rty):
        raise NotImplementedError(f'MUL_ROUND_SATURATE({aty}, {bty}, {rty}) not implemented.')

    @MUL_ROUND_SATURATE.register(SMT2Float)
    def _(self, aty: SMT2Float, bty: SMT2Float, rty: str):
        return self._fp_sat(aty, self.MUL_ROUND(aty, bty, rty))

    @singledispatchmethod
    def FMA_ROUND_SATURATE(self, aty, bty, cty, rty):
        raise NotImplementedError(f'FMA_ROUND_SATURATE({aty}, {bty}, {cty}, {rty}) not implemented.')

    @FMA_ROUND_SATURATE.register(SMT2Float)
    def _(self, aty: SMT2Float, bty: SMT2Float, cty: SMT2Float, rty: str):
        return self._fp_sat(aty, self.FMA_ROUND(aty, bty, cty, rty))

    @singledispatchmethod
    def logical_op3(self, aty, bty, cty, imm):
        raise NotImplementedError(f'logical_op3({aty}, {bty}, {cty}, {imm}) not implemented.')

    @logical_op3.register(u32)
    def _(self, aty: u32, bty: u32, cty: u32, imm: u8):
        return lambda x, y, z, a: SExprList(Symbol('logical_op3'), x, y, z, a)

    @singledispatchmethod
    def ISNAN(self, aty):
        raise NotImplementedError(f'ISNAN({aty}) not implemented.')

    @ISNAN.register(SMT2Float)
    def _(self, aty: SMT2Float):
        return lambda x: bool_to_pred(SExprList(Symbol('fp.isNaN'), x))

    @singledispatchmethod
    def subnormal_check(self, aty):
        raise NotImplementedError(f'subnormal_check({aty}) not implemented.')

    @subnormal_check.register(SMT2Float)
    def _(self, aty: SMT2Float):
        return lambda a: bool_to_pred(SExprList(Symbol("fp.isSubnormal"), a))

    @singledispatchmethod
    def ADD_CARRY(self, aty, bty, cfty):
        raise NotImplementedError(f'ADD_CARRY({aty}, {bty}, {cfty} not implemented.')

    @ADD_CARRY.register(BV)
    def _(self, aty: BV, bty: BV, cfty: carryflag):
        w = aty.w

        # it's always unsigned
        return lambda x, y, z: SExprList(Symbol(f"ADD_CARRY_u{w}"), x, y, extract_cf(z))

    @singledispatchmethod
    def SUB_CARRY(self, aty, bty, cfty):
        raise NotImplementedError(f'SUB_CARRY({aty}, {bty}, {cfty} not implemented.')

    @SUB_CARRY.register(BV)
    def _(self, aty: BV, bty: BV, cfty: carryflag):
        w = aty.w
        # it's always unsigned
        return lambda x, y, z: SExprList(Symbol(f"SUB_CARRY_u{w}"), x, y, extract_cf(z))

def get_libs(backend):
    assert backend == "smt2", f"Don't support backend {backend} for ptxlibc"

    return [PTXLibSMT2()]

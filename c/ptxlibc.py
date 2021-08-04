try:
    from functools import singledispatchmethod # 3.8+
except ImportError:
    from singledispatchmethod import singledispatchmethod

from xlatir.xir.xirlib import XIRLib
from xlatir.xir.xirlibc import CBasicType, c_float, SINGLETONS, CSigned, CUnsigned, CInteger, uint64_t, uint32_t, uint16_t, double, CFP, int32_t, int64_t, int16_t

class PTXLibC(XIRLib):
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
        return "fminf_ptx"

    @MIN.register(double)
    def _(self, aty: double, bty: double):
        return "fmin_ptx"

    @MIN.register(CBasicType)
    def _(self, aty: CBasicType, bty: CBasicType):
        return "MIN"

    @singledispatchmethod
    def MAX(self, aty, bty):
        raise NotImplementedError(f"MAX({aty}, {bty}) not implemented.")

    @MAX.register(c_float)
    def _(self, aty: c_float, bty: c_float):
        return "fmaxf_ptx"

    @MAX.register(double)
    def _(self, aty: double, bty: double):
        return "fmax_ptx"

    @MAX.register(CBasicType)
    def _(self, aty: CBasicType, bty: CBasicType):
        return "MAX"

    @singledispatchmethod
    def SAR(self, aty, bty):
        raise NotImplementedError(f"SAR({aty}, {bty}) not implemented.")

    @SAR.register(CSigned)
    def _(self, aty: CSigned, bty: uint32_t):
        # dispatch on second argument doesn't quite mimic '*', '*'
        # TODO: eliminate >>?
        if isinstance(bty, uint32_t):
            return "SHR"
        else:
            return ">>"

    # this mimics the original dictionary, but makes little sense?
    @SAR.register(CBasicType)
    def _(self, aty: CBasicType, bty: CBasicType):
        return ">>"

    @singledispatchmethod
    def LOG2(self, aty):
        raise NotImplementedError(f"LOG2({aty}) not implemented.")

    # use CFP since C files use _Generic to dispatch
    @LOG2.register(CFP)
    def _(self, aty: CFP):
        return "LOG2"

    @singledispatchmethod
    def FTZ(self, aty):
        raise NotImplementedError(f"FTZ({aty}) not implemented.")

    # use CFP since C files use _Generic to dispatch
    @FTZ.register(CFP)
    def _(self, aty: CFP):
        return "FTZ"

    @singledispatchmethod
    def SINE(self, aty):
        raise NotImplementedError(f"SINE({aty}) not implemented.")

    # use CFP since C files use _Generic to dispatch
    @SINE.register(CFP)
    def _(self, aty: CFP):
        return "SINE"

    @singledispatchmethod
    def COSINE(self, aty):
        raise NotImplementedError(f"COSINE({aty}) not implemented.")

    # use CFP since C files use _Generic to dispatch
    @COSINE.register(CFP)
    def _(self, aty: CFP):
        return "COSINE"

    @singledispatchmethod
    def COPYSIGN(self, aty):
        raise NotImplementedError(f"COPYSIGN({aty}) not implemented.")

    # use CFP since C files use _Generic to dispatch
    @COPYSIGN.register(CFP)
    def _(self, aty: CFP):
        return "COPYSIGN"

    @singledispatchmethod
    def SQRT(self, aty):
        raise NotImplementedError(f"SQRT({aty}) not implemented.")

    @SQRT.register(c_float)
    def _(self, aty: c_float):
        return "sqrtf"

    @SQRT.register(double)
    def _(self, aty: double):
        return "sqrt"

    @singledispatchmethod
    def ABSOLUTE(self, aty):
        raise NotImplementedError(f"ABSOLUTE({aty}) not implemented.")

    @ABSOLUTE.register(c_float)
    def _(self, aty: c_float):
        return "fabsf"

    @ABSOLUTE.register(double)
    def _(self, aty: double):
        return "fabs"

    @ABSOLUTE.register(int32_t)
    def _(self, aty: int32_t):
        return "abs"

    @ABSOLUTE.register(int64_t)
    def _(self, aty: int64_t):
        return "labs" # depends on 64-bit model!

    @ABSOLUTE.register(int16_t)
    def _(self, aty: int16_t):
        return "abs"

    @singledispatchmethod
    def POW(self, aty, bty):
        raise NotImplementedError(f"POW({aty}, {bty}) not implemented.")

    @POW.register(c_float)
    def _(self, aty: c_float, bty: c_float):
        return "powf"

    @POW.register(double)
    def _(self, aty: double, bty: double):
        return "pow"

    @singledispatchmethod
    def FMA(self, aty, bty, cty):
        raise NotImplementedError(f"FMA({aty}, {bty}, {cty}) not implemented.")

    @FMA.register(CFP)
    def _(self, aty: CFP, bty: CFP, cty: CFP):
        return "FMA"

    @singledispatchmethod
    def ADD_ROUND(self, aty, bty, rty):
        raise NotImplementedError(f"ADD_ROUND({aty}, {bty}, {rty}) not implemented.")

    @ADD_ROUND.register(CFP)
    def _(self, aty: CFP, bty: CFP, rty: str):
        return "ADD_ROUND"

    @singledispatchmethod
    def MUL_ROUND(self, aty, bty, rty):
        raise NotImplementedError(f"MUL_ROUND({aty}, {bty}, {rty}) not implemented.")

    @MUL_ROUND.register(CFP)
    def _(self, aty: CFP, bty: CFP, rty: str):
        return "MUL_ROUND"

    @singledispatchmethod
    def SUB_ROUND(self, aty, bty, rty):
        raise NotImplementedError(f"SUB_ROUND({aty}, {bty}, {rty}) not implemented.")

    @SUB_ROUND.register(CFP)
    def _(self, aty: CFP, bty: CFP, rty: str):
        return "SUB_ROUND"

    @singledispatchmethod
    def DIV_ROUND(self, aty, bty, rty):
        raise NotImplementedError(f"DIV_ROUND({aty}, {bty}, {rty}) not implemented.")

    @DIV_ROUND.register(CFP)
    def _(self, aty: CFP, bty: CFP, rty: str):
        return "DIV_ROUND"

    @singledispatchmethod
    def FMA_ROUND(self, aty, bty, cty, rty):
        raise NotImplementedError(f"FMA_ROUND({aty}, {bty}, {cty}, {rty}) not implemented.")

    @FMA_ROUND.register(CFP)
    def _(self, aty: CFP, bty: CFP, cty: CFP, rty: str):
        return "FMA_ROUND"

    @singledispatchmethod
    def RCP_ROUND(self, aty, rty):
        raise NotImplementedError(f"RCP_ROUND({aty}, {rty}) not implemented.")

    @RCP_ROUND.register(CFP)
    def _(self, aty: CFP, rty: str):
        return "RCP_ROUND"

    @singledispatchmethod
    def SQRT_ROUND(self, aty, rty):
        raise NotImplementedError(f"SQRT_ROUND({aty}, {rty}) not implemented.")

    @SQRT_ROUND.register(CFP)
    def _(self, aty: CFP, rty: str):
        return "SQRT_ROUND"

    @singledispatchmethod
    def MACHINE_SPECIFIC_execute_rem_divide_by_zero_unsigned(self, aty):
        raise NotImplementedError(f"MACHINE_SPECIFIC_execute_rem_divide_by_zero_unsigned({aty}) not implemented")

    @MACHINE_SPECIFIC_execute_rem_divide_by_zero_unsigned.register(CUnsigned)
    def _(self, aty: CUnsigned):
        return ''

    @singledispatchmethod
    def MACHINE_SPECIFIC_execute_rem_divide_by_neg(self, aty, bty):
        raise NotImplementedError(f"MACHINE_SPECIFIC_execute_rem_divide_by_neg({aty}, {bty}) not implemented")

    # should be CInteger?/CSigned?
    @MACHINE_SPECIFIC_execute_rem_divide_by_neg.register(CBasicType)
    def _(self, aty: CBasicType, bty: CBasicType):
        return 'MACHINE_SPECIFIC_execute_rem_divide_by_neg'

    @singledispatchmethod
    def MACHINE_SPECIFIC_execute_div_divide_by_zero_integer(self, aty):
        raise NotImplementedError(f"MACHINE_SPECIFIC_execute_div_divide_by_zero_integer({aty}) not implemented")

    @MACHINE_SPECIFIC_execute_div_divide_by_zero_integer.register(CInteger)
    def _(self, aty: CInteger):
        return ''

    @singledispatchmethod
    def zext_64(self, aty):
        raise NotImplementedError(f"zext_64({aty}) not implemented.")

    @zext_64.register(CInteger)
    def _(self, aty: uint64_t):
        return 'uint64_t'

    @singledispatchmethod
    def sext_64(self, aty):
        raise NotImplementedError(f"sext_64({aty}) not implemented.")

    @sext_64.register(CInteger)
    def _(self, aty: CInteger):
        return 'int64_t'

    @singledispatchmethod
    def sext_32(self, aty):
        raise NotImplementedError(f"sext_32({aty}) not implemented.")

    @sext_32.register(CInteger)
    def _(self, aty: CInteger):
        return 'int32_t'

    @singledispatchmethod
    def sext_16(self, aty):
        raise NotImplementedError(f"sext_16({aty}) not implemented.")

    @sext_16.register(CInteger)
    def _(self, aty: CInteger):
        return 'int16_t'

    @singledispatchmethod
    def truncate_64(self, aty):
        raise NotImplementedError(f"truncate_64({aty}) not implemented.")

    @truncate_64.register(CInteger)
    def _(self, aty: CInteger):
        return 'uint64_t'

    @singledispatchmethod
    def truncate_32(self, aty):
        raise NotImplementedError(f"truncate_32({aty}) not implemented.")

    @truncate_32.register(CInteger)
    def _(self, aty: CInteger):
        return 'uint32_t'

    @singledispatchmethod
    def truncate_16(self, aty):
        raise NotImplementedError(f"truncate_16({aty}) not implemented.")

    @truncate_16.register(CInteger)
    def _(self, aty: CInteger):
        return 'uint16_t'




def get_libs(backend):
    assert backend == "c", f"Don't support backend {backend} for ptxlibc"

    return [PTXLibC()]

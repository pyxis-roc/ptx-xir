from xlatir.xir.xirlib import XIRLib

class PTXLib(XIRLib):
    def MIN(self, aty, bty):
        raise NotImplementedError(f"MIN({aty}, {bty}) not implemented.")

    def min(self, aty, bty):
        raise NotImplementedError(f"min({aty}, {bty}) not implemented.")

    def MAX(self, aty, bty):
        raise NotImplementedError(f"MAX({aty}, {bty}) not implemented.")

    def SAR(self, aty, bty):
        raise NotImplementedError(f"SAR({aty}, {bty}) not implemented.")

    def SHL_LIT(self, aty, bty):
        raise NotImplementedError(f"SHL_LIT({aty}, {bty}) not implemented.")

    def SHR_LIT(self, aty, bty):
        raise NotImplementedError(f"SHR_LIT({aty}, {bty}) not implemented.")

    def SAR_LIT(self, aty, bty):
        raise NotImplementedError(f"SAR_LIT({aty}, {bty}) not implemented.")

    def LOG2(self, aty):
        raise NotImplementedError(f"LOG2({aty}) not implemented.")

    def FTZ(self, aty):
        raise NotImplementedError(f"FTZ({aty}) not implemented.")

    def SINE(self, aty):
        raise NotImplementedError(f"SINE({aty}) not implemented.")

    def COSINE(self, aty):
        raise NotImplementedError(f"COSINE({aty}) not implemented.")

    def COPYSIGN(self, aty):
        raise NotImplementedError(f"COPYSIGN({aty}) not implemented.")

    def SQRT(self, aty):
        raise NotImplementedError(f"SQRT({aty}) not implemented.")

    def ABSOLUTE(self, aty):
        raise NotImplementedError(f"ABSOLUTE({aty}) not implemented.")

    def POW(self, aty, bty):
        raise NotImplementedError(f"POW({aty}, {bty}) not implemented.")

    def FMA(self, aty, bty, cty):
        raise NotImplementedError(f"FMA({aty}, {bty}, {cty}) not implemented.")

    def ADD_ROUND(self, aty, bty, rty):
        raise NotImplementedError(f"ADD_ROUND({aty}, {bty}, {rty}) not implemented.")

    def MUL_ROUND(self, aty, bty, rty):
        raise NotImplementedError(f"MUL_ROUND({aty}, {bty}, {rty}) not implemented.")

    def SUB_ROUND(self, aty, bty, rty):
        raise NotImplementedError(f"SUB_ROUND({aty}, {bty}, {rty}) not implemented.")

    def DIV_ROUND(self, aty, bty, rty):
        raise NotImplementedError(f"DIV_ROUND({aty}, {bty}, {rty}) not implemented.")

    def FMA_ROUND(self, aty, bty, cty, rty):
        raise NotImplementedError(f"FMA_ROUND({aty}, {bty}, {cty}, {rty}) not implemented.")

    def RCP_ROUND(self, aty, rty):
        raise NotImplementedError(f"RCP_ROUND({aty}, {rty}) not implemented.")

    def SQRT_ROUND(self, aty, rty):
        raise NotImplementedError(f"SQRT_ROUND({aty}, {rty}) not implemented.")

    def MACHINE_SPECIFIC_execute_rem_divide_by_zero_unsigned(self, aty):
        raise NotImplementedError(f"MACHINE_SPECIFIC_execute_rem_divide_by_zero_unsigned({aty}) not implemented")

    def MACHINE_SPECIFIC_execute_rem_divide_by_neg(self, aty, bty):
        raise NotImplementedError(f"MACHINE_SPECIFIC_execute_rem_divide_by_neg({aty}, {bty}) not implemented")

    def MACHINE_SPECIFIC_execute_div_divide_by_zero_integer(self, aty):
        raise NotImplementedError(f"MACHINE_SPECIFIC_execute_div_divide_by_zero_integer({aty}) not implemented")

    def zext_64(self, aty):
        raise NotImplementedError(f"zext_64({aty}) not implemented.")

    def sext_64(self, aty):
        raise NotImplementedError(f"sext_64({aty}) not implemented.")

    def sext_32(self, aty):
        raise NotImplementedError(f"sext_32({aty}) not implemented.")

    def sext_16(self, aty):
        raise NotImplementedError(f"sext_16({aty}) not implemented.")

    def truncate_64(self, aty):
        raise NotImplementedError(f"truncate_64({aty}) not implemented.")

    def truncate_32(self, aty):
        raise NotImplementedError(f"truncate_32({aty}) not implemented.")

    def truncate_16(self, aty):
        raise NotImplementedError(f"truncate_16({aty}) not implemented.")

    def compare_eq(self, aty, bty):
        raise NotImplementedError(f"compare_eq({aty}, {bty}) not implemented.")

    def compare_equ(self, aty, bty):
        raise NotImplementedError(f"compare_equ({aty}, {bty}) not implemented.")

    def compare_ne(self, aty, bty):
        raise NotImplementedError(f"compare_ne({aty}, {bty}) not implemented.")

    def compare_neu(self, aty, bty):
        raise NotImplementedError(f"compare_neu({aty}, {bty}) not implemented.")

    def compare_lt(self, aty, bty):
        raise NotImplementedError(f"compare_lt({aty}, {bty}) not implemented.")

    def compare_ltu(self, aty, bty):
        raise NotImplementedError(f"compare_ltu({aty}, {bty}) not implemented.")

    def compare_le(self, aty, bty):
        raise NotImplementedError(f"compare_le({aty}, {bty}) not implemented.")

    def compare_leu(self, aty, bty):
        raise NotImplementedError(f"compare_leu({aty}, {bty}) not implemented.")

    def compare_gt(self, aty, bty):
        raise NotImplementedError(f"compare_gt({aty}, {bty}) not implemented.")

    def compare_gtu(self, aty, bty):
        raise NotImplementedError(f"compare_gtu({aty}, {bty}) not implemented.")

    def compare_ge(self, aty, bty):
        raise NotImplementedError(f"compare_ge({aty}, {bty}) not implemented.")

    def compare_geu(self, aty, bty):
        raise NotImplementedError(f"compare_geu({aty}, {bty}) not implemented.")

    def compare_lo(self, aty, bty):
        raise NotImplementedError(f"compare_lo({aty}, {bty}) not implemented.")

    def compare_ls(self, aty, bty):
        raise NotImplementedError(f"compare_ls({aty}, {bty}) not implemented.")

    def compare_hi(self, aty, bty):
        raise NotImplementedError(f"compare_hi({aty}, {bty}) not implemented.")

    def compare_hs(self, aty, bty):
        raise NotImplementedError(f"compare_hs({aty}, {bty}) not implemented.")

    def compare_num(self, aty, bty):
        raise NotImplementedError(f"compare_num({aty}, {bty}) not implemented.")

    def compare_nan(self, aty, bty):
        raise NotImplementedError(f"compare_nan({aty}, {bty}) not implemented.")

    def ADD_SATURATE(self, aty, bty):
        raise NotImplementedError(f'ADD_SATURATE({aty}, {bty}) not implemented.')

    def SUB_SATURATE(self, aty, bty):
        raise NotImplementedError(f'SUB_SATURATE({aty}, {bty}) not implemented.')

    def MUL_SATURATE(self, aty, bty):
        raise NotImplementedError(f'MUL_SATURATE({aty}, {bty}) not implemented.')

    def ADD_ROUND_SATURATE(self, aty, bty, rty):
        raise NotImplementedError(f'ADD_ROUND_SATURATE({aty}, {bty}, {rty}) not implemented.')

    def SUB_ROUND_SATURATE(self, aty, bty, rty):
        raise NotImplementedError(f'SUB_ROUND_SATURATE({aty}, {bty}, {rty}) not implemented.')

    def MUL_ROUND_SATURATE(self, aty, bty, rty):
        raise NotImplementedError(f'MUL_ROUND_SATURATE({aty}, {bty}, {rty}) not implemented.')

    def FMA_ROUND_SATURATE(self, aty, bty, cty, rty):
        raise NotImplementedError(f'FMA_ROUND_SATURATE({aty}, {bty}, {cty}, {rty}) not implemented.')

    def logical_op3(self, aty, bty, cty, imm):
        raise NotImplementedError(f'logical_op3({aty}, {bty}, {cty}, {imm}) not implemented.')

    def ISNAN(self, aty):
        raise NotImplementedError(f'ISNAN({aty}) not implemented.')

    def subnormal_check(self, aty):
        raise NotImplementedError(f'subnormal_check({aty}) not implemented.')

def get_libs(backend):
    # hack
    return []

SRC=../src
SMTSRC=.
TOOLS=../tools
TARGET ?= build
XIR2X=xir2x.py
INSNS ?= all

all: $(TARGET)/ptx_executable_semantics.smt2

$(TARGET)/lop3_lut.smt2: $(TOOLS)/lop3_lut_gen.py
	$(TOOLS)/lop3_lut_gen.py -x smt2 $@

$(TARGET)/readbyte_prmt.smt2: $(TOOLS)/prmt_readbyte_gen.py
	$(TOOLS)/prmt_readbyte_gen.py smt2 > $@

$(TARGET)/ptx.smt2: $(TARGET)/../ptx_executable_semantics_xir_smt2.py $(TARGET)/lop3_lut.smt2 $(TARGET)/readbyte_prmt.smt2
	$(XIR2X) $(XIR2X_FLAGS) -b ../src/ptxlib.py -b ptxlibsmt2.py --pemdeps $(SRC)/lop3_lut.py --pem $(SRC)/utils.py -l$(SRC)/ptxlib.pyi -lxirbuiltin.pyi -I$(TARGET) -I$(SMTSRC) $< smt2 $@ $(INSNS)

$(TARGET)/ptx_executable_semantics.smt2: $(TARGET)/ptx.smt2
	z3 $< && cp $< $@


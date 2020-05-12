SRC=../src
SMTSRC=.
TOOLS=../tools
TARGET ?= build

ifeq ($(XIR2X),)
	$(error XIR2X variable must be set to point to xir2x.py)
endif

all: $(TARGET)/ptx_executable_semantics.smt2

$(TARGET)/lop3_lut.smt2: $(TOOLS)/lop3_lut_gen.py
	$(TOOLS)/lop3_lut_gen.py -x smt2 $@

$(TARGET)/readbyte_prmt.smt2: $(TOOLS)/prmt_readbyte_gen.py
	$(TOOLS)/prmt_readbyte_gen.py smt2 > $@

$(TARGET)/ptx.smt2: $(TARGET)/../ptx_executable_semantics_xir.py $(TARGET)/lop3_lut.smt2 $(TARGET)/readbyte_prmt.smt2
	$(XIR2X) --pemdeps $(SRC)/lop3_lut.py --pem $(SRC)/utils.py -l$(SRC)/ptxlib.pyi -l$(SRC)/xirbuiltin.pyi -I$(TARGET) -I$(SMTSRC) $< smt2 $@

$(TARGET)/ptx_executable_semantics.smt2: $(TARGET)/ptx.smt2
	z3 $< && cp $< $@

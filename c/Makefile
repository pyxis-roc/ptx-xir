SRC=../src
CSRC=.
TOOLS=../tools
TARGET ?= build
XIR2X=xir2x.py

all: $(TARGET)/ptxc.c

$(TARGET)/ptxc_utils_template.h: $(CSRC)/ptxc_utils_template.tmplh $(CSRC)/ptxc_utils_template.script
	$(CSRC)/ctempl_script.py $(CSRC)/ptxc_utils_template.script $@

$(TARGET)/ptxc.c: $(TARGET)/../ptx_executable_semantics_xir.py $(TARGET)/lop3_lut.h $(TARGET)/ptxc_utils_template.h $(TARGET)/readbyte_prmt.h
	$(XIR2X) --pemdeps $(SRC)/lop3_lut.py --pem $(SRC)/utils.py -lxirbuiltin.pyi -l$(SRC)/ptxlib.pyi $< c $@ all

$(TARGET)/lop3_lut.h: $(TOOLS)/lop3_lut_gen.py
	$(TOOLS)/lop3_lut_gen.py -x c $@

$(TARGET)/readbyte_prmt.h: $(TOOLS)/prmt_readbyte_gen.py
	$(TOOLS)/prmt_readbyte_gen.py c > $@

.PHONY: test

test:
	gcc -I . -I $(TARGET) $(TARGET)/ptxc.c -lm
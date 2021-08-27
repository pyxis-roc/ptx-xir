TARGET ?= build
CTESTSDIR ?= ../ptx-semantics-tests/v6.5/c
SMT2TESTSDIR ?= ../ptx-semantics-tests/v6.5/ptx-smt2

all:

$(TARGET)/c:
	mkdir -p $@

$(TARGET)/smt2:
	mkdir -p $@

.PHONY: c smt2 legacy

c: $(TARGET)/c
	$(MAKE) -C c TARGET=../$(TARGET)/c

smt2: $(TARGET)/smt2
	$(MAKE) -C smt2 TARGET=../$(TARGET)/smt2

legacy: $(TARGET)
	cp $(SCDIR)/exec_semantics/ptx_executable_semantics_xir.py $(TARGET)/ptx_executable_semantics_xir.py.orig
	cp $(SCDIR)/exec_semantics/utils.py src/utils.py
	src/rewrite.py $(TARGET)/ptx_executable_semantics_xir.py.orig $(TARGET)/ptx_executable_semantics_xir_c.py c
	src/rewrite.py $(TARGET)/ptx_executable_semantics_xir.py.orig $(TARGET)/ptx_executable_semantics_xir_smt2.py smt2

c-tests: $(TARGET)/c/ptxc.c
	c/generate_xir_c_test_cases.py --source $< --header $(<:.c=.h) --altfakecheaders=/usr/share/python3-pycparser/fake_libc_include/ $(CTESTSDIR)

smt2-tests: $(TARGET)/smt2/ptx.smt2
	smt2/generate_xir_smt2_test_cases.py -s $< $(SMT2TESTSDIR)

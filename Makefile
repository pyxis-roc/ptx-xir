TARGET ?= build

all:

$(TARGET)/c:
	mkdir -p $@

$(TARGET)/smt2:
	mkdir -p $@

.PHONY: c smt2

c:
	$(MAKE) -C c TARGET=../$(TARGET)/c

smt2: $(TARGET)/smt2
	$(MAKE) -C smt2 TARGET=../$(TARGET)/smt2


CC ?= clang
CFLAGS ?= -Wall -march=native -O3 -fomit-frame-pointer -fwrapv -fPIC -fPIE

INCLUDE ?= -Icommon/
RANDOMLIB ?= common/notrandombytes.c common/notrandombytes1.c
BIN ?= bin

MIN_NLIMBS    ?= 1
MAX_NLIMBS    ?= 16
NLIMBS        := $(shell seq $(MIN_NLIMBS) $(MAX_NLIMBS))

GMP_TARGETS   := $(addprefix $(BIN)/gmp_try_expm_, $(NLIMBS))
GMP_CHECKSUMS := $(addsuffix .out, $(GMP_TARGETS))

ZK_TARGETS    := $(addprefix $(BIN)/zk_try_expm_, $(NLIMBS))
ZK_CHECKSUMS  := $(addsuffix .out, $(ZK_TARGETS))

#--

.PHONY: __phony

defaults: default-gmp default-zk
all: all-gmp all-zk
run-all: run-all-gmp run-all-zk

#--

default-gmp: $(BIN)/gmp_try_expm_32

all-gmp: $(GMP_TARGETS)
run-all-gmp: $(GMP_CHECKSUMS)

$(GMP_TARGETS):
$(BIN)/gmp_try_expm_%: __phony | $(BIN)
	$(CC) $(CFLAGS) -o $@ -DNLIMBS=$* $(INCLUDE) common/try-expm.c bindings/gmp-expm.c $(RANDOMLIB) -lgmp

$(BIN)/gmp_try_expm_%.out: $(BIN)/gmp_try_expm_%
	(./$< > $@ 2>&1 || true)

#--

default-zk: $(BIN)/zk_try_expm_32

all-zk: $(ZK_TARGETS)
run-all-zk: $(ZK_CHECKSUMS)

$(ZK_TARGETS):
$(BIN)/zk_try_expm_%: $(BIN)/ring_ops_%.s __phony | $(BIN)
	$(CC) $(CFLAGS) -o $@ -DNLIMBS=$* $(INCLUDE) $< common/try-expm.c bindings/zk-expm.c $(RANDOMLIB) -lgmp

$(BIN)/zk_try_expm_%.out: $(BIN)/zk_try_expm_%
	(./$< > $@ 2>&1 || true)

$(BIN)/ring_ops_%.s:
	$(MAKE) -C ../src/ ring_ops_$*.s
	mv ../src/ring_ops_$*.s $@

#--

check: __phony
	for i in $$(seq $(MIN_NLIMBS) $(MAX_NLIMBS)); do \
		zk=$$(cat $(BIN)/zk_try_expm_$$i.out); \
		gmp=$$(cat $(BIN)/gmp_try_expm_$$i.out); \
		if [ "$$zk" = "$$gmp" ] ; then echo -n "OK"; else echo -n "FAIL"; fi; \
		echo " - $$i - $$zk/$$gmp"; \
	done

#--
$(BIN): ; mkdir -p $@

#--

.PHONY: clean
clean:
	rm -fr $(BIN)


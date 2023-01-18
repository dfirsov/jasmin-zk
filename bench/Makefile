CC ?= clang
CFLAGS ?= -Wall -march=native -O3 -fomit-frame-pointer -fwrapv -fPIC -fPIE

INCLUDE ?= -Icommon/
BIN ?= bin

MIN_NLIMBS    ?= 1
MAX_NLIMBS    ?= 16
NLIMBS        := $(shell seq $(MIN_NLIMBS) $(MAX_NLIMBS))

GMP_TARGETS   := $(addprefix $(BIN)/gmp_bench_expm_, $(NLIMBS))
GMP_CHECKSUMS := $(addsuffix .out, $(GMP_TARGETS))

ZK_TARGETS    := $(addprefix $(BIN)/zk_bench_expm_, $(NLIMBS))
ZK_CHECKSUMS  := $(addsuffix .out, $(ZK_TARGETS))

#--

.PHONY: __phony

defaults: default-gmp default-zk
all: all-gmp all-zk
run-all: run-all-gmp run-all-zk

#--

default-gmp: $(BIN)/gmp_bench_expm_32

all-gmp: $(GMP_TARGETS)
run-all-gmp: $(GMP_CHECKSUMS)

$(GMP_TARGETS):
$(BIN)/gmp_bench_expm_%: __phony | $(BIN)
	$(CC) $(CFLAGS) -o $@ -DNLIMBS=$* $(INCLUDE) bench-gmp-expm.c -lgmp

$(BIN)/gmp_bench_expm_%.out: $(BIN)/gmp_bench_expm_%
	(./$< > $@ 2>&1 || true)

#--

default-zk: $(BIN)/zk_bench_expm_32

all-zk: $(ZK_TARGETS)
run-all-zk: $(ZK_CHECKSUMS)

$(ZK_TARGETS):
$(BIN)/zk_bench_expm_%: $(BIN)/ring_ops_%.s __phony | $(BIN)
	$(CC) $(CFLAGS) -o $@ -DNLIMBS=$* $(INCLUDE) -I../test/bindings bench-zk-expm.c $< -lgmp

$(BIN)/zk_bench_expm_%.out: $(BIN)/zk_bench_expm_%
	(./$< > $@ 2>&1 || true)

$(BIN)/ring_ops_%.s:
	$(MAKE) -C ../src/ ring_ops_$*.s
	mv ../src/ring_ops_$*.s $@

#--
$(BIN): ; mkdir -p $@

#--

.PHONY: clean
clean:
	rm -fr $(BIN)

#--
#$ for i in $(seq 1 16); do echo -n "$i,"; sed -n '3,+0p' bin/gmp_bench_expm_$i.out; done

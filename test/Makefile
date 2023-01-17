CC ?= clang
CFLAGS ?= -Wall -march=native -O3 -fomit-frame-pointer -fwrapv -fPIC -fPIE

INCLUDE ?= -Icommon/
RANDOMLIB ?= common/notrandombytes.c common/notrandombytes1.c
BIN ?= bin

MIN_NLIMBS    := 1
MAX_NLIMBS    := 32
NLIMBS        := $(shell seq $(MIN_NLIMBS) $(MAX_NLIMBS))
GMP_TARGETS   := $(addprefix $(BIN)/gmp_try_expm_, $(NLIMBS))
GMP_CHECKSUMS := $(addsuffix .out, $(GMP_TARGETS))

#--

default: default-gmp

#--

default-gmp: gmp_try_exmp_32

all-gmp: $(GMP_TARGETS)
run-all-gmp: $(GMP_CHECKSUMS)

$(BIN)/gmp_try_expm_%: common/try-expm.c bindings/gmp-expm.c $(RANDOMLIB) | $(BIN)
	$(CC) $(CFLAGS) -o $@ -DNLIMBS=$* $(INCLUDE) $^ -lgmp

$(BIN)/gmp_try_expm_%.out: $(BIN)/gmp_try_expm_%
	./$< > $@

#--

$(BIN): ; mkdir -p $@

#--

.PHONY: clean
clean:
	rm -fr $(BIN)


CC ?= clang
CFLAGS ?= -Wall -march=native -O3 -fomit-frame-pointer -fwrapv -fPIC -fPIE

#--

default: gmp_example

#--

gmp_example: gmp_example.c ../bindings/gmp-expm.c
	$(CC) $(CFLAGS) -o $@ -DNLIMBS=32 $^ -lgmp

#--
.PHONY: clean
clean:
	rm -f gmp_example

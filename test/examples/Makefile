CC ?= clang
CFLAGS ?= -Wall -march=native -O3 -fomit-frame-pointer -fwrapv -fPIC -fPIE

RANDOMLIB ?= ../common/notrandombytes.c ../common/notrandombytes1.c

#--

default: gmp_example zk_example

#--

gmp_example: example.c ../bindings/gmp-expm.c
	$(CC) $(CFLAGS) -o $@ -DNLIMBS=32 $^ -lgmp

#--

zk_example: example.c ../bindings/zk-expm.c ring_ops_32.s $(RANDOMLIB)
	$(CC) $(CFLAGS) -o $@ -DNLIMBS=32 $^ -lgmp

ring_ops_32.s:
	$(MAKE) -C ../../src/ ring_ops_32.s
	mv ../../src/ring_ops_32.s $@

#--
.PHONY: clean
clean:
	rm -f gmp_example zk_example *.s

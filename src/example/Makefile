
example : example.c ../schnorr_protocol.h ../schnorr_protocol.o
#	gcc example.c ../schnorr_protocol.o ./syscalls/notrandombytes1.c ./syscalls/notrandombytes.c -o $@
	gcc example.c ../schnorr_protocol.o ./syscalls/randombytes1.c ./syscalls/jasmin_syscall.c -o $@

../schnorr_protocol.o : $(wildcard ../*.jazz)
	make -C .. schnorr_protocol.o

run : example
	./example


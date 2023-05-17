
example : example.c ../schnorr_protocol.h ../schnorr_protocol.o
	gcc example.c ../schnorr_protocol.o notrandombytes1.c notrandombytes.c -o $@

../schnorr_protocol.o : $(wildcard ../*.jazz)
	make -C .. schnorr_protocol.o

run : example
	./example


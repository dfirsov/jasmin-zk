JASMIN  ?= jasminc

default: schnorr_protocol.o

schnorr_protocol.s: $(wildcard *.jazz)
	$(JASMIN) schnorr_protocol.jazz -o $@

schnorr_protocol.o : schnorr_protocol.s



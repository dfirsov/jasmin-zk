JASMIN  ?= jasminc

default: schnorr_protocol.o

schnorr_protocol.s: $(wildcard *.jazz) constants.jazz
	$(JASMIN) schnorr_protocol.jazz -o $@

schnorr_protocol.o : schnorr_protocol.s

constants.jazz : constants.py
	python3 constants.py

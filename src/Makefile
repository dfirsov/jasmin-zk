JASMIN  ?= jasminc

.PHONY: __phony
ring_ops_%.s: __phony
	$(MAKE) params_$*.jinc
	$(JASMIN) -nowarning ring_ops.jazz -o $@

params_%.jinc:
	echo "param int nlimbs = $*;" > params.jinc

#--

clean:
	rm *.s

distclean: clean
	rm -f params.jinc

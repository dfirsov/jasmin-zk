.PHONY: clean skylake0.svg

skylake0.svg:
	for i in $$(seq 1 16); do echo -n "$$i, "; sed -n '3,+0p' baseline0/gmp_bench_expm_$$i.out; done > skylake0.gmp.csv
	for i in $$(seq 1 16); do echo -n "$$i, "; sed -n '3,+0p' baseline0/zk_bench_expm_$$i.out; done > skylake0.zk.csv
	gnuplot skylake0.gnu
  #inkscape skylake0.svg --export-pdf=skylake0.pdf

clean:
	rm *.csv

distclean: clean
	rm *.svg

set term svg enhanced background rgb 'white' size 600,380

set style line 100 lt 1 lc rgb "#dcdcdc"  lw 0.4
set grid xtics ytics mxtics mytics ls 100
set mytics 2

set xlabel "number of 64-bit limbs"
set ylabel "expm - cpu cycles"

set output "skylake0.svg"

plot \
"skylake0.gmp.csv" using 1:2 title '' with lines, \
"skylake0.zk.csv"  using 1:2 title '' with lines, \
"skylake0.gmp.csv" using 1:2 title 'gmp', \
"skylake0.zk.csv"  using 1:2 title 'jasmin'


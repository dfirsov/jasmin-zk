require import RealExp CoreReal Real StdOrder.

import RealOrder.


op r(n k : real) : real = (floor (4%r^k  / n))%r .
op t' (x n k : real) = (floor (x * r n k / 4%r^k))%r.
op t (x n k : real)  : real = x - (t' x n k) * n.


lemma r_pos n (k : real): 
   0%r <= n < 2%r^k =>
  r n k >= 0%r. smt. qed.

lemma nn_bound n (k : real) : 
  0%r <= n < 2%r^k =>
  n*n < 4%r^k. 
  have -> : 4%r = 2%r ^ 2%r. smt.
  have -> : 2%r ^ 2%r ^ k = (2%r ^ k) * (2%r ^ k) . smt.
smt.
qed.  

lemma st1 n (k : real) : (4%r^k / n - 1%r) < r n k <= (4%r^k / n).
smt(floor_bound).
qed.

lemma st2 x n (k : real) : x >= 0%r =>
 0%r <= n < 2%r^k =>
  x * (4%r^k / n - 1%r) <= x * r n k <= x* (4%r^k / n).
move => x_pos [n_bound1  n_bound2].
rewrite /r.
split.
case (x = 0%r). progress. 
move => xnz.
apply ler_pmul2l. smt. 
smt. 
move => _.
case (x = 0%r). progress. 
move => xnz.
apply ler_pmul2l. smt. 
smt. 
qed.

lemma st3 x n (k : real) : x >= 0%r =>  0%r <= n < 2%r^k =>
  (x / n) - (x / 4%r^k)
    <= (x * r n k) / 4%r^k
    <= x / n.
move => x_pos [n_bound1 n_bound2].
have ->: (x / n) - (x / 4%r^k) = (x * (4%r^k / n - 1%r)) / 4%r^k.
simplify.
  pose a := 4%r ^ k. smt.
have ->:  x / n = (x* (4%r^k / n)) / 4%r^k.
  pose a := 4%r ^ k. smt.
split.
progress.
smt(ler_pmul2r st2  invr_gt0 rpow_gt0).
move => _. 
apply ler_pmul2r. 
smt( invr_gt0 rpow_gt0 ).
smt(st2).
qed.


lemma st4_1 x n (k : real) : 
   0%r <= n < 2%r^k =>
   0%r <= x < n * n => 
   x / 4%r^k < 1%r. 
move => [n_bound1 n_bound2] x_bound.
have : x < 4%r ^ k. smt.
clear n_bound1 n_bound2.
move => p. smt.
qed.

 
lemma st4 x n (k : real) : 
  0%r <= x < n * n =>
  0%r <= n < 2%r^k =>
  (x / n) - 1%r
    <= (x * r n k) / 4%r^k
       <= x / n.
move => n_bnds x_pos.
split.
have x_lt1 : x / 4%r^k < 1%r. smt.
smt.
move => _. smt.
qed.


lemma st6 x n (k : real) : 
  0%r <= x < n * n =>
  0%r <= n < 2%r^k =>
 x - 2%r * n < t' x n k * n <= x.
proof. move => x_bounds n_bounds.
  have st5_1 : x / n - 2%r < (floor (x / n - 1%r)) %r.
  smt.
  have st5_2 : (floor (x / n - 1%r)) %r <= t' x n k.
  rewrite /t'.
  apply le_fromint.
  apply floor_mono.  
  smt(st4).
  have st5_3: t' x n k <= x / n.
  rewrite /t'.
  smt (st4 floor_le).
split.
  have tr : x / n - 2%r  < t' x n k. smt. 
  have -> : (x - 2%r * n) = (x/n - 2%r)  * n. smt.
  smt.
move => _.
smt.
qed.


lemma st7 x n (k : real) : 
  0%r <= x < n *  n =>
  0%r <= n < 2%r^k =>
  -x  <= - t' x n k * n < 2%r*n - x.
move => x_bounds n_bounds.
split.
apply ler_opp2. smt(st6).
move => _.
apply ltr_opp2. simplify.
have ->: - (2%r * n - x)
  = (x - 2%r * n). smt.
smt(st6).
qed.


lemma st8 x n (k : real) :
  0%r <= x < n * n =>
  0%r <= n < 2%r^k =>
  0%r  <= t x n k < 2%r*n .
smt(st7). qed.


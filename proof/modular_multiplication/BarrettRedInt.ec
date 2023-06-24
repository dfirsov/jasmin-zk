require import RealExp CoreReal Real StdOrder.

import RealOrder.


op r(n k : real) : real = (floor (4%r^k  / n))%r .
op t' (x n k : real) = (floor (x * r n k / 4%r^k))%r.
op t (x n k : real)  : real = x - (t' x n k) * n.



lemma r_pos n (k : real): 
   0%r <= n < 2%r^k =>
  r n k >= 0%r. rewrite /r. move => Q. smt(@Real @RealExp).  qed.

  
lemma nn_bound n (k : real) : 
  0%r <= n < 2%r^k =>
  n*n < 4%r^k. 
  have -> : 4%r = 2%r ^ 2%r. smt(@RealExp).
  have -> : 2%r ^ 2%r ^ k = (2%r ^ k) * (2%r ^ k). smt(@RealExp).
  smt().
qed.  


lemma st1 n (k : real) : (4%r^k / n - 1%r) < r n k <= (4%r^k / n).
smt(floor_bound @RealExp).
qed.


lemma st2 x n (k : real) : x >= 0%r =>
 0%r <= n < 2%r^k =>
  x * (4%r^k / n - 1%r) <= x * r n k <= x* (4%r^k / n).
move => x_pos [n_bound1  n_bound2].
rewrite /r.
split.
case (x = 0%r). progress. 
move => xnz.
apply ler_pmul2l. smt(). 
smt(@Real @RealExp). 
move => _.
case (x = 0%r). progress. 
move => xnz.
apply ler_pmul2l. smt(). 
smt(@Real). 
qed.


lemma st3 x n (k : real) : x >= 0%r =>  0%r <= n < 2%r^k =>
  (x / n) - (x / 4%r^k)
    <= (x * r n k) / 4%r^k
    <= x / n.
move => x_pos [n_bound1 n_bound2].
have ->: (x / n) - (x / 4%r^k) = (x * (4%r^k / n - 1%r)) / 4%r^k.
simplify.
  pose a := 4%r ^ k. smt(@RealExp @Real).
have ->:  x / n = (x* (4%r^k / n)) / 4%r^k.
  pose a := 4%r ^ k. smt(@RealExp @Real).
split.
progress.
smt(ler_pmul2r st2  invr_gt0 rpow_gt0).
move => _. 
apply ler_pmul2r. 
smt(invr_gt0 rpow_gt0 ).
smt(st2).
qed.


lemma st4_1 x n (k : real) : 
   0%r <= n < 2%r^k =>
   0%r <= x < n * n => 
   x / 4%r^k < 1%r. 
move => [n_bound1 n_bound2] x_bound.
have : x < 4%r ^ k. smt(nn_bound).
clear n_bound1 n_bound2.
move => p. smt().
qed.

 
lemma st4 x n (k : real) : 
  0%r <= x < n * n =>
  0%r <= n < 2%r^k =>
  (x / n) - 1%r
    <= (x * r n k) / 4%r^k
       <= x / n.
move => n_bnds x_pos.
split.
have x_lt1 : x / 4%r^k < 1%r. smt(st4_1).
smt(st3).
move => _. smt(st3).
qed.

require import FloorCeil.
lemma st6 x n (k : real) : 
  0%r <= x < n * n =>
  0%r <= n < 2%r^k =>
 x - 2%r * n < t' x n k * n <= x.
proof. move => x_bounds n_bounds.
  have st5_1 : x / n - 2%r < (floor (x / n - 1%r)) %r.
  smt(@Real).
  have st5_2 : (floor (x / n - 1%r)) %r <= t' x n k.
  rewrite /t'.
  apply le_fromint. 
  apply floor_mono.  
  smt(st4).
  have st5_3: t' x n k <= x / n.
  rewrite /t'.
  smt (st4 floor_le).
split.
  have tr : x / n - 2%r  < t' x n k. smt(@Real). 
  have -> : (x - 2%r * n) = (x/n - 2%r)  * n. smt().
  smt().
move => _.
smt(@RealOrder).
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
  = (x - 2%r * n). smt().
smt(st6).
qed.


lemma barrett_bound x n (k : real) :
  0%r <= x < n * n =>
  0%r <= n < 2%r^k =>
  0%r  <= t x n k < 2%r*n .
smt(st7). qed.



require import Int IntDiv.
import Ring.IntID.

op ri(n k : int) : int = (4^k  %/ n).
op ti' (x n k : int) : int = (x * ri n k %/ 4^k).
op ti (x n k : int)  : int = x - (ti' x n k) * n.

lemma divz_eqP (m d n : int) :
  0 < d => m %/ d = n <=> n * d <= m < (n + 1) * d.
proof. smt(@IntDiv).
qed.

lemma floor_div1 a b : 0 < b => a %/ b = floor (a%r / b%r).
move => qp.
apply (divz_eqP     a b (floor (a%r / b%r)) qp).
progress. 
have h1 : (floor (a%r / b%r))%r <= a%r / b%r.
smt (floor_bound).
progress. 
have h2 : (a%r / b%r) * b%r <= a%r. smt().
smt(@Real).
have h1 : a%r < (floor (a%r / b%r) + 1)%r * b%r.
smt (floor_bound).
progress. 
have h2 : a%r < ((a%r / b%r) + 1%r) * b%r. smt().
smt().
qed.


lemma mult_lemma1 a b : a%r * b%r = (a * b)%r.
smt(). qed.

require import RealExp.


lemma exp_lemma1 a :  0 < a => forall  b, 0 <= b  => a%r ^ b%r = (a ^ b)%r.
move => apos. apply intind.
simplify. smt(@RealExp @Ring).
progress. 
have -> : (a ^ (i + 1)) = a * a ^ i. smt(@Ring).
have -> : (a * a ^ i)%r = a%r * (a^i) %r. 
smt(@Ring).
rewrite - H0. simplify. 
have -> : (i + 1)%r = i%r + 1%r. smt().
rewrite rpowD. smt(). smt(@Real @RealExp).
qed.


lemma same_ri (n k : int) : 0 < n => 0 <= k =>
  r n%r k%r = (ri n k)%r.
move => npos kpos.
rewrite /r /ri.
congr.
rewrite floor_div1. auto.
congr. congr.
apply exp_lemma1. auto. auto.
qed.


lemma same_t' (x n k : int) : 0 < n => 0 <= k =>
  t' x%r n%r k%r = (ti' x n k)%r.
move => npos kpos.
rewrite /t' /ti'.
rewrite same_ri. auto. auto.
congr.
rewrite floor_div1. smt(@Ring @StdOrder).
congr. congr.
smt().
rewrite exp_lemma1. auto. auto. auto.
qed.


lemma same_t (x n k : int) : 0 < n => 0 <= k =>
  t x%r n%r k%r = (ti x n k)%r.
progress.
rewrite /t /ti. rewrite same_t'. auto. auto.
smt().
qed.


op barrett_reduction (x n k : int) 
  = let r = ti x n k in (if r < n then r else r - n).

  
lemma barrett_reduction_correct (x n k : int) : 
   0 <= x < n*n
   => 0 < n < 2^k
   => 0 <= k
   => barrett_reduction x n k = x %% n.
rewrite /barrett_reduction.
simplify.
have timn :  ti x n k %% n = x %% n.
rewrite /ti. 
rewrite - modzDm.
have ->: (- ti' x n k * n) %% n  = 0. 
  have -> : (- ti' x n k * n) = (- ti' x n k) * n.  smt().
rewrite - modzMml. 
rewrite modzMl. auto.
simplify. apply modz_mod.
case (ti x n k < n).
progress. rewrite - timn.
rewrite modz_small.
 progress.
  have : 0%r <= (ti x n k)%r.
  rewrite - same_t. smt(). smt(). 
  have kk : 0%r <= t x%r n%r k%r && t x%r n%r k%r < 2%r * n%r.
  apply barrett_bound. progress. progress.  smt(). smt(). split. smt(). move => q. smt(exp_lemma1).
  elim kk. auto. smt().
  have -> : `|n| = n. smt().
  have kk : 0%r <= t x%r n%r k%r && t x%r n%r k%r < 2%r * n%r.
  apply barrett_bound. progress. progress.  smt(). smt(). smt(exp_lemma1).  smt(). auto.
progress.
have :  (ti x n k)%r < (2 * n)%r.
rewrite - same_t. smt(). smt().
  have kk : 0%r <= t x%r n%r k%r && t x%r n%r k%r < 2%r * n%r.
  apply barrett_bound. progress. progress. smt(). smt(). smt(exp_lemma1).  
  smt(). smt(). 
qed.

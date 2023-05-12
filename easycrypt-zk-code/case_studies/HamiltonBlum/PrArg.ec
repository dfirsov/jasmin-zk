pragma Goals:printall.
require import AllCore DBool Bool List Distr Int IntDiv AuxResults FSet DJoin.
require import StdRing StdOrder StdBigop.
(*---*) import RField RealOrder Bigreal BRA.
import BRM.


(*

The section below contains the derivation of the zero-knowledge upper-bound for a Blum-protocol

1. x = x/(1 + z) + xz/(z+1)
2. x/(1 + z) = x - xz/(z+1)
3. xz/(z+1) <= z
   |x / (1/2 + eps) - 2*b| 
=  2 * (|x / (1/2 + eps)/2 - 2*b/2|)
=  2 * (|x / (1 + 2*eps) - b|)
=  2 * (|x - x2eps/(1 + 2*eps) - b|)
<= 2 * (|x - b|) + 2x2eps/(1 + 2*eps)
<= 2 * (|x - b|) + 2*eps
<= 2 * eps + 2 * eps
<= 4eps
*)

section. 

lemma pr2 (x e : real) :
    0%r <= x <= 1%r
 => 0%r <= e <= 1%r
 => x = x/(1%r + e) + x * e/(e + 1%r).
smt().
qed.


local lemma pr3 (x e : real) :
    0%r <= x <= 1%r
 => 0%r <= e <= 1%r
 => x/(1%r + e) = x - x * e/(e + 1%r).
smt (pr2).
qed.

lemma pr_e1 (a e : real) : 
  0%r <= a <= 1%r =>
  `| a - 1%r/2%r | <= e =>
  a <= 1%r/2%r + e.
smt().
qed.


lemma pr_e2 (a e : real) : 
  0%r <= a <= 1%r =>
  `| a - 1%r/2%r | <= e =>
  a >= 1%r/2%r - e.
smt().
qed.


local lemma pr12 (x p b e : real) : 
  0%r <= x <= 1%r =>
  0%r <= p <= 1%r =>
  0%r <= b <= 1%r =>
  0%r <= e <= 1%r =>
  x <= p =>
  p <= (1%r/2%r + e)  =>
  (1%r/2%r - e)  <= p =>
  (x / p - x / (1%r/2%r + e)) =  x * ((1%r/2%r + e) - p) / (p * (1%r/2%r + e))   .
smt(@Real).
qed.


local lemma kk (a b c : real) : 
  a <= b =>
  0%r <= c <= 1%r =>
  a / c <= b / c.
smt(@Real).
qed.

local lemma pr13 (x p b e : real) : 
  0%r <= x <= 1%r =>
  0%r <= p <= 1%r =>
  0%r <= b <= 1%r =>
  0%r <= e <= 1%r/2%r =>
  x <= p =>
  p <= (1%r/2%r + e)  =>
  (1%r/2%r - e)  <= p =>
  x * ((1%r/2%r + e) - p) / (p * (1%r/2%r + e)) 
    <=   x * (2%r * e) / (p * (1%r/2%r + e)) .
progress.
apply kk. smt(). progress;smt().
qed.

local lemma pr14 (x p b e : real) : 
  0%r <= x <= 1%r =>
  0%r <= p <= 1%r =>
  0%r <= b <= 1%r =>
  0%r <= e < 1%r/2%r =>
  x <= p =>
  p <= (1%r/2%r + e)  =>
  (1%r/2%r - e)  <= p =>
     x * (2%r * e) / (p * (1%r/2%r + e)) 
     <=  x * (2%r * e) / ((1%r/2%r - e) * (1%r/2%r + e)).
smt().
qed.


local lemma pr15 (x p b e : real) : 
  0%r <= x <= 1%r =>
  0%r <= p <= 1%r =>
  0%r <= b <= 1%r =>
  0%r <= e < 1%r/2%r =>
  x <= p =>
  p <= (1%r/2%r + e)  =>
  (1%r/2%r - e)  <= p =>
     x * (2%r * e) / ((1%r/2%r - e) * (1%r/2%r + e))
     =  x * (2%r * e) / ((1%r/4%r - e*e)).
smt().
qed.

local lemma pr17 (x p b e : real) : 
  0%r <= x <= 1%r =>
  0%r <= p <= 1%r =>
  0%r <= b <= 1%r =>
  0%r <= e < 1%r/4%r =>
  x <= p =>
  p <= (1%r/2%r + e)  =>
  (1%r/2%r - e)  <= p =>
       (x / p - x / (1%r/2%r + e))
     <=   16%r * e .
progress.
rewrite (pr12 x p b e);auto. smt().
apply (ler_trans (x * (2%r * e) / (p * (1%r/2%r + e)))).
apply (pr13 x p b e);auto. smt().
apply (ler_trans (x * (2%r * e) / ((1%r / 2%r - e) * (1%r / 2%r + e)))). 
apply (pr14 x p b e);auto. smt().
rewrite  (pr15 x p b e);auto. smt(). smt().
qed.



local lemma step1 (x p b e : real) : 
  0%r <= x <= 1%r =>
  0%r <= p <= 1%r =>
  0%r <= b <= 1%r =>
  0%r <= e < 1%r/4%r =>
  x <= p =>
  p <= (1%r/2%r + e) =>
  (1%r/2%r - e) <= p =>
  `| x / p - 2%r * b| <=
  `| x / (1%r/2%r + e) - 2%r * b| + 16%r * e.
progress.
apply (ler_trans (`| x / (1%r/2%r + e) - 2%r * b| + (x / p - x / (1%r/2%r + e)))). smt(). 
have fff : (x / p - x / (1%r / 2%r + e)) <= 16%r * e.
apply (pr17 x p b e);auto.
smt().
qed.

local lemma rp1 x e b  : 
  0%r <= x <= 1%r =>
  0%r <= b <= 1%r =>
  0%r <= e < 1%r/4%r =>
  `| x / (1%r/2%r + e) - 2%r * b|
  = 2%r * (`|x - x*2%r*e / (1%r + 2%r*e) - b|).
smt (pr3).
qed.

local lemma step2 (x p b e : real) : 
  0%r <= x <= 1%r =>
  0%r <= p <= 1%r =>
  0%r <= b <= 1%r =>
  0%r <= e < 1%r/4%r =>
  x <= p =>
  p <= (1%r/2%r + e) =>
  (1%r/2%r - e) <= p =>
   `| x / (1%r/2%r + e) - 2%r * b| + 16%r * e <=
    2%r * (`|x - b|) + 20%r * e.
progress.
rewrite rp1;auto. smt(@Real).
qed.

lemma main_fin (x p b e : real) : 
  0%r <= x <= 1%r =>
  0%r <= p <= 1%r =>
  0%r <= b <= 1%r =>
  0%r <= e < 1%r/4%r =>
  x <= p =>
  p <= (1%r/2%r + e) =>
  (1%r/2%r - e) <= p =>
  `| x / p - 2%r * b|  <= 2%r * `|x - b| + 20%r * e.
progress. apply (ler_trans (`| x / (1%r/2%r + e) - 2%r * b| + 16%r*e)). 
smt(step1).
apply (step2 x p b e);auto.
qed.

end section.


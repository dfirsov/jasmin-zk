require import Core Int Ring IntDiv StdOrder List.

import Ring.IntID IntOrder.

require import JModel.
require import JBigNum.

require import Array7 Array14 Array28.

abbrev nlimbs = 7.
abbrev dnlimbs = 14.

clone import BigNum as W64x4 with
 op nlimbs <- nlimbs,
 theory R.A <= Array7,
 theory R2.A <= Array14
 proof gt0_nlimbs by done.


clone import BigNum as W64x8 with
 op nlimbs <- dnlimbs,
 theory R.A <= Array14,
 theory R2.A <= Array28
 proof gt0_nlimbs by done.

 
type R = W64.t Array7.t.
type R2 = W64.t Array14.t.

(* 2 ^ (64 * nlimbs)  *)
abbrev M = 2 ^ (64 * nlimbs).


op P : int. 

(* parameter for the Barrett reduction  *)
op Ri : int  = 4 ^ (64 * nlimbs) %/ P.

axiom P_prime: prime P.
axiom ppos : 2 * P < W64x4.modulusR.
axiom P_pos : 2 <= P.


(* Embedding into ring theory *)
require ZModP.
clone import ZModP.ZModField as Zp with
        op p <= P
        rename "zmod" as "zp"
        proof prime_p by exact P_prime.

        
(** "Implements" relation *)
abbrev ImplWord x y = W64.to_uint x = y.
abbrev ImplZZ x y = W64x4.valR x = y.
abbrev ImplZZ2 x y = W64x4.valR2 x = y.
abbrev ImplFp x y = W64x4.valR x = asint y.


op pR: R.
axiom pRE: ImplZZ pR P.


op zeroR : R = W64x4.R.A.of_list W64.zero (List.nseq nlimbs W64.zero).



lemma nseqS' ['a]:
  forall (n : int) (x : 'a), 0 < n => nseq n x = x :: nseq (n - 1) x.
smt(nseqS).
qed.


lemma zeroRE: valR zeroR = 0.
proof.
rewrite /zeroR.
do? (rewrite nseqS'; first by trivial). simplify.
rewrite nseq0.
by rewrite /zeroR W64x4.R.bn2seq /= W64x4.R.A.of_listK 1:/# /bn_seq.
qed.


op (^) (x : zp)(n : W64x4.R.t) : zp = inzp (asint x ^ W64x4.valR n).


(******************************************************************)
(*                  ABSTRACT SPECIFICATIONS                       *)
(******************************************************************)

module ASpecFp = {
  (* INTEGER OPS *)
  proc addn(a b: int): bool * int = {
    var c, r;
    c <- W64x4.modulusR <= (a+b);
    r <- (a + b) %% W64x4.modulusR;
    return (c, r);
  }
  proc muln(a b: int): int = {
    var r;
    r <- a * b;
    return r;
  }
 proc redm(a: int): int = {
   var r;
   r <- a %% P;
  return r;
 }
 proc div2(a, n: int): int = {
   var r;
   r <- a %/  (2 ^ n);
  return r;
 }

  proc subn(a b: int): bool * int = {
    var c, r;
    c <- a < b;
    r <- (a - b) %% W64x4.modulusR;
    return (c, r);
  }

  proc dsubn(a b: int): bool * int = {
    var c, r;
    c <- a < b;
    r <- (a - b) %% W64x8.modulusR;
    return (c, r);
  }
  
  proc ctseln(cond: bool, c a: int): int = {
    var r;
    r <- (if cond then a else c);
    return r;
  }
  proc cminusP(a : int): int = {
    var r;
    r <- if a < P then a else a-P;
    return r;
  }

  
  (********************)
  (* Finite Field Ops *)
  (********************)
  proc copym(a: zp): zp = {
    var r;
    r <- a;
    return r;
  }
  proc set0m(): zp = {
    var r;
    r <- Zp.zero;
    return r;
  }

  proc mulm(a b: zp): zp = {
    var r;
    r <- a * b;
    return r;
  }
  proc expm(a : zp,  b: W64x4.R.t): zp = {
    var r;
    r <- a ^ b;
    return r;
  }
  
}.

require import IntDiv.
module CSpecFp = {

 proc redm(a r k: int): int = {
   var xr, xrf, xrfn, t, b;
  xr    <@ ASpecFp.muln(a,r);
  xrf   <@ ASpecFp.div2(xr, 2*k);
  xrf <- xrf %% 2^k;
  xrfn  <@ ASpecFp.muln(xrf, P);
  (b,t) <@ ASpecFp.dsubn(a, xrfn);
  t     <@ ASpecFp.cminusP(t);
  return t;
 }


 proc dcminusP(a: int): int = {
  var c, x, r;
  (c, x) <@ ASpecFp.dsubn(a, P);
  r <@ ASpecFp.ctseln(c, x, a);
  return r;
 }

 proc mulm(a b: int): int = {
  var c, z;
  c <@ ASpecFp.muln(a,b);
  z <@ ASpecFp.redm(c);
  return z;
 }

}.


equiv mulm_eq:
 CSpecFp.mulm ~ ASpecFp.mulm : a{1} = asint a{2} /\ b{1} = asint b{2}  ==> res{1} = asint res{2}.
proof.  proc. inline*. wp.  skip. progress.
smt(@Zp).
qed.

equiv cminusP_eq:
 ASpecFp.cminusP ~ CSpecFp.dcminusP: ={arg} /\ a{2}<W64x8.modulusR  ==> ={res}.
proof.
proc; inline*; wp; skip => &1 &2.
move => [q1  q2].
case (a{2} < P). auto. move => qq. smt(). rewrite q1. move => qq. rewrite qq.
rewrite modz_small. split.  smt().
move => ?. have ->: `|W64x8.modulusR| = W64x8.modulusR. rewrite /W64x8.modulusR. smt(@Ring).
smt(P_pos). auto.
qed.


require import BarrettRedInt.
require import Real RealExp.


equiv redm_eq:
 ASpecFp.redm ~ CSpecFp.redm: ={a} /\ r{2} = (4 ^ k{2} %/ P) 
  /\ 0 < P < W64x4.modulusR
  /\ 0 <= a{2} < P * P
  /\ 0 < P < 2 ^ k{2} 
  /\ 0 <= k{2} ==> ={res}.
proc. inline*. wp. skip. progress.
rewrite -  (barrett_reduction_correct a{2} P k{2} ). auto. auto.  auto. 
rewrite /barrett_reduction. simplify. rewrite /ti. rewrite /ti'. rewrite /ri.
have ->: 2 ^ (2 * k{2}) = 4 ^ k{2}. smt(@Real).
have <-:  a{2} - a{2} * (4 ^ k{2} %/ P) %/ 4 ^ k{2} * P
 = (a{2} - a{2} * (4 ^ k{2} %/ P) %/ 4 ^ k{2}  %%  2 ^ k{2} * P) %% W64x8.modulusR.
rewrite modz_small.
 have ->: a{2} * (4 ^ k{2} %/ P) %/ 4 ^ k{2}  = ti' a{2} P k{2}. 
  rewrite /ti. rewrite /ti'. rewrite /ri. auto.
have -> : ti' a{2} P k{2} %% 2 ^ k{2} = ti' a{2} P k{2}. 
rewrite modz_small. rewrite /ti'. split. 
apply divz_ge0. 
smt(exprn_ege1).
rewrite /ri. 
  have : 0 <= (4 ^ k{2} %/ P). apply divz_ge0.  smt(P_pos). smt(exprn_ege1). smt().
  have ->: `|2 ^ k{2}| = 2 ^ k{2}. smt().
  have : (ti' a{2} P k{2})%r < (2 ^ k{2})%r.
   rewrite - same_t'. auto. auto.
  have qq :  a{2}%r - 2%r * P%r < (t' a{2}%r P%r k{2}%r) * P%r <= a{2}%r. 
   apply st6. smt(). split. smt().  move => ?. rewrite  exp_lemma1. auto. auto. smt(@Real).
  smt(). smt(). auto.
have -> : a{2} - a{2} * (4 ^ k{2} %/ P) %/ 4 ^ k{2} * P
 = ti a{2} P k{2}. rewrite /ti. rewrite /ti'. rewrite /ri. auto.
split. 
   have : 0%r <= (ti a{2} P k{2})%r < 2%r * P%r.
   rewrite - same_t. auto. auto.
     apply (st8 a{2}%r P%r k{2}%r _ _). split.  smt(). smt(). smt(exp_lemma1).
  progress. smt(). 
move => _.
have ->: `|W64x4.modulusR2| = W64x4.modulusR2. rewrite /W64x4.modulusR2. smt(@Ring).
   have : 0%r <= (ti a{2} P k{2})%r < 2%r * P%r.
   rewrite - same_t. auto. auto. 
     apply (st8 a{2}%r P%r k{2}%r _ _). split. smt(). smt().
split. smt(). move => ?. smt(exp_lemma1).
  progress. 
   have : 2 * P < W64x4.modulusR2. rewrite /W64x4.modulusR2. 
   have : W64x8.M ^ (nlimbs) <= W64x8.M ^ (2 * nlimbs).
   apply ler_weexpn2l. smt(). smt().
   have : 2 * P <= W64x8.M ^ ( nlimbs) .    
    have ->: W64x8.M ^ nlimbs = W64x4.modulusR. rewrite /W64x4.modulusR. auto. smt(ppos).
smt(). smt().
 have ->: a{2} * (4 ^ k{2} %/ P) %/ 4 ^ k{2}  = ti' a{2} P k{2}. 
  rewrite /ti. rewrite /ti'. rewrite /ri. auto.
have -> : ti' a{2} P k{2} %% 2 ^ k{2} = ti' a{2} P k{2}. 
rewrite modz_small. rewrite /ti'. split. 
  have : 0 <= ri P k{2} %/ 4 ^ k{2}. apply divz_ge0. smt(exprn_ege1). rewrite /ri.
  apply divz_ge0.  smt(P_pos). smt(exprn_ege1). smt(). 
  have ->: `|2 ^ k{2}| = 2 ^ k{2}. smt().
  have : (ti' a{2} P k{2})%r < (2 ^ k{2})%r.
   rewrite - same_t'. auto. auto.
  have qq :  a{2}%r - 2%r * P%r < (t' a{2}%r P%r k{2}%r) * P%r <= a{2}%r.
   apply st6. smt().  split. smt(). move => ?. smt(exp_lemma1).
  smt().
  smt(). auto.
auto.
auto.
qed.

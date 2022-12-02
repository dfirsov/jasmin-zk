require import Core Int IntDiv Ring IntDiv StdOrder List.

require import JModel JBigNum.

require import Array32 Array64 Array128.

import Ring.IntID IntOrder.

abbrev nlimbs = 32.
abbrev dnlimbs = 64.

clone import BigNum as W64xN with
 op nlimbs <- nlimbs,
 theory R.A <= Array32,
 theory R2.A <= Array64
 proof gt0_nlimbs by done.


clone import BigNum as W64x2N with
 op nlimbs <- dnlimbs,
 theory R.A <= Array64,
 theory R2.A <= Array128
 proof gt0_nlimbs by done.

 
type R = W64.t Array32.t.
type R2 = W64.t Array64.t.

op M = 2 ^ (64 * nlimbs).
op P : int. 

op D : int distr.

axiom ppos : P < W64xN.modulusR.
axiom P_pos : 2 <= P.


(* Embedding into ring theory *)
require ZModP.
clone import ZModP.ZModRing as Zp with
        op p <= P
        rename "zmod" as "zp".


        
(** "Implements" relation *)
abbrev ImplWord x y = W64.to_uint x = y.
abbrev ImplZZ x y = W64xN.valR x = y.
abbrev ImplZZ2 x y = W64xN.valR2 x = y.
abbrev ImplFp x y = W64xN.valR x = asint y.


op pR: R.
axiom pRE: W64xN.valR pR = P.

op zeroR : R = W64xN.R.A.of_list W64.zero (List.nseq nlimbs W64.zero).

lemma nseqS' ['a]:
  forall (n : int) (x : 'a), 0 < n => nseq n x = x :: nseq (n - 1) x.
smt(nseqS).
qed.


lemma zeroRE: valR zeroR = 0.
proof.
rewrite /zeroR.
do? (rewrite nseqS'; first by trivial). simplify.
rewrite nseq0.
by rewrite /zeroR W64xN.R.bn2seq /= W64xN.R.A.of_listK 1:/# /bn_seq.
qed.


op (^) (x : zp)(n : int) : zp = inzp (asint x ^ n).


(******************************************************************)
(*                  ABSTRACT SPECIFICATIONS                       *)
(******************************************************************)
module ASpecFp = {

  (* Integer Operations  *)

  proc addn(a b: int): bool * int = {
    var c, r;
    c <- W64xN.modulusR <= (a+b);
    r <- (a + b) %% W64xN.modulusR;
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
    r <- (a - b) %% W64xN.modulusR;
    return (c, r);
  }

  proc dsubn(a b: int): bool * int = {
    var c, r;
    c <- a < b;
    r <- (a - b) %% W64x2N.modulusR;
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

 
  (* Finite Ring Ops *)

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
  
  proc expm(a : zp,  b: int): zp = {
    var r;
    r <- a ^ b;
    return r;
  }
  
}.

(******************************************************************)
(*                  CONCRETE SPECIFICATIONS                       *)
(******************************************************************)
module CSpecFp = {

 proc redm(a r k: int): int = {
   var xr, xrf, xrfn, t, b;
   xr    <@ ASpecFp.muln(a,r);
   xrf   <@ ASpecFp.div2(xr, 2*k);
   xrf   <- xrf %% 2^k;
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

 proc rsample(a:int) : int * int = {
   var x, b, i,z;
   x <- witness;
   b <- true;
   i <- 0;
   while(b){
     x <$ D;
     (b , z) <@ ASpecFp.subn(x,a);
     b <- !b;
     i <- i + 1;
   }
   return (i,x);
 }

}.



require RejectionSampling.
clone import RejectionSampling as RS with type X <- int,
                                          op d <- D.


op RSP a x =  x < a.
lemma rsample_pr1  a1  &m r : 
  Pr[CSpecFp.rsample(a1) @ &m : res = r]
  =  Pr[RS.sample(RSP a1, 0) @ &m : res = r].
byequiv (_: arg{1} = a1 /\ c{2} = 0 /\ P{2} = RSP a1  ==> _) .
proc. sp.
while (a{1} = a1 /\ P{2} = RSP a1 /\ i{1} = c{2} /\ b{1} = !b{2} /\ x{1} = x{2} ).
wp. inline*. wp.  rnd. skip. progress. rewrite /RSP.
skip. progress. auto. auto.
qed.

require import Real AllCore.

lemma rsample_pr a1 &m i x : 1 <= i => RSP a1 x =>
    Pr[CSpecFp.rsample(a1) @ &m : res = (i,x) ]
     = (mu D (predC (RSP a1)) ^ (i - 1) * mu D (pred1 x)).
progress.
rewrite rsample_pr1.
have ->: Pr[RS.sample(RSP a1, 0) @ &m : res = (i, x)] 
 = Pr[RS.sample(RSP a1, 0) @ &m : res.`2 = x /\ res.`1 = i]. 
rewrite Pr[mu_eq]. smt(). auto.
rewrite   (Indexed.prob  &m (RSP a1) (fun z => z = x) _ (i - 1) _).
progress.  auto. smt(). congr. simplify. smt(@Distr).
qed.



lemma rsample_lossless a1 &m  : 0%r < mu D (RSP a1) =>
    Pr[CSpecFp.rsample(a1) @ &m : true ]
     = 1%r.
have ->: Pr[CSpecFp.rsample(a1) @ &m : true ]
  =  Pr[RS.sample(RSP a1, 0) @ &m : true ].
byequiv (_: arg{1} = a1 /\ c{2} = 0 /\ P{2} = RSP a1  ==> _) .
proc. sp.
while (a{1} = a1 /\ P{2} = RSP a1  /\ b{1} = !b{2} /\ x{1} = x{2} ).
wp. inline*. wp.  rnd. skip. progress. rewrite /RSP.
    skip. progress. auto. auto.
progress.
have xx : Pr[RS.sample(RSP a1, 0) @ &m : RSP a1 res.`2 ] = 1%r.
apply (Correctness.rj_lossless &m (RSP a1) 0 _) .  auto. 
smt(@Distr).
qed.



equiv mulm_eq:
 CSpecFp.mulm ~ ASpecFp.mulm: 
  a{1} = asint a{2} /\ b{1} = asint b{2}  
    ==> res{1} = asint res{2}.
proof.  proc. inline*. wp.  skip. progress.
smt(@Zp).
qed.

equiv cminusP_eq:
 ASpecFp.cminusP ~ CSpecFp.dcminusP: 
 ={arg} /\ a{2}<W64x2N.modulusR ==> ={res}.
proof.
proc; inline*; wp; skip => &1 &2.
move => [q1  q2].
case (a{2} < P). auto. move => qq. smt(). rewrite q1. move => qq. rewrite qq.
rewrite modz_small. split.  smt().
move => ?. have ->: `|W64x2N.modulusR| = W64x2N.modulusR. rewrite /W64x2N.modulusR. smt(@Ring).
smt(P_pos). auto.
qed.


require import BarrettRedInt.
require import Real RealExp.

(* parameter for the Barrett reduction  *)
op Ri : int  = 4 ^ (64 * nlimbs) %/ P.

equiv redm_eq:
 ASpecFp.redm ~ CSpecFp.redm: ={a} /\ r{2} = (4 ^ k{2} %/ P) 
  /\ 0 < P < W64xN.modulusR
  /\ 0 <= a{2} < P * P
  /\ 0 < P < 2 ^ k{2} 
  /\ 0 <= k{2} ==> ={res}.
proc. inline*. wp. skip. progress.
rewrite -  (barrett_reduction_correct a{2} P k{2} ). auto. auto.  auto. 
rewrite /barrett_reduction. simplify. rewrite /ti. rewrite /ti'. rewrite /ri.
have ->: 2 ^ (2 * k{2}) = 4 ^ k{2}. smt(@Real).
have <-:  a{2} - a{2} * (4 ^ k{2} %/ P) %/ 4 ^ k{2} * P
 = (a{2} - a{2} * (4 ^ k{2} %/ P) %/ 4 ^ k{2}  %%  2 ^ k{2} * P) %% W64x2N.modulusR.
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
have ->: `|W64xN.modulusR2| = W64xN.modulusR2. rewrite /W64xN.modulusR2. smt(@Ring).
   have : 0%r <= (ti a{2} P k{2})%r < 2%r * P%r.
   rewrite - same_t. auto. auto. 
     apply (st8 a{2}%r P%r k{2}%r _ _). split. smt(). smt().
split. smt(). move => ?. smt(exp_lemma1).
  progress. 
   have : 2 * P < W64xN.modulusR2. rewrite /W64xN.modulusR2. 
   have : W64x2N.M ^ (nlimbs) <= W64x2N.M ^ (2 * nlimbs).
   apply ler_weexpn2l. smt(). smt().
   have : P <= W64x2N.M ^ ( nlimbs) .    
    have ->: W64x2N.M ^ nlimbs = W64xN.modulusR. rewrite /W64xN.modulusR. auto. smt(ppos).
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

require import Core Int Ring IntDiv StdOrder List.

import Ring.IntID IntOrder.

require import JModel.
require import JBigNum.

require import Array4 Array8 Array16.

abbrev nlimbs = 4.

clone import BigNum as W64x4 with
 op nlimbs <- nlimbs,
 theory R.A <= Array4,
 theory R2.A <= Array8
 proof gt0_nlimbs by done.


clone import BigNum as W64x8 with
 op nlimbs <- 8,
 theory R.A <= Array8,
 theory R2.A <= Array16
 proof gt0_nlimbs by done.

 
type R = W64.t Array4.t.
type R2 = W64.t Array8.t.

abbrev M = 115792089237316195423570985008687907853269984665640564039457584007913129639936.


op P : int. 

axiom P_prime: prime P.
axiom ppos : 2 * P < W64x4.modulusR.


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

op zeroR : R = W64x4.R.A.of_list W64.zero
                 [ W64.zero; W64.zero; W64.zero; W64.zero ].



lemma zeroRE: valR zeroR = 0.
proof.
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

  (* proc subn(a b: int): bool * int = { *)
  (*   var c, r; *)
  (*   c <- a < b; *)
  (*   r <- (a - b) %% W64x4.modulusR; *)
  (*   return (c, r); *)
  (* }   *)

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

}.


equiv cminusP_eq:
 ASpecFp.cminusP ~ CSpecFp.dcminusP: ={arg} /\ a{2}<W64x8.modulusR  ==> ={res}.
proof.
proc; inline*; wp; skip => &1 &2.
have ->: W64x8.modulusR = 2^512 by rewrite W64x8.R.bn_modulusE /= !mulrA expr0.
progress. smt.
(* case (a{2} < P). auto. progress. *)
(* have : (a{2} - P) < modulusR.  smt. progress. smt. *)
qed.


require import BarrettRedInt.
require import Real RealExp.
equiv redm_eq:
 ASpecFp.redm ~ CSpecFp.redm: ={a} /\ r{2} = (nlimbs ^ k{2} %/ P) 
  /\ 0 < P < W64x4.modulusR
  /\ 0 <= a{2} < P * P
  /\ 0 < P < 2 ^ k{2} 
  /\ 0 <= k{2} ==> ={res}.
proc. inline*. wp. skip. progress.
rewrite -  (barrett_reduction_correct a{2} P k{2} ). auto. auto.  auto. 
rewrite /barrett_reduction. simplify. rewrite /ti. rewrite /ti'. rewrite /ri.
have ->: 2 ^ (2 * k{2}) = 4 ^ k{2}. smt.
have <-:  a{2} - a{2} * (nlimbs ^ k{2} %/ P) %/ nlimbs ^ k{2} * P
 = (a{2} - a{2} * (nlimbs ^ k{2} %/ P) %/ nlimbs ^ k{2}  %% 2 ^ k{2} * P) %% W64x4.modulusR2.
rewrite modz_small.

 have ->: a{2} * (nlimbs ^ k{2} %/ P) %/ nlimbs ^ k{2}  = ti' a{2} P k{2}. 
  rewrite /ti. rewrite /ti'. rewrite /ri. auto.

have -> : ti' a{2} P k{2} %% 2 ^ k{2} = ti' a{2} P k{2}. 
rewrite modz_small. rewrite /ti'. split. smt. move => ?.
(* admit. admit. *)

  have ->: `|2 ^ k{2}| = 2 ^ k{2}. smt().
  have : (ti' a{2} P k{2})%r < (2 ^ k{2})%r.
   rewrite - same_t'. auto. auto.

  have qq :  a{2}%r - 2%r * P%r < (t' a{2}%r P%r k{2}%r) * P%r <= a{2}%r.
   apply st6. smt. timeout 10. smt.
  smt.
  smt. auto.


have -> : a{2} - a{2} * (nlimbs ^ k{2} %/ P) %/ nlimbs ^ k{2} * P
 = ti a{2} P k{2}. rewrite /ti. rewrite /ti'. rewrite /ri. auto.

split. 
   have : 0%r <= (ti a{2} P k{2})%r < 2%r * P%r.
   rewrite - same_t. auto. auto.
     apply (st8 a{2}%r P%r k{2}%r _ _). split.  smt. smt. smt.
  progress. smt. 
move => _.
have ->: `|W64x4.modulusR2| = W64x4.modulusR2. smt.
   have : 0%r <= (ti a{2} P k{2})%r < 2%r * P%r.
   rewrite - same_t. auto. auto. 
     apply (st8 a{2}%r P%r k{2}%r _ _). smt.
split. smt. move => ?. timeout 10. smt.
  progress.   
   have : 2 * P < W64x4.modulusR2.   timeout 15. smt.
smt.

 have ->: a{2} * (nlimbs ^ k{2} %/ P) %/ nlimbs ^ k{2}  = ti' a{2} P k{2}. 
  rewrite /ti. rewrite /ti'. rewrite /ri. auto.

have -> : ti' a{2} P k{2} %% 2 ^ k{2} = ti' a{2} P k{2}. 
rewrite modz_small. rewrite /ti'. split. smt. move => ?.
(* admit. admit. *)

  have ->: `|2 ^ k{2}| = 2 ^ k{2}. smt().
  have : (ti' a{2} P k{2})%r < (2 ^ k{2})%r.
   rewrite - same_t'. auto. auto.

  have qq :  a{2}%r - 2%r * P%r < (t' a{2}%r P%r k{2}%r) * P%r <= a{2}%r.
   apply st6. smt. timeout 10. smt.
  smt.
  smt. auto.

 
auto.
auto.
qed.

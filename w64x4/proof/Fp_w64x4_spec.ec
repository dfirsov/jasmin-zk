require import Core Int Ring IntDiv StdOrder List.

import Ring.IntID IntOrder.

require import JModel.
require import JBigNum.

require import Array4 Array8.

abbrev nlimbs = 4.

clone import BigNum as W64x4 with
 op nlimbs <- nlimbs,
 theory R.A <= Array4,
 theory R2.A <= Array8
 proof gt0_nlimbs by done.

type R = W64.t Array4.t.
type R2 = W64.t Array8.t.

abbrev M = 115792089237316195423570985008687907853269984665640564039457584007913129639936.
(* modular operations modulo P *)


op P : int. 

axiom P_prime: prime P.
axiom ppos : 2 * P < M.


(* Embedding into ring theory *)
require ZModP.
clone import ZModP.ZModField as Zp with
        op p <= P
        rename "zmod" as "zp"
        proof prime_p by exact P_prime.

        
(** "Implements" relation *)
abbrev ImplWord x y = W64.to_uint x = y.
abbrev ImplZZ x y = valR x = y.
abbrev ImplZZ2 x y = valR2 x = y.
abbrev ImplFp x y = valR x = asint y.


op pR: R.
axiom pRE: ImplZZ pR P.

op zeroR : R = R.A.of_list W64.zero
                 [ W64.zero; W64.zero; W64.zero; W64.zero ].



lemma zeroRE: valR zeroR = 0.
proof.
by rewrite /zeroR R.bn2seq /= R.A.of_listK 1:/# /bn_seq.
qed.


op (^) (x : zp)(n : R.t) : zp = inzp (asint x ^ W64x4.valR n).


(******************************************************************)
(*                  ABSTRACT SPECIFICATIONS                       *)
(******************************************************************)

module ASpecFp = {
  (* INTEGER OPS *)
  proc addn(a b: int): bool * int = {
    var c, r;
    c <- modulusR <= (a+b);
    r <- (a + b) %% modulusR;
    return (c, r);
  }
  proc muln(a b: int): int = {
    var r;
    r <- a * b;
    return r;
  }

  proc subn(a b: int): bool * int = {
    var c, r;
    c <- a < b;
    r <- (a - b) %% modulusR;
    return (c, r);
  }  
  proc ctseln(cond: bool, c a: int): int = {
    var r;
    r <- (if cond then a else c);
    return r;
  }
  proc cminusP(a: int): int = {
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
  (* modular operations: finite field [Fp] *)
  proc addm(a b: zp): zp = {
    var r;
    r <- a + b;
    return r;
  }
  proc mulm(a b: zp): zp = {
    var r;
    r <- a * b;
    return r;
  }
  proc expm(a : zp,  b: R.t): zp = {
    var r;
    r <- a ^ b;
    return r;
  }
  
}.


module CSpecFp = {
 proc addm(a b: zp): int = {
  var c, x, r;
  (c, x) <@ ASpecFp.addn(asint a, asint b);
  r <@ ASpecFp.cminusP(x);
  return r;
 }
 proc cminusP(a: int): int = {
  var c, x, r;
  (c, x) <@ ASpecFp.subn(a, P);
  r <@ ASpecFp.ctseln(c, x, a);
  return r;
 }

}.

equiv cminusP_eq:
 ASpecFp.cminusP ~ CSpecFp.cminusP: ={a} /\ a{2}<modulusR ==> ={res}.
proof.
proc; inline*; wp; skip => &1 &2.
have ->: modulusR = 2^256 by rewrite R.bn_modulusE /= !mulrA expr0. 
progress. smt.
qed.

equiv addm_eq:
 ASpecFp.addm ~ CSpecFp.addm: ={a,b} ==> asint res{1}=res{2}.
proof.
proc; simplify.
+ inline*; wp; skip => /> &2.
  have ->: (asint a{2} + asint b{2}) %% modulusR = (asint a{2} + asint b{2}).
   rewrite modz_small. progress. smt. smt.
   done.
  case: (asint a{2} + asint b{2} < P) => H.
   by rewrite addE modz_small; smt(rg_asint).
  rewrite addE. smt. 
qed.



require import Core Int IntDiv Ring IntDiv StdOrder List Distr Real.
require import AuxLemmas.

from Jasmin require import JModel JBigNum.
require import Array32 Array64 Array128.
import Ring.IntID IntOrder.

abbrev nlimbs = 32.
abbrev dnlimbs = 64.

require import Array3.

clone import BigNum as W64xN with
 op nlimbs <- nlimbs,
 theory R.A <= Array32,
 theory R2.A <= Array64,
 theory Array3 <= Array3
proof*.
realize gt0_nlimbs by done.


op as_word (x : bool) : W64.t  = x ? W64.one : W64.zero.
op ith_bitword64 (n : W64.t) (x : int)  : W64.t = as_word (n.[x]).


lemma ones64 : (2^64  - 1)  = 18446744073709551615. smt(). qed.
op as_bool (x : W64.t) : bool  = (x = W64.one).
op as_w64 (x : bool) : W64.t  = x ? W64.one : W64.zero.


lemma kok (a b c : real) : 0%r <= a => 0%r < b => 1%r < c =>
 a <= b / c => a < b.
smt(@Real).
qed.


clone import BigNum as W64x2N with
 op nlimbs <- dnlimbs,
 theory R.A <= Array64,
 theory R2.A <= Array128,
 theory Array3 <= Array3
proof*.
realize gt0_nlimbs by done.

 
type R = W64.t Array32.t.
type R2 = W64.t Array64.t.

op M : int = W64xN.modulusR.

op D : int distr = duniform (range 0 M).
lemma D_ll : is_lossless D. apply duniform_ll.  
 have q : 0 < Top.M . smt. smt(@List). qed.
lemma D_uni : is_uniform D. smt(@Distr). qed.
lemma D_sup x : x \in D <=> 0 <= x < M. smt(@Distr). qed.
lemma D_mu x : x \in D => mu1 D x = Real.inv M%r. smt(@Distr). qed.


(* Embedding Zp theory *)
require ZModP.
clone import ZModP.ZModField as Zp.
  (* TODO proof* or make this theory abstract *)


op (^^) (x : zmod)(n : int) : zmod = ZModpRing.exp x n. 
op (^) (x : zmod)(n : int) : zmod = inzmod (asint x ^ n).

lemma M_pos : 2 < M. rewrite /M. rewrite /W64xN.modulusR.
smt(@Int). qed.


(* opaque constants to make typechecking faster *)
op Ri : int = nasty_id (4 ^ (64 * nlimbs) %/ p).
lemma Ri_def : Ri = (4 ^ (64 * nlimbs) %/ p).
rewrite /Ri. smt(nasty_id). qed.

op oneR : R = (of_list W64.zero (W64.one :: nseq (nlimbs - 1) W64.zero ))%Array32.

op R : W64.t Array64.t = W64xN.R2.bn_ofint Ri.

op Rip : int = nasty_id (4 ^ (dnlimbs * nlimbs) %/ (p-1)).
lemma Rip_def: Rip = 4 ^ (dnlimbs * nlimbs) %/ (p-1).
rewrite /Rip. smt(nasty_id). qed.


(* cyclic group generator *)
lemma P_pos : 2 <= p. smt(@Zp). qed.
axiom M_P : p < M.

lemma pmoval:  p - 1 < W64xN.modulusR. by smt(@Int M_P). qed.
        
(** "Implements" relation *)
abbrev ImplWord x y = W64.to_uint x = y.
abbrev ImplZZ x y = W64xN.valR x = y.
abbrev ImplZZ2 x y = W64xN.valR2 x = y.
abbrev ImplFp x y = W64xN.valR x = asint y.

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
  
  proc redm(a p: int): int = {
    var r;
    r <- a %% p;
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

  proc swapr(a : zmod, b : zmod, c : bool) = {
    return c ? (b,a) : (a, b);
  }

  proc cminusP(a: int): int = {
    var r;
    r <- if a < p then a else a-p;
    return r;
  }
  

  proc cminus(a p: int): int = {
    var r;
    r <- if a < p then a else a-p;
    return r;
  }

  proc rsample(a : int): int = {
    var r;
    r <$ duniform (range 0 a);
    return r;
  }

 
  (* Finite Ring Ops *)
  proc addm(a b p: int): int = {
    var r;
    r <- a + b;
    return r %% p;
  }

  proc copym(a: zmod): zmod = {
    var r;
    r <- a;
    return r;
  }
  
  proc set0m(): zmod = {
    var r;
    r <- Zp.zero;
    return r;
  }

  proc mulm(a b: zmod): zmod = {
    var r;
    r <- a * b;
    return r;
  }
  
  proc expm(a : zmod,  b: int): zmod = {
    var r;
    r <- a ^ b;
    return r;
  }
  
}.
require import Distr DInterval. 
(******************************************************************)
(*                  CONCRETE SPECIFICATIONS                       *)
(******************************************************************)

require import BitEncoding.

module CSpecFp = {
 proc swapr(a : W64xN.R.t, b : W64xN.R.t, c : bool) = {
   return c ? (b,a) : (a, b);
 }

 proc ith_bit (r: W64xN.R.t, ctr:int) : W64.t = {
    return (nth false (BS2Int.int2bs (64 * nlimbs) (W64xN.valR r)) ctr) ? W64.one : W64.zero;
 }


 proc addm(a b p: int): int = {
  var c, x, r;
  (c, x) <@ ASpecFp.addn(a, b);
  r <@ ASpecFp.cminus(x, p);
  return r;
 }

 proc redm(a r k p: int): int = {
   var xr, xrf, xrfn, t, b;
   xr    <@ ASpecFp.muln(a,r);
   xrf   <@ ASpecFp.div2(xr, 2*k);
   xrf   <- xrf %% 2^k;
   xrfn  <@ ASpecFp.muln(xrf, p);
   (b,t) <@ ASpecFp.dsubn(a, xrfn);
   t     <@ ASpecFp.cminus(t,p);
   return t;
 }

 proc dcminusP(a: int): int = {
  var c, x, r;
  (c, x) <@ ASpecFp.dsubn(a, p);
  r <@ ASpecFp.ctseln(c, x, a);
  return r;
 }

 proc cminus(a p: int): int = {
  var c, x, r;
  (c, x) <@ ASpecFp.subn(a, p);
  r <@ ASpecFp.ctseln(c, x, a);
  return r;
 }


 proc dcminus(a p: int): int = {
  var c, x, r;
  (c, x) <@ ASpecFp.dsubn(a, p);
  r <@ ASpecFp.ctseln(c, x, a);
  return r;
 }



 proc mulm(a b p: int): int = {
  var c, z;
  c <@ ASpecFp.muln(a,b);
  z <@ ASpecFp.redm(c,p);
  return z;
 }

 proc rsample(a:int) : int * int = {
   var x, b, i,z;
   x <- 0;
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


equiv addm_eq:
 ASpecFp.addm ~ CSpecFp.addm: ={a,b,p} /\ 0 <= a{1} < p{1} /\ 0 <= b{1} < p{1} /\ 0 <= 2*p{1} < W64xN.modulusR ==> res{1}=res{2}.
proof.
proc; simplify.
 inline*. wp. skip.
progress.
  have ->: (a{2} +  b{2}) %% W64xN.modulusR = (a{2} +  b{2}).
   rewrite modz_small. split. smt. move => H5. 
   have ->: `|W64xN.modulusR| = W64xN.modulusR. smt.
   smt. done.
  case: (a{2} + b{2} < p{2}) => H5.
   rewrite   modz_small. smt(rg_asint). done.
   smt.
qed.


equiv cminusP_eq:
 ASpecFp.cminusP ~ CSpecFp.dcminusP: 
 ={arg} /\ a{2}<W64x2N.modulusR ==> ={res}.
proof.
proc; inline*; wp; skip => &1 &2.
move => [q1  q2].
case (a{2} < p). auto. move => qq. smt(). rewrite q1. move => qq. rewrite qq.
rewrite modz_small. split.  smt().
move => ?. have ->: `|W64x2N.modulusR| = W64x2N.modulusR. rewrite /W64x2N.modulusR. smt(@Ring).
smt(P_pos). auto.
qed.


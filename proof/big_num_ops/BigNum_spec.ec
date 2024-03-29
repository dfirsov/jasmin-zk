require import Core Int IntDiv Ring IntDiv StdOrder List Distr Real DInterval.
import Ring.IntID IntOrder.
import StdBigop Bigint BIA.

require import BitEncoding.
import BS2Int.

require import AuxLemmas.

from Jasmin require import JModel.

require export BigNum_instances.
import W64xN R.

op as_word (x : bool) : W64.t  = x ? W64.one : W64.zero.
op ith_bitword64 (n : W64.t) (x : int)  : W64.t = as_word (n.[x]).

lemma ones64 : (2^64  - 1)  = 18446744073709551615. auto. qed.
op as_bool (x : W64.t) : bool  = (x = W64.one).
op as_w64 (x : bool) : W64.t  = x ? W64.one : W64.zero.

 
op D : int distr = duniform (range 0 W64xN.modulusR).
lemma D_ll : is_lossless D. apply duniform_ll.  
 have q : 0 < W64xN.modulusR. auto. smt(@List). qed.
lemma D_uni : is_uniform D. smt(@Distr). qed.
lemma D_sup x : x \in D <=> 0 <= x < W64xN.modulusR. smt(@Distr). qed.
lemma D_mu x : x \in D => mu1 D x = Real.inv W64xN.modulusR%r. smt(@Distr). qed.

lemma M_pos : 2 < W64xN.modulusR. auto. qed.


(** "Implements" relation *)
abbrev ImplZZ x y = W64xN.valR x = y.
  
op oneR  : W64xN.R.t = W64xN.R.A.of_list W64.zero (W64.one :: nseq (nlimbs - 1) W64.zero).
op zeroR : W64xN.R.t = W64xN.R.A.of_list W64.zero (List.nseq nlimbs W64.zero).

lemma zeroRE: W64xN.valR zeroR = 0.
rewrite /zeroR.
have nseqS'  : forall  (n : int) (x : W64.t), 0 < n => nseq n x = x :: nseq (n - 1) x. smt(nseqS).
do? (rewrite nseqS'; first by trivial). simplify.
rewrite nseq0.
by rewrite /zeroR W64xN.R.bn2seq /= W64xN.R.A.of_listK 1:/# /bn_seq.
qed.


lemma oneRE: ImplZZ oneR 1.
rewrite /oneR /valR /bnk.
do? (rewrite range_ltn; first by trivial ).
simplify. rewrite range_geq. auto.
do rewrite big_consT.
rewrite big_nil.
 have -> : W64xN.R.dig ((W64xN.R.A.of_list W64.zero (W64.one :: nseq (nlimbs - 1) W64.zero)))%W64xN.R.A 0 = 1.
 simplify. smt(@W64 @W64xN.R.A).
 have q : forall x, 0 < x < nlimbs => W64xN.R.dig ((W64xN.R.A.of_list W64.zero (W64.one :: nseq (nlimbs - 1) W64.zero)))%W64xN.R.A x = 0.
 move => x xp. rewrite /dig.
   have ->: to_uint ((W64xN.R.A.of_list W64.zero (W64.one :: nseq (nlimbs - 1) W64.zero)).[x])%A = 0. 
   have nseqS'  : forall  (n : int) (x : W64.t), 0 < n => nseq n x = x :: nseq (n - 1) x. smt(nseqS).
    do? (rewrite nseqS'; first by trivial). simplify. 
   rewrite nseq0.
  have -> : (A.of_list W64.zero [W64.one; W64.zero]).[x]%A = W64.zero.  
smt(A.get_of_list). smt().
smt(@List).  
do? (rewrite q; first smt()). auto.
qed.



module ASpecFp = {
  proc addn(a b: int): bool * int = {
    var c, r;
    c <- W64xN.modulusR <= (a+b);
    r <- (a + b) %% W64xN.modulusR;
    return (c, r);
  }
  proc daddn(a b: int): bool * int = {
    var c, r;
    c <- W64x2N.modulusR <= (a+b);
    r <- (a + b) %% W64x2N.modulusR;
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
  proc addm(a b p: int): int = {
    var r;
    r <- a + b;
    return r %% p;
  }  
}.


module CSpecFp = {
 proc swapr(a : W64xN.R.t, b : W64xN.R.t, c : bool) = {
   return c ? (b,a) : (a, b);
 }
 proc ith_bit (r: W64xN.R.t, ctr:int) : W64.t = {
    return (nth false (BS2Int.int2bs (64 * nlimbs) (W64xN.valR r)) ctr) 
              ? W64.one : W64.zero;
 }
 proc addm(a b p: int): int = {
  var c, x, r;
  (c, x) <@ ASpecFp.addn(a, b);
  r <@ ASpecFp.cminus(x, p);
  return r;
 }
 proc daddm(a b p: int): int = {
  var c, x, r;
  (c, x) <@ ASpecFp.daddn(a, b);
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
   rewrite modz_small. split. smt(). move => H5. 
   have ->: `|W64xN.modulusR| = W64xN.modulusR. auto. 
   smt(). done.
  case: (a{2} + b{2} < p{2}) => H5.
   rewrite   modz_small. 
   smt().
   done.
   smt().
qed.


equiv daddm_eq:
 ASpecFp.addm ~ CSpecFp.daddm: ={a,b,p} /\ 0 <= a{1} < p{1} /\ 0 <= b{1} < p{1} /\ 0 <= 2*p{1} < W64x2N.modulusR ==> res{1}=res{2}.
proof.
proc; simplify.
 inline*. wp. skip.
progress.
  have ->: (a{2} +  b{2}) %% W64x2N.modulusR = (a{2} +  b{2}).
   rewrite modz_small. split. smt(). move => H5. 
   have ->: `|W64x2N.modulusR| = W64x2N.modulusR. auto.
   smt(). done.
  case: (a{2} + b{2} < p{2}) => H5.
   rewrite   modz_small. smt(). done.
   smt().
qed.


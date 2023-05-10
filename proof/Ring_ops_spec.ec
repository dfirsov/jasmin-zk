require import Core Int IntDiv Ring IntDiv StdOrder List Distr .

from Jasmin require import JBigNum.
from Jasmin require import Array32 Array64 Array128.

from Jasmin require import JModel.



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

op M : int = W64xN.modulusR.


op D : int distr = duniform (range 0 M).
lemma D_ll : is_lossless D. apply duniform_ll.  
 have q : 0 < Top.M . smt. smt(@List). qed.
lemma D_uni : is_uniform D. smt(@Distr). qed.
lemma D_sup x : x \in D <=> 0 <= x < M. smt(@Distr). qed.
lemma D_mu x : x \in D => mu1 D x = Real.inv M%r. smt(@Distr). qed.




(* Embedding into ring theory *)
require ZModP.
clone import ZModP.ZModField as Zp 
        rename "zmod" as "zp".


op (^^) (x : zp)(n : int) : zp = ZModpRing.exp x n.

lemma M_pos : 2 < M. rewrite /M. rewrite /W64xN.modulusR.
smt(@Int). qed.

(* constants to make typechecking faster *)
op Ri : int.
axiom Ri_def : Ri = 4 ^ (64 * nlimbs) %/ p.
op Rip : int.
axiom Rip_def: Rip = 4 ^ (dnlimbs * nlimbs) %/ (p-1).

(* cyclic group generator *)
op g : zp.   

axiom P_pos : 2 <= p.
axiom M_P : p < M.

lemma pmoval:  p - 1 < W64xN.modulusR. by smt(@Int M_P). qed.

axiom p_val_prop1 x : W64xN.valR x < (p-1) * (p-1). 
axiom p_val_prop2 : 2*p < W64xN.modulusR. 



axiom exp_pow x n : x ^^ n = x ^^ (n %% (p-1)).
axiom exps (s : zp) c : Sub.val (s ^^ c) = ((Sub.val s) ^ c) %% p.


        
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
require import Distr DInterval. 
(******************************************************************)
(*                  CONCRETE SPECIFICATIONS                       *)
(******************************************************************)
module CSpecFp = {
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



require RejectionSampling.
clone import RejectionSampling as RS with type X <- int,
                                          op d <- D,
                                          op defX <- 0.


op RSP (a:int) x =  x < a.
lemma rsample_pr1  a1  &m r : 
  Pr[CSpecFp.rsample(a1) @ &m : res = r]
  =  Pr[RS.sample(RSP a1, 0) @ &m : res = r].
byequiv (_: arg{1} = a1 /\ c{2} = 0 /\ P{2} = RSP a1  ==> _) .
proc. sp.
while (a{1} = a1 /\ P{2} = RSP a1 /\ i{1} = c{2} /\ b{1} = !b{2} /\ x{1} = x{2} ).
wp. inline*. wp.  rnd. skip. progress. rewrite /RSP.  
skip. progress. auto. auto.
qed.

lemma rsample_pr2  a1  &m PP : 
  Pr[CSpecFp.rsample(a1) @ &m : PP res]
  =  Pr[RS.sample(RSP a1, 0) @ &m : PP res].
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
have ->: Pr[RS.sample(RSP a1, 0) @ &m  : res = (i, x)] 
 = Pr[RS.sample(RSP a1, 0) @ &m : res.`2 = x /\ res.`1 = i]. 
rewrite Pr[mu_eq]. smt(). auto.
rewrite   (Indexed.prob  &m (RSP a1) (fun z => z = x) _ (i - 1) _).
progress.  auto. smt(). congr. simplify. smt(@Distr).
qed.

require import Aux.

(* need to prove what Top.M equals to (W64x2N.modulusR ?) *)
lemma rsample_uni &m x P : P < M =>  0 <= x =>  RSP P x =>
    Pr[CSpecFp.rsample(P) @ &m : res.`2 = x ]
     = 1%r / P%r.
move => H1 H2 H3.
rewrite  (rsample_pr2 P &m (fun (rres : int * int) => rres.`2 = x)). 
simplify.
rewrite (Correctness.ph_main  &m (RSP P)  (fun rres => rres = x) ). smt().
 have -> : mu D (predC (RSP P)) = 1%r - mu D (RSP P).
rewrite mu_not.  smt. 
 have q : mu D (RSP P) > 0%r. 
 apply witness_support.
  exists 0. smt.
 smt.
have -> : mu D (transpose (=) x) = 1%r / M%r. apply  D_mu. 
have : x < M. smt(). smt (D_sup).
have -> : mu D (predC (RSP P)) = 1%r - mu D ((RSP P)).  
rewrite mu_not. rewrite /weight.
rewrite is_losslessP. apply D_ll. smt().
have -> : mu D (RSP P) = P%r / M%r. rewrite /RSP.
have -> : mu D (transpose Int.(<) P)
 = mu D (LessThan P).
apply mu_eq_support.
smt (D_sup). 
rewrite (d_uni_sum D M _ _ _ P _ _). apply D_uni.
apply D_ll. move => x0. rewrite /LessThan. move => q. 
smt(D_sup).
smt. smt(). congr.
rewrite - (D_mu x _). 
 have : x < M. smt. smt(D_sup). simplify. 
rewrite mu1_uni_ll. apply D_uni. apply D_ll.
have -> : x \in D = true. 
 have : x < M. smt. smt(D_sup). simplify. smt().
smt.
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


lemma rsample_lossless2 a1 &m  : 
    Pr[CSpecFp.rsample(a1) @ &m :  ! (res.`2 \in D) ]
     = 0%r.
byphoare (_: arg = a1 ==> _). hoare.  proc.
sp. while (x \in D). wp.  inline*. wp.  rnd. skip.
progress. skip. progress. smt. auto. auto.
qed.

lemma rsample_lossless3 a1 &m  : 0%r < mu D (RSP a1) =>
    Pr[CSpecFp.rsample(a1) @ &m : (res.`2 \in D)  ]
     = 1%r.
move => ass.
rewrite - (rsample_lossless a1 &m). 
auto.
have -> : Pr[CSpecFp.rsample(a1) @ &m : true]
 = Pr[CSpecFp.rsample(a1) @ &m : res.`2 \in D]
  + Pr[CSpecFp.rsample(a1) @ &m : !(res.`2 \in D)].
rewrite Pr[mu_split (res.`2 \in D)] . auto.
rewrite rsample_lossless2. auto.
qed.


lemma rsample_lossless4 P &m  : 0 < P < M =>
    Pr[CSpecFp.rsample(P) @ &m : LessThan P res.`2  ]
     = 1%r.
move => PP.
rewrite - (Correctness.rj_lossless &m (RSP P) 0 _ ).  
 apply witness_support.
  exists 0. split. rewrite /RSP. smt. smt.
rewrite -   (rsample_pr2 P &m (fun (rres : int * int) => RSP P rres.`2)).
simplify.
have -> : Pr[CSpecFp.rsample(P) @ &m : RSP P res.`2]
 = Pr[CSpecFp.rsample(P) @ &m : res.`2 \in D /\ (RSP P res.`2)].
rewrite Pr[mu_split (res.`2 \in D)] . auto. 
have ->: Pr[CSpecFp.rsample(P) @ &m : RSP P res.`2 /\ (res.`2 \notin D)]
 = 0%r. timeout 15. smt. simplify.
rewrite Pr[mu_eq]. smt. auto.
rewrite Pr[mu_eq]. 
progress.  
rewrite /D.
apply supp_duniform.
have : res{hr}.`2 < M. smt.
smt.
smt(). smt(D_sup).
smt(). auto.
qed.



equiv rsample_eq P:
 CSpecFp.rsample ~ ASpecFp.rsample: 
  ={arg} /\ arg{1} = P /\ 0 < P < M ==> res{1}.`2 = res{2}.
proof.  
bypr res{1}.`2 res{2}. 
progress. move => &1 &2 aa [H ] H0. 
progress. rewrite - H.  rewrite  H0.
case (LessThan P aa). move => c1.
rewrite (rsample_uni &1 aa _ _). 
smt(). smt(). smt().
byphoare (_: arg = P ==> _). proc.
rnd. skip. simplify. move => &hr pa.
rewrite pa.
 rewrite duniform1E.
have -> : aa \in range 0 P = true. smt. simplify.
congr.  smt(@List). auto. auto.
move => c2.
have ->: Pr[CSpecFp.rsample(P) @ &1 : res.`2 = aa] = 0%r.
have ->: 
  Pr[CSpecFp.rsample(P) @ &1 : res.`2 = aa] = 
  Pr[CSpecFp.rsample(P) @ &1 : (res.`2 = aa) /\ ! LessThan  P res.`2].
rewrite Pr[mu_eq]. auto. auto. 
have : Pr[CSpecFp.rsample(P) @ &1 : LessThan P res.`2] = 1%r. apply rsample_lossless4. smt.
move => q. 
 have ops : Pr[CSpecFp.rsample(P) @ &1 : ! LessThan P res.`2] = 0%r.
 have : 1%r = Pr[CSpecFp.rsample(P) @ &1 : LessThan P res.`2]
     + Pr[CSpecFp.rsample(P) @ &1 : ! (LessThan P res.`2)] . 
  rewrite - (rsample_lossless P &1). 
 apply witness_support.
  exists 0. smt.
  rewrite Pr[mu_split (LessThan P res.`2)]. auto.
  smt.
timeout 15. smt.
byphoare (_: arg = P ==> _).
hoare. proc.
rnd. skip. move => &hr Q1 r0 Q2.
have : LessThan P r0. rewrite /LessThan. split.  smt(@Distr @DInterval @List).
progress. smt(@Distr @DInterval @List).
smt(). auto. auto.
qed.


equiv mulm_eq:
 CSpecFp.mulm ~ ASpecFp.mulm: 
  a{1} = asint a{2} /\ b{1} = asint b{2} /\ p{1} = p
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
case (a{2} < p). auto. move => qq. smt(). rewrite q1. move => qq. rewrite qq.
rewrite modz_small. split.  smt().
move => ?. have ->: `|W64x2N.modulusR| = W64x2N.modulusR. rewrite /W64x2N.modulusR. smt(@Ring).
smt(P_pos). auto.
qed.


require import BarrettRedInt.
require import Real RealExp.

(* parameter for the Barrett reduction  *)

equiv redm_eq:
 ASpecFp.redm ~ CSpecFp.redm: ={a, p} /\ r{2} = (4 ^ k{2} %/ p{2}) 
  /\ 0 < p{2} < W64xN.modulusR
  /\ 0 <= a{2} < p{2} * p{2}
  /\ 0 < p{2} < 2 ^ k{2} 
  /\ 0 <= k{2} ==> ={res}.
proc. inline*. wp. skip. progress.
rewrite -  (barrett_reduction_correct a{2} p{2} k{2} ). auto. auto.  auto. 
rewrite /barrett_reduction. simplify. rewrite /ti. rewrite /ti'. rewrite /ri.
have ->: 2 ^ (2 * k{2}) = 4 ^ k{2}. smt(@Real).
have <-:  a{2} - a{2} * (4 ^ k{2} %/ p{2}) %/ 4 ^ k{2} * p{2}
 = (a{2} - a{2} * (4 ^ k{2} %/ p{2}) %/ 4 ^ k{2}  %%  2 ^ k{2} * p{2}) %% W64x2N.modulusR.
rewrite modz_small.
 have ->: a{2} * (4 ^ k{2} %/ p{2}) %/ 4 ^ k{2}  = ti' a{2} p{2} k{2}. 
  rewrite /ti. rewrite /ti'. rewrite /ri. auto.
have -> : ti' a{2} p{2} k{2} %% 2 ^ k{2} = ti' a{2} p{2} k{2}. 
rewrite modz_small. rewrite /ti'. split. 
apply divz_ge0. 
smt(exprn_ege1).
rewrite /ri. 
  have : 0 <= (4 ^ k{2} %/ p{2}). apply divz_ge0.  smt(). smt(exprn_ege1). smt().
  have ->: `|2 ^ k{2}| = 2 ^ k{2}. smt().
  have : (ti' a{2} p{2} k{2})%r < (2 ^ k{2})%r.
   rewrite - same_t'. auto. auto.
  have qq :  a{2}%r - 2%r * p{2}%r < (t' a{2}%r p{2}%r k{2}%r) * p{2}%r <= a{2}%r. 
   apply st6. smt(). split. smt().  move => ?. rewrite  exp_lemma1. auto. auto. smt(@Real).
  smt(). smt(). auto.
have -> : a{2} - a{2} * (4 ^ k{2} %/ p{2}) %/ 4 ^ k{2} * p{2}
 = ti a{2} p{2} k{2}. rewrite /ti. rewrite /ti'. rewrite /ri. auto.
split. 
   have : 0%r <= (ti a{2} p{2} k{2})%r < 2%r * p{2}%r.
   rewrite - same_t. auto. auto.
     apply (st8 a{2}%r p{2}%r k{2}%r _ _). split.  smt(). smt(). smt(exp_lemma1).
  progress. smt(). 
move => _.
have ->: `|W64xN.modulusR2| = W64xN.modulusR2. rewrite /W64xN.modulusR2. smt(@Ring).
   have : 0%r <= (ti a{2} p{2} k{2})%r < 2%r * p{2}%r.
   rewrite - same_t. auto. auto. 
     apply (st8 a{2}%r p{2}%r k{2}%r _ _). split. smt(). smt().
split. smt(). move => ?. smt(exp_lemma1).
  progress. 
   have : 2 * p{2} < W64xN.modulusR2. rewrite /W64xN.modulusR2. 
   have : W64x2N.M ^ (nlimbs) <= W64x2N.M ^ (2 * nlimbs).
   apply ler_weexpn2l. smt(). smt().
   have : p{2} <= W64x2N.M ^ nlimbs.
    have ->: W64x2N.M ^ nlimbs = W64xN.modulusR. rewrite /W64xN.modulusR. auto. smt().
smt(). smt().
 have ->: a{2} * (4 ^ k{2} %/ p{2}) %/ 4 ^ k{2}  = ti' a{2} p{2} k{2}. 
  rewrite /ti. rewrite /ti'. rewrite /ri. auto.
have -> : ti' a{2} p{2} k{2} %% 2 ^ k{2} = ti' a{2} p{2} k{2}. 
rewrite modz_small. rewrite /ti'. split. 
  have : 0 <= ri p{2} k{2} %/ 4 ^ k{2}. apply divz_ge0. smt(exprn_ege1). rewrite /ri.
  apply divz_ge0.  smt(). smt(exprn_ege1). smt(). 
  have ->: `|2 ^ k{2}| = 2 ^ k{2}. smt().
  have : (ti' a{2} p{2} k{2})%r < (2 ^ k{2})%r.
   rewrite - same_t'. auto. auto.
  have qq :  a{2}%r - 2%r * p{2}%r < (t' a{2}%r p{2}%r k{2}%r) * p{2}%r <= a{2}%r.
   apply st6. smt().  split. smt(). move => ?. smt(exp_lemma1).
  smt().
  smt(). auto.
smt().
auto.
qed.

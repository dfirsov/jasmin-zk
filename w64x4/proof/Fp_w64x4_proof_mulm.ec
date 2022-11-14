require import AllCore IntDiv CoreMap List.

require import JModel JBigNum.
require import Fp_w64x4_spec Fp_w64x4_extract Ith_Bit64.
import Array16 Array8 Array4.
import Zp W64x4 R.
import StdBigop Bigint BIA.


equiv mul1first_eq:
 M.mul1 ~ MulOps.mul1:
 a{1}=ak{2} /\ ={b}
 ==>
 (res.`1,res.`2,res.`3,res.`4){1} = (W64.zero,res.`1,res.`2,res.`3){2}.
proof.
proc; simplify.
wp.
while ( #pre /\ ={r,i} /\ (a,of_0,cf,_zero){1}=(ak,_of,_cf,W64.zero){2} /\ 
        1 <= i{2} <= nlimbs /\ !_of{2}).
 wp; skip => />; smt(Array8.get_setE Array8.set_set_if).
wp; skip => />; smt (Array8.set_set_if).
qed.


equiv mul1acc_eq :
 M.mul1acc ~ MulOps.mul1acc:
 W64.to_uint k{1} = k{2} /\ ={a,b} /\ (_zero,of_0,cf,r){1}=(W64.zero,_of,_cf,x){2} /\
  0 <= k{2} < nlimbs
 ==>
 (res.`1,res.`2,res.`3,res.`4){1} = (W64.zero,res.`1,res.`2,res.`3){2}.
proof.
proc. simplify.
wp. while ( #pre /\ ={i} /\ (aux,_zero){1}=(nlimbs-1,W64.zero){2} /\ 
            0 <= i{2} <= nlimbs-1 /\ kk{1} = k{2}).
 wp; skip => />; smt(Array8.get_setE Array8.set_set_if).
wp; skip; smt(Array8.get_setE Array8.set_set_if).
qed.


equiv dmul1first_eq:
 M.dmul1 ~ W64x8.MulOps.mul1:
 a{1}=ak{2} /\ ={b}
 ==>
 (res.`1,res.`2,res.`3,res.`4){1} = (W64.zero,res.`1,res.`2,res.`3){2}.
proof.
proc; simplify.
wp.
while ( #pre /\ ={r,i} /\ (a,of_0,cf,_zero){1}=(ak,_of,_cf,W64.zero){2} /\ 
        1 <= i{2} <= dnlimbs /\ !_of{2}).
 wp; skip => />; smt(Array16.get_setE Array16.set_set_if).
wp; skip => />; smt (Array16.set_set_if).
qed.


equiv dmul1acc_eq :
 M.dmul1acc ~ W64x8.MulOps.mul1acc:
   W64.to_uint k{1} = k{2} /\ ={a,b} /\ (_zero,of_0,cf,r){1}=(W64.zero,_of,_cf,x){2} /\
  0 <= k{2} < dnlimbs
 ==>
 (res.`1,res.`2,res.`3,res.`4){1} = (W64.zero,res.`1,res.`2,res.`3){2}.
proof.
proc. simplify.
wp. while ( #pre /\ ={i} /\ (aux,_zero){1}=(8-1,W64.zero){2} /\ 
            0 <= i{2} <= 8-1 /\ kk{1} = k{2}).
 wp; skip => />; smt(Array16.get_setE Array16.set_set_if).
wp; skip; smt(Array16.get_setE Array16.set_set_if).
qed.


equiv muln_spec aa bb:
 M.bn_muln ~ ASpecFp.muln:
  ImplZZ a{1} a{2} /\ ImplZZ b{1} b{2} /\ aa = a{1} /\ bb = b{1}
  ==> 
  ImplZZ2 res{1}.`4 res{2}
     /\ res{1}.`1 = W64.zero /\ !res{1}.`2 /\ !res{1}.`3 /\ valR2 res{1}.`4 = valR aa * valR bb.
proof.
transitivity 
 MulOps.mulR
 ( ={a,b} ==> res{1}.`2=res{2}.`1 /\ res{1}.`3=res{2}.`2 /\ res{1}.`4=res{2}.`3 /\  res{1}.`1 = W64.zero  )
 ( ImplZZ a{1} a{2} /\ ImplZZ b{1} b{2} /\ aa = a{1} /\ bb = b{1}
   ==> !res{1}.`1 /\ !res{1}.`2 /\ ImplZZ2 res{1}.`3 res{2} /\ valR2 res{1}.`3 = valR aa * valR bb).
+ by move=> /> &1 &2 H1 H2; exists (a{1},b{1}).
+ by move=> /> /#.
+ proc; simplify.
  while ( #pre /\ (i,_zero,of_0,cf,r){1}=(k,W64.zero,_of,_cf,r){2} /\
          1 <= k{2} <= nlimbs ).
  wp. call mul1acc_eq. wp. skip. progress. 
rewrite of_uintK.
apply modz_small. split. smt(). smt(). smt(). smt(). smt().
  wp; call mul1first_eq; wp; skip => /> . 
+ proc.
  transitivity {1}
    { (_of,_cf,r) <@ MulOps.mulR(a,b); }
    ( ={a,b} ==> ={_cf,_of,r} )
    ( ImplZZ a{1} a{2} /\ ImplZZ b{1} b{2} /\ aa = a{1} /\ bb = b{1} ==> !_cf{1} /\ !_of{1} /\ ImplZZ2 r{1} r{2} /\ valR2 r{1} = valR aa * valR bb ).
  progress. exists a{1} b{1}; auto.
  + by move=> /> *.
  + by inline MulOps.mulR; sim.
  + by ecall {1} (mulR_ph a{1} b{1}); wp; skip.
qed.


equiv dmuln_spec:
 M.dbn_muln ~ ASpecFp.muln:
  W64x8.valR a{1} = a{2} /\  W64x8.valR b{1} = b{2}
  ==> 
 W64x8.valR2 res{1}.`4 = res{2}
     /\ res{1}.`1 = W64.zero /\ !res{1}.`2 /\ !res{1}.`3.
proof.
transitivity 
 W64x8.MulOps.mulR
 ( ={a,b} ==> res{1}.`2=res{2}.`1 /\ res{1}.`3=res{2}.`2 /\ res{1}.`4=res{2}.`3 /\  res{1}.`1 = W64.zero )
 ( W64x8.valR a{1} = a{2} /\ W64x8.valR b{1} = b{2} 
   ==> !res{1}.`1 /\ !res{1}.`2 /\ W64x8.valR2 res{1}.`3 = res{2}).
+ by move=> /> &1 &2 H1 H2; exists (a{1},b{1}).
+ by move=> /> /#.
+ proc; simplify.
  while ( #pre /\ (i,_zero,of_0,cf,r){1}=(k,W64.zero,_of,_cf,r){2} /\
          1 <= k{2} <= dnlimbs ).
  wp. call dmul1acc_eq. wp. skip. progress.
rewrite of_uintK.
apply modz_small. split. smt(). smt(). smt(). smt(). smt().
  by wp; call dmul1first_eq; wp; skip => /> /#.
+ proc.
  transitivity {1}
    { (_of,_cf,r) <@ W64x8.MulOps.mulR(a,b); }
    ( ={a,b} ==> ={_cf,_of,r} )
    ( W64x8.valR a{1} = a{2} /\ W64x8.valR b{1} = b{2} ==> !_cf{1} /\ !_of{1} /\ W64x8.valR2 r{1} = r{2} ).
  + by move=> /> &1; exists a{1} b{1}; auto.
  + by move=> /> *.
  + by inline W64x8.MulOps.mulR; sim.
  + by ecall {1} (W64x8.mulR_ph a{1} b{1}); wp; skip.
qed.


equiv dsubc_spec:
 M.dbn_subc ~ ASpecFp.dsubn:
  W64x8.valR a{1} = a{2} /\ W64x8.valR b{1} = b{2} (* /\ W64x8.valR b{1}  <= W64x8.valR a{1} *)
  ==> res{1}.`1=res{2}.`1 /\ W64x8.valR res{1}.`2 = res{2}.`2.
proof.
transitivity 
 W64x8.R.Ops.subcR
 ( (a,b,false){1}=(a,b,c){2} ==> ={res} )
 (W64x8.valR  a{1} = a{2} /\ W64x8.valR b{1} = b{2} /\ !c{1} (* /\ W64x8.valR b{1}  <= W64x8.valR a{1} *)
   ==> res{1}.`1 = res{2}.`1 /\ W64x8.valR res{1}.`2 = res{2}.`2 ).
+ by move=> /> &1 &2 H1 H2 ; exists (a{1},b{1},false).
+ by move=> /> *.
+ proc; simplify.
  unroll {2} 3; rcondt {2} 3; first by auto.
  exlim a{1}, b{1} => aa bb.
  while (={i,b} /\ 1 <= i{2} <= dnlimbs /\ 
         (cf, aa){1}=(c, a){2} /\
         (forall k, 0 <= k < i{2} => a{1}.[k] = r{2}.[k])%Array8 /\
         (forall k, i{2} <= k < dnlimbs => a{1}.[k] = aa.[k])%Array8).
   wp; skip => /> &1 &2 Hi1 _ Hh1 Hh2 Hi2.
   split => *; first smt().
   split => *; first smt().
   split.
    move=> k Hk1 Hk2.
    pose X := (subc _ _ _)%W64.
    pose Y := (subc _ _ _)%W64.
    have ->: X=Y by smt().
    case: (k = i{2}) => ?.
     by rewrite !set_eqiE /#.
    by rewrite !set_neqiE /#.
   move=> k Hk1 Hk2.
   by rewrite set_neqiE /#.
  wp; skip => />.
  split => *.
   split => k *.
    by rewrite (_:k=0) 1:/# !set_eqiE /#.
   by rewrite set_neqiE /#.
  by apply Array8.ext_eq; smt().
+ proc; simplify.
  transitivity {1}
   { (c,r) <@ W64x8.R.Ops.subcR(a,b,c); }
   ( ={a,b,c} ==> ={c,r} )
   ( W64x8.valR a{1} = a{2} /\ W64x8.valR b{1} = b{2} /\ !c{1}  (* /\ W64x8.valR b{1}  <= W64x8.valR a{1} *) ==> ={c} 
   /\ W64x8.valR r{1} = r{2} ).
  + by move=> /> &2 H  ; exists a{2} b{2} false.
  + by auto.
  + by inline*; sim.
  + ecall {1} (W64x8.R.subcR_ph a{1} b{1} c{1}); wp; skip => /> &m Hc [c r] /= -> .
progress. 
    by rewrite W64x8.R.bn_borrowE 1:/# b2i0 /bn_modulus /=.
qed.


lemma dbn_cmov_correct x y z :
  phoare[ M.dbn_cmov :  arg = (x,y,z)  ==> res = if x then z else y ] = 1%r.
proc.
while (cond = x /\ b = z /\ i <= dnlimbs 
  /\ (forall j, 0 <= j < i => a.[j] = if cond then z.[j] else y.[j])
  /\ (forall j, i <= j < dnlimbs => a.[j] = y.[j])) (dnlimbs - i). progress.
wp.  skip.  progress. smt().   smt(@Array8). smt(@Array8). smt(). wp.  skip. progress. smt(@Array8). smt().
apply Array8.ext_eq. progress. smt(@Array8). 
qed.


(* lemma dbn_set0_correct : *)
(*   phoare[ M.bn_set0 : true  ==> W64x4.valR res = 0 ] = 1%r. *)
(* proc. *)
(* while (i <= nlimbs  *)
(*   /\ (forall j, 0 <= j < i => a.[j]%Array4 = W64.zero)) (nlimbs - i). progress. *)
(* wp.  skip.  progress. smt().  smt(@Array4). smt(). wp.  skip. progress. smt(). smt(). *)
(* rewrite - zeroRE. congr. *)
(* apply Array4.ext_eq. progress.  rewrite H1. smt().  *)
(* rewrite /zeroR. smt(@Array4). *)
(* qed. *)


require import List.

op oneR : R = (of_list W64.zero (W64.one :: nseq (nlimbs - 1) W64.zero ))%Array4.

lemma nseqS' ['a]:
  forall (n : int) (x : 'a), 0 < n => nseq n x = x :: nseq (n - 1) x.
smt(nseqS).
qed.

lemma oneRE: ImplZZ oneR 1.
rewrite /oneR /valR /bnk.
do? (rewrite range_ltn; first by trivial ).
simplify. rewrite range_geq. auto.
do rewrite big_consT.
rewrite big_nil.
 have -> : dig ((of_list W64.zero (W64.one :: nseq 3 W64.zero)))%Array4 0 = 1.
 simplify. smt(@Int).
 have q : forall x, 0 < x < nlimbs => dig ((of_list W64.zero (W64.one :: nseq 3 W64.zero)))%Array4 x = 0.
 move => x xp. rewrite /dig.
   have ->: to_uint ((of_list W64.zero (W64.one :: nseq 3 W64.zero)).[x])%Array4 = 0. 
    do? (rewrite nseqS'; first by trivial). simplify. 
   rewrite nseq0. 
  have -> : (of_list W64.zero [W64.one; W64.zero; W64.zero; W64.zero]).[x]%Array4 = W64.zero. 
rewrite get_of_list. smt().
smt(@List).  smt(@W64). smt().
do? (rewrite q; first smt()). simplify. auto.
qed.


lemma bn_set1_correct :
  phoare[ M.bn_set1 : true  ==> W64x4.valR res = 1 ] = 1%r.
proc.
while (0 < i <= nlimbs 
  /\ (forall j, 1 <= j < i => a.[j]%Array4 = W64.zero) /\ a.[0]%Array4 = W64.one) (nlimbs - i). progress.
wp.  skip.  progress. smt(). smt().  smt(@Array4). smt(@Array4). smt(). wp.  skip. progress. smt(@Array4). smt().
rewrite - oneRE. congr.
apply Array4.ext_eq. progress.  
case (x = 0). progress. progress.
rewrite H2. smt(). 
rewrite /oneR. smt(@Array4 @List).
qed.



lemma dbn_copy_correct x :
  phoare[ M.dbn_copy :  arg = x  ==> res = x ] = 1%r.
proc.
while (a = x /\ i <= dnlimbs 
  /\ (forall j, 0 <= j < i => r.[j] = x.[j])
  ) (dnlimbs - i). progress.
wp.  skip.  progress. smt(). smt(@Array8). smt(). wp.  skip. progress. smt(). smt().
apply Array8.ext_eq. progress. smt(). 
qed.


lemma bn_copy_correct x :
  phoare[ M.bn_copy :  arg = x  ==> res = x ] = 1%r.
proc.
while (a = x /\ i <= nlimbs 
  /\ (forall j, 0 <= j < i => r.[j]%Array4 = x.[j]%Array4)
  ) (dnlimbs - i). progress.
wp.  skip.  progress. smt(). smt(@Array4). smt(). wp.  skip. progress. smt(). smt().
apply Array4.ext_eq. progress. smt(). 
qed.



equiv dcminusP_spec:
 M.dcminusP ~ ASpecFp.cminusP:
 W64x8.valR p{1} = P /\ W64x8.valR x{1} = a{2} ==> W64x8.valR res{1}  =res{2}.
proof.
transitivity CSpecFp.dcminusP
 ( W64x8.valR p{1} = P /\ W64x8.valR x{1} = a{2} ==> W64x8.valR res{1}  = res{2} )
 ( ={a} /\ a{2} < W64x8.modulusR ==> ={res} ).
  progress. exists (W64x8.valR x{1}). progress. smt(@W64x8).
+ by auto. 
proc. 
(ecall {1} (dbn_cmov_correct cf{1} z{1} x{1})).  simplify.
conseq (_:  ( (W64x8.valR (if cf{1} then x{1} else z{1}))%W64x8 = r{2} )). progress.
inline ASpecFp.ctseln. wp.   simplify.
seq 2 0 : ((W64x8.valR p{1})%W64x8 = P /\ (W64x8.valR x{1})%W64x8 = a{2} /\ z{1} = x{1}).
(ecall {1} (dbn_copy_correct x{1})).  wp. skip. progress.
seq 1 1 : (cf{1} = c{2} /\ W64x8.valR z{1} = x{2} 
  /\ (W64x8.valR p{1})%W64x8 = P /\ (W64x8.valR x{1})%W64x8 = a{2}).
call  dsubc_spec.  skip. progress.
skip. progress.   smt().
+ symmetry; conseq cminusP_eq; smt().
qed.


import W64x8.


lemma bn_div2_correct z :
  phoare[ M.div2 : arg = (z,dnlimbs)  ==> (W64x8.valR res) = (W64x8.valR2 z) %/  W64x8.modulusR ] = 1%r.
proc. sp.
while (aux = dnlimbs /\ i <= dnlimbs /\ forall j, 0 <= j < i => r.[j] = x.[dnlimbs + j]) (dnlimbs - i). 
progress. wp. skip. progress.
smt(). smt(@Array8). smt(). skip. progress.
smt(). smt().
have ->:  W64x8.modulusR  = W64x8.M^dnlimbs.  rewrite /R.bn_modulus. auto. 
have ->: (R2.bnk (2*dnlimbs) x{hr})%R2 = valR2 x{hr}. auto.
rewrite R2.bghint_div. auto.
rewrite - R.bnkup0.
rewrite /bnkup.
have ->: 
  bigi predT (fun (i1 : int) => to_uint r0.[i1] * W64x8.M ^ (i1 - 0)) 0 dnlimbs
  = bigi predT (fun (i1 : int) => to_uint x{hr}.[i1 + dnlimbs] * W64x8.M ^ (i1 - 0)) 0 dnlimbs.
apply eq_big_int. progress. smt(). 
  have ->: bigi predT (fun (i1 : int) => to_uint x{hr}.[i1] * W64x8.M ^ (i1 - dnlimbs)) dnlimbs
  (2 * dnlimbs)  = bigi predT (fun (i1 : int) => to_uint x{hr}.[i1] * W64x8.M ^ (i1 - dnlimbs)) (0 + dnlimbs)
  (2 * dnlimbs). auto.
rewrite big_addn. simplify. auto.
qed.



lemma bn_shrink_correct a  :
  phoare[ M.bn_shrink : arg = a  ==> W64x4.valR res = W64x8.valR a %% W64x4.modulusR ] = 1%r.
proc.
sp.
while (i <= nlimbs /\ forall j, 0 <= j < i => r.[j]%Array4 = x.[j]%Array8) (nlimbs - i). 
progress. wp. skip. progress.
smt(). smt(@Array4). smt(). skip. progress.
smt(). smt(). 
rewrite /W64x4.modulusR. auto.
rewrite W64x8.R.bn_mod. auto. 
rewrite /bnk. 
apply eq_big_seq. progress. rewrite H1. split.
smt (mem_range_le). 
smt (mem_range_gt).
auto.
qed.


lemma bn_expand_correct : forall a,
      phoare[ M.bn_expand : arg = a  ==> W64x8.valR res =  W64x4.valR a ] = 1%r.
 have  bn_expand_correct : forall a, 
    hoare[ M.bn_expand : arg = a  ==> W64x8.valR res = W64x4.valR a ].
   move => a.
   proc.
   sp. 
    seq 1 : (a = x /\ i = nlimbs /\ forall i, i < nlimbs => r.[i] = x.[i]%Array4).
    while (i <= nlimbs /\ forall j, 0 <= j < i => r.[j] = x.[j]%Array4). wp.  skip. progress.
    smt(). smt(@Array4 @Array8). skip. progress.
    smt().  smt(). smt(@Array8 @Array4). 
    seq 2 : (a = x /\  (forall j, 0 <= j < nlimbs => r.[j]%Array8 = x.[j]%Array4)
         /\ (forall j, nlimbs <= j < 2*nlimbs => r.[j] = W64.zero)).     
    while (a = x /\ nlimbs <= i <= 2*nlimbs 
         /\ (forall j, 0 <= j < nlimbs => r.[j]%Array8 = x.[j]%Array4)
         /\ (forall j, nlimbs <= j < i => r.[j] = W64.zero) ). wp.  skip. progress.
    smt(). smt().
    have z : i{hr} <> j. smt(). 
    rewrite - H1. auto.  smt(@Array4 @Array8).
    case (j = i{hr}). smt(@Array4 @Array8).
    progress.
    have : j < i{hr}.  smt().
    progress.
    rewrite - (H2 j).  smt().
    smt(@Array4 @Array8). wp. 
    skip.  progress.
    smt(@Array4 @Array8). smt(). smt(). 
    skip.  progress.
    have -> : valR r{hr} = (bn_seq ((to_list r{hr}))%Array8).
    apply W64x8.R.bn2seq. 
    rewrite /to_list.
    have -> : dnlimbs = nlimbs + nlimbs. smt().
    rewrite mkseq_add. auto. auto.
    have -> : mkseq (fun (i0 : int) => r{hr}.[i0]) nlimbs 
      = mkseq (fun (i0 : int) => x{hr}.[i0]%Array4) nlimbs.
    apply eq_in_mkseq. progress. 
    simplify.
    have ->: mkseq (fun (i0 : int) => r{hr}.[nlimbs + i0]) nlimbs
      = mkseq (fun (i0 : int) => W64.zero) nlimbs.
    apply eq_in_mkseq. progress. rewrite H0. smt(). auto.
    rewrite mkseq_nseq. 
    rewrite /bn_seq.
    rewrite foldr_cat.
    have ->: (foldr (fun (w : W64.t) (r0 : int) => to_uint w + W64x8.M * r0) 0
         (nseq nlimbs W64.zero)) = 0.  
       have gen : forall n, 0 <= n => foldr (fun (w : W64.t) (r0 : int) => to_uint w + W64x8.M * r0) 0
                     (nseq n  W64.zero) = 0.
       apply intind. progress. rewrite nseq0. simplify. auto.
       progress. rewrite nseqS. auto. simplify. rewrite H2. auto.
       apply gen. auto.
    rewrite W64x4.R.bn2seq. rewrite /bn_seq. rewrite /to_list. 
    pose f := (fun (w : W64.t) (r0 : int) => to_uint w + W64x8.M * r0).
    simplify. auto.    
move => a.
bypr. progress.
 have ->:  1%r = Pr[M.bn_expand(arg{m}) @ &m : true ] . 
byphoare. proc.  while (true) (2*nlimbs -i). progress. wp. skip. smt().
wp. while true (nlimbs - i). progress. wp. skip. smt().
wp.  skip. smt(). auto. auto.
  have ->: Pr[M.bn_expand(arg{m}) @ &m : true]
  = Pr[M.bn_expand(arg{m}) @ &m : (W64x8.valR res =  W64x4.valR arg{m}) ]  
    + Pr[M.bn_expand(arg{m}) @ &m : (W64x8.valR res <>  W64x4.valR arg{m}) ].
rewrite Pr[mu_split (W64x8.valR res =  W64x4.valR arg{m})]. simplify.   auto.
have ->: Pr[M.bn_expand(arg{m}) @ &m : valR res <> valR arg{m}] = 0%r.
byphoare (_: arg = arg{m} ==> _). 
hoare. simplify. conseq (bn_expand_correct arg{m}). auto. auto. auto.
qed.

   
equiv breduce_cspec:
 M.bn_breduce ~ CSpecFp.redm:
     W64x8.valR a{1} = a{2} 
 /\  W64x8.valR r{1} = r{2} 
 /\  W64x4.valR p{1} = P
 /\  k{2} = 64 * nlimbs
   ==>  (W64x4.valR res{1}) = res{2}  %% W64x4.modulusR.
proof. proc.
sp.
simplify.
seq 0 0 : (valR a{1} = a{2} /\ valR r{1} = r{2} /\ ImplZZ p{1} P /\ k{2} = 64 * nlimbs). 
skip. auto.
seq 1 1 : (valR a{1} = a{2} /\ valR r{1} = r{2} /\ ImplZZ p{1} P /\ k{2} = 64 * nlimbs
    /\ W64x8.valR2 xr{1} = xr{2} (* /\ xr{2} = a{2} * r{2} *)).
call dmuln_spec. skip. progress.
seq 1 1 : (valR a{1} = a{2} /\ valR r{1} = r{2} /\ ImplZZ p{1} P /\ k{2} = 64 * nlimbs
    /\ W64x8.valR2 xr{1} = xr{2} /\ W64x8.valR xrf{1} = xrf{2} ).
ecall {1} (bn_div2_correct xr{1}). inline*. wp.  skip.  progress. rewrite H0.
  rewrite /W64x8.modulusR. clear H0 H. smt.
seq 1 1 : (valR a{1} = a{2} /\ valR r{1} = r{2} /\ ImplZZ p{1} P /\ k{2} = 64 * nlimbs
    /\ W64x8.valR2 xr{1} = xr{2} /\  valR xrfd{1} =  xrf{2}   ).
ecall {1} (bn_shrink_correct xrf{1}). wp. skip. progress. rewrite H0.  smt.
seq 1 1 : (valR a{1} = a{2} /\ valR r{1} = r{2} /\ ImplZZ p{1} P /\ k{2} = 64 * nlimbs
    /\ W64x8.valR2 xr{1} = xr{2} /\ valR xrfd{1} = xrf{2} 
    /\  W64x8.valR xrfn{1} = xrfn{2}).
ecall  (muln_spec xrfd{1} p{1}). skip. progress.
seq 1 1 : (valR a{1} = a{2} /\ valR r{1} = r{2} /\ ImplZZ p{1} P /\ k{2} = 64 * nlimbs
    /\ W64x8.valR2 xr{1} = xr{2} /\ W64x4.valR xrfd{1} = xrf{2} 
    /\ W64x8.valR xrfn{1} = xrfn{2}
    /\ W64x8.valR t{1} = t{2}).
call dsubc_spec. skip. progress.
seq 1 0 : (valR a{1} = a{2} /\ valR r{1} = r{2} /\ ImplZZ p{1} P /\ k{2} = 64 * nlimbs
    /\ W64x8.valR2 xr{1} = xr{2} /\ W64x4.valR xrfd{1} = xrf{2} 
    /\ W64x8.valR xrfn{1} = xrfn{2}
    /\ W64x8.valR t{1} = t{2}
    /\ W64x8.valR pp{1} = W64x4.valR p{1}).
ecall {1} (bn_expand_correct p{1}). skip. progress.
seq 1 1 : (valR a{1} = a{2} /\ valR r{1} = r{2} /\ ImplZZ p{1} P /\ k{2} = 64 * nlimbs
    /\ W64x8.valR2 xr{1} = xr{2} /\ W64x4.valR xrfd{1} = xrf{2} 
    /\ W64x8.valR xrfn{1} = xrfn{2}
    /\ W64x8.valR t{1} = t{2}
    /\ W64x8.valR pp{1} = W64x4.valR p{1}
    /\ W64x8.valR t{1} = t{2} ).
call dcminusP_spec. skip. progress. smt().
seq 1 0 : (valR a{1} = a{2} /\ valR r{1} = r{2} /\ ImplZZ p{1} P /\ k{2} = 64 * nlimbs
    /\ W64x8.valR2 xr{1} = xr{2} /\ W64x4.valR xrfd{1} = xrf{2} 
    /\ W64x8.valR xrfn{1} = xrfn{2}
    /\ W64x8.valR t{1} = t{2}
    /\ W64x8.valR pp{1} = W64x4.valR p{1}
    /\ W64x8.valR t{1} = t{2}
    /\ W64x4.valR res_0{1} = W64x8.valR t{1} %% W64x4.modulusR).
ecall {1} (bn_shrink_correct t{1}). skip. progress.
skip.  progress. 
qed.


equiv bnreduce_spec:
 M.bn_breduce ~ ASpecFp.redm:
  valR a{1} = a{2}
  /\ ImplZZ p{1} P
  /\ valR r{1} = (4 ^ (64 * nlimbs) %/ P) 
  /\ 0 < P < W64x4.modulusR
  /\ 0 <= a{2} < P * P
  /\ 0 < P < 2 ^ (64 * nlimbs)
  /\ 0 <= valR r{1} ==> valR res{1} = res{2} .
proof. 
  have redm_simp:
 equiv [ ASpecFp.redm ~ ASpecFp.redm: ={arg} ==> res{1} = res{2} %% W64x4.modulusR ].
 proc. wp.  skip. progress. smt. 
symmetry. transitivity ASpecFp.redm
 (={arg} ==> res{1} = res{2} %% W64x4.modulusR)
 (valR a{2} = a{1}
  /\ ImplZZ p{2} P
  /\ valR r{2} = (nlimbs ^ (64 * nlimbs) %/ P) 
  /\ 0 < P < W64x4.modulusR
  /\ 0 <= a{1} < P * P
  /\ 0 < P < 2 ^ (64 * nlimbs)
  /\ 0 <= valR r{2} ==> valR res{2} = res{1} %% W64x4.modulusR).
smt(). auto. conseq redm_simp. 
symmetry.
transitivity CSpecFp.redm
 (W64x8.valR a{1} = a{2} 
 /\  W64x8.valR r{1} = r{2} 
 /\  W64x4.valR p{1} = P
 /\  k{2} = 64 * nlimbs
   ==>  (W64x4.valR res{1}) = res{2}  %% W64x4.modulusR)
 (={a} /\ r{1} = (nlimbs ^ k{1} %/ P) 
  /\ 0 < P < W64x4.modulusR
  /\ 0 <= a{1} < P * P
  /\ 0 < P < 2 ^ k{1} 
  /\ 0 <= k{1} ==> ={res}). 
move => &1 &2 q. 
exists (valR a{1} , valR r{1} , 64 * nlimbs). split. smt(). 
split. smt(). split.  
have ->: (valR a{1}, valR r{1}, 64 * nlimbs).`2 = valR r{1}. auto.
have ->: (valR a{1}, valR r{1}, 64 * nlimbs).`3 = 64 * nlimbs. auto.
rewrite q. smt().
 simplify. split.  split.  smt(). smt(). 
split. smt(). split. smt(). 
have ->: Fp_w64x4_spec.M = W64x4.modulusR. clear q. smt.
smt(). auto.
conseq breduce_cspec.
symmetry. conseq redm_eq. auto. auto.
qed.



lemma q (a b p : int) : 0 <= a < p => 0 <= b < p => a * b < p * p.
smt. qed.

equiv mulm_cspec:
 M.mulm ~ CSpecFp.mulm:
  valR a{1} = a{2}
  /\ valR b{1} = b{2}
  /\ valR a{1} < P
  /\ valR b{1} < P
  /\ ImplZZ p{1} P
  /\ valR r{1} = (4 ^ (64 * nlimbs) %/ P) 
  (* /\ 0 < P < 2 ^ (64 * nlimbs) *)
   ==> valR res{1} =  res{2} .
proc. 
call bnreduce_spec.
ecall (muln_spec a{1} b{1}).
wp. skip. progress.  smt. smt.
smt. rewrite H6.  
apply q. smt.
smt. smt. smt.
smt.
qed.


equiv mulm_spec:
 M.mulm ~ ASpecFp.mulm:
  valR a{1} = asint a{2}
  /\ valR b{1} = asint b{2}
  /\ valR p{1} = P
  /\ valR r{1} = (4 ^ (64 * nlimbs) %/ P) 
   ==> valR res{1} = asint res{2} .
transitivity CSpecFp.mulm
 (valR a{1} = a{2}
  /\ valR b{1} = b{2}
  /\ valR a{1} < P
  /\ valR b{1} < P
  /\ ImplZZ p{1} P
  /\ valR r{1} = (4 ^ (64 * nlimbs) %/ P) 
   ==> valR res{1} =  res{2})
 (a{1} = asint a{2} /\ b{1} = asint b{2}  ==> res{1} = asint res{2}).
move=> /> &1 &2 H1 H2 H3 H4; exists (valR a{1}, valR b{1}). smt. progress.
conseq mulm_cspec. 
conseq mulm_eq.
qed.




require import BitEncoding.
import BS2Int.

require Abstract_exp_proof_8.



clone import Abstract_exp_proof_8 as Exp with type R  <- t,
                                                 op P <- P,
                                                 op Rsize <- 256,
                                                 op valR <- W64x4.valR,
                                                 op of_int <- bn_ofint,
                                                 op idR <- bn_ofint 1,
                                                 op ( ** ) <- Int.( * ),
                                                 op ( *** ) <=  fun a b => bn_ofint ((valR%W64x4 a * valR%W64x4 b) %% P)
proof*.
realize Rsize_max. smt(). qed.
realize Rsize_pos. smt(). qed.
realize valr_pos. smt (@W64x4). qed.
realize iii.  rewrite /Rbits. 
progress. rewrite  size_int2bs. auto. qed.
realize valr_ofint.  progress.
rewrite bn_ofintK. smt.
qed.
realize P_pos. smt. qed.
realize ofint_valr. smt(@W64x4). qed.
realize rbits_bitsr. 
progress. rewrite /Rbits. rewrite /bitsR. 
  have ->: (valR (bn_ofint (bs2int x)))%W64x4 = bs2int x.
rewrite bn_ofintK. smt. smt. qed.
realize bitsr_rbits. 
rewrite /Rbits. rewrite /bitsR.
progress.
rewrite int2bsK. auto. simplify. progress. smt(bnk_cmp).
have : 0 <= valR  x < W64x4.M ^ nlimbs.
rewrite /valR. 
apply (bnk_cmp nlimbs).
progress. smt.
smt(@W64x4).
qed.
realize exp_prop7. progress. smt. qed.
realize exp_prop6. progress.
have ->: (valR (bn_ofint ((valR a * valR b) %% P)) * valR c) %% P
  = ((valR a * valR ((bn_ofint ((valR b * valR c) %% P)))) %% P). 
rewrite valr_ofint. smt.
rewrite valr_ofint. smt.
rewrite modzMml.
rewrite modzMmr. smt.
auto.
qed.
realize exp_prop5. progress. 
rewrite valr_ofint. progress. smt. simplify. 
rewrite modz_small. smt.
smt. qed.
realize mult_valr. progress. smt. qed.
realize idR_leP. smt. qed.



  
op R : W64.t Array8.t.
axiom R_prop : valR R = 4 ^ (64 * nlimbs) %/ P.

module MultM = {
  proc ith_bit = M.ith_bit
  proc swapr   = M.swapr
  proc opr (p:W64.t Array4.t, a:W64.t Array4.t,
             b:W64.t Array4.t) : W64.t Array4.t = {
    var r;
    r <@ M.mulm(R,p,a,b);
    return r;
  }
}.



lemma ones64 : (2^64  - 1)  = 18446744073709551615. smt(). qed.
lemma swap_lemma :
      equiv[ MultM.swapr ~ Spec.swapr :
              a{2} = x{1} /\ b{2} = y{1} /\ swap_0{1} = as_w64 c{2} ==> ={res}].
proc.  simplify.
seq 2 0 : (i{1} = 0 /\ a{2} = x{1} /\ b{2} = y{1} /\ swap_0{1} = as_w64 c{2} /\ 
   ((as_bool swap_0{1} => mask{1} = (of_int 18446744073709551615)%W64 )
              /\ (as_bool swap_0{1} = false => mask{1} = (of_int 0)%W64))).
wp. skip. progress. smt(@W64). smt.
while {1} (0 <= i{1} /\ ((as_bool swap_0{1} => mask{1} = (of_int 18446744073709551615)%W64 )
              /\ (as_bool swap_0{1} = false => mask{1} = (of_int 0)%W64)) 
   /\ (forall j, 0 <= j < i{1} => (x{1}.[j])%Array4 = (if as_bool swap_0{1} then (b{2}.[j]) else (a{2}.[j]))%Array4 )  
   /\ (forall j, 0 <= j < i{1} => (y{1}.[j])%Array4 = (if as_bool swap_0{1} then (a{2}.[j]) else (b{2}.[j]))%Array4 )  
   /\ (forall j, i{1} <= j => (x{1}.[j])%Array4 =  (a{2}.[j]))%Array4
   /\ (forall j, i{1} <= j => (y{1}.[j])%Array4 =  (b{2}.[j]))%Array4
 ) (nlimbs - i{1} + 1).
progress. wp.  skip.  progress.   smt().
case (j <  i{hr}). progress.  timeout 15. smt.
progress.
have : j = i{hr}. smt.
progress.
have ->: (x{hr}.[i{hr} <-
    x{hr}.[i{hr}] `^` (x{hr}.[i{hr}] `^` y{hr}.[i{hr}] `&` mask{hr})].[i{hr}])%Array4
 = (x{hr}.[i{hr}] `^` (x{hr}.[i{hr}] `^` y{hr}.[i{hr}] `&` mask{hr}))%Array4. smt.
case (as_bool swap_0{hr}). progress.
rewrite H4. auto.  rewrite H0. auto. rewrite H5. auto. rewrite - ones64. 
have -> : ((a{m}.[i{hr}])%Array4 `^` (b{m}.[i{hr}])%Array4 `&`
 (of_int W64.max_uint)%W64) = a{m}.[i{hr}]%Array4 `^` ((b{m}.[i{hr}])%Array4 `&`
 (of_int W64.max_uint)%W64). smt. 
have ->: ((b{m}.[i{hr}])%Array4 `&` (of_int W64.max_uint)%W64) = ((b{m}.[i{hr}])%Array4). smt.
smt(@W64).
progress. rewrite H4. auto.  rewrite H1. smt(). auto. 
case (j <  i{hr}). progress.  timeout 15. smt.
progress.
have : j = i{hr}. smt.
progress.
have ->: (y{hr}.[i{hr} <-
   y{hr}.[i{hr}] `^` (x{hr}.[i{hr}] `^` y{hr}.[i{hr}] `&` mask{hr})].[i{hr}])%Array4
 = (y{hr}.[i{hr}] `^` (x{hr}.[i{hr}] `^` y{hr}.[i{hr}] `&` mask{hr}))%Array4. smt.
case (as_bool swap_0{hr}). progress.
rewrite H4. auto.  rewrite H0. auto. rewrite H5. auto. rewrite - ones64. 
have -> : ((a{m}.[i{hr}])%Array4 `^` (b{m}.[i{hr}])%Array4 `&`
 (of_int W64.max_uint)%W64) = a{m}.[i{hr}]%Array4 `^` ((b{m}.[i{hr}])%Array4 `&`
 (of_int W64.max_uint)%W64). smt. 
have ->: ((b{m}.[i{hr}])%Array4 `&` (of_int W64.max_uint)%W64) = ((b{m}.[i{hr}])%Array4). smt.
smt(@W64).
progress. rewrite H4. auto.  rewrite H1. smt(). smt(@W64).
smt. smt. smt.
skip. progress. smt().   smt().   smt(). 
case (c{2} = false). progress.  
apply Array4.ext_eq.  progress. rewrite H5. progress. smt(). rewrite /as_bool. rewrite /as_w64. simplify. smt(@W64).
apply Array4.ext_eq.  progress. rewrite H6. progress. smt(). rewrite /as_bool. rewrite /as_w64. simplify. smt(@W64).
progress. have ->: c{2} = true. smt(). simplify.
progress. 
apply Array4.ext_eq.  progress. rewrite H5. progress. smt(). rewrite /as_bool. rewrite /as_w64. simplify. smt(@W64).
apply Array4.ext_eq.  progress. rewrite H6. progress. smt(). rewrite /as_bool. rewrite /as_w64. simplify. smt(@W64).
qed.




lemma okll : 
  equiv[ MultM.opr ~ M.mulm :
            a{1} = a{2} /\ b{1} = b{2} /\  p{1} = p{2} /\ r{2} = R ==>
            ={res}].
proc. inline M.mulm. sim. wp.  skip.  auto.
qed.

lemma okl : 
  equiv[ MultM.opr ~ Exp.Spec.mul :
            a{1} = a{2} /\ b{1} = b{2} /\  valR p{1} = P /\ valR a{1} < P /\ valR b{1} < P ==>
            ={res} /\ valR res{1} < P].
symmetry.
transitivity ASpecFp.mulm 
  (ImplFp arg{1}.`1  arg{2}.`1 /\ ImplFp arg{1}.`2  arg{2}.`2 ==> ImplFp res{1} res{2} )
  (ImplFp a{2} a{1} /\ ImplFp b{2} b{1} /\  valR p{2} = P /\ valR a{2} < P /\ valR b{2} < P ==>
            ImplFp res{2} res{1} /\ valR res{2} < P).
    progress. 
  exists (inzp (valR a{1}), inzp (valR b{1}) )%W64x4. progress.
rewrite inzpK. rewrite modz_small. smt. smt.
rewrite inzpK. rewrite modz_small. smt. smt.
rewrite inzpK. rewrite modz_small. smt. smt.
rewrite inzpK. rewrite modz_small. smt. smt.
progress. smt. 
proc.  wp. skip.  progress.
       rewrite H H0.
smt.
auto.
symmetry. 
transitivity M.mulm 
  (={p,a,b} /\ r{2} = R ==> ={res})
  (ImplFp a{1} a{2} /\
  ImplFp b{1} b{2} /\ ImplZZ p{1} P /\ valR a{1} < P /\ valR b{1} < P /\ r{1} = R ==> ImplFp res{1} res{2} /\ valR res{1} < P).
progress. exists (R,p{1},a{1},b{1}). progress. auto.
conseq okll. auto.
conseq mulm_spec. progress. rewrite H4. apply R_prop. 
progress.  smt.
qed.

module MM = {
  proc ith_bit (kk:W64.t Array4.t, ctr:W64.t) : W64.t = {
    var bit:W64.t;
    var c1:W64.t;
    var c2:W64.t;
    var r:W64.t;
    
    c1 <- (ctr `>>` (W8.of_int 6));
    c2 <- (ctr - (c1 * (W64.of_int 64)));
    r <- kk.[(W64.to_uint c1)]%Array4;
    bit <@ IB.ith_bit64 (r, c2);
    return (bit);
  }

}.
lemma ith_bit_lemmaEq :
      equiv[ MM.ith_bit ~ M.ith_bit : ={arg} ==> ={res}].
proc.
seq 2 4 : (={c1, c2,kk}). wp.
skip. progress.
have -> : 63 = 2^6 - 1. smt().
rewrite and_mod. auto. simplify.
have x:  to_uint (ctr{2} `>>` (of_int 6)%W8) = to_uint ctr{2} %/ 64. smt.
rewrite to_uint_eq.
auto.
rewrite to_uintB.  rewrite /(\ule). smt.
rewrite to_uintM_small.  smt.
rewrite  shr_div_le.
auto. simplify. smt.
sim.
qed.




lemma ith_bit_lemma' :
      equiv[ M.ith_bit ~ Spec.ith_bit : arg{1}.`1 = arg{2}.`1 /\  W64.to_uint arg{1}.`2 = arg{2}.`2 /\
 0 <= ctr{2} && ctr{2} < 256 ==>
              ={res} /\ (res{2} = W64.one \/ res{2} = W64.zero)].
transitivity MM.ith_bit
   (={arg} ==> ={res})
   (arg{1}.`1 = arg{2}.`1 /\  W64.to_uint arg{1}.`2 = arg{2}.`2 /\
 0 <= ctr{2} && ctr{2} < 256 ==>
              ={res} /\ (res{2} = W64.one \/ res{2} = W64.zero)).
progress. smt(). smt().
symmetry. conseq ith_bit_lemmaEq. auto. auto.
proc.
seq 3 0 : (to_uint c1{1} = (to_uint ctr{1} %/ 64) /\ to_uint c2{1} = (to_uint ctr{1} %% 64) /\ to_uint ctr{1} = ctr{2}
  /\ r{1} = kk{1}.[(to_uint ctr{1} %/ 64)]%Array4 /\ r{2} = kk{1} /\ 0 <= ctr{2} && ctr{2} < 256 ).
wp.  skip. progress.
smt.
rewrite modzE.
have <-: to_uint (ctr{1} `>>` (of_int 6)%W8) = to_uint ctr{1} %/ 64. smt.
rewrite to_uintB. rewrite /(\ule). smt.
smt.
smt.
exists* r{1}, c2{1}. elim*. progress.
call {1} (ithbit64 r_L c2_L). skip.
progress. smt. smt.
rewrite /ith_bitword64.  rewrite H0.
rewrite /ith_bitR. rewrite /Rbits. rewrite /valR.
rewrite /ith_bit.
rewrite /as_word.
rewrite /as_w64.
have ->: (kk{1}.[to_uint ctr{1} %/ 64])%Array4.[to_uint ctr{1} %% 64]
  = nth false (int2bs 256 ((valR kk{1}))%W64x4) (to_uint ctr{1}) .
rewrite - get_w2bits.
rewrite - get_to_list.
have -> : (W64.w2bits (nth witness ((to_list kk{1}))%Array4 (to_uint ctr{1} %/ 64)))
 = ((nth witness (map W64.w2bits (to_list kk{1}))%Array4 (to_uint ctr{1} %/ 64))).
rewrite - (nth_map witness witness W64.w2bits). progress.   smt. smt.
auto.
have -> : (nth witness (map W64.w2bits ((to_list kk{1}))%Array4)
     (to_uint ctr{1} %/ 64))
 = (nth [] (map W64.w2bits ((to_list kk{1}))%Array4)
     (to_uint ctr{1} %/ 64)).
rewrite (nth_change_dfl [] witness). progress.  smt. smt. auto.
rewrite - (BitChunking.nth_flatten false 64 (map W64.w2bits ((to_list kk{1}))%Array4) (to_uint ctr{1})).
rewrite  List.allP. progress. timeout 5.
have : exists z, z \in ((to_list kk{1}))%Array4 /\ x = W64.w2bits z.
apply mapP. auto. elim. progress.
have ->: (flatten (map W64.w2bits ((to_list kk{1}))%Array4))  = (int2bs 256 ((valR kk{1}))%W64x4).
have -> : (valR kk{1})%W64x4 = bs2int (flatten (map W64.w2bits ((to_list kk{1}))%Array4)).
rewrite /bnk.
have ->: range 0 4 = [0;1;2;3].  rewrite range_ltn. auto.
rewrite range_ltn. auto. rewrite range_ltn. auto.
simplify. rewrite range_ltn. auto.
simplify. rewrite range_geq. auto. auto.
rewrite big_consT.
rewrite big_consT.
rewrite big_consT.
rewrite big_consT.
rewrite big_nil.
rewrite /to_list.
have ->: 4 = 0 + 1 + 1 + 1 + 1 . smt().
rewrite   mkseqS. auto.
rewrite   mkseqS. auto.
rewrite   mkseqS. auto.
rewrite   mkseqS. auto.
rewrite mkseq0. simplify.
rewrite flatten_cons.
rewrite flatten_cons.
rewrite flatten_cons.
rewrite flatten_cons.
rewrite flatten_nil.
rewrite cats0.
rewrite bs2int_cat.
rewrite bs2int_cat.
rewrite bs2int_cat. simplify.
smt.
have ->: 256 = size (flatten (map W64.w2bits ((to_list kk{1}))%Array4)).
rewrite /to_list.
have ->: 4 = 0 + 1 + 1 + 1 + 1 . smt().
rewrite   mkseqS. auto.
rewrite   mkseqS. auto.
rewrite   mkseqS. auto.
rewrite   mkseqS. auto.
rewrite mkseq0. simplify.
rewrite flatten_cons.
rewrite flatten_cons.
rewrite flatten_cons.
rewrite flatten_cons.
rewrite flatten_nil.
rewrite size_cat.
rewrite size_cat.
rewrite size_cat.
rewrite size_cat.
simplify. auto.
rewrite  bs2intK. auto. auto.
auto. smt().
qed.


lemma expm_real_spec : 
      equiv[ Exp.M1.iterop_spec ~ Exp.M7(MultM).iterop :
            ImplZZ m{2} P /\
            ={x} /\
            bs2int n{1} = valR n{2} /\ size n{1} = 256 /\ valR x{1} < P ==>
            ={res}].
apply (Exp.iterop_real_speac MultM _ _ _). 
transitivity M.swapr
  (={arg} ==> ={res})
  (a{2} = x{1} /\ b{2} = y{1} /\ swap_0{1} = (as_w64 c{2}) ==>
          ={res}).
progress. smt(). smt().
proc. sim.
symmetry.
transitivity Spec.swapr
  (={arg} ==> ={res})
  (a{1} = x{2} /\ b{1} = y{2} /\ swap_0{2} = (as_w64 c{1}) ==>
          ={res}).
smt(). smt().
proc. sim.
symmetry. conseq swap_lemma. smt(). 
transitivity MultM.ith_bit
  (={arg} ==> ={res})
  (arg{1}.`1 = arg{2}.`1 /\ ImplWord ctr{1} ctr{2} /\ 0 <= ctr{2} && ctr{2} < 256 ==>
          ={res} /\ (res{2} = W64.one \/ res{2} = W64.zero)).
smt(). smt().
proc. sim.
conseq ith_bit_lemma'.
conseq okl. smt(). auto. auto.
qed.

lemma to_uintP: forall (x y : R), valR (x *** y) = (valR x * valR y) %% P.
progress. rewrite /( *** ). smt.
qed.


lemma kk :  forall (n : int), 0 <= n => forall (a : zp) (b : t), valR%W64x4 b < P =>
  ImplFp b a =>
  ImplFp ((^) b n) (inzp (asint a ^ n)).
apply intind. progress.
rewrite exp_prop1.
have -> : (asint a ^ 0) = 1. smt.
rewrite /asint.
have -> : (Sub.val (inzp 1))%Sub = 1. smt.
smt.
progress.
have ->: ((^) b (i + 1)) = b *** ((^) b  i).
rewrite exp_prop3. auto. auto.  auto.
rewrite exp_prop2.
rewrite exp_prop7. smt.
have ->: inzp (asint a ^ (i + 1)) =  inzp (asint a * (asint a ^ i)).
smt.
have ->:  inzp (asint a * (asint a ^ i)) = (inzp (asint a)) * (inzp (asint a ^ i)).
smt.
rewrite - H2. 
have ->: asint (inzp (valR%W64x4 b) * inzp (valR%W64x4 b ^ i))
  = (asint (inzp (valR%W64x4 b)) * (asint  (inzp (valR%W64x4 b ^ i)))) %% P.
smt.
have ih :  ImplFp (b ^ i)  (inzp (valR%W64x4 b ^ i)).
smt.
rewrite - ih.
have ->: asint (inzp (valR%W64x4 b)) = valR%W64x4 b. smt.
simplify. 
rewrite  to_uintP /=. done.
qed.


lemma left_end :
 equiv[ ASpecFp.expm ~ Exp.M1.iterop_spec  :
    ImplFp x{2} a{1} /\  bs2int n{2}  = valR b{1} /\ valR%W64x4 x{2} < P ==> ImplFp res{2} res{1}]. 
proc.
wp.  skip.  progress.
rewrite  (kk (bs2int n{2}) _ a{1}). smt. auto. auto. smt.
qed.


lemma right_end : 
 equiv[ M7(MultM).iterop ~ M.expm : r{2} = R /\ ={m,x,n} ==> ={res} ].
proc. sim.
seq  7  13 : (={x1,x2,x3,x4,d,ctr,n,m} /\ r{2} = R).
call (_:true). sim.
call (_:true). sim.
wp. 
    call okll.
ecall {2} (bn_copy_correct x{2}).
wp. 
call (_:true). sim. 
call {2} bn_set1_correct.
call {2} bn_set1_correct. wp. skip. progress.
smt. smt.
while (={x1,x2,x3,x4,d,ctr,n,m} /\ r{2} = R). wp.
call (_:true). sim. wp.
call (_:true). sim. wp.
call okll.
call okll.
call (_:true). sim. wp.
call (_:true). sim. wp. 
call (_:true). sim. wp. 
skip. progress.
smt.
skip.
progress. 
qed.


lemma expm_correct : 
      equiv[ ASpecFp.expm ~ M.expm :
             ImplZZ m{2} P /\
             asint a{1} = valR x{2} /\
             b{1} = n{2}  /\ 
             valR x{2} < P /\ 
             r{2} = R
             ==> asint res{1} = valR{2}%W64x4 res{2}]. 
simplify.
transitivity Exp.M1.iterop_spec
  (ImplFp x{2} a{1} /\  bs2int n{2} = valR b{1} /\ size n{2} = 256  /\ valR%W64x4 x{2} < P ==> ImplFp res{2} res{1})
  (ImplZZ m{2} P /\
             x{1} =  x{2} /\
            bs2int n{1} = valR n{2} /\ size n{1} = 256 /\ valR x{2} < P /\ r{2} = R ==>
            res{1} =  res{2}).
progress.
exists (x{2}, int2bs 256 (valR b{1})).
progress. smt.
smt.
smt.
smt.
smt. smt.
conseq left_end.  smt.
symmetry.
transitivity M7(MultM).iterop
 (r{1} = R /\ ={m,x,n}  ==> ={res})
 (p{2} = P /\ size n{2} = 256 /\
             x{1} =  x{2} /\
                         ImplZZ m{1} P /\
             valR n{1} = bs2int  n{2}  /\ valR x{2} < P  ==>
            res{1} =  res{2}).
progress.
exists (m{1}, x{1}, n{1}). progress. smt(). smt.
smt(). auto.
symmetry.
conseq right_end. smt().
progress.
symmetry.
conseq expm_real_spec. progress.
smt().
smt.
progress.
qed.

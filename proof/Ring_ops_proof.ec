require import AllCore IntDiv CoreMap List.

require import JModel JBigNum Ith_Bit64.
require import Ring_ops_spec Ring_ops_extract.
import Array128 Array64 Array32.
import Zp W64xN R.
import StdBigop Bigint BIA.

op R : W64.t Array64.t = R2.bn_ofint Ri.
require import BarrettRedInt.

lemma kok (a b c : real) : 0%r <= a => 0%r < b => 1%r < c =>
 a <= b / c => a < b.
smt(@Real).
qed.


require import RealExp.
lemma R_prop : W64x2N.valR R = 4 ^ (64 * nlimbs) %/ P.
rewrite /R.
have q1: 0 <= Ri. rewrite /Ri. 
rewrite divz_ge0. smt(P_pos). smt(@Ring).

have q2: Ri < W64x2N.modulusR .   
  have ->: W64x2N.modulusR = (2^ (64 * dnlimbs)). rewrite /W64x2N.modulusR. smt(@Ring).

  have -> : Ri = (ri P (64 * nlimbs)). rewrite /Ri. rewrite /ri. smt().
  have : (ri P (64 * nlimbs))%r <= ((4 ^ (64*nlimbs))%r / P%r).  rewrite - same_ri. smt(P_pos). smt().
  rewrite /r.  rewrite - exp_lemma1. smt(). smt(). smt(floor_bound).

  have -> : (4 ^ (64 * nlimbs))%r = ((2 * 2) ^ (64 * nlimbs))%r. smt().
  have -> : ((2 * 2) ^ (64 * nlimbs))%r = ((2 ^ (2 * 64 * nlimbs)))%r. smt(@Ring).
  have->: (2 ^ (2 * 64 * nlimbs))%r = (2 ^ (64 * dnlimbs))%r. smt(@RealExp @Ring).
  pose x := ri P (64 * nlimbs).
  move => q.
  have : x%r < 2%r ^ (64 * dnlimbs)%r. apply (kok x%r (2%r ^ (64 * dnlimbs)%r) P%r).
  have ->: x = Ri. rewrite /x /Ri /ri. smt().
   smt(@RealExp). smt(@RealExp). smt(P_pos). rewrite exp_lemma1. smt(). smt(). apply q.
    have ->: 2%r ^ (64 * dnlimbs)%r = (2 ^ (64 * dnlimbs))%r. 
    rewrite - exp_lemma1. smt(). smt(). smt().
smt(@Real).
have ->: (W64x2N.valR ((R2.bn_ofint Ri))%R2)%W64x2N   = Ri.
rewrite W64x2N.R.bn_ofintK. 
smt( modz_small). 
rewrite /Ri. smt().
qed.


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
 wp; skip => />; smt(Array64.get_setE Array64.set_set_if).
wp; skip => />; smt (Array64.set_set_if).
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
 wp; skip => />; smt(Array64.get_setE Array64.set_set_if).
wp; skip; smt(Array64.get_setE Array64.set_set_if).
qed.


equiv dmul1first_eq:
 M.dmul1 ~ W64x2N.MulOps.mul1:
 a{1}=ak{2} /\ ={b}
 ==>
 (res.`1,res.`2,res.`3,res.`4){1} = (W64.zero,res.`1,res.`2,res.`3){2}.
proof.
proc; simplify.
wp.
while ( #pre /\ ={r,i} /\ (a,of_0,cf,_zero){1}=(ak,_of,_cf,W64.zero){2} /\ 
        1 <= i{2} <= dnlimbs /\ !_of{2}).
 wp; skip => />; smt(Array128.get_setE Array128.set_set_if).
wp; skip => />; smt (Array128.set_set_if).
qed.


equiv dmul1acc_eq :
 M.dmul1acc ~ W64x2N.MulOps.mul1acc:
   W64.to_uint k{1} = k{2} /\ ={a,b} /\ (_zero,of_0,cf,r){1}=(W64.zero,_of,_cf,x){2} /\
  0 <= k{2} < dnlimbs
 ==>
 (res.`1,res.`2,res.`3,res.`4){1} = (W64.zero,res.`1,res.`2,res.`3){2}.
proof.
proc. simplify.
wp. while ( #pre /\ ={i} /\ (aux,_zero){1}=(dnlimbs-1,W64.zero){2} /\ 
            0 <= i{2} <= dnlimbs-1 /\ kk{1} = k{2}).
 wp; skip => />; smt(Array128.get_setE Array128.set_set_if).
wp; skip; smt(Array128.get_setE Array128.set_set_if).
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
  W64x2N.valR a{1} = a{2} /\  W64x2N.valR b{1} = b{2}
  ==> 
 W64x2N.valR2 res{1}.`4 = res{2}
     /\ res{1}.`1 = W64.zero /\ !res{1}.`2 /\ !res{1}.`3.
proof.
transitivity 
 W64x2N.MulOps.mulR
 ( ={a,b} ==> res{1}.`2=res{2}.`1 /\ res{1}.`3=res{2}.`2 /\ res{1}.`4=res{2}.`3 /\  res{1}.`1 = W64.zero )
 ( W64x2N.valR a{1} = a{2} /\ W64x2N.valR b{1} = b{2} 
   ==> !res{1}.`1 /\ !res{1}.`2 /\ W64x2N.valR2 res{1}.`3 = res{2}).
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
    { (_of,_cf,r) <@ W64x2N.MulOps.mulR(a,b); }
    ( ={a,b} ==> ={_cf,_of,r} )
    ( W64x2N.valR a{1} = a{2} /\ W64x2N.valR b{1} = b{2} ==> !_cf{1} /\ !_of{1} /\ W64x2N.valR2 r{1} = r{2} ).
  + by move=> /> &1; exists a{1} b{1}; auto.
  + by move=> /> *.
  + by inline W64x2N.MulOps.mulR; sim.
  + by ecall {1} (W64x2N.mulR_ph a{1} b{1}); wp; skip.
qed.


equiv dsubc_spec:
 M.dbn_subc ~ ASpecFp.dsubn:
  W64x2N.valR a{1} = a{2} /\ W64x2N.valR b{1} = b{2} (* /\ W64x2N.valR b{1}  <= W64x2N.valR a{1} *)
  ==> res{1}.`1=res{2}.`1 /\ W64x2N.valR res{1}.`2 = res{2}.`2.
proof.
transitivity 
 W64x2N.R.Ops.subcR
 ( (a,b,false){1}=(a,b,c){2} ==> ={res} )
 (W64x2N.valR  a{1} = a{2} /\ W64x2N.valR b{1} = b{2} /\ !c{1} (* /\ W64x2N.valR b{1}  <= W64x2N.valR a{1} *)
   ==> res{1}.`1 = res{2}.`1 /\ W64x2N.valR res{1}.`2 = res{2}.`2 ).
+ by move=> /> &1 &2 H1 H2 ; exists (a{1},b{1},false).
+ by move=> /> *.
+ proc; simplify.
  unroll {2} 3; rcondt {2} 3; first by auto.
  exlim a{1}, b{1} => aa bb.
  while (={i,b} /\ 1 <= i{2} <= dnlimbs /\ 
         (cf, aa){1}=(c, a){2} /\
         (forall k, 0 <= k < i{2} => a{1}.[k] = r{2}.[k])%Array64 /\
         (forall k, i{2} <= k < dnlimbs => a{1}.[k] = aa.[k])%Array64).
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
  by apply Array64.ext_eq; smt().
+ proc; simplify.
  transitivity {1}
   { (c,r) <@ W64x2N.R.Ops.subcR(a,b,c); }
   ( ={a,b,c} ==> ={c,r} )
   ( W64x2N.valR a{1} = a{2} /\ W64x2N.valR b{1} = b{2} /\ !c{1}  (* /\ W64x2N.valR b{1}  <= W64x2N.valR a{1} *) ==> ={c} 
   /\ W64x2N.valR r{1} = r{2} ).
  + by move=> /> &2 H  ; exists a{2} b{2} false.
  + by auto.
  + by inline*; sim.
  + ecall {1} (W64x2N.R.subcR_ph a{1} b{1} c{1}); wp; skip => /> &m Hc [c r] /= -> .
progress. 
    by rewrite W64x2N.R.bn_borrowE 1:/# b2i0 /bn_modulus /=.
qed.


lemma dbn_cmov_correct x y z :
  phoare[ M.dbn_cmov :  arg = (x,y,z)  ==> res = if x then z else y ] = 1%r.
proc.
while (cond = x /\ b = z /\ i <= dnlimbs 
  /\ (forall j, 0 <= j < i => a.[j] = if cond then z.[j] else y.[j])
  /\ (forall j, i <= j < dnlimbs => a.[j] = y.[j])) (dnlimbs - i). progress.
wp.  skip.  progress. smt().   smt(@Array64). smt(@Array64). smt(). wp.  skip. progress. smt(@Array64). smt().
apply Array64.ext_eq. progress. smt(@Array64). 
qed.


(* lemma dbn_set0_correct : *)
(*   phoare[ M.bn_set0 : true  ==> W64xN.valR res = 0 ] = 1%r. *)
(* proc. *)
(* while (i <= nlimbs  *)
(*   /\ (forall j, 0 <= j < i => a.[j]%Array32 = W64.zero)) (nlimbs - i). progress. *)
(* wp.  skip.  progress. smt().  smt(@Array32). smt(). wp.  skip. progress. smt(). smt(). *)
(* rewrite - zeroRE. congr. *)
(* apply Array32.ext_eq. progress.  rewrite H1. smt().  *)
(* rewrite /zeroR. smt(@Array32). *)
(* qed. *)


require import List.

op oneR : R = (of_list W64.zero (W64.one :: nseq (nlimbs - 1) W64.zero ))%Array32.

    (* TODO: nlimbs specific *)
lemma oneRE: ImplZZ oneR 1.
rewrite /oneR /valR /bnk.
do? (rewrite range_ltn; first by trivial ).
simplify. rewrite range_geq. auto.
do rewrite big_consT.
rewrite big_nil.
 have -> : dig ((of_list W64.zero (W64.one :: nseq (nlimbs - 1) W64.zero)))%Array32 0 = 1.
 simplify. smt(@Int).
 have q : forall x, 0 < x < nlimbs => dig ((of_list W64.zero (W64.one :: nseq (nlimbs - 1) W64.zero)))%Array32 x = 0.
 move => x xp. rewrite /dig.
   have ->: to_uint ((of_list W64.zero (W64.one :: nseq (nlimbs - 1) W64.zero)).[x])%Array32 = 0. 
    do? (rewrite nseqS'; first by trivial). simplify. 
   rewrite nseq0. 
  have -> : (of_list W64.zero [W64.one; W64.zero; W64.zero; W64.zero; W64.zero]).[x]%Array32 = W64.zero. 
rewrite get_of_list. smt().
smt(@List).  smt(@W64). smt().
do? (rewrite q; first smt()). auto.
qed.


lemma bn_set1_correct :
  phoare[ M.bn_set1 : true  ==> W64xN.valR res = 1 ] = 1%r.
proc.
while (0 < i <= nlimbs 
  /\ (forall j, 1 <= j < i => a.[j]%Array32 = W64.zero) /\ a.[0]%Array32 = W64.one) (nlimbs - i). progress.
wp.  skip.  progress. smt(). smt().  smt(@Array32). smt(@Array32). smt(). wp.  skip. progress. smt(@Array32). smt().
rewrite - oneRE. congr.
apply Array32.ext_eq. progress.  
case (x = 0). progress. progress.
rewrite H2. smt(). 
rewrite /oneR. smt(@Array32 @List).
qed.



lemma dbn_copy_correct x :
  phoare[ M.dbn_copy :  arg = x  ==> res = x ] = 1%r.
proc.
while (a = x /\ i <= dnlimbs 
  /\ (forall j, 0 <= j < i => r.[j] = x.[j])
  ) (dnlimbs - i). progress.
wp.  skip.  progress. smt(). smt(@Array64). smt(). wp.  skip. progress. smt(). smt().
apply Array64.ext_eq. progress. smt(). 
qed.


lemma bn_copy_correct x :
  phoare[ M.bn_copy :  arg = x  ==> res = x ] = 1%r.
proc.
while (a = x /\ i <= nlimbs 
  /\ (forall j, 0 <= j < i => r.[j]%Array32 = x.[j]%Array32)
  ) (dnlimbs - i). progress.
wp.  skip.  progress. smt(). smt(@Array32). smt(). wp.  skip. progress. smt(). smt().
apply Array32.ext_eq. progress. smt(). 
qed.



equiv dcminusP_spec:
 M.dcminusP ~ ASpecFp.cminusP:
 W64x2N.valR p{1} = P /\ W64x2N.valR x{1} = a{2} ==> W64x2N.valR res{1}  =res{2}.
proof.
transitivity CSpecFp.dcminusP
 ( W64x2N.valR p{1} = P /\ W64x2N.valR x{1} = a{2} ==> W64x2N.valR res{1}  = res{2} )
 ( ={a} /\ a{2} < W64x2N.modulusR ==> ={res} ).
  progress. exists (W64x2N.valR x{1}). progress. smt(@W64x2N).
+ by auto. 
proc. 
(ecall {1} (dbn_cmov_correct cf{1} z{1} x{1})).  simplify.
conseq (_:  ( (W64x2N.valR (if cf{1} then x{1} else z{1}))%W64x2N = r{2} )). progress.
inline ASpecFp.ctseln. wp.   simplify.
seq 2 0 : ((W64x2N.valR p{1})%W64x2N = P /\ (W64x2N.valR x{1})%W64x2N = a{2} /\ z{1} = x{1}).
(ecall {1} (dbn_copy_correct x{1})).  wp. skip. progress.
seq 1 1 : (cf{1} = c{2} /\ W64x2N.valR z{1} = x{2} 
  /\ (W64x2N.valR p{1})%W64x2N = P /\ (W64x2N.valR x{1})%W64x2N = a{2}).
call  dsubc_spec.  skip. progress.
skip. progress.   smt().
+ symmetry; conseq cminusP_eq; smt().
qed.


import W64x2N.


lemma bn_div2_correct z :
  phoare[ M.div2 : arg = (z,dnlimbs)  ==> (W64x2N.valR res) = (W64x2N.valR2 z) %/  W64x2N.modulusR ] = 1%r.
proc. sp.
while (aux = dnlimbs /\ i <= dnlimbs /\ forall j, 0 <= j < i => r.[j] = x.[dnlimbs + j]) (dnlimbs - i). 
progress. wp. skip. progress.
smt(). smt(@Array64). smt(). skip. progress.
smt(). smt().
have ->:  W64x2N.modulusR  = W64x2N.M^dnlimbs.  rewrite /R.bn_modulus. auto. 
have ->: (R2.bnk (2*dnlimbs) x{hr})%R2 = valR2 x{hr}. auto.
rewrite R2.bghint_div. auto.
rewrite - R.bnkup0.
rewrite /bnkup.
have ->: 
  bigi predT (fun (i1 : int) => to_uint r0.[i1] * W64x2N.M ^ (i1 - 0)) 0 dnlimbs
  = bigi predT (fun (i1 : int) => to_uint x{hr}.[i1 + dnlimbs] * W64x2N.M ^ (i1 - 0)) 0 dnlimbs.
apply eq_big_int. progress. smt(). 
  have ->: bigi predT (fun (i1 : int) => to_uint x{hr}.[i1] * W64x2N.M ^ (i1 - dnlimbs)) dnlimbs
  (2 * dnlimbs)  = bigi predT (fun (i1 : int) => to_uint x{hr}.[i1] * W64x2N.M ^ (i1 - dnlimbs)) (0 + dnlimbs)
  (2 * dnlimbs). auto.
rewrite big_addn. simplify. auto.
qed.



lemma bn_shrink_correct a  :
  phoare[ M.bn_shrink : arg = a  ==> W64xN.valR res = W64x2N.valR a %% W64xN.modulusR ] = 1%r.
proc.
sp.
while (i <= nlimbs /\ forall j, 0 <= j < i => r.[j]%Array32 = x.[j]%Array64) (nlimbs - i). 
progress. wp. skip. progress.
smt(). smt(@Array32). smt(). skip. progress.
smt(). smt(). 
rewrite /W64xN.modulusR. auto.
rewrite W64x2N.R.bn_mod. auto. 
rewrite /bnk. 
apply eq_big_seq. progress. rewrite H1. split.
smt (mem_range_le). 
smt (mem_range_gt).
auto.
qed.


lemma bn_expand_correct : forall a,
      phoare[ M.bn_expand : arg = a  ==> W64x2N.valR res =  W64xN.valR a ] = 1%r.
 have  bn_expand_correct : forall a, 
    hoare[ M.bn_expand : arg = a  ==> W64x2N.valR res = W64xN.valR a ].
   move => a.
   proc.
   sp. 
    seq 1 : (a = x /\ i = nlimbs /\ forall i, i < nlimbs => r.[i] = x.[i]%Array32).
    while (i <= nlimbs /\ forall j, 0 <= j < i => r.[j] = x.[j]%Array32). wp.  skip. progress.
    smt(). smt(@Array32 @Array64). skip. progress.
    smt().  smt(). smt(@Array64 @Array32). 
    seq 2 : (a = x /\  (forall j, 0 <= j < nlimbs => r.[j]%Array64 = x.[j]%Array32)
         /\ (forall j, nlimbs <= j < 2*nlimbs => r.[j] = W64.zero)).     
    while (a = x /\ nlimbs <= i <= 2*nlimbs 
         /\ (forall j, 0 <= j < nlimbs => r.[j]%Array64 = x.[j]%Array32)
         /\ (forall j, nlimbs <= j < i => r.[j] = W64.zero) ). wp.  skip. progress.
    smt(). smt().
    have z : i{hr} <> j. smt(). 
    rewrite - H1. auto.  smt(@Array32 @Array64).
    case (j = i{hr}). smt(@Array32 @Array64).
    progress.
    have : j < i{hr}.  smt().
    progress.
    rewrite - (H2 j).  smt().
    smt(@Array32 @Array64). wp. 
    skip.  progress.
    smt(@Array32 @Array64). smt(). smt(). 
    skip.  progress.
    have -> : valR r{hr} = (bn_seq ((to_list r{hr}))%Array64).
    apply W64x2N.R.bn2seq. 
    rewrite /to_list.
    have -> : dnlimbs = nlimbs + nlimbs. smt().
    rewrite mkseq_add. auto. auto.
    have -> : mkseq (fun (i0 : int) => r{hr}.[i0]) nlimbs 
      = mkseq (fun (i0 : int) => x{hr}.[i0]%Array32) nlimbs.
    apply eq_in_mkseq. progress. 
    simplify.
    have ->: mkseq (fun (i0 : int) => r{hr}.[nlimbs + i0]) nlimbs
      = mkseq (fun (i0 : int) => W64.zero) nlimbs.
    apply eq_in_mkseq. progress. rewrite H0. smt(). auto.
    rewrite mkseq_nseq. 
    rewrite /bn_seq.
    rewrite foldr_cat.
    have ->: (foldr (fun (w : W64.t) (r0 : int) => to_uint w + W64x2N.M * r0) 0
         (nseq nlimbs W64.zero)) = 0.  
       have gen : forall n, 0 <= n => foldr (fun (w : W64.t) (r0 : int) => to_uint w + W64x2N.M * r0) 0
                     (nseq n  W64.zero) = 0.
       apply intind. progress. rewrite nseq0. simplify. auto.
       progress. rewrite nseqS. auto. simplify. rewrite H2. auto.
       apply gen. auto.
    rewrite W64xN.R.bn2seq. rewrite /bn_seq. rewrite /to_list. 
    pose f := (fun (w : W64.t) (r0 : int) => to_uint w + W64x2N.M * r0).
    simplify. auto.    
move => a.
bypr. progress.
 have ->:  1%r = Pr[M.bn_expand(arg{m}) @ &m : true ] . 
byphoare. proc.  while (true) (2*nlimbs -i). progress. wp. skip. smt().
wp. while true (nlimbs - i). progress. wp. skip. smt().
wp.  skip. smt(). auto. auto.
  have ->: Pr[M.bn_expand(arg{m}) @ &m : true]
  = Pr[M.bn_expand(arg{m}) @ &m : (W64x2N.valR res =  W64xN.valR arg{m}) ]  
    + Pr[M.bn_expand(arg{m}) @ &m : (W64x2N.valR res <>  W64xN.valR arg{m}) ].
rewrite Pr[mu_split (W64x2N.valR res =  W64xN.valR arg{m})]. simplify.   auto.
have ->: Pr[M.bn_expand(arg{m}) @ &m : valR res <> valR arg{m}] = 0%r.
byphoare (_: arg = arg{m} ==> _). 
hoare. simplify. conseq (bn_expand_correct arg{m}). auto. auto. auto.
qed.

   
equiv breduce_cspec:
 M.bn_breduce ~ CSpecFp.redm:
     W64x2N.valR a{1} = a{2} 
 /\  W64x2N.valR r{1} = r{2} 
 /\  W64xN.valR p{1} = P
 /\  k{2} = 64 * nlimbs
   ==>  (W64xN.valR res{1}) = res{2}  %% W64xN.modulusR.
proof. proc.
sp.
simplify.
seq 0 0 : (valR a{1} = a{2} /\ valR r{1} = r{2} /\ ImplZZ p{1} P /\ k{2} = 64 * nlimbs). 
skip. auto.
seq 1 1 : (valR a{1} = a{2} /\ valR r{1} = r{2} /\ ImplZZ p{1} P /\ k{2} = 64 * nlimbs
    /\ W64x2N.valR2 xr{1} = xr{2} (* /\ xr{2} = a{2} * r{2} *)).
call dmuln_spec. skip. progress.
seq 1 1 : (valR a{1} = a{2} /\ valR r{1} = r{2} /\ ImplZZ p{1} P /\ k{2} = 64 * nlimbs
    /\ W64x2N.valR2 xr{1} = xr{2} /\ W64x2N.valR xrf{1} = xrf{2} ).
ecall {1} (bn_div2_correct xr{1}). inline*. wp.  skip. move => &1 &2 z. split. auto. move => _.
move => r zz. split. smt(). split. smt(). split. smt(). split. smt(). split. smt(). rewrite zz.
have -> : W64x2N.modulusR = 2 ^ (2 * k{2}). smt(@Ring). smt().
seq 1 1 : (valR a{1} = a{2} /\ valR r{1} = r{2} /\ ImplZZ p{1} P /\ k{2} = 64 * nlimbs
    /\ W64x2N.valR2 xr{1} = xr{2} /\  valR xrfd{1} =  xrf{2}   ).
ecall {1} (bn_shrink_correct xrf{1}). wp. skip. progress. rewrite H0.  
have ->: W64xN.modulusR = Ring_ops_spec.M. rewrite /W64xN.modulusR. rewrite /M. smt(@Ring). rewrite /M. smt(@Ring). 
seq 1 1 : (valR a{1} = a{2} /\ valR r{1} = r{2} /\ ImplZZ p{1} P /\ k{2} = 64 * nlimbs
    /\ W64x2N.valR2 xr{1} = xr{2} /\ valR xrfd{1} = xrf{2} 
    /\  W64x2N.valR xrfn{1} = xrfn{2}).
ecall  (muln_spec xrfd{1} p{1}). skip. progress.
seq 1 1 : (valR a{1} = a{2} /\ valR r{1} = r{2} /\ ImplZZ p{1} P /\ k{2} = 64 * nlimbs
    /\ W64x2N.valR2 xr{1} = xr{2} /\ W64xN.valR xrfd{1} = xrf{2} 
    /\ W64x2N.valR xrfn{1} = xrfn{2}
    /\ W64x2N.valR t{1} = t{2}).
call dsubc_spec. skip. progress.
seq 1 0 : (valR a{1} = a{2} /\ valR r{1} = r{2} /\ ImplZZ p{1} P /\ k{2} = 64 * nlimbs
    /\ W64x2N.valR2 xr{1} = xr{2} /\ W64xN.valR xrfd{1} = xrf{2} 
    /\ W64x2N.valR xrfn{1} = xrfn{2}
    /\ W64x2N.valR t{1} = t{2}
    /\ W64x2N.valR pp{1} = W64xN.valR p{1}).
ecall {1} (bn_expand_correct p{1}). skip. progress.
seq 1 1 : (valR a{1} = a{2} /\ valR r{1} = r{2} /\ ImplZZ p{1} P /\ k{2} = 64 * nlimbs
    /\ W64x2N.valR2 xr{1} = xr{2} /\ W64xN.valR xrfd{1} = xrf{2} 
    /\ W64x2N.valR xrfn{1} = xrfn{2}
    /\ W64x2N.valR t{1} = t{2}
    /\ W64x2N.valR pp{1} = W64xN.valR p{1}
    /\ W64x2N.valR t{1} = t{2} ).
call dcminusP_spec. skip. progress. smt().
seq 1 0 : (valR a{1} = a{2} /\ valR r{1} = r{2} /\ ImplZZ p{1} P /\ k{2} = 64 * nlimbs
    /\ W64x2N.valR2 xr{1} = xr{2} /\ W64xN.valR xrfd{1} = xrf{2} 
    /\ W64x2N.valR xrfn{1} = xrfn{2}
    /\ W64x2N.valR t{1} = t{2}
    /\ W64x2N.valR pp{1} = W64xN.valR p{1}
    /\ W64x2N.valR t{1} = t{2}
    /\ W64xN.valR res_0{1} = W64x2N.valR t{1} %% W64xN.modulusR).
ecall {1} (bn_shrink_correct t{1}). skip. progress.
skip.  progress. 
qed.


equiv bnreduce_spec:
 M.bn_breduce ~ ASpecFp.redm:
  valR a{1} = a{2}
  /\ ImplZZ p{1} P
  /\ valR r{1} = (ri P (64 * nlimbs))  
  /\ 0 < P < W64xN.modulusR
  /\ 0 <= a{2} < P * P
  /\ 0 < P < 2 ^ (64 * nlimbs)
  /\ 0 <= valR r{1} ==> valR res{1} = res{2} .
proof. 
  have redm_simp:
 equiv [ ASpecFp.redm ~ ASpecFp.redm: ={arg} ==> res{1} = res{2} %% W64xN.modulusR ].
 proc. wp.  skip. progress. 
rewrite (pmod_small (a{2} %% P)) . split.  apply modz_ge0. smt(P_pos modz_ge0). move => _.
smt(ltz_pmod P_pos ppos). auto.
symmetry. transitivity ASpecFp.redm
 (={arg} ==> res{1} = res{2} %% W64xN.modulusR)
 (valR a{2} = a{1}
  /\ ImplZZ p{2} P
  /\ valR r{2} =  (ri P (64 * nlimbs))  
  /\ 0 < P < W64xN.modulusR
  /\ 0 <= a{1} < P * P
  /\ 0 < P < 2 ^ (64 * nlimbs)
  /\ 0 <= valR r{2} ==> valR res{2} = res{1} %% W64xN.modulusR).
smt(). 
auto. conseq redm_simp. 
symmetry.
transitivity CSpecFp.redm
 (W64x2N.valR a{1} = a{2} 
 /\  W64x2N.valR r{1} = r{2} 
 /\  W64xN.valR p{1} = P
 /\  k{2} = 64 * nlimbs
   ==>  (W64xN.valR res{1}) = res{2}  %% W64xN.modulusR)
 (={a} /\ r{1} = (ri P k{1}) 
  /\ 0 < P < W64xN.modulusR
  /\ 0 <= a{1} < P * P
  /\ 0 < P < 2 ^ k{1} 
  /\ 0 <= k{1} ==> ={res}). 
move => &1 &2 q. 
exists (valR a{1} , valR r{1} , 64 * nlimbs). split. smt(). 
split. smt(). split. smt().   split.  smt(). 
split. smt(). split. split. smt().  move => ?. 
have ->: (valR a{1}, valR r{1}, 64 * nlimbs).`3 = 64 * nlimbs. smt().
 have ->: 2 ^ (dnlimbs * nlimbs) = W64xN.modulusR. clear q. rewrite /W64xN.modulusR. smt(@Ring).
smt(). smt(). auto.
conseq breduce_cspec.
symmetry. conseq redm_eq. auto. auto.
qed.


lemma q (a b p : int) : 0 <= a < p => 0 <= b < p => a * b < p * p.
smt(@Int). qed.

equiv mulm_cspec:
 M.mulm ~ CSpecFp.mulm:
  valR a{1} = a{2}
  /\ valR b{1} = b{2}
  /\ valR a{1} < P
  /\ valR b{1} < P
  /\ ImplZZ p{1} P
  /\ valR r{1} = ri P (64 * nlimbs)
   ==> valR res{1} =  res{2} .
proc. 
call bnreduce_spec.
ecall (muln_spec a{1} b{1}).
wp. skip.
move => &1 &2 H1. split. smt().
move => q1 r1 r2 r3 . split. simplify. rewrite - r3.
smt(@W64xN @W64x2N).
   split.  simplify. smt().
split. smt().
split.  smt (P_pos bnk_cmp).
split.  smt (P_pos bnk_cmp).
split.  split. smt (P_pos).
have -> :  2 ^ (dnlimbs * nlimbs) = W64xN.modulusR. rewrite /W64xN.modulusR. smt(@Ring).
smt(ppos). smt(W64x2N.R.bnk_cmp).
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
move=> /> &1 &2 H1 H2 H3 _; exists (valR a{1}, valR b{1}).  progress.
smt(@Zp).
smt(@Zp). auto.
conseq mulm_cspec. 
conseq mulm_eq.
qed.




require import BitEncoding.
import BS2Int.

require MontgomeryLadder.



clone import MontgomeryLadder as Exp with type R  <- t,
                                                 op P <- P,
                                                 op Rsize <- 64*nlimbs,
                                                 op valR <- W64xN.valR,
                                                 op of_int <- bn_ofint,
                                                 op idR <- bn_ofint 1,
                                                 op ( ** ) <- Int.( * ),
                                                 op ( *** ) <=  fun a b => bn_ofint ((valR%W64xN a * valR%W64xN b) %% P)
proof*.
realize Rsize_max. smt(). qed.
realize Rsize_pos. smt(). qed.
realize valr_pos. smt (@W64xN). qed.
realize iii.  rewrite /Rbits. 
progress. rewrite  size_int2bs. auto. qed.
realize valr_ofint.  progress.
rewrite bn_ofintK. apply modz_small. split. auto. smt(ppos).
qed.
realize P_pos. smt(P_pos). qed.
realize ofint_valr. smt(@W64xN). qed.
realize rbits_bitsr. 
progress. rewrite /Rbits. rewrite /bitsR. 
  have ->: (valR (bn_ofint (bs2int x)))%W64xN = bs2int x.
rewrite bn_ofintK. apply modz_small.
rewrite /W64xN.modulusR. 
split. apply bs2int_ge0. 
have ->: `|W64x2N.M ^ nlimbs| = W64x2N.M ^ nlimbs. smt(@Int).
have xx : bs2int x < 2 ^ (64*nlimbs).  
    have o : forall n (s : bool list),  n = size s => bs2int s < 2 ^ n. smt(bs2int_le2Xs).
(* have -> : Ring_ops_spec.M = W64xN.modulusR. rewrite /W64xN.modulusR. smt(@Ring). *)
(* rewrite /W64xN.modulusR. *)
    (* ??? *)
have ->:  (dnlimbs * nlimbs) = 2048. smt().
clear o. rewrite -H. smt(bs2int_le2Xs).
have <- : 2 ^ (64*nlimbs) = W64x2N.M ^ nlimbs. smt(@Ring).
move => ?. assumption.
smt(bs2intK). qed.
realize bitsr_rbits. 
rewrite /Rbits. rewrite /bitsR.
progress.
rewrite int2bsK. auto. simplify. progress. smt(bnk_cmp).
have : 0 <= valR  x < W64xN.M ^ nlimbs.
apply (bnk_cmp nlimbs).
smt(@Ring).
smt(@W64xN).
qed.
realize exp_prop7. progress.
have -> : valR a * valR b = valR b * valR a. smt(@Int). auto.
qed.
realize exp_prop6. progress.
have ->: (valR (bn_ofint ((valR a * valR b) %% P)) * valR c) %% P
  = ((valR a * valR ((bn_ofint ((valR b * valR c) %% P)))) %% P). 
rewrite valr_ofint. 
split. rewrite modz_ge0. smt(P_pos).
smt(ltz_pmod P_pos).
rewrite valr_ofint. 
split. rewrite modz_ge0. smt(P_pos).
smt(ltz_pmod P_pos).
rewrite modzMml.
rewrite modzMmr. smt(@Int).
auto.
qed.
realize exp_prop5. progress. 
rewrite valr_ofint. progress. smt(P_pos). simplify. 
rewrite modz_small. smt(bnk_cmp P_pos).
smt(bnK). qed.
realize mult_valr. progress. 
rewrite valr_ofint. 
split. rewrite modz_ge0. smt(P_pos).
smt(ltz_pmod P_pos).
smt(ltz_pmod P_pos). qed.
realize idR_leP. 
rewrite bnk_ofintK. auto. smt(@Ring P_pos). qed.

  


module MultM = {
  proc ith_bit = M.ith_bit
  proc swapr   = M.swapr
  proc opr (p:W64.t Array32.t, a:W64.t Array32.t,
             b:W64.t Array32.t) : W64.t Array32.t = {
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
wp. skip. progress. smt(@W64). smt(@W64).
while {1} (0 <= i{1} /\ ((as_bool swap_0{1} => mask{1} = (of_int 18446744073709551615)%W64 )
              /\ (as_bool swap_0{1} = false => mask{1} = (of_int 0)%W64)) 
   /\ (forall j, 0 <= j < i{1} => (x{1}.[j])%Array32 = (if as_bool swap_0{1} then (b{2}.[j]) else (a{2}.[j]))%Array32 )  
   /\ (forall j, 0 <= j < i{1} => (y{1}.[j])%Array32 = (if as_bool swap_0{1} then (a{2}.[j]) else (b{2}.[j]))%Array32 )  
   /\ (forall j, i{1} <= j => (x{1}.[j])%Array32 =  (a{2}.[j]))%Array32
   /\ (forall j, i{1} <= j => (y{1}.[j])%Array32 =  (b{2}.[j]))%Array32
 ) (nlimbs - i{1} + 1).
progress. wp.  skip.  progress.   smt().
case (j <  i{hr}). progress. smt(@Array32).
progress.
have : j = i{hr}. smt().
progress.
have ->: (x{hr}.[i{hr} <-
    x{hr}.[i{hr}] `^` (x{hr}.[i{hr}] `^` y{hr}.[i{hr}] `&` mask{hr})].[i{hr}])%Array32
 = (x{hr}.[i{hr}] `^` (x{hr}.[i{hr}] `^` y{hr}.[i{hr}] `&` mask{hr}))%Array32. smt(@Array32).
case (as_bool swap_0{hr}). progress.
rewrite H4. auto.  rewrite H0. auto. rewrite H5. auto. rewrite - ones64. 
have -> : ((a{m}.[i{hr}])%Array32 `^` (b{m}.[i{hr}])%Array32 `&`
 (of_int W64.max_uint)%W64) = a{m}.[i{hr}]%Array32 `^` ((b{m}.[i{hr}])%Array32 `&`
 (of_int W64.max_uint)%W64).
pose x := a{m}.[i{hr}]%Array32.
pose y := b{m}.[i{hr}]%Array32.
pose z := (of_int W64.max_uint)%W64.
rewrite andwDl.
have ->: (x `&` z) = x. smt (W64.andw1_s).
auto.
have ->: ((b{m}.[i{hr}])%Array32 `&` (of_int W64.max_uint)%W64) = ((b{m}.[i{hr}])%Array32). 
pose y := b{m}.[i{hr}]%Array32.
pose z := (of_int W64.max_uint)%W64.
smt (W64.andw1_s).
smt(@W64).
progress. rewrite H4. auto.  rewrite H1. smt(). auto. 
case (j <  i{hr}). progress. smt(@Array32).
progress.
have : j = i{hr}. smt().
progress.
have ->: (y{hr}.[i{hr} <-
   y{hr}.[i{hr}] `^` (x{hr}.[i{hr}] `^` y{hr}.[i{hr}] `&` mask{hr})].[i{hr}])%Array32
 = (y{hr}.[i{hr}] `^` (x{hr}.[i{hr}] `^` y{hr}.[i{hr}] `&` mask{hr}))%Array32. smt(@Array32).
case (as_bool swap_0{hr}). progress.
rewrite H4. auto.  rewrite H0. auto. rewrite H5. auto. rewrite - ones64. 
have -> : ((a{m}.[i{hr}])%Array32 `^` (b{m}.[i{hr}])%Array32 `&`
 (of_int W64.max_uint)%W64) = a{m}.[i{hr}]%Array32 `^` ((b{m}.[i{hr}])%Array32 `&`
 (of_int W64.max_uint)%W64). 
pose x := a{m}.[i{hr}]%Array32.
pose y := b{m}.[i{hr}]%Array32.
pose z := (of_int W64.max_uint)%W64.
rewrite andwDl.
have ->: (x `&` z) = x. smt (W64.andw1_s).
auto.
have ->: ((b{m}.[i{hr}])%Array32 `&` (of_int W64.max_uint)%W64) = ((b{m}.[i{hr}])%Array32).
pose y := b{m}.[i{hr}]%Array32.
pose z := (of_int W64.max_uint)%W64.
smt (W64.andw1_s).
smt(@W64).
progress. rewrite H4. auto.  rewrite H1. smt(). smt(@W64).
smt(@Array32). smt(@Array32). smt().
skip. progress. smt().   smt().   smt(). 
case (c{2} = false). progress.  
apply Array32.ext_eq.  progress. rewrite H5. progress. smt(). rewrite /as_bool. rewrite /as_w64. simplify. smt(@W64).
apply Array32.ext_eq.  progress. rewrite H6. progress. smt(). rewrite /as_bool. rewrite /as_w64. simplify. smt(@W64).
progress. have ->: c{2} = true. smt(). simplify.
progress. 
apply Array32.ext_eq.  progress. rewrite H5. progress. smt(). rewrite /as_bool. rewrite /as_w64. simplify. smt(@W64).
apply Array32.ext_eq.  progress. rewrite H6. progress. smt(). rewrite /as_bool. rewrite /as_w64. simplify. smt(@W64).
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
  exists (inzp (valR a{1}), inzp (valR b{1}) )%W64xN. progress.
rewrite inzpK. rewrite modz_small. smt(bnk_cmp). smt(@Zp).
rewrite inzpK. rewrite modz_small. smt(bnk_cmp). smt(@Zp).
rewrite inzpK. rewrite modz_small. smt(bnk_cmp). smt(@Zp).
rewrite inzpK. rewrite modz_small. smt(bnk_cmp). smt(@Zp).
progress. 
have : valR res{1} = valR res{2}. smt().
smt(@W64xN).
proc.  wp. skip.  progress.
       rewrite H H0.
rewrite valr_ofint. 
split. rewrite modz_ge0. smt(P_pos).
smt(ltz_pmod P_pos).
smt(@Zp).
auto.
symmetry. 
transitivity M.mulm 
  (={p,a,b} /\ r{2} = R ==> ={res})
  (ImplFp a{1} a{2} /\
  ImplFp b{1} b{2} /\ ImplZZ p{1} P /\ valR a{1} < P /\ valR b{1} < P /\ r{1} = R ==> ImplFp res{1} res{2} /\ valR res{1} < P).
progress. exists (R,p{1},a{1},b{1}). progress. auto.
conseq okll. auto.
conseq mulm_spec. progress. rewrite H4. apply R_prop. 
progress. smt(@Zp @W64xN).
qed.

module MM = {
  proc ith_bit (kk:W64.t Array32.t, ctr:W64.t) : W64.t = {
    var bit:W64.t;
    var c1:W64.t;
    var c2:W64.t;
    var r:W64.t;
    c1 <- (ctr `>>` (W8.of_int 6));
    c2 <- (ctr - (c1 * (W64.of_int 64)));
    r <- kk.[(W64.to_uint c1)]%Array32;
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
have x:  to_uint (ctr{2} `>>` (of_int 6)%W8) = to_uint ctr{2} %/ 64. 
rewrite shr_div_le. auto. smt(@Ring).
rewrite to_uint_eq.
auto.
rewrite to_uintB.  rewrite /(\ule).
rewrite to_uintM_small. rewrite x.  
rewrite W64.to_uint_small. auto.
have  : to_uint ctr{2} %/ 64 * 64 <= to_uint ctr{2}. smt (divz_eqP). 
have  :  0 <= to_uint ctr{2} && to_uint ctr{2} < W64x2N.M.
apply (W64.to_uint_cmp ctr{2}). clear x.
pose x := to_uint ctr{2} %/ 64 * 64.
pose y := to_uint ctr{2}.
smt().
rewrite x.  smt(shr_div_le). 
rewrite to_uintM_small. rewrite x.  
have ->: to_uint ((of_int 64))%W64 = 64.
rewrite W64.to_uint_small.  auto. auto.
have  : to_uint ctr{2} %/ 64 * 64 <= to_uint ctr{2}. smt (divz_eqP). 
have  :  0 <= to_uint ctr{2} && to_uint ctr{2} < W64x2N.M.
apply (W64.to_uint_cmp ctr{2}). clear x.
pose x := to_uint ctr{2} %/ 64 * 64.
pose y := to_uint ctr{2}.
smt().
rewrite  shr_div_le.
auto. simplify. 
smt (@W64 @IntDiv).
sim.
qed.



lemma mkseqS' ['a]:
  forall (f : int -> 'a) (n : int),
    0 < n => mkseq f n = rcons (mkseq f (n - 1)) (f (n - 1)).
smt(mkseqS).
qed.

lemma ith_bit_lemma' :
      equiv[ M.ith_bit ~ Spec.ith_bit : arg{1}.`1 = arg{2}.`1 /\  W64.to_uint arg{1}.`2 = arg{2}.`2 /\
 0 <= ctr{2} && ctr{2} < 64*nlimbs ==>
              ={res} /\ (res{2} = W64.one \/ res{2} = W64.zero)].
transitivity MM.ith_bit
   (={arg} ==> ={res})
   (arg{1}.`1 = arg{2}.`1 /\  W64.to_uint arg{1}.`2 = arg{2}.`2 /\
 0 <= ctr{2} && ctr{2} < 64*nlimbs ==>
              ={res} /\ (res{2} = W64.one \/ res{2} = W64.zero)).
progress. smt(). smt().
symmetry. conseq ith_bit_lemmaEq. auto. auto.
proc.
seq 3 0 : (to_uint c1{1} = (to_uint ctr{1} %/ 64) /\ to_uint c2{1} = (to_uint ctr{1} %% 64) /\ to_uint ctr{1} = ctr{2}
  /\ r{1} = kk{1}.[(to_uint ctr{1} %/ 64)]%Array32 /\ r{2} = kk{1} /\ 0 <= ctr{2} && ctr{2} < 64*nlimbs ).
wp.  skip. progress.
rewrite shr_div_le. auto. smt(@Ring).
rewrite modzE.
have <-: to_uint (ctr{1} `>>` (of_int 6)%W8) = to_uint ctr{1} %/ 64. rewrite shr_div_le. auto. smt(@Ring).
rewrite to_uintB. rewrite /(\ule).
            rewrite to_uintM_small.
have x:  to_uint (ctr{1} `>>` (of_int 6)%W8) = to_uint ctr{1} %/ 64.
rewrite shr_div_le. auto. smt(@Ring).
rewrite W64.to_uint_small. auto.
have  : to_uint ctr{1} %/ 64 * 64 <= to_uint ctr{1}. smt (divz_eqP).
have  :  0 <= to_uint ctr{1} && to_uint ctr{1} < W64x2N.M.
apply (W64.to_uint_cmp ctr{1}).
pose xx := to_uint ctr{1} %/ 64 * 64.
pose yy := to_uint ctr{1}.
smt().
rewrite W64.to_uint_small. auto.
have ->:  to_uint (ctr{1} `>>` (of_int 6)%W8) = to_uint ctr{1} %/ 64.
rewrite shr_div_le. auto. smt(@Ring).
smt (divz_eqP).
rewrite shr_div_le.  auto.
rewrite W64.to_uintM.
rewrite W64.to_uint_small. auto.
rewrite shr_div_le.  auto. smt(@W64).
rewrite shr_div_le. auto. smt(@Ring).
exists* r{1}, c2{1}. elim*. progress.
call {1} (ithbit64 r_L c2_L). skip.
progress. smt(). smt().
rewrite /ith_bitword64.  rewrite H0.
rewrite /ith_bitR. rewrite /Rbits. rewrite /valR.
rewrite /ith_bit.
rewrite /as_word.
rewrite /as_w64.
have ->: (kk{1}.[to_uint ctr{1} %/ 64])%Array32.[to_uint ctr{1} %% 64]
  = nth false (int2bs (64 * nlimbs) ((valR kk{1}))%W64xN) (to_uint ctr{1}) .
rewrite - get_w2bits.
rewrite - get_to_list.
have -> : (W64.w2bits (nth witness ((to_list kk{1}))%Array32 (to_uint ctr{1} %/ 64)))
 = ((nth witness (map W64.w2bits (to_list kk{1}))%Array32 (to_uint ctr{1} %/ 64))).
rewrite - (nth_map witness witness W64.w2bits). progress.   smt(). smt(@W64xN).
auto.
have -> : (nth witness (map W64.w2bits ((to_list kk{1}))%Array32)
     (to_uint ctr{1} %/ 64))
 = (nth [] (map W64.w2bits ((to_list kk{1}))%Array32)
     (to_uint ctr{1} %/ 64)).
rewrite (nth_change_dfl [] witness). progress.  smt(). smt(@W64xN @List). auto.
rewrite - (BitChunking.nth_flatten false 64 (map W64.w2bits ((to_list kk{1}))%Array32) (to_uint ctr{1})).
rewrite  List.allP. progress.
have : exists z, z \in ((to_list kk{1}))%Array32 /\ x = W64.w2bits z.
apply mapP. auto. elim. progress.
have ->: (flatten (map W64.w2bits ((to_list kk{1}))%Array32))  = (int2bs (64*nlimbs) ((valR kk{1}))%W64xN).
have -> : (valR kk{1})%W64xN = bs2int (flatten (map W64.w2bits ((to_list kk{1}))%Array32)).
rewrite /bnk.
do? (rewrite range_ltn; first by trivial).
simplify. rewrite range_geq. auto. auto.
do? rewrite big_consT.
rewrite big_nil.
rewrite /to_list.
do? (rewrite mkseqS'; first by trivial).
rewrite mkseq0. simplify.
do? rewrite flatten_cons.
rewrite flatten_nil.
rewrite cats0.
do? rewrite bs2int_cat.
simplify.
have ->:  18446744073709551616 ^ 0 = 1. smt(@Ring).
simplify.
smt(@Ring).
have ->: 64*nlimbs = size (flatten (map W64.w2bits ((to_list kk{1}))%Array32)).
rewrite /to_list.
do? (rewrite mkseqS'; first by trivial).
rewrite mkseq0. simplify.
do? rewrite flatten_cons.
rewrite flatten_nil.
do? rewrite size_cat.
simplify. auto.
rewrite  bs2intK. auto. auto.
auto. smt().
qed.


lemma expm_real_spec : 
      equiv[ Exp.M1.iterop_spec ~ Exp.M7(MultM).iterop :
            ImplZZ m{2} P /\
            ={x} /\
            bs2int n{1} = valR n{2} /\ size n{1} = 64*nlimbs /\ valR x{1} < P ==>
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
  (arg{1}.`1 = arg{2}.`1 /\ ImplWord ctr{1} ctr{2} /\ 0 <= ctr{2} && ctr{2} < 64*nlimbs ==>
          ={res} /\ (res{2} = W64.one \/ res{2} = W64.zero)).
smt(). smt().
proc. sim.
conseq ith_bit_lemma'.
conseq okl. smt(). auto. auto.
qed.


lemma to_uintP: forall (x y : R), valR (x *** y) = (valR x * valR y) %% P.
progress. rewrite /( *** ). simplify. 
rewrite valr_ofint. split. apply modz_ge0. smt(P_pos).
smt(ltz_pmod P_pos). auto.
qed.


lemma kk :  forall (n : int), 0 <= n => forall (a : zp) (b : t), valR%W64xN b < P =>
  ImplFp b a =>
  ImplFp ((^) b n) (inzp (asint a ^ n)).
apply intind. progress.
rewrite exp_prop1.
have -> : (asint a ^ 0) = 1. smt(@Ring).
rewrite /asint.
have -> : (Sub.val (inzp 1))%Sub = 1. smt(@Zp).
rewrite valr_ofint. split. auto. smt(P_pos). auto.
progress.
have ->: ((^) b (i + 1)) = b *** ((^) b  i).
rewrite exp_prop3. auto. auto.  auto.
rewrite exp_prop2.
rewrite exp_prop7. simplify. auto. 
have ->: inzp (asint a ^ (i + 1)) =  inzp (asint a * (asint a ^ i)).
smt(@Ring).
have ->:  inzp (asint a * (asint a ^ i)) = (inzp (asint a)) * (inzp (asint a ^ i)).
smt(@Zp).
rewrite - H2. 
have ->: asint (inzp (valR%W64xN b) * inzp (valR%W64xN b ^ i))
  = (asint (inzp (valR%W64xN b)) * (asint  (inzp (valR%W64xN b ^ i)))) %% P.
simplify. smt(@Zp).
have ih :  ImplFp (b ^ i)  (inzp (valR%W64xN b ^ i)).
simplify. smt(@Zp).
rewrite - ih.
have ->: asint (inzp (valR%W64xN b)) = valR%W64xN b. simplify. smt(@Zp).
simplify. 
rewrite  to_uintP /=. done.
qed.


lemma left_end :
 equiv[ ASpecFp.expm ~ Exp.M1.iterop_spec  :
    ImplFp x{2} a{1} /\  bs2int n{2}  =  b{1} /\ valR%W64xN x{2} < P ==> ImplFp res{2} res{1}]. 
proc.
wp.  skip.  progress.
rewrite  (kk (bs2int n{2}) _ a{1}). smt(@BS2Int). auto. auto. smt(@Zp).
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
call {2} bn_set1_correct. wp. skip. progress. rewrite - H.
rewrite  bnK. auto.
rewrite - H0. rewrite  bnK. auto.
while (={x1,x2,x3,x4,d,ctr,n,m} /\ r{2} = R). wp.
call (_:true). sim. wp.
call (_:true). sim. wp.
call okll.
call okll.
call (_:true). sim. wp.
call (_:true). sim. wp. 
call (_:true). sim. wp. 
skip. progress.
smt(@W64).
skip.
progress. 
qed.


lemma expm_correct : 
      equiv[ ASpecFp.expm ~ M.expm :
             ImplZZ m{2} P /\
             asint a{1} = valR x{2} /\
             b{1} = valR n{2}  /\ 
             valR x{2} < P /\ 
             r{2} = R
             ==> asint res{1} = valR{2}%W64xN res{2}]. 
simplify.
transitivity Exp.M1.iterop_spec
  (ImplFp x{2} a{1} /\  bs2int n{2} = b{1} /\ size n{2} = 64 * nlimbs  /\ valR%W64xN x{2} < P ==> ImplFp res{2} res{1})
  (ImplZZ m{2} P /\
             x{1} =  x{2} /\
            bs2int n{1} = valR n{2} /\ size n{1} = 64 * nlimbs /\ valR x{2} < P /\ r{2} = R ==>
            res{1} =  res{2}).
progress.
exists (x{2}, int2bs (64*nlimbs) (b{1})).
progress. smt().
rewrite int2bsK. auto. split.  smt(@W64xN). 
have ->: 2^ (64*nlimbs) =  W64x2N.M ^ nlimbs . smt(@Ring).
  
have qq:  0 <= b{1} &&  b{1} < W64x2N.M ^ nlimbs.  rewrite H1. apply bnk_cmp.
elim qq. auto.
auto.
smt(@BS2Int). rewrite - H1.
rewrite int2bsK.  auto. split. smt(@W64xN).
have ->: 2^ (64*nlimbs) =  W64x2N.M ^ nlimbs . smt(@Ring). 
have qq:  0 <= b{1} && b{1} < W64x2N.M ^ nlimbs. rewrite H1. apply bnk_cmp.
elim qq. auto.   auto.
smt(@BS2Int).
smt().
conseq left_end.  smt().
symmetry.
transitivity M7(MultM).iterop
 (r{1} = R /\ ={m,x,n}  ==> ={res})
 (p{2} = P /\ size n{2} = 64*nlimbs /\
             x{1} =  x{2} /\
                         ImplZZ m{1} P /\
             valR n{1} = bs2int  n{2}  /\ valR x{2} < P  ==>
            res{1} =  res{2}).
progress.
exists (m{1}, x{1}, n{1}). progress. smt(). smt(@BS2Int).
smt(). auto.
symmetry.
conseq right_end. smt().
progress.
symmetry.
conseq expm_real_spec. progress.
smt().
smt().
progress.
qed.

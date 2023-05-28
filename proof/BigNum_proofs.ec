require import AllCore IntDiv CoreMap List RealExp.
import StdBigop Bigint BIA.

from Jasmin require import JModel.

require import W64_SchnorrExtract.

require import BigNum_spec AuxLemmas.
import W64xN R.

require import BitEncoding.
import BS2Int.

module M = M(Syscall).

equiv addc_spec:
 M.bn_addc ~ ASpecFp.addn:
  ImplZZ a{1} a{2} /\ ImplZZ b{1} b{2}
  ==> res{1}.`1=res{2}.`1 /\ ImplZZ res{1}.`2 res{2}.`2.
proof.
transitivity 
 R.Ops.addcR
 ( ={a,b} /\ !c{2} ==> ={res} )
 ( ImplZZ a{1} a{2} /\ ImplZZ b{1} b{2} /\ !c{1}
   ==> res{1}.`1 = res{2}.`1 /\ ImplZZ res{1}.`2 res{2}.`2 ).
+ by move=> /> &1 &2 H1 H2; exists (a{1},b{1},false).
+ by move=> /> *.
+ proc; simplify.
  unroll {2} 3; rcondt {2} 3; first by auto.
  exlim a{1}, b{1} => aa bb.
  while (={i,b} /\ 1 <= i{2} <= nlimbs /\
         (cf,aa){1}=(c,a){2} /\
         (forall k, 0 <= k < i{2} => a{1}.[k] = r{2}.[k])%A /\
         (forall k, i{2} <= k < nlimbs => a{1}.[k] = aa.[k])%A).
   wp; skip => /> &1 &2 Hi1 Hi2 H1 H2 Hi.
   split => *; first smt().
   split => *; first smt().
   split.
    move=> k Hk1 Hk2.
    pose X := (addc _ _ _)%W64.
    pose Y := (addc _ _ _)%W64.
    have ->: X=Y by smt().
    case: (k = i{2}) => ?.  smt(@A). smt(@A).
    (*  by rewrite !set_eqiE /#. *)
    (* by rewrite !set_neqiE /#. *)
   move=> k Hk1 Hk2. smt(@A).
   (* by rewrite A.set_neqiE /#. *)
  wp; skip => /> &2.
  move=> Hc; split => *.
   split => k *. 
    (* by rewrite (_:k=0) 1:/# !set_eqiE /#. *)
        smt(@A).
        smt(@A).
   (* by rewrite set_neqiE /#. *)
  apply A.ext_eq; smt().
+ proc; simplify.
  transitivity {1}
   { (c,r) <@ R.Ops.addcR(a,b,c); }
   ( ={a,b,c} ==> ={c,r} )
   ( ImplZZ a{1} a{2} /\ ImplZZ b{1} b{2} /\ !c{1} ==> ={c} /\ ImplZZ r{1} r{2} ).
  + by move=> /> &2 H; exists a{2} b{2} false.
  + by auto.
  + by inline*; sim.
  + ecall {1} (R.addcR_ph a{1} b{1} c{1}); wp; skip => /> &m Hc [c r] /= -> ?.
    by  rewrite bn_carryE 1:/# b2i0 /bn_modulus /=.
qed.


lemma addc_ph x y:
  phoare[ M.bn_addc :  arg = (x, y)  ==> (valR res.`2) = (valR x + valR y) %% W64xN.modulusR ] = 1%r.
bypr. progress.
 have <- : Pr[ASpecFp.addn(valR a{m}, valR b{m} ) @ &m : (valR a{m} + valR b{m}) %% W64xN.modulusR = res.`2] = 1%r. 
  byphoare (_: arg = (valR a{m}, valR b{m}) ==> _).
proc. wp. skip. progress. auto. auto.
byequiv. conseq addc_spec.  
progress.  smt(). auto. auto.
qed.

lemma bn_cmov_correct x y z :
  phoare[ M.bn_cmov :  arg = (x,y,z)  ==> res = if x then z else y ] = 1%r.
proc.
while (cond = x /\ b = z /\ i <= nlimbs 
  /\ (forall j, 0 <= j < i => a.[j]%A = if cond then z.[j] else y.[j])%A
  /\ (forall j, i <= j < nlimbs => a.[j] = y.[j]) )%A (nlimbs - i). progress.
wp.  skip.  progress. smt().   smt(@A). smt(@A). smt(). wp.  skip. progress. smt(@A). smt().
apply A.ext_eq. progress. smt(@A). 
qed.


lemma bn_eq_correct x1 x2 :
  phoare[ M.bn_eq :  arg = (x1,x2) ==> (res = W64.one) = (valR x1 = valR x2)  /\ (res = W64.zero \/ res = W64.one) ] = 1%r.
proc. sp. inline M.sn_cmov.  wp.
while (i <= nlimbs /\ ((result = W64.zero) <=> (forall j, 0 <= j < i => a.[j] = b.[j])%A)) (nlimbs - i). progress.
wp.  skip.  progress. smt(). smt(@W64xN).
smt(@W64xN).
smt().
skip. 
progress.
smt().
smt().
case (result0 = W64.zero). simplify.
move => c1.
rewrite (A.ext_eq a{hr} b{hr} ). 
have qq : i0 = nlimbs. smt().
rewrite - qq.
smt(). auto.
elim H1. move => H11 H12.
simplify.
have ->: (W64.zero = W64.one) = false. smt(@W64).
smt(@A @W64xN).
smt().
qed.


lemma bn_copy_correct x :
  phoare[ M.bn_copy :  arg = x  ==> res = x ] = 1%r.
proc.
while (a = x /\ i <= nlimbs 
  /\ (forall j, 0 <= j < i => r.[j] = x.[j])%A
  ) (nlimbs - i). progress.
wp.  skip.  progress. smt(). smt(@A). smt(). wp.  skip. progress. smt(). smt().
apply A.ext_eq. progress. smt(). 
qed.


equiv subc_spec:
 M.bn_subc ~ ASpecFp.subn:
  W64xN.valR a{1} = a{2} /\ W64xN.valR b{1} = b{2} (* /\ W64xN.valR b{1}  <= W64xN.valR a{1} *)
  ==> res{1}.`1=res{2}.`1 /\ W64xN.valR res{1}.`2 = res{2}.`2.
proof.
transitivity 
 W64xN.R.Ops.subcR
 ( (a,b,false){1}=(a,b,c){2} ==> ={res} )
 (W64xN.valR  a{1} = a{2} /\ W64xN.valR b{1} = b{2} /\ !c{1} (* /\ W64xN.valR b{1}  <= W64xN.valR a{1} *)
   ==> res{1}.`1 = res{2}.`1 /\ W64xN.valR res{1}.`2 = res{2}.`2 ).
+ by move=> /> &1 &2 H1 H2 ; exists (a{1},b{1},false).
+ by move=> /> *.
+ proc; simplify.
  unroll {2} 3; rcondt {2} 3; first by auto.
  exlim a{1}, b{1} => aa bb.
  while (={i,b} /\ 1 <= i{2} <= dnlimbs /\ 
         (cf, aa){1}=(c, a){2} /\
         (forall k, 0 <= k < i{2} => a{1}.[k] = r{2}.[k])%A /\
         (forall k, i{2} <= k < dnlimbs => a{1}.[k] = aa.[k])%A).
   wp; skip => /> &1 &2 Hi1 _ Hh1 Hh2 Hi2.
   split => *; first smt().
   split => *; first smt().
   split.
    move=> k Hk1 Hk2.
    pose X := (subc _ _ _)%W64.
    pose Y := (subc _ _ _)%W64.
    have ->: X=Y by smt().
    case: (k = i{2}) => ?. smt(@A). smt(@A).
    (*  by rewrite !A.set_eqiE /#. *)
    (* by rewrite !set_neqiE /#. *)
   move=> k Hk1 Hk2.
   (* by rewrite set_neqiE /#. *) smt(@A).
  wp; skip => />.
  split => *.
   split => k *.
    (* by rewrite (_:k=0) 1:/# !set_eqiE /#. *) smt(@A).
   (* by rewrite set_neqiE /#. *) smt(@A).
  by apply A.ext_eq; smt().
+ proc; simplify.
  transitivity {1}
   { (c,r) <@ W64xN.R.Ops.subcR(a,b,c); }
   ( ={a,b,c} ==> ={c,r} )
   ( W64xN.valR a{1} = a{2} /\ W64xN.valR b{1} = b{2} /\ !c{1}  (* /\ W64xN.valR b{1}  <= W64xN.valR a{1} *) ==> ={c} 
   /\ W64xN.valR r{1} = r{2} ).
  + by move=> /> &2 H  ; exists a{2} b{2} false.
  + by auto.
  + by inline*; sim.
  + ecall {1} (W64xN.R.subcR_ph a{1} b{1} c{1}); wp; skip => /> &m Hc [c r] /= -> .
progress. 
    by rewrite W64xN.R.bn_borrowE 1:/# b2i0 /bn_modulus /=.
qed.


equiv cminus_spec:
 M.cminusP ~ ASpecFp.cminus:
 W64xN.valR p{1} = p{2} /\ W64xN.valR x{1} = a{2} /\ 0 <= p{2}  ==> W64xN.valR res{1}  =res{2}.
proof.
transitivity CSpecFp.cminus
 ( W64xN.valR p{1} = p{2} /\ W64xN.valR x{1} = a{2} /\ 0 <= p{2}  ==> W64xN.valR res{1}  = res{2} )
 ( ={a,p} /\ a{2} < W64xN.modulusR /\ 0 <= p{2} ==> ={res} ).
  progress. exists (W64xN.valR x{1}, W64xN.valR  p{1}). progress. smt(@W64xN). smt(@W64xN).
auto.
proc.
(ecall {1} (bn_cmov_correct cf{1} z{1} x{1})).  simplify.
conseq (_:  ( (W64xN.valR (if cf{1} then x{1} else z{1}))%W64xN = r{2} )). progress.
inline ASpecFp.ctseln. wp.   simplify.
seq 2 0 : ((W64xN.valR p{1})%W64x2N = p{2} /\ (W64xN.valR x{1})%W64x2N = a{2} /\ z{1} = x{1} /\ 0 <= p{2}  ).
(ecall {1} (bn_copy_correct x{1})).  wp. skip. progress.
seq 1 1 : (cf{1} = c{2} /\ W64xN.valR z{1} = x{2}
  /\ (W64xN.valR p{1})%W64xN = p{2} /\ (W64xN.valR x{1})%W64xN = a{2}  /\ 0 <= p{2}).
call  subc_spec.  skip. progress.
skip. progress.   smt().
proc. inline*. wp.  skip.  progress.
case (a{2} < p{2} = true). move => q. rewrite q. simplify. auto.
move => q. 
have -> : a{2} < p{2} = false. smt(). simplify.
have : p{2} <= a{2}. smt().
move => qq.
have qqq : a{2} - p{2} < modulusR. smt(@Int).
smt(@Int).
qed.



equiv addm_spec_eq:
 M.bn_addm2 ~ ASpecFp.addm:
    W64xN.valR a{1} = a{2} /\ ImplZZ b{1} b{2} /\  ImplZZ p{1} p{2}
 /\ 0 <= a{2} < p{2} /\ 0 <= b{2} < p{2} /\ 0 <= 2*p{2} < W64xN.modulusR
  ==> ImplZZ res{1} res{2}.
proof.
transitivity CSpecFp.addm
 (ImplZZ a{1} a{2} /\ ImplZZ b{1} b{2} /\ ImplZZ p{1} p{2} /\ 0 <= a{2} < p{2} /\ 0 <= b{2} < p{2} /\ 0 <= 2*p{2} < W64xN.modulusR ==> ImplZZ res{1} res{2} )
 (={a,b,p} /\ 0 <= a{2} < p{2} /\ 0 <= b{2} < p{2} /\ 0 <= 2*p{2} < W64xN.modulusR ==> res{1}=  res{2}).
  progress. smt(). smt().
+ proc; simplify.
  call cminus_spec.
  exists* a{1}. elim*. move => a_L.
  exists* b{1}. elim*. move => b_L.
  call {1} (addc_ph a_L b_L). inline*. wp. skip. progress. smt(@W64xN).  
+ symmetry; conseq addm_eq.  progress. smt(). smt(). smt(). smt(). 
qed.


lemma bn_addm_correct aa bb pp:
  phoare[ M.bn_addm2 : a = aa /\ b = bb /\ p = pp /\ 0 <= valR a < valR p /\ 0 <= valR b < valR p /\ 0 <= 2* (valR p) < W64xN.modulusR  ==> (valR aa + valR bb)%% (valR pp) = valR res ] = 1%r.
proof. bypr. progress.
 have <- : Pr[ASpecFp.addm(valR a{m}, valR b{m}, valR p{m}) @ &m : (valR a{m} + valR b{m}) %% valR p{m} =  res] = 1%r. 
  byphoare (_: arg = (valR a{m}, valR b{m}, valR p{m}) ==> _).
proc. wp. skip. smt(). auto. auto.
byequiv. conseq addm_spec_eq.
smt(). smt(). auto. auto.
qed.




lemma bn_set0_correct :
  phoare[ M.bn_set0 : true  ==> W64xN.valR res = 0 ] = 1%r.
proc.
while (i <= nlimbs
  /\ (forall j, 0 <= j < i => a.[j]%A = W64.zero)) (nlimbs - i). progress.
wp.  skip.  progress. smt().  smt(@A). smt(). wp.  skip. progress. smt(). smt().
rewrite - zeroRE. congr.
apply A.ext_eq. progress.  
rewrite /zeroR. smt(@A @List). 
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
 wp; skip => />; smt(R2.A.get_setE R2.A.set_set_if).
wp; skip => />; smt (R2.A.set_set_if).
qed.


equiv mul1acc_eq :
 M.mul1acc ~ MulOps.mul1acc:
 W64.to_uint k{1} = k{2} /\ ={a,b} /\ (_zero,of_0,cf,r){1}=(W64.zero,_of,_cf,x){2} /\
  0 <= k{2} < nlimbs
 ==>
 (res.`1,res.`2,res.`3,res.`4){1} = (W64.zero,res.`1,res.`2,res.`3){2}.
proof.
proc. simplify.
wp. while ( #pre /\ ={i} /\ (aux,_zero){1}=(nlimbs-1,W64.zero) /\ 
            0 <= i{2} <= nlimbs-1 /\ kk{1} = k{2}).
 wp; skip => />; smt(R2.A.get_setE R2.A.set_set_if).
wp; skip; smt(R2.A.get_setE R2.A.set_set_if).
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
+ proc; simplify. wp.
  while ( #pre /\ (i,_zero,of_0,cf){1}=(k,W64.zero,_of,_cf){2} /\
          1 <= k{2} <= nlimbs /\ bp{1} = b{2} /\ rp{1} = r{2} ).
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



lemma oneRE: ImplZZ oneR 1.
rewrite /oneR /valR /bnk.
do? (rewrite range_ltn; first by trivial ).
simplify. rewrite range_geq. auto.
do rewrite big_consT.
rewrite big_nil.
 have -> : dig ((A.of_list W64.zero (W64.one :: nseq (nlimbs - 1) W64.zero)))%A 0 = 1.
 simplify. smt(@W64 @A).
 have q : forall x, 0 < x < nlimbs => dig ((A.of_list W64.zero (W64.one :: nseq (nlimbs - 1) W64.zero)))%A x = 0.
 move => x xp. rewrite /dig.
   have ->: to_uint ((A.of_list W64.zero (W64.one :: nseq (nlimbs - 1) W64.zero)).[x])%A = 0. 
    do? (rewrite nseqS'; first by trivial). simplify. 
   rewrite nseq0. 
  have -> : (A.of_list W64.zero [W64.one; W64.zero ]).[x]%A = W64.zero.  
smt(A.get_of_list). smt().
smt(@List).  
do? (rewrite q; first smt()). auto.
qed.


lemma bn_set1_correct :
  phoare[ M.bn_set1 : true  ==> W64xN.valR res = 1 ] = 1%r.
proc.
while (0 < i <= nlimbs 
  /\ (forall j, 1 <= j < i => a.[j]%A = W64.zero) /\ a.[0]%A = W64.one) (nlimbs - i). progress.
wp.  skip.  progress. smt(). smt().  smt(@A). smt(@A). smt(). wp.  skip. progress. smt(@A). smt().
rewrite - oneRE. congr.
apply A.ext_eq. progress.  
case (x = 0). progress. progress.
rewrite /A."_.[_]" in H2.
rewrite H2. smt().
rewrite /oneR. smt(@A @List).
qed.



lemma bn_div2_correct z :
  phoare[ M.div2 : arg = (z,dnlimbs)  ==> (W64x2N.valR res) = (W64x2N.valR2 z) %/  W64x2N.modulusR ] = 1%r.
proc. sp.
while (aux = dnlimbs /\ i <= dnlimbs /\ forall j, (0 <= j < i => R2.A."_.[_]" r j =  (W64x2N.R2.A."_.[_]" x (dnlimbs + j)))) (dnlimbs - i). 
progress. wp. skip. progress.
smt(). smt(@R2.A). smt(). skip. progress.
smt(). smt().
have ->:  W64x2N.modulusR  = W64x2N.M^dnlimbs.  rewrite /R.bn_modulus. auto. 
have ->: (W64x2N.R2.bnk (2*dnlimbs) x{hr})%R2 = W64x2N.valR2 x{hr}. auto.
rewrite W64x2N.R2.bn_div_kup.
auto.
rewrite - W64x2N.R.bnkup0.
rewrite /bnkup.
have ->: 
  bigi predT (fun (i1 : int) => to_uint (R2.A."_.[_]" r0 i1)%R2.A * W64x2N.M ^ (i1 - 0)) 0 dnlimbs
  = bigi predT (fun (i1 : int) => to_uint (W64x2N.R2.A."_.[_]" x{hr} (i1 + dnlimbs)) * W64x2N.M ^ (i1 - 0)) 0 dnlimbs.
apply eq_big_int. progress. smt(). 
  have ->: bigi predT (fun (i1 : int) => to_uint (W64x2N.R2.A."_.[_]" x{hr} (i1)) * W64x2N.M ^ (i1 - dnlimbs)) dnlimbs
  (2 * dnlimbs)  = bigi predT (fun (i1 : int) => to_uint (W64x2N.R2.A."_.[_]" x{hr} (i1)) * W64x2N.M ^ (i1 - dnlimbs)) (0 + dnlimbs)
  (2 * dnlimbs). auto.
rewrite big_addn. simplify. auto.
qed.



lemma bn_shrink_correct a  :
  phoare[ M.bn_shrink : arg = a  ==> W64xN.valR res = W64x2N.valR a %% W64xN.modulusR ] = 1%r.
proc.
sp.
while (i <= nlimbs /\ forall j, 0 <= j < i => r.[j]%A = (R2.A."_.[_]" x j)) (nlimbs - i). 
progress. wp. skip. progress.
smt(). smt(@A). smt(). skip. progress.
smt(). smt(). 
rewrite /W64xN.modulusR. auto.
rewrite W64x2N.R.bn_mod. auto. 
rewrite /bnk. 
apply eq_big_seq. progress. rewrite /A."_.[_]" in H1. rewrite H1. split.
smt (mem_range). 
smt (mem_range). 
auto.
qed.


lemma bn_expand_correct : forall a,
      phoare[ M.bn_expand : arg = a  ==> W64x2N.valR res =  W64xN.valR a ] = 1%r.
 have  bn_expand_correct : forall a, 
    hoare[ M.bn_expand : arg = a  ==> W64x2N.valR res = W64xN.valR a ].
   move => a.
   proc.
   sp. 
    seq 1 : (a = x /\ i = nlimbs /\ forall i, i < nlimbs => (W64x2N.R.A."_.[_]" r i) = x.[i]%A).
    while (i <= nlimbs /\ forall j, 0 <= j < i => (W64x2N.R.A."_.[_]" r j) = x.[j]%A). wp.  skip. progress.
    smt(). smt(@A @R2.A). skip. progress.
    smt().  smt(). smt(@R2.A @A). sp.
    seq 2 : (a = x /\  (forall j, 0 <= j < nlimbs => (W64x2N.R.A."_.[_]" r j) = x.[j]%A)
         /\ (forall j, nlimbs <= j < 2*nlimbs => (W64x2N.R.A."_.[_]" r j) = W64.zero)).     
    while (a = x /\ nlimbs <= i <= 2*nlimbs 
         /\ (forall j, 0 <= j < nlimbs => (W64x2N.R.A."_.[_]" r j) = x.[j]%A)
         /\ (forall j, nlimbs <= j < i => (W64x2N.R.A."_.[_]" r j) = W64.zero) /\ aux = 64 ). wp.  skip. progress.
    smt(). smt().
    have z : i{hr} <> j. smt(). 
    rewrite - H1. auto.  smt(@A @R2.A).
    case (j = i{hr}). smt(@A @R2.A).
    progress.
    have : j < i{hr}.  smt().
    progress.
    rewrite - (H2 j).  smt().
    smt(@A @R2.A). wp. 
    skip.  progress.
    smt(@A @R2.A). smt(). smt(). 
    skip.  progress.
    have -> : W64x2N.valR r{hr} = (bn_seq ((R2.A.to_list r{hr}))).
    apply W64x2N.R.bn2seq. 
    rewrite /to_list.
    have -> : dnlimbs = nlimbs + nlimbs. smt().
    rewrite mkseq_add. auto. auto.
    have -> : mkseq (fun (i0 : int) => (W64x2N.R.A."_.[_]" r{hr} i0)) nlimbs 
      = mkseq (fun (i0 : int) => x{hr}.[i0]%A) nlimbs.
    apply eq_in_mkseq. progress. 
    simplify.
    have ->: mkseq (fun (i0 : int) => (W64x2N.R.A."_.[_]" r{hr} (nlimbs + i0))  ) nlimbs
      = mkseq (fun (i0 : int) => W64.zero) nlimbs.
    apply eq_in_mkseq. progress. rewrite H0. smt(). auto.
    have -> : mkseq (fun (_ : int) => W64.zero) nlimbs = nseq nlimbs W64.zero.   
     pose s := (nseq nlimbs W64.zero).
    rewrite (eq_mkseq (fun (x: int) => W64.zero) (nth W64.zero s)). 
   apply fun_ext.    apply fun_ext. progress. move => x. smt.
   have ->: nlimbs = size s. rewrite /s. rewrite size_nseq. smt.
apply mkseq_nth. 
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
have ->: Pr[M.bn_expand(arg{m}) @ &m : W64x2N.valR res <> valR arg{m}] = 0%r.
byphoare (_: arg = arg{m} ==> _). 
hoare. simplify. conseq (bn_expand_correct arg{m}). auto. auto. auto.
qed.


lemma bn_expand_ho : forall a,
      hoare[ M.bn_expand : arg = a  ==> W64x2N.valR res =  W64xN.valR a ].
move => a. bypr. progress.
have q : 1%r = Pr[W64_SchnorrExtract.M(Syscall).bn_expand(arg{m}) @ &m : true]. 
byphoare (_: arg = arg{m} ==> _). proc*. call (bn_expand_correct ( arg{m})). auto. auto. auto.
have z :  Pr[W64_SchnorrExtract.M(Syscall).bn_expand(arg{m}) @ &m : true] = Pr[W64_SchnorrExtract.M(Syscall).bn_expand(arg{m}) @ &m :
   W64x2N.valR res <> valR arg{m}] +  Pr[W64_SchnorrExtract.M(Syscall).bn_expand(arg{m}) @ &m :
   W64x2N.valR res = valR arg{m}].
rewrite Pr[mu_split (W64x2N.valR res <> valR arg{m})]. simplify. auto.
have w :  Pr[W64_SchnorrExtract.M(Syscall).bn_expand(arg{m}) @ &m : W64x2N.valR res = valR arg{m}] = 1%r.
byphoare (_: arg = arg{m} ==> _). conseq (bn_expand_correct ( arg{m})).  auto. auto.
rewrite Pr[mu_split W64x2N.valR res = valR arg{m}]. simplify. 
have ->: Pr[W64_SchnorrExtract.M(Syscall).bn_expand(arg{m}) @ &m :
   W64x2N.valR res <> valR arg{m} /\ W64x2N.valR res <> valR arg{m}] =
Pr[W64_SchnorrExtract.M(Syscall).bn_expand(arg{m}) @ &m :
   W64x2N.valR res <> valR arg{m}]. rewrite Pr[mu_eq]. auto. auto.
have easy_fact1 : Pr[W64_SchnorrExtract.M(Syscall).bn_expand(arg{m}) @ &m :
   W64x2N.valR res <> valR arg{m}] = 0%r. smt(@Distr).
have easy_fact2 : Pr[W64_SchnorrExtract.M(Syscall).bn_expand(arg{m}) @ &m :
   W64x2N.valR res <> valR arg{m} /\ W64x2N.valR res = valR arg{m}]
 <= Pr[W64_SchnorrExtract.M(Syscall).bn_expand(arg{m}) @ &m :
   W64x2N.valR res <> valR arg{m}]. smt(@Distr).
have easy_fact3 : Pr[W64_SchnorrExtract.M(Syscall).bn_expand(arg{m}) @ &m :
   W64x2N.valR res <> valR arg{m} /\ W64x2N.valR res = valR arg{m}] = 0%r. smt(@Distr).
smt().
qed.





(* ith_bit  *)

module IB = {
  proc ith_bit64 (k:W64.t, ctr:W64.t) : W64.t = {    
    var bit:W64.t;
    var p:W64.t;    
    bit <- k;
    p <- ctr;
    p <- (p `&` (W64.of_int 63));
    bit <- (bit `>>` (truncateu8 p));
    bit <- (bit `&` (W64.of_int 1));
    return (bit);
  }  
}.
  
lemma ithbit64 a b :
 phoare[ IB.ith_bit64   : arg = (a,b) /\
     0 <= to_uint ctr < 64 ==> res = ith_bitword64 a (to_uint b) ] = 1%r.
proc. 
wp.  skip. progress.
rewrite /ith_bitword64.
rewrite /as_word.
rewrite /truncateu8.
have -> : (to_uint (ctr{hr} `&` (of_int 63)%W64))
  = (to_uint ctr{hr} %% 2 ^ 6).
rewrite - to_uint_and_mod. auto.
smt. simplify.
have -> : (of_int (to_uint ctr{hr} %% 64))%W8 = (of_int (to_uint ctr{hr}))%W8.
smt.
rewrite /(`>>`).
rewrite /(`>>>`).
rewrite /W64.(`&`).
rewrite /map2.
case (k{hr}.[to_uint ctr{hr}]).
progress.
apply W64.ext_eq.
progress.
rewrite initiE. auto.
simplify.
rewrite initiE. auto.
simplify.
case (x = 0).
progress. smt.
progress.
have -> : W64.one.[x] = false.
apply w64oneP. smt().
auto.
progress.
apply W64.ext_eq.
progress.
rewrite initiE. auto.
simplify.
rewrite initiE. auto.
simplify.
case (x = 0).
progress. smt.
progress.
rewrite w64oneP. smt(). simplify.
auto.
qed.

module MM = {
  proc ith_bit (kk:W64.t A.t, ctr:W64.t) : W64.t = {
    var bit:W64.t;
    var c1:W64.t;
    var c2:W64.t;
    var r:W64.t;
    c1 <- (ctr `>>` (W8.of_int 6));
    c2 <- (ctr - (c1 * (W64.of_int 64)));
    r <- kk.[(W64.to_uint c1)]%A;
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
have  : to_uint ctr{2} %/ 64 * 64 <= to_uint ctr{2}. smt. (* smt (divz_eqP).  *)
have  :  0 <= to_uint ctr{2} && to_uint ctr{2} < W64x2N.M.
apply (W64.to_uint_cmp ctr{2}). clear x.
pose x := to_uint ctr{2} %/ 64 * 64.
pose y := to_uint ctr{2}.
smt().
rewrite x.  smt(shr_div_le). 
rewrite to_uintM_small. rewrite x.  
have ->: to_uint ((of_int 64))%W64 = 64.
rewrite W64.to_uint_small.  auto. auto.
have  : to_uint ctr{2} %/ 64 * 64 <= to_uint ctr{2}. smt. (* smt (divz_eqP).  *)
have  :  0 <= to_uint ctr{2} && to_uint ctr{2} < W64x2N.M.
apply (W64.to_uint_cmp ctr{2}). clear x.
pose x := to_uint ctr{2} %/ 64 * 64.
pose y := to_uint ctr{2}.
smt().
rewrite  shr_div_le.
auto. simplify. 
smt (@W64 @IntDiv).
sim. wp. skip. auto.
qed.

lemma ith_bit_lemma_cspec :
      equiv[ M.ith_bit ~ CSpecFp.ith_bit : arg{1}.`1 = arg{2}.`1 /\  W64.to_uint arg{1}.`2 = arg{2}.`2 /\
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
  /\ r{1} = kk{1}.[(to_uint ctr{1} %/ 64)]%A /\ r{2} = kk{1} /\ 0 <= ctr{2} && ctr{2} < 64*nlimbs ).
wp.  skip. progress.
rewrite shr_div_le. auto. smt(@Ring).
rewrite modzE.
have <-: to_uint (ctr{1} `>>` (of_int 6)%W8) = to_uint ctr{1} %/ 64. rewrite shr_div_le. auto. smt(@Ring).
rewrite to_uintB. rewrite /(\ule).
            rewrite to_uintM_small.
have x:  to_uint (ctr{1} `>>` (of_int 6)%W8) = to_uint ctr{1} %/ 64.
rewrite shr_div_le. auto. smt(@Ring).
rewrite W64.to_uint_small. auto.
have  : to_uint ctr{1} %/ 64 * 64 <= to_uint ctr{1}. (* smt (divz_eqP). *) smt.
have  :  0 <= to_uint ctr{1} && to_uint ctr{1} < W64x2N.M.
apply (W64.to_uint_cmp ctr{1}).
pose xx := to_uint ctr{1} %/ 64 * 64.
pose yy := to_uint ctr{1}.
smt().
rewrite W64.to_uint_small. auto.
have ->:  to_uint (ctr{1} `>>` (of_int 6)%W8) = to_uint ctr{1} %/ 64.
rewrite shr_div_le. auto. smt(@Ring).
smt.
(* smt (divz_eqP). *)
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
have ->: (kk{1}.[to_uint ctr{1} %/ 64])%A.[to_uint ctr{1} %% 64]
  = nth false (BS2Int.int2bs (64 * nlimbs) ((valR kk{1}))%W64xN) (to_uint ctr{1}) .
rewrite - get_w2bits.
rewrite /A."_.[_]".
rewrite - A.get_to_list.
have -> : (W64.w2bits (nth witness ((to_list kk{1}))%A (to_uint ctr{1} %/ 64)))
 = ((nth witness (map W64.w2bits (to_list kk{1}))%A (to_uint ctr{1} %/ 64))).
rewrite - (nth_map witness witness W64.w2bits). progress.   smt(). smt(@W64xN).
auto.
have -> : (nth witness (map W64.w2bits ((to_list kk{1}))%A)
     (to_uint ctr{1} %/ 64))
 = (nth [] (map W64.w2bits ((to_list kk{1}))%A)
     (to_uint ctr{1} %/ 64)).
rewrite (nth_change_dfl [] witness). progress.  smt(). smt(@W64xN @List). auto.
rewrite - (BitChunking.nth_flatten false 64 (map W64.w2bits ((to_list kk{1}))%A) (to_uint ctr{1})).
rewrite  List.allP. progress.
have : exists z, z \in ((to_list kk{1}))%A /\ x = W64.w2bits z.
apply mapP. auto. elim. progress.
have ->: (flatten (map W64.w2bits ((to_list kk{1}))%A))  = (int2bs (64*nlimbs) ((valR kk{1}))%W64xN).
have -> : (valR kk{1})%W64xN = bs2int (flatten (map W64.w2bits ((to_list kk{1}))%A)).
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
(* have ->:  18446744073709551616 ^ 0 = 1. smt(@Ring). *)
(* simplify. *)
smt(@Ring).
have ->: 64*nlimbs = size (flatten (map W64.w2bits ((to_list kk{1}))%A)).
rewrite /to_list.
do? (rewrite mkseqS'; first by trivial).
rewrite mkseq0. simplify.
do? rewrite flatten_cons.
rewrite flatten_nil.
do? rewrite size_cat.
simplify. auto.
rewrite  bs2intK. auto. auto.
smt().
auto. smt().
qed.


lemma swap_lemma_cspec :
      equiv[ M.swapr ~ CSpecFp.swapr :
              a{2} = x{1} /\ b{2} = y{1} /\ swap_0{1} = as_w64 c{2} ==> ={res}].
proc.  simplify.
seq 2 0 : (i{1} = 0 /\ a{2} = x{1} /\ b{2} = y{1} /\ swap_0{1} = as_w64 c{2} /\ 
   ((as_bool swap_0{1} => mask{1} = (of_int 18446744073709551615)%W64 )
              /\ (as_bool swap_0{1} = false => mask{1} = (of_int 0)%W64))).
wp. skip. progress. smt(@W64). smt(@W64).
while {1} (0 <= i{1} /\ ((as_bool swap_0{1} => mask{1} = (of_int 18446744073709551615)%W64 )
              /\ (as_bool swap_0{1} = false => mask{1} = (of_int 0)%W64)) 
   /\ (forall j, 0 <= j < i{1} => (x{1}.[j])%A = (if as_bool swap_0{1} then (b{2}.[j]) else (a{2}.[j]))%A )  
   /\ (forall j, 0 <= j < i{1} => (y{1}.[j])%A = (if as_bool swap_0{1} then (a{2}.[j]) else (b{2}.[j]))%A )  
   /\ (forall j, i{1} <= j => (x{1}.[j])%A =  (a{2}.[j]))%A
   /\ (forall j, i{1} <= j => (y{1}.[j])%A =  (b{2}.[j]))%A
 ) (nlimbs - i{1} + 1).
progress. wp.  skip.  progress.   smt().
case (j <  i{hr}). progress. smt(@A).
progress.
have : j = i{hr}. smt().
progress.
rewrite - /A."_.[_]".
rewrite - /A."_.[_<-_]".
have ->: (x{hr}.[i{hr} <-
    x{hr}.[i{hr}] `^` (x{hr}.[i{hr}] `^` y{hr}.[i{hr}] `&` mask{hr})].[i{hr}])%A
 = (x{hr}.[i{hr}] `^` (x{hr}.[i{hr}] `^` y{hr}.[i{hr}] `&` mask{hr}))%A. smt(@A).
case (as_bool swap_0{hr}). progress.
rewrite H4. auto.  rewrite H0. auto. rewrite H5. auto. rewrite - ones64. 
have -> : ((a{m}.[i{hr}])%A `^` (b{m}.[i{hr}])%A `&`
 (of_int W64.max_uint)%W64) = a{m}.[i{hr}]%A `^` ((b{m}.[i{hr}])%A `&`
 (of_int W64.max_uint)%W64).
pose x := a{m}.[i{hr}]%A.
pose y := b{m}.[i{hr}]%A.
pose z := (of_int W64.max_uint)%W64.
rewrite andwDl.
have ->: (x `&` z) = x. smt (W64.andw1_s).
auto.
have ->: ((b{m}.[i{hr}])%A `&` (of_int W64.max_uint)%W64) = ((b{m}.[i{hr}])%A). 
pose y := b{m}.[i{hr}]%A.
pose z := (of_int W64.max_uint)%W64.
smt (W64.andw1_s).
smt(@W64).
progress. rewrite H4. auto.  rewrite H1. smt(). auto. 
case (j <  i{hr}). progress. smt(@A).
progress.
have : j = i{hr}. smt().
progress.
rewrite - /A."_.[_]".
rewrite - /A."_.[_<-_]".
have ->: (y{hr}.[i{hr} <-
   y{hr}.[i{hr}] `^` (x{hr}.[i{hr}] `^` y{hr}.[i{hr}] `&` mask{hr})].[i{hr}])%A
 = (y{hr}.[i{hr}] `^` (x{hr}.[i{hr}] `^` y{hr}.[i{hr}] `&` mask{hr}))%A. smt(@A).
case (as_bool swap_0{hr}). progress.
rewrite H4. auto.  rewrite H0. auto. rewrite H5. auto. rewrite - ones64. 
have -> : ((a{m}.[i{hr}])%A `^` (b{m}.[i{hr}])%A `&`
 (of_int W64.max_uint)%W64) = a{m}.[i{hr}]%A `^` ((b{m}.[i{hr}])%A `&`
 (of_int W64.max_uint)%W64). 
pose x := a{m}.[i{hr}]%A.
pose y := b{m}.[i{hr}]%A.
pose z := (of_int W64.max_uint)%W64.
rewrite andwDl.
have ->: (x `&` z) = x. smt (W64.andw1_s).
auto.
have ->: ((b{m}.[i{hr}])%A `&` (of_int W64.max_uint)%W64) = ((b{m}.[i{hr}])%A).
pose y := b{m}.[i{hr}]%A.
pose z := (of_int W64.max_uint)%W64.
smt (W64.andw1_s).
smt(@W64).
progress. rewrite H4. auto.  rewrite H1. smt(). smt(@W64).
smt(@A). smt(@A). smt().
skip. progress. smt().   smt().   smt(). 
case (c{2} = false). progress.  
apply A.ext_eq.  progress. 
rewrite - /A."_.[_]".
rewrite H5. progress. smt(). rewrite /as_bool. rewrite /as_w64. simplify. smt(@W64).
apply A.ext_eq.  progress. rewrite - /A."_.[_]". rewrite H6. progress. smt(). rewrite /as_bool. rewrite /as_w64. simplify. smt(@W64).
progress. have ->: c{2} = true. smt(). simplify.
progress. 
apply A.ext_eq.  progress. rewrite - /A."_.[_]". rewrite H5. progress. smt(). rewrite /as_bool. rewrite /as_w64. simplify. smt(@W64).
apply A.ext_eq.  progress. rewrite - /A."_.[_]". rewrite H6. progress. smt(). rewrite /as_bool. rewrite /as_w64. simplify. smt(@W64).
qed.


lemma swap_lemma_ph xx yy ss :
      phoare [ M.swapr : arg = (xx,yy,as_w64 ss) ==> res = if ss then (yy, xx) else (xx, yy)  ] = 1%r.
bypr.
progress.
have ->: 1%r = Pr[ CSpecFp.swapr(x{m},y{m},as_bool swap_0{m}) @&m : res =  if ss then (yy, xx) else (xx, yy)  ].
byphoare (_: arg = (x{m},y{m},as_bool swap_0{m}) ==> _). proc.
skip.  progress. smt. smt(). auto.
byequiv. conseq swap_lemma_cspec.  smt(). smt(). auto. auto.
qed.


module AddM = {
  proc addm(x : int,y:int,z:int) = {
    return (x + y) %% z;
  }
}.

require import DoubleBigNum_proofs.
lemma bn_addm_equiv aaa bbb ppp:
  equiv[ M.bn_addm ~ AddM.addm:
    a{1} = aaa /\ b{1} = bbb /\ p{1} = ppp 
    /\ x{2} = valR aaa /\ y{2} = valR bbb /\ z{2} = valR ppp
    /\ 0 <= valR a{1} < valR p{1}
    /\ 0 <= valR b{1} < valR p{1}
    (* /\ 0 <= 2* (valR p{1}) < W64x2N.modulusR  *)
    ==>  valR res{1} = res{2} ].
proc. wp. sp.
seq 1 0 : (  a{1} = aaa /\
  b{1} = bbb /\
  p{1} = ppp /\
  (0 <= valR a{1} && valR a{1} < valR p{1}) /\
  (0 <= valR b{1} && valR b{1} < valR p{1}) /\
  x{2} = valR aaa /\ y{2} = valR bbb /\ z{2} = valR ppp /\
  W64x2N.valR aa{1} = W64xN.valR a{1}). 
call {1} (bn_expand_correct aaa). skip. progress.   
seq 1 0 : (#pre /\ W64x2N.valR bb{1} = W64xN.valR b{1}). 
call {1} (bn_expand_correct bbb). skip. progress. 
seq 1 0 : (#pre /\ W64x2N.valR pp{1} = W64xN.valR p{1}). 
call {1} (bn_expand_correct ppp). skip. progress. 
seq 1 0 : (#pre /\ W64x2N.valR cc{1} = (W64x2N.valR aa{1} + W64x2N.valR bb{1})  %% W64x2N.valR pp{1}).
exists* pp{1}. elim*. move => pp_.
exists* aa{1}. elim*. move => aa_.
exists* bb{1}. elim*. move => bb_.
call {1} (dbn_addm_correct aa_ bb_ pp_). skip. progress. 
smt(@W64x2N). rewrite H3 H5. assumption.
smt(@W64x2N). rewrite H4 H5. assumption.
smt(@W64x2N). 
rewrite H5. 
 have fact1 : valR p{1} < W64xN.modulusR. smt(@W64xN).
 have fact2 : 2 * W64xN.modulusR <  W64x2N.modulusR. 
 rewrite /W64xN.modulusR.
 rewrite /W64x2N.modulusR.
 have ->: dnlimbs = 2 * nlimbs. auto.
 smt.
smt().
smt().
exists* cc{1}. elim*. move => cc_.
call {1} (bn_shrink_correct cc_). skip. progress. rewrite H7 H6 H3 H4 H5. 
pose w := (valR a{1} + valR b{1}) %% valR p{1}. smt(@IntDiv @W64xN).
qed.

lemma bn_addm_ph aaa bbb ppp:
  phoare[ M.bn_addm : a = aaa /\ b = bbb /\ p = ppp /\ 0 <= valR a < valR p /\ 0 <= valR b < valR p 
        ==> (valR aaa + valR bbb)%% (valR ppp) = valR res ] = 1%r .
bypr. progress.
have ->: 1%r = Pr[ AddM.addm(valR a{m}, valR b{m}, valR p{m}) @ &m : (valR a{m} + valR b{m}) %% valR p{m} = res ].
byphoare (_: arg = (valR a{m}, valR b{m}, valR p{m}) ==> _).
proc. skip. auto. auto. auto.
byequiv. conseq (bn_addm_equiv a{m} b{m} p{m}).
progress. progress. auto. auto.
qed.

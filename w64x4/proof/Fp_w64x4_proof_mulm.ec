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


equiv muln_spec:
 M.bn_muln ~ ASpecFp.muln:
  ImplZZ a{1} a{2} /\ ImplZZ b{1} b{2}
  ==> 
  ImplZZ2 res{1}.`4 res{2}
     /\ res{1}.`1 = W64.zero /\ !res{1}.`2 /\ !res{1}.`3.
proof.
transitivity 
 MulOps.mulR
 ( ={a,b} ==> res{1}.`2=res{2}.`1 /\ res{1}.`3=res{2}.`2 /\ res{1}.`4=res{2}.`3 /\  res{1}.`1 = W64.zero )
 ( ImplZZ a{1} a{2} /\ ImplZZ b{1} b{2} 
   ==> !res{1}.`1 /\ !res{1}.`2 /\ ImplZZ2 res{1}.`3 res{2}).
+ by move=> /> &1 &2 H1 H2; exists (a{1},b{1}).
+ by move=> /> /#.
+ proc; simplify.
  while ( #pre /\ (i,_zero,of_0,cf,r){1}=(k,W64.zero,_of,_cf,r){2} /\
          1 <= k{2} <= nlimbs ).
  wp. call mul1acc_eq. wp. skip. smt.
   (* by wp; call mul1acc_eq; wp; skip => /> /#. *)
  by wp; call mul1first_eq; wp; skip => /> /#.
+ proc.
  transitivity {1}
    { (_of,_cf,r) <@ MulOps.mulR(a,b); }
    ( ={a,b} ==> ={_cf,_of,r} )
    ( ImplZZ a{1} a{2} /\ ImplZZ b{1} b{2} ==> !_cf{1} /\ !_of{1} /\ ImplZZ2 r{1} r{2} ).
  + by move=> /> &1; exists a{1} b{1}; auto.
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
  wp. call dmul1acc_eq. wp. skip. smt.
   (* by wp; call dmul1acc_eq; wp; skip => /> /#;smt. *)
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
wp.  skip.  progress. smt.   smt. smt. smt. wp.  skip. progress. smt. smt.
apply Array8.ext_eq. progress. smt. 
qed.


lemma dbn_set0_correct :
  phoare[ M.bn_set0 : true  ==> W64x4.valR res = 0 ] = 1%r.
proc.
while (i <= nlimbs 
  /\ (forall j, 0 <= j < i => a.[j]%Array4 = W64.zero)) (nlimbs - i). progress.
wp.  skip.  progress. smt().  smt(@Array4). smt(). wp.  skip. progress. smt(). smt().
rewrite - zeroRE. congr.
apply Array4.ext_eq. progress.  rewrite H1. smt(). 
rewrite /zeroR. smt(@Array4).
qed.


lemma dbn_copy_correct x :
  phoare[ M.dbn_copy :  arg = x  ==> res = x ] = 1%r.
proc.
while (a = x /\ i <= dnlimbs 
  /\ (forall j, 0 <= j < i => r.[j] = x.[j])
  ) (dnlimbs - i). progress.
wp.  skip.  progress. smt. smt. smt. wp.  skip. progress. smt. smt.
apply Array8.ext_eq. progress. smt. 
qed.


equiv dcminusP_spec:
 M.dcminusP ~ ASpecFp.cminusP:
 W64x8.valR p{1} = P /\ W64x8.valR x{1} = a{2} ==> W64x8.valR res{1}  =res{2}.
proof.
transitivity CSpecFp.dcminusP
 ( W64x8.valR p{1} = P /\ W64x8.valR x{1} = a{2} ==> W64x8.valR res{1}  = res{2} )
 ( ={a} /\ a{2} < W64x8.modulusR ==> ={res} ).
  progress. exists (W64x8.valR x{1}). progress. smt.
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
smt. smt. smt. skip. progress.
smt. smt.
have ->:  W64x8.modulusR  = W64x8.M^dnlimbs.  rewrite /R.bn_modulus. auto. 
have ->: (R2.bnk (2*dnlimbs) x{hr})%R2 = valR2 x{hr}. auto.
rewrite R2.bghint_div. auto.
rewrite - R.bnkup0.
rewrite /bnkup.
have ->: 
  bigi predT (fun (i1 : int) => to_uint r0.[i1] * W64x8.M ^ (i1 - 0)) 0 dnlimbs
  = bigi predT (fun (i1 : int) => to_uint x{hr}.[i1 + dnlimbs] * W64x8.M ^ (i1 - 0)) 0 dnlimbs.
apply eq_big_int. progress. smt. 
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
smt. smt. smt. skip. progress.
progress. 
smt. smt. 
have ->: W64x4.modulusR = W64x8.M ^ nlimbs. smt.
rewrite W64x8.R.bn_mod. auto. 
rewrite /bnk. 
apply eq_big_seq. progress. rewrite H1. smt. auto.
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
    smt. smt. skip. progress.
    smt.  smt. smt. 
    seq 2 : (a = x /\  (forall j, 0 <= j < nlimbs => r.[j]%Array8 = x.[j]%Array4)
         /\ (forall j, nlimbs <= j < 2*nlimbs => r.[j] = W64.zero)).     
    while (a = x /\ nlimbs <= i <= 2*nlimbs 
         /\ (forall j, 0 <= j < nlimbs => r.[j]%Array8 = x.[j]%Array4)
         /\ (forall j, nlimbs <= j < i => r.[j] = W64.zero) ). wp.  skip. progress.
    smt. smt.
    have z : i{hr} <> j. smt. 
    rewrite - H1. auto.  smt.
    case (j = i{hr}). smt.
    progress.
    have : j < i{hr}. timeout 10. smt.
    progress.
    rewrite - (H2 j).  smt.
    smt. wp. 
    skip.  progress.
    smt. smt. smt. 
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
    apply eq_in_mkseq. progress. rewrite H0. smt. auto.
    rewrite mkseq_nseq. 
    rewrite /bn_seq.
    rewrite foldr_cat.
    have ->: (foldr (fun (w : W64.t) (r0 : int) => to_uint w + W64x8.M * r0) 0
         (nseq nlimbs W64.zero)) = 0.  
       have gen : forall n, 0 <= n => foldr (fun (w : W64.t) (r0 : int) => to_uint w + W64x8.M * r0) 0
                     (nseq n  W64.zero) = 0.
       apply intind. progress. rewrite nseq0. simplify. auto.
       progress. rewrite nseqS. auto. search  foldr. simplify. rewrite H2. auto.
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
ecall {1} (bn_shrink_correct xrf{1}). wp. skip. progress. smt.
seq 1 1 : (valR a{1} = a{2} /\ valR r{1} = r{2} /\ ImplZZ p{1} P /\ k{2} = 64 * nlimbs
    /\ W64x8.valR2 xr{1} = xr{2} /\ valR xrfd{1} = xrf{2} 
    /\  W64x8.valR xrfn{1} = xrfn{2}).
call muln_spec. skip. progress.
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
  /\ valR r{1} = (nlimbs ^ (64 * nlimbs) %/ P) 
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




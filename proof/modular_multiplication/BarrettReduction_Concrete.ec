require import Core Int Ring IntDiv StdOrder List Distr Real RealExp.
import Ring.IntID IntOrder.

require import BarrettRedInt BarrettReduction_Abstract BigNum_spec BigNum_proofs.
require import W64_SchnorrExtract.
require import AuxLemmas.
import W64x2N.
import W64xN.


op ri_uncompute p = (nasty_id ri) p (dnlimbs * nlimbs).
lemma ri_un p : ri_uncompute (valR p)%W64xN = ri (valR p)%W64xN (dnlimbs * nlimbs).
    rewrite /ri_uncompute nasty_id. trivial.
qed.


equiv breduce_cspec:
 M(Syscall).bn_breduce ~ CSpecFp.redm:
     W64x2N.valR a{1} = a{2} 
 /\  W64x2N.valR r{1} = r{2} 
 /\  W64xN.valR p{1} = p{2}
 /\  k{2} = 64 * nlimbs
 /\  0 < p{2}
   ==>  (W64xN.valR res{1}) = res{2}  %% W64xN.modulusR.
proof. proc.
sp.
simplify.
seq 0 0 : (_a{1} = a{1} /\ valR a{1} = a{2} /\ valR r{1} = r{2} /\ ImplZZ p{1} p{2} /\ k{2} = 64 * nlimbs  /\  0 < p{2}). 
skip. auto.
seq 1 1 : (valR a{1} = a{2} /\ valR r{1} = r{2} /\ ImplZZ p{1} p{2} /\ k{2} = 64 * nlimbs /\  0 < p{2}
    /\ W64x2N.valR2 xr{1} = xr{2} (* /\ xr{2} = a{2} * r{2} *)).
call dmuln_spec. skip. progress.
seq 1 1 : (valR a{1} = a{2} /\ valR r{1} = r{2} /\ ImplZZ p{1} p{2} /\ k{2} = 64 * nlimbs /\  0 < p{2}
    /\ W64x2N.valR2 xr{1} = xr{2} /\ W64x2N.valR xrf{1} = xrf{2} ).
ecall {1} (bn_div2_correct xr{1}). inline*. wp.  skip. move => &1 &2 z. split. auto. move => _.
move => r zz. split. smt(). split. smt(). split. smt(). split. smt(). split. smt(). rewrite zz.
have -> : W64x2N.modulusR = 2 ^ (2 * k{2}). smt(@Ring). smt().
seq 1 1 : (valR a{1} = a{2} /\ valR r{1} = r{2} /\ ImplZZ p{1} p{2} /\ k{2} = 64 * nlimbs  /\  0 < p{2}
    /\ W64x2N.valR2 xr{1} = xr{2} /\  W64xN.valR xrfd{1} =  xrf{2}   ).
ecall {1} (bn_shrink_correct xrf{1}). wp. skip. progress. 
seq 2 1 : (valR a{1} = a{2} /\ valR r{1} = r{2} /\ ImplZZ p{1} p{2} /\ k{2} = 64 * nlimbs  /\  0 < p{2}
    /\ W64x2N.valR2 xr{1} = xr{2} /\ valR xrfd{1} = xrf{2} 
    /\  W64x2N.valR xrfn{1} = xrfn{2}).
ecall  (muln_spec xrfd{1} p{1}). wp. skip. progress.
seq 2 1 : (valR a{1} = a{2} /\ valR r{1} = r{2} /\ ImplZZ p{1} p{2} /\ k{2} = 64 * nlimbs  /\  0 < p{2}
    /\ W64x2N.valR2 xr{1} = xr{2} /\ W64xN.valR xrfd{1} = xrf{2} 
    /\ W64x2N.valR xrfn{1} = xrfn{2}
    /\ W64x2N.valR t{1} = t{2}).
call dsubc_spec. wp. skip. progress.
seq 1 0 : (valR a{1} = a{2} /\ valR r{1} = r{2} /\ ImplZZ p{1} p{2} /\ k{2} = 64 * nlimbs /\  0 < p{2}
    /\ W64x2N.valR2 xr{1} = xr{2} /\ W64xN.valR xrfd{1} = xrf{2} 
    /\ W64x2N.valR xrfn{1} = xrfn{2}
    /\ W64x2N.valR t{1} = t{2}
    /\ W64x2N.valR pp{1} = W64xN.valR p{1}).
ecall {1} (bn_expand_correct p{1}). skip. progress.
seq 1 1 : (valR a{1} = a{2} /\ valR r{1} = r{2} /\ ImplZZ p{1} p{2} /\ k{2} = 64 * nlimbs /\  0 < p{2}
    /\ W64x2N.valR2 xr{1} = xr{2} /\ W64xN.valR xrfd{1} = xrf{2} 
    /\ W64x2N.valR xrfn{1} = xrfn{2}
    /\ W64x2N.valR t{1} = t{2}
    /\ W64x2N.valR pp{1} = W64xN.valR p{1}
    /\ W64x2N.valR t{1} = t{2} ).
call dcminusP_spec. skip. progress.
seq 1 0 : (valR a{1} = a{2} /\ valR r{1} = r{2} /\ ImplZZ p{1} p{2} /\ k{2} = 64 * nlimbs /\  0 < p{2}
    /\ W64x2N.valR2 xr{1} = xr{2} /\ W64xN.valR xrfd{1} = xrf{2} 
    /\ W64x2N.valR xrfn{1} = xrfn{2}
    /\ W64x2N.valR t{1} = t{2}
    /\ W64x2N.valR pp{1} = W64xN.valR p{1}
    /\ W64x2N.valR t{1} = t{2}
    /\ W64xN.valR res_0{1} = W64x2N.valR t{1} %% W64xN.modulusR).
ecall {1} (bn_shrink_correct t{1}). skip. progress.
skip.  progress. 
qed.


lemma modulusR_val : 
W64xN.modulusR =  2 ^ (dnlimbs * nlimbs). rewrite /W64xN.modulusR. smt(@Ring).
qed.

equiv bnreduce_spec:
 M(Syscall).bn_breduce ~ ASpecFp.redm:
  valR a{1} = a{2}
  /\ ImplZZ p{1} p{2}
  /\ valR r{1} = ri_uncompute p{2} (* (ri p{2} (64 * nlimbs))   *)
  /\ 0 < p{2} < W64xN.modulusR
  /\ 0 <= a{2} < p{2} * p{2}
  /\ 0 <= valR r{1} ==> valR res{1} = res{2} .
proof. 
  have redm_simp:
 equiv [ ASpecFp.redm ~ ASpecFp.redm: ={arg} /\ 0 < p{2} < W64xN.modulusR  ==> res{1} = res{2} %% W64xN.modulusR ].
 proc. wp.  skip. progress. 
rewrite (pmod_small (a{2} %% p{2})) . split.  apply modz_ge0. 
smt().
move => q.
smt(ltz_pmod).
auto.
symmetry. transitivity ASpecFp.redm
 (={arg} /\ 0 < p{2} && p{2} < W64xN.modulusR ==> res{1} = res{2} %% W64xN.modulusR)
 (valR a{2} = a{1}
  /\ ImplZZ p{2} p{1}
  /\ valR r{2} =  (ri p{1} (64 * nlimbs))  
  /\ 0 < p{1} < W64xN.modulusR
  /\ 0 <= a{1} < p{1} * p{1}
  /\ 0 < p{1} < W64xN.modulusR
  /\ 0 <= valR r{2} ==> valR res{2} = res{1} %% W64xN.modulusR).
smt(ri_un).
auto. conseq redm_simp. 
symmetry.
transitivity CSpecFp.redm
 (W64x2N.valR a{1} = a{2} 
 /\  W64x2N.valR r{1} = r{2} 
 /\  W64xN.valR p{1} = p{2}
 /\  k{2} = 64 * nlimbs 
 /\ 0 < p{2}
   ==>  (W64xN.valR res{1}) = res{2}  %% W64xN.modulusR)
 (={a,p} /\ r{1} = (ri p{2} k{1}) 
  /\ 0 < p{2} < W64xN.modulusR
  /\ 0 <= a{1} < p{2} * p{2}
  /\ 0 < p{2} < 2 ^ k{1} 
  /\ 0 <= k{1} ==> ={res}). 
move => &1 &2 q. 
exists (valR a{1} , valR r{1} , 64 * nlimbs, valR p{1}). split. smt(). 
split. smt(). split. smt().   split.  smt(). 
split. smt(). split. split. smt().  move => ?. 
have ->: (valR a{1}, valR r{1}, 64 * nlimbs).`3 = 64 * nlimbs. smt().
 have ->: 2 ^ (dnlimbs * nlimbs) = W64xN.modulusR. clear q. rewrite /W64xN.modulusR. smt(@Ring).
smt(). smt(). auto.
conseq breduce_cspec.
symmetry. conseq redm_eq. 
smt(). smt(). 
qed.


lemma bnreduce_spec_ph aa pp:
 phoare [ M(Syscall).bn_breduce :  a = aa /\ p = pp
  /\ valR r = ri_uncompute (valR p)
  /\ 0 < valR p < W64xN.modulusR
  /\ 0 <= valR a < valR p * valR p
  /\ 0 < valR p < W64xN.modulusR 
      ==> valR res = valR aa %% valR pp ] = 1%r.
proof. bypr. progress.
 have <- : Pr[ASpecFp.redm(valR a{m}, valR p{m}) @ &m : valR a{m} %% valR p{m} = res] = 1%r. 
  byphoare (_: arg = (valR a{m}, valR p{m}) ==> _).
proc. wp. skip. smt(). auto. auto.
byequiv. conseq bnreduce_spec.  
progress. 
smt(@W64x2N). smt(). auto. auto.
qed.

op [opaque] big_value (n : int) = 4 ^ (64 * nlimbs) %/ n.
lemma bn_bnreduce_correct &m r x n:
 W64x2N.valR r =  big_value (W64xN.valR n)
 => 0 < (W64xN.valR n) 
 => W64x2N.valR x < valR n * valR n
 => Pr[ M(Syscall).bn_breduce(r,x,n) @&m : W64xN.valR res = W64x2N.valR x %% W64xN.valR n ] = 1%r.
proof.  move => eq1 c2 c3.
byphoare (_: arg = (r,x,n) ==> _).
conseq (bnreduce_spec_ph x n).
progress. rewrite eq1. rewrite /big_value. rewrite /ri_uncompute nasty_id /ri. smt().
smt(@W64xN).
smt(@W64x2N).
smt(@W64xN).
auto. auto.
qed.

lemma bnreduce_small_spec_ph aaa ppp:
 phoare [ M(Syscall).bn_breduce_small :  a = aaa /\ p = ppp
  /\ valR r = ri_uncompute (valR p)
  /\ 0 < valR p < W64xN.modulusR
  /\ 0 <= valR a < valR p * valR p
  /\ 0 < valR p < W64xN.modulusR 
      ==> valR res = valR aaa %% valR ppp ] = 1%r.
proc. 
simplify.
seq 3 : (  a = aaa /\
  p = ppp /\
  valR r = (ri_uncompute (valR p)) /\
  (0 < valR p && valR p < W64xN.modulusR) /\
  (0 <= valR a && valR a < valR p * valR p) /\
  0 < valR p && valR p < W64xN.modulusR /\ 
  valR aa = valR a) 1%r.  
call (_:true). 
while (i <= 2*nlimbs /\ aux = 2*nlimbs) .  wp.  skip. smt().
wp. while (i <= 32) .  wp.  skip. smt(). wp. skip. progress. 
wp.  skip. auto.
call (bn_expand_correct aaa).  wp. skip. progress.
exists* aa. elim*. move => aa0.
call (bnreduce_spec_ph aa0 ppp). skip. progress. smt(@W64xN). smt().
smt(). 
hoare. simplify. call (bn_expand_ho aaa). wp.  skip. progress. auto.
qed.

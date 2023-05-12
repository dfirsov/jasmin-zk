require import AllCore IntDiv CoreMap List.
require import BitEncoding.
import BS2Int.
from Jasmin require import JModel. (* only properties of bs2int function *)

require MontgomeryLadder_Abstract.
require import Ring_ops_spec.
require import Ring_ops_proof.
require import W64_SchnorrExtract.

import W64xN.
import Zp.

require import ModularMultiplication_Concrete.
section.

clone import MontgomeryLadder_Abstract as Exp with type R  <- zp,
                                                   op idR <- Zp.one,
                                                   op ( *** ) <-  Zp.( * )
proof*.
realize op_assoc. smt(@Zp). qed.
realize op_id. smt(@Zp). qed.
realize op_id'. smt(@Zp). qed.


local module ML_Spec = {
  proc mladder_1 (x :zp , n : bits ) : zp = {
    var x1 , x2 , i , b, cf;
    (x1,x2) <- (Zp.one , x);
    i <- size n;
    b <- false;
    while (0 < i) {
      (cf,i) <@ ASpecFp.subn(i,1);
      b <- ith_bit n i ;
      (x1,x2) <@ ASpecFp.swapr (x1,x2,b);
      (x1,x2) <@ ASpecFp.swapr (x1*x1,x1*x2,b);
    }
    return x1 ;
  } 

  proc mladder_2 (x :zp , n : int) : zp = {
    var x1 , x2 , i , b, cf;
    (x1,x2) <- (Zp.one , x);
    i <- 32*64;
    b <- false;
    while (0 < i) {
      (cf,i) <@ ASpecFp.subn(i,1);
      b <- ith_bit (int2bs (32*64) n) i ;
      (x1,x2) <@ ASpecFp.swapr (x1,x2,b);
      (x1,x2) <@ ASpecFp.swapr (x1*x1,x1*x2,b);
    }
    return x1 ;
  } 

  proc mladder_3 (x :zp , n : W64xN.R.t) : zp = {
    var x1 , x2 , i , b, cf;
    (x1,x2) <- (Zp.one , x);
    i <- 64*nlimbs;
    b <- W64.zero;
    while (0 < i) {
      (cf,i)  <@ ASpecFp.subn(i,1);
      b       <@ CSpecFp.ith_bit(n, i) ;
      (x1,x2) <@ ASpecFp.swapr (x1,x2,as_bool b);
      (x1,x2) <@ ASpecFp.swapr (x1*x1,x1*x2,as_bool b);
    }
    return x1 ;
  }

}.



local lemma ml_equiv_M_3 :
  equiv [M(Syscall).expm ~ ML_Spec.mladder_3 : W64xN.valR x{1} = asint x{2} /\ valR n{1} =  valR n{2} /\ valR m{1} = Zp.p /\ (W64x2N.valR r{1}) = ri_uncompute Zp.p ==> valR res{1} = asint res{2}].
proof. proc.
while (W64.to_uint i{1} = i{2} /\ valR x{1} = asint x{2} /\ valR x1{1} = asint x1{2} /\ valR x2{1} = asint x2{2} /\ n{1} =  n{2} /\ as_bool b{1} = as_bool b{2} /\ valR m{1} = Zp.p /\ i{2} <= 2048 /\ (W64x2N.valR r{1}) = ri_uncompute Zp.p).
ecall{1} (swap_lemma_ph x1{1} x2{1} (as_bool b{1})). simplify.
ecall{1} (bn_mulm_correct x11{1} x2{1} m{1}). simplify.
ecall{1} (bn_mulm_correct x1{1} x1{1} m{1}). simplify.
ecall{1} (bn_copy_correct x1{1}). simplify.
ecall{1} (swap_lemma_ph x1{1} x2{1} (as_bool b{1})). simplify.
inline ASpecFp.swapr.
wp. simplify.
call ith_bit_lemma_cspec.
inline*. wp.  simplify.
skip. progress.
have f1 : to_uint i{1} < modulusR. smt.
have -> : (to_uint i{1} - 1) %% modulusR = (to_uint i{1} - 1). smt.
smt(@W64).
smt.
have -> : (to_uint i{1} - 1) %% modulusR = (to_uint i{1} - 1). timeout 10. smt.
smt.
smt(@W64xN).
smt(@W64xN).
smt.
smt().
smt(@W64xN).
smt. 
smt(@W64xN).
smt.
timeout 15. smt.
smt.
smt.
smt.
smt.
wp. 
simplify.
ecall{1} (bn_copy_correct x1{1}). simplify.
ecall{1} (bn_copy_correct x{1}). simplify.
ecall{1} (bn_set1_correct). simplify.
wp.  skip. progress.
smt.
smt.
qed.


local lemma ml_equiv_1_2 :
  equiv [ML_Spec.mladder_1 ~ ML_Spec.mladder_2 : x{1} = x{2} /\ bs2int n{1} = n{2} /\ size n{1} = nlimbs * 64  ==> ={res}].
proc.
while (={x,x1,x2,i,b} /\ bs2int n{1} =  n{2} /\ size n{1} = nlimbs * 64).
call (_:true). skip. auto.
call (_:true). skip. auto.
wp.  call (_:true). sim. skip. progress.
have <- : n{1} = (int2bs 2048 (bs2int n{1})). 
search int2bs bs2int .
rewrite - H.
rewrite   bs2intK. auto.
auto.
wp.  skip. progress.
smt(). 
qed.



local lemma ml_equiv_2_3 :
  equiv [ML_Spec.mladder_2 ~ ML_Spec.mladder_3 : x{1} = x{2} /\ n{1} =  valR n{2} ==> ={res}].
proc.
while (={x,x1,x2,i} /\ n{1} = valR n{2} /\ b{1} = as_bool b{2}).
call (_:true). skip. auto.
call (_:true). skip. auto.
inline CSpecFp.ith_bit. wp. 
call (_:true). sim. skip. progress.
smt(@W64).
wp. 
skip. progress.
rewrite /as_bool. smt(@W64).
qed.


local lemma ml_equiv_abs_1 : 
  equiv [ML_Abstract.mladder ~ ML_Spec.mladder_1 : ={arg} /\ size n{1} < W64xN.modulusR ==> ={res}].
proc. inline*.  wp.
while (={x,n,x1,x2,i,b} /\ i{1} < modulusR). 
wp. skip. progress. smt.
smt. smt. smt.
smt. smt. smt.
wp. skip.  progress.
qed.


require import BarrettRedInt Real RealExp. 

lemma R_prop : W64x2N.valR R = 4 ^ (64 * nlimbs) %/ p.
rewrite /R.
have q1: 0 <= Ri. rewrite Ri_def.
rewrite divz_ge0. smt(P_pos). smt(@Ring).
have q2: Ri < W64x2N.modulusR .
  have ->: W64x2N.modulusR = (2^ (64 * dnlimbs)). rewrite /W64x2N.modulusR. smt(@Ring).
  have -> : Ri = (ri p (64 * nlimbs)). rewrite /Ri. rewrite /ri. rewrite Ri_def. smt().
  have : (ri p (64 * nlimbs))%r <= ((4 ^ (64*nlimbs))%r / p%r).  rewrite - same_ri. smt(P_pos). smt().
  rewrite /r.  rewrite - exp_lemma1. smt(). smt(). smt(floor_bound).
  have -> : (4 ^ (64 * nlimbs))%r = ((2 * 2) ^ (64 * nlimbs))%r. smt().
  have -> : ((2 * 2) ^ (64 * nlimbs))%r = ((2 ^ (2 * 64 * nlimbs)))%r. smt(@Ring).
  have->: (2 ^ (2 * 64 * nlimbs))%r = (2 ^ (64 * dnlimbs))%r. smt(@RealExp @Ring).
  pose x := ri p (64 * nlimbs).
  move => q.
  have : x%r < 2%r ^ (64 * dnlimbs)%r. apply (kok x%r (2%r ^ (64 * dnlimbs)%r) p%r).
  have ->: x = Ri. rewrite /x Ri_def /ri. smt().
   smt(@RealExp). smt(@RealExp). smt(P_pos). rewrite exp_lemma1. smt(). smt(). apply q.
    have ->: 2%r ^ (64 * dnlimbs)%r = (2 ^ (64 * dnlimbs))%r.
    rewrite - exp_lemma1. smt(). smt(). smt().
smt(@Real).
rewrite W64x2N.R.bn_ofintK. rewrite - Ri_def.
smt.
qed.


local lemma ml_equiv_abs_conc : 
  equiv [ML_Abstract.iterop_spec ~ M(Syscall).expm : 
  ImplZZ m{2} p 
  /\ asint x{1} = valR x{2} 
  /\ bs2int n{1} = valR n{2} 
  /\ size n{1} = 64*nlimbs 
  /\ asint x{1} < p 
  /\ r{2} = R
    ==> asint res{1} = valR res{2}
  ].
transitivity  ML_Abstract.mladder
  (={arg} /\ size n{1} = 64*nlimbs ==> ={res})
  (ImplZZ m{2} p /\
            asint x{1} = valR x{2} /\
            bs2int n{1} = valR n{2} /\ size n{1} = 64*nlimbs /\ asint x{1} < p /\ r{2} = R  ==>
            asint res{1} = valR res{2}).

progress. 
exists (arg{1}).  smt.
auto.
proc*.
ecall {2} (mladder_correct_ph x{2} n{2}).
inline*. wp.  skip. progress. smt().

transitivity ML_Spec.mladder_1
 (={arg} /\ size n{1} < W64xN.modulusR ==> ={res})
 (ImplZZ m{2} p /\
  asint x{1} = valR x{2} /\
  bs2int n{1} = valR n{2} /\ size n{1} = dnlimbs * nlimbs /\ asint x{1} < p /\ r{2} = R ==> asint res{1} = valR res{2}).
progress. smt.
smt().
conseq ml_equiv_abs_1.

transitivity ML_Spec.mladder_2
  (x{1} = x{2} /\ bs2int n{1} = n{2} /\ size n{1} = nlimbs * 64  ==> ={res})
  (ImplZZ m{2} p /\
  asint x{1} = valR x{2} /\
    valR n{2} =  n{1} /\ (* size n{2} = dnlimbs * nlimbs /\ *)  asint x{1} < p /\ r{2} = R ==> asint res{1} = valR res{2}).
progress. 
exists (x{1},  valR n{2}).
progress. auto.
conseq ml_equiv_1_2.

transitivity ML_Spec.mladder_3
  (x{1} = x{2} /\ n{1} =  valR n{2} ==> ={res})
  (ImplZZ m{2} p /\
  asint x{1} = valR x{2} /\
    valR n{2} = valR n{1} /\ (* size n{2} = dnlimbs * nlimbs /\ *)  asint x{1} < p /\ r{2} = R ==> asint res{1} = valR res{2}).
progress. 
exists (x{1},  n{2}). progress. smt. auto.
conseq ml_equiv_2_3.
symmetry.
conseq ml_equiv_M_3.
progress. smt.
smt .
progress.
smt.
qed.



local lemma exp_same_comp (x : zp) : forall n, 0 <= n => (x ^ n)%Ring_ops_spec = (x ^ n)%Exp.
apply intind. progress.
smt.
progress.
have ->: (x ^ (i + 1))%Ring_ops_spec = x * (x^ i)%Ring_ops_spec. 
 rewrite /(^).
 have ->: asint x ^ (i + 1) = (asint x) * (asint x ^ i). smt.
 smt.  
have ->: (x ^ (i + 1))%Exp = x * (x^ i)%Exp. smt.
rewrite H0.
auto.
qed.


lemma expm_correct :
      equiv[ ASpecFp.expm ~ M(Syscall).expm :
             ImplZZ m{2} p /\
             asint a{1} = valR x{2} /\
             b{1} = valR n{2}  /\
             valR x{2} < p /\
             r{2} = R
             ==> asint res{1} = valR{2}%W64xN res{2}].

transitivity ML_Abstract.iterop_spec
 (arg{1}.`1 = arg{2}.`1 /\ arg{1}.`2 = bs2int arg{2}.`2   ==> ={res})
 (ImplZZ m{2} p /\
             asint x{1} = valR x{2} /\
             bs2int n{1} = valR n{2}  /\
             valR x{2} < p /\
             r{2} = R /\ size n{1} = (nlimbs * 64)
             ==> asint res{1} = valR{2}%W64xN res{2}).
progress.
exists (arg{1}.`1, int2bs (nlimbs * 64) arg{1}.`2).
progress.
smt.
smt.
smt.
auto.
proc. sp. skip. progress. 
pose N := bs2int n{2}.           
apply exp_same_comp. smt.
conseq ml_equiv_abs_conc.
progress.
smt.
qed.


lemma bn_expm_correct rr mm xx nn:
  phoare[ M(Syscall).expm : r = rr /\ m = mm /\ x = xx /\ n = nn /\
                   ImplZZ m p /\
                   valR x < p /\
                   r = R ==> (valR res) = ((valR xx) ^ (valR nn)) %% p ] = 1%r.
bypr. progress.
have <- : Pr[ASpecFp.expm(inzp (valR x{m}), valR n{m}) @ &m : asint res =  ((valR x{m}) ^ (valR n{m})) %% p ] = 1%r.
  byphoare (_: arg = (inzp (valR x{m}), valR n{m}) ==> _).
proc. inline*. wp. skip. progress.
rewrite inzpK.
have -> :  asint (inzp (valR x{m}))  =  (valR x{m} ).
rewrite inzpK.
smt (@W64xN). auto.
auto. auto.
byequiv.
symmetry. conseq expm_correct.
progress.
rewrite inzpK.
smt (@W64xN).
smt(). auto. auto.
qed.

end section.

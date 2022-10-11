require import AllCore IntDiv CoreMap List.

require import JModel.
require import BitEncoding.
import BS2Int.

require import Abstract_exp_proof_1.
require import Abstract_exp_proof_2.
require import Abstract_exp_proof_3.
require import Abstract_exp_proof_4.
require import Abstract_exp_proof_5.
require import Abstract_exp_proof_6.
require import Abstract_exp_proof_7.

import IterOp.
import Zp.

module M8 = {
  proc expm_spec (x:R, n:R) : R = {
    return (x ^ (valR n));
  }  
}.






lemma kk :  forall (n : int), 0 <= n => forall (a : zp) (b : R),
  ImplFp b a =>
  ImplFp (b ^ n) (inzp (asint a ^ n)).
apply intind. progress. 
rewrite exp_prop1.
have -> : (asint a ^ 0) = 1. smt.
rewrite /asint.
have -> : (Sub.val (inzp 1))%Sub = 1. smt.
smt(valR_one).
progress.
have ->: (b ^ (i + 1)) = b *** (b ^ i).
rewrite exp_prop3. auto. auto.
rewrite exp_prop2.
rewrite exp_prop7. auto.
have ->: inzp (asint a ^ (i + 1)) =  inzp (asint a * (asint a ^ i)).
smt.
have ->:  inzp (asint a * (asint a ^ i)) = (inzp (asint a)) * (inzp (asint a ^ i)).
smt.
rewrite - H1.
have ->: asint (inzp (valR b) * inzp (valR b ^ i))
  = (asint (inzp (valR b)) * (asint  (inzp (valR b ^ i)))) %% P.
smt.
have ih :  ImplFp (b ^ i)  (inzp (valR b ^ i)).
rewrite H1. apply H0. auto.
rewrite - ih.
have ->: asint (inzp (valR b)) = valR b. smt.
have ->: valR (b *** (b ^ i)) =  (valR b) * (valR (b ^ i)) %%P.
rewrite  to_uintP /=. done.
auto.
qed.


lemma exp_real_speacc :
 equiv[ Spec.expm ~ M8.expm_spec  : 
    ImplFp arg{2}.`1 arg{1}.`1 /\ valR arg{2}.`2 = arg{1}.`2 ==> ImplFp res{2} res{1}].
proc. 
wp.  skip.  progress.
apply kk.
smt.
auto.
qed.


lemma exp_real_speac2 :
 equiv[ M8.expm_spec ~ M1.expm_spec   : arg{1}.`1 = arg{2}.`1 /\  valR arg{1}.`2 = bs2int arg{2}.`2 ==> ={res}] .
proc. skip. progress.
smt().
qed.



section.
declare module M <: BasicOps.

declare axiom exp_swap :
 equiv[ M.swapr ~ Spec.swapr    : arg{2}.`1 = arg{1}.`1 /\ arg{2}.`2 = arg{1}.`2 /\   arg{1}.`3 = as_w64 arg{2}.`3
    ==> ={res}].

declare axiom exp_ithbit :
 equiv[ M.ith_bit ~ Spec.ith_bit    : arg{2}.`1 = arg{1}.`1 /\  arg{2}.`2 = W64.to_uint arg{1}.`2 
    /\ 0 <= ctr{2} < Rsize ==> ={res} /\ (res{2} = W64.one \/ res{2} = W64.zero) ].

declare axiom exp_mulm : 
  equiv [ M.mulm ~ Spec.mul: arg{1}.`2 = arg{2}.`1 /\ arg{1}.`3 = arg{2}.`2 /\   ImplR p{1} P  ==> ={res} ].

declare axiom stateless_M (x y : glob M) : x = y.

lemma exp_real_speac :
 equiv[ M1.expm_spec ~ M7(M).expm  : valR arg{2}.`1 = P 
   /\  arg{1}.`1 = arg{2}.`2
   /\ bs2int arg{1}.`2 = valR arg{2}.`3
   /\ size arg{1}.`2 = Rsize
     ==> ={res}].
transitivity M2.expm
   (={arg} /\  0 < size arg{1}.`2 ==> ={res}) 
  (valR arg{2}.`1 = P 
   /\  arg{1}.`1 = arg{2}.`2
   /\ bs2int arg{1}.`2 = valR arg{2}.`3
   /\ size arg{1}.`2 = Rsize
     ==> ={res} ).
progress.  exists arg{1}. progress. smt(Rsize_pos). auto.
symmetry.
conseq expm_correct.
auto. auto.
transitivity M3.expm
  (={arg} /\  0 < size n{1} ==> ={res})
  (valR arg{2}.`1 = P 
   /\  arg{1}.`1 = arg{2}.`2
   /\ bs2int arg{1}.`2 = valR arg{2}.`3
   /\ size arg{1}.`2 = Rsize
     ==> ={res} ).
progress. 
exists arg{1}. progress. smt(Rsize_pos). auto.
conseq exp_2_3.
transitivity M4.expm
  (arg{1}.`1 = arg{2}.`1 /\ (bitsR arg.`2{1}) = (arg.`2{2})  /\ size n{1} = Rsize /\  0 < size n{1} ==> ={res})
(valR arg{2}.`1 = P 
   /\  arg{1}.`1 = arg{2}.`2
   /\ arg{1}.`2 = arg{2}.`3
     ==> ={res} ).
progress. 
exists (x{1} , ( n{2})). progress. 
smt (bitsR_prop).
smt(Rsize_pos). auto.
conseq exp_3_4_1.  progress.
 
transitivity M5.expm
  (={arg} ==> ={res})
  (valR arg{2}.`1 = P 
   /\  arg{1}.`1 = arg{2}.`2
   /\ arg{1}.`2 = arg{2}.`3
     ==> ={res} ).
progress. 
exists (x{1} , ( n{2})). progress.  smt(). auto.
conseq exp_4_5.  
transitivity M6(M).expm
 (arg{2}.`2 = arg{1}.`1 /\ arg{2}.`3 = arg{1}.`2 /\  valR m{2} = P ==> ={res})
  (={arg} ==> ={res}).
progress. smt(). smt().
conseq (exp_5_6 M exp_swap exp_ithbit exp_mulm). 
conseq (exp_6_7 M).
smt (stateless_M).
qed.


lemma exp_pre_fin :
 equiv[ Spec.expm ~ M7(M).expm  : valR arg{2}.`1  = P 
   /\  ImplFp  arg{2}.`2 arg{1}.`1
   /\ arg{1}.`2 =  valR arg{2}.`3
     ==> ImplFp res{2} res{1} ].
transitivity M8.expm_spec
  (ImplFp arg{2}.`1 arg{1}.`1 /\ valR arg{2}.`2 = arg{1}.`2 ==> ImplFp res{2} res{1})
  (valR arg{2}.`1 = P 
   /\  arg{1}.`1 = arg{2}.`2
   /\  arg{1}.`2 =  arg{2}.`3
     ==> ={res}).
progress. exists (x{2},n{2}). progress. smt(). auto.
conseq exp_real_speacc.   
transitivity M1.expm_spec  
  (arg{1}.`1 = arg{2}.`1 /\ valR arg{1}.`2 = bs2int arg{2}.`2 ==> ={res})
  (valR arg{2}.`1 = P 
   /\  arg{1}.`1 = arg{2}.`2
   /\ bs2int arg{1}.`2 = valR arg{2}.`3
   /\ size arg{1}.`2 = Rsize
     ==> ={res}).
progress. 
exists (x{1},  Rbits n{2}).
progress.
smt().
smt(rsize_prop).
smt().
conseq exp_real_speac2. 
conseq exp_real_speac.
qed.

end section.

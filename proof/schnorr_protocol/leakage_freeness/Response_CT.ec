require import List Int AllCore Distr.

from Jasmin require import JModel.

require import W64_SchnorrExtract_ct.
require import BigNum_LF.
require import ModularMultiplication_Concrete_CT.
require import BarretReduction_Concrete_CT.

(* response LEAKAGES  *)
op response_f  : leakages_t = 
 bn_addm_f ++ LeakAddr [] :: (mulm_t ++
 LeakAddr [] :: (bn_cmov_f 32 ++
 LeakAddr [] :: LeakAddr [] :: LeakAddr [] :: (
 bn_eq_t ++
 LeakAddr [] :: (bn_eq_t ++
 LeakAddr [] :: (set1_f 32 ++
 LeakAddr [] :: (
 set0_f 32 ++
 LeakAddr [] :: 
 LeakAddr [] :: (
 bn_breduce_small_f ++
 LeakAddr [] :: (
 bn_breduce_small_f ++
 LeakAddr [] :: (
 bn_breduce_small_f ++
 LeakAddr [] :: 
 LeakAddr [] :: 
 LeakAddr [] :: []))))))))).


lemma response_leakages start_l :
   hoare [ M(Syscall).response : M.leakages = start_l
     ==> M.leakages = response_f  ++ start_l ].
proof. proc.
wp. ecall (bn_addm_leakages M.leakages).
wp. ecall (bn_mulm_leakages M.leakages).
wp. inline M(Syscall).check_challenge.
wp. ecall (bn_cmov_leakages M.leakages).
wp. ecall (bn_eq_leakages M.leakages).
wp. ecall (bn_eq_leakages M.leakages).
wp. ecall (bn_set1_leakages M.leakages).
wp. ecall (bn_set0_leakages M.leakages).
wp. ecall (bn_breduce_small_leakages M.leakages).
wp. ecall (bn_breduce_small_leakages M.leakages).
wp. ecall (bn_breduce_small_leakages M.leakages).
wp. skip. simplify.
progress.
rewrite /response_f. 
do ? (rewrite - catA; simplify; congr; simplify).
rewrite - catA. simplify.
auto.
qed.


lemma response_ll: islossless M(Syscall).response.
proc.
wp. call (bn_addm_ll).
wp. call (bn_mulm_ll).
wp. inline M(Syscall).check_challenge.
wp. call (bn_cmov_ll).
wp. call (bn_eq_ll).
wp. call (bn_eq_ll).
wp. call (bn_set1_ll).
wp. call (bn_set0_ll).
wp. call (bn_breduce_small_ll).
wp. call (bn_breduce_small_ll).
wp. call (bn_breduce_small_ll).
wp. auto.
qed.


lemma response_leakages_ph start_l :
   phoare [ M(Syscall).response : M.leakages = start_l 
     ==> M.leakages = response_f  ++ start_l ] = 1%r.
phoare split !  1%r 0%r. auto.
conseq response_ll. hoare. conseq (response_leakages start_l).
qed.


lemma response_ct &m l sin :  M.leakages{m} = l
 => Pr[ M(Syscall).response(sin)@&m : M.leakages = response_f ++ l ] = 1%r.
move => lh.
byphoare (_: (glob M) = (glob M){m} ==> _ ).
conseq (response_leakages_ph l).
auto. auto. auto.
qed.

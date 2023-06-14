require import List Int AllCore Distr.

from Jasmin require import JModel.

require import W64_SchnorrExtract_ct.
require import BigNum_LF.
require import ModularMultiplication_Concrete_CT.
require import BarretReduction_Concrete_CT.
require import MontomeryLadder_Concrete_CT.

(* verify LEAKAGES  *)
op verify_f  : leakages_t =
 LeakAddr [] :: bn_eq_t ++
 LeakAddr [] :: set1_f 32 ++
 LeakAddr [] :: expm_t ++
 LeakAddr [] :: bn_eq_t ++
 LeakAddr [] :: expm_t ++
 LeakAddr [] :: mulm_t ++
 LeakAddr [] :: expm_t ++
 LeakAddr [] :: bn_breduce_small_f ++
 LeakAddr [] :: bn_breduce_small_f ++
 LeakAddr [] :: bn_breduce_small_f ++
 LeakAddr [] :: bn_breduce_small_f ++
 LeakAddr [] :: 
 LeakAddr [] :: 
 LeakAddr [] :: 
 LeakAddr [] :: 
 LeakAddr [] :: 
 LeakAddr [] :: [].


lemma verify_leakages start_l :
   hoare [ M(Syscall).verify : M.leakages = start_l
     ==> M.leakages = verify_f  ++ start_l ].
proof. proc.
wp. ecall (bn_eq_leakages M.leakages).
wp. ecall (bn_set1_leakages M.leakages).
wp. ecall (bn_expm_leakages M.leakages).
wp. ecall (bn_eq_leakages M.leakages).
wp. ecall (bn_expm_leakages M.leakages).
wp. ecall (bn_mulm_leakages M.leakages).
wp. ecall (bn_expm_leakages M.leakages).
wp. ecall (bn_breduce_small_leakages M.leakages).
wp. ecall (bn_breduce_small_leakages M.leakages).
wp. ecall (bn_breduce_small_leakages M.leakages).
wp. ecall (bn_breduce_small_leakages M.leakages).
wp. skip. 
progress.
rewrite /verify_f.
do ? (rewrite - catA; simplify).
auto.
qed.


lemma verify_ll: islossless M(Syscall).verify.
proc.
wp. call (bn_eq_ll).
wp. call (bn_set1_ll).
wp. call (bn_expm_ll).
wp. call (bn_eq_ll).
wp. call (bn_expm_ll).
wp. call (bn_mulm_ll).
wp. call (bn_expm_ll).
wp. call (bn_breduce_small_ll).
wp. call (bn_breduce_small_ll).
wp. call (bn_breduce_small_ll).
wp. call (bn_breduce_small_ll).
wp. auto.
qed.


lemma verify_leakages_ph start_l :
   phoare [ M(Syscall).verify : M.leakages = start_l 
     ==> M.leakages = verify_f  ++ start_l ] = 1%r.
phoare split !  1%r 0%r. auto.
conseq verify_ll. hoare. conseq (verify_leakages start_l).
qed.


lemma verify_ct &m l sin :  M.leakages{m} = l
 => Pr[ M(Syscall).verify(sin)@&m : M.leakages = verify_f ++ l ] = 1%r.
move => lh.
byphoare (_: (glob M) = (glob M){m} ==> _ ).
conseq (verify_leakages_ph l).
auto. auto. auto.
qed.



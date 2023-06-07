require import List Int AllCore Distr.
from Jasmin require import JModel.

require import AuxLemmas.
require import BigNum_LF.


require import W64_SchnorrExtract_ct.
module M1 = W64_SchnorrExtract_ct.M(W64_SchnorrExtract_ct.Syscall).

(* random_bit LEAKAGES  *)
op random_bit_t : leakages_t =  LeakAddr [] ::  LeakAddr [0] :: LeakAddr [] :: LeakAddr [] :: [].

lemma random_bit_leakages start_l : 
  hoare [ M(Syscall).random_bit : M.leakages = start_l ==> M.leakages = random_bit_t ++ start_l].
proc. wp. call (_:true). rnd. skip. progress.
wp. skip. progress. 
qed.

lemma random_bit_ll : islossless M(Syscall).random_bit.
proc. inline*. wp. rnd. wp. skip.
progress. 
apply dmap_ll.
apply dmap_ll.
apply  DList.dlist_ll. smt(@W8).
qed.


lemma random_bit_leakages_ph start_l :
  phoare [ M(Syscall).random_bit : M.leakages = start_l 
            ==> M.leakages = random_bit_t ++ start_l ] = 1%r.
phoare split !  1%r 0%r. auto.
conseq random_bit_ll. hoare. conseq (random_bit_leakages start_l).
qed.


(* uniform_binary_choice LEAKAGES  *)

op uniform_binary_choice_t : leakages_t = bn_cmov_f 32 ++
[LeakAddr []; LeakAddr []] ++ random_bit_t ++ LeakAddr [] :: [].

lemma uniform_binary_choice_leakages start_l : 
  hoare [ M(Syscall).uniform_binary_choice : M.leakages = start_l 
    ==> M.leakages = uniform_binary_choice_t ++ start_l].
proc.
pose suf1 :=  [LeakAddr []] ++ start_l.
seq 3 : (M.leakages = random_bit_t ++ suf1 ).
wp.  call (random_bit_leakages suf1).  wp.  skip. progress. 
pose suf2 :=  [LeakAddr []; LeakAddr []] ++ random_bit_t ++ suf1.
seq 6 : (M.leakages = bn_cmov_f 32 ++ suf2 ).
wp.  call (bn_cmov_leakages suf2).  wp.  skip. progress.  
rewrite /suf2 /suf1. 
skip. progress.
rewrite /uniform_binary_choice_t. 
do? rewrite - catA. simplify. 
do? rewrite  catA.  auto.
qed.

lemma uniform_binary_choice_ll : 
  islossless M(Syscall).uniform_binary_choice.
proc. 
wp. call bn_cmov_ll. 
wp. call random_bit_ll.
auto.
qed.

lemma uniform_binary_choice_leakages_ph start_l : 
  phoare [ M(Syscall).uniform_binary_choice : M.leakages = start_l 
    ==> M.leakages = uniform_binary_choice_t ++ start_l] = 1%r.
phoare split !  1%r 0%r. auto.
conseq uniform_binary_choice_ll. hoare. conseq (uniform_binary_choice_leakages start_l).
qed.

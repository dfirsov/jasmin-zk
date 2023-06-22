require import List Int AllCore. 
require import W64_SchnorrExtract_ct.
from Jasmin require import JModel.

require import BigNum_LF.
require import ModularMultiplication_Concrete_CT.
require import BarretReduction_Concrete_CT.

op expm_t_prefix : leakages_t = LeakCond true :: LeakAddr [] :: LeakAddr [] :: LeakAddr [] :: (copy_f 32 ++
                                                               [LeakAddr []] ++
                                                               copy_g 32 ++
                                                               copy_prefix ++
                                                               [LeakAddr []] ++
                                                               set1_g 32 ++
                                                               set1_prefix ++
                                                               [LeakAddr []]).
op expm_step_acc i =
  LeakCond (W64.zero \ult i) :: LeakAddr [] :: (swapr_f 32 ++
                                                  ([LeakAddr []] ++ mulm_t ++
                                                   ([LeakAddr []] ++ mulm_t ++
                                                    ([LeakAddr []] ++
                                                     copy_f 32 ++
                                                     ([LeakAddr []] ++
                                                      swapr_f 32 ++
                                                      ([LeakAddr []] ++
                                                       ith_bit_t
                                                         (i + W64.one -
                                                          W64.one) ++
                                                       (LeakAddr [] ::
                                                        LeakAddr [] ::
                                                        []))))))).


op [opaque] expm_step (i : int) : leakages_t = iteri i (fun i r => expm_step_acc (W64.of_int (2048 - (i + 1))) ++ r) [].

lemma expm_step0 : expm_step 0 = []. smt(@Int). qed.
lemma expm_stepS i : 0 < i =>  expm_step i
 =  expm_step_acc (W64.of_int (2048 - i))
    ++ expm_step (i-1). rewrite /expm_step.
progress.
search iteri.
have ->: i = (i-1)+1. smt().
rewrite iteriS. smt(). simplify. auto. qed.

lemma expm_stepSS i : 0 <= i < 2048 =>  expm_step (2048 -  i)
  = expm_step_acc (W64.of_int i) ++ expm_step (2048 - (i + 1)).
progress.
case ((2048 - i) = 0).
progress.
have : i = 0. smt().
progress. rewrite expm_stepS. auto. simplify. auto.
move => q.
rewrite expm_stepS. smt().
simplify. smt().
qed.
  

op [opaque] expm_t : leakages_t = expm_step 2048 ++ expm_t_prefix.

lemma bn_expm_leakages l :
  hoare [ M(Syscall).bn_expm : M.leakages = l
     ==> M.leakages = expm_t ++ l].
proc.
seq 19 : (M.leakages = expm_t_prefix ++ l /\ i = (W64.of_int (32 * 64)) ).

pose suf1 :=  [LeakAddr []] ++ l.
seq 6 : (M.leakages = set1_f 32 ++ suf1 ).
wp.  call (bn_set1_leakages suf1). simplify. wp. skip. progress.

pose suf2 :=  [LeakAddr []] ++ set1_f 32 ++ suf1.
seq 3 : (M.leakages = copy_f 32 ++ suf2).
wp.  call (bn_copy_leakages suf2). simplify. wp. skip. progress.

pose suf3 :=  [LeakAddr []] ++ copy_f 32 ++ suf2.
seq 3 : (M.leakages = copy_f 32 ++ suf3).
wp.  call (bn_copy_leakages suf3). simplify. wp. skip. progress.
wp. skip. progress.
rewrite /suf3 /suf2 /suf1.
rewrite /expm_t_prefix.
do ? rewrite catA. simplify. smt(@List).
while (W64.zero \ult (i + W64.one) /\ ( M.leakages = expm_step (2048 - (to_uint i)) ++ expm_t_prefix ++ l)  /\ (i <> W64.zero => (i - W64.one) \ult (W64.of_int 2048))  ).
exists* i. elim*. move => i_var.
pose suf1 :=  LeakAddr [] :: LeakAddr [] ::  expm_step (2048 - to_uint (i_var)) ++ expm_t_prefix ++ l.
seq 6 : (M.leakages = (ith_bit_t (i_var - W64.one)) ++ suf1 /\ i_var = i + W64.one /\ W64.zero \ult i_var /\ (i + W64.one <> W64.zero => i \ult (W64.of_int 2048))).
wp.  call (ith_bit_leakages suf1 (i_var - W64.one)). simplify.
wp. skip. progress. smt(@W64).  smt(@W64).
pose suf2 :=  [LeakAddr []]  ++ ith_bit_t (i_var - W64.one) ++ suf1.
seq 4 : (M.leakages = (swapr_f 32) ++ suf2 /\ i_var = i + W64.one /\ W64.zero \ult i_var /\ (i + W64.one <> W64.zero => i \ult (W64.of_int 2048))).
wp.  call (swapr_leakages suf2).
wp. skip. progress.
pose suf3 :=  [LeakAddr []]  ++ swapr_f 32 ++ suf2.
seq 3 : (M.leakages = copy_f 32 ++ suf3 /\ i_var = i + W64.one /\ W64.zero \ult i_var /\ (i + W64.one <> W64.zero => i \ult (W64.of_int 2048))).
wp.  call (bn_copy_leakages suf3).
wp. skip. progress.
pose suf4 :=  [LeakAddr []]  ++ copy_f 32 ++ suf3.
seq 3 : (M.leakages = mulm_t ++ suf4 /\ i_var = i + W64.one /\ W64.zero \ult i_var /\ (i + W64.one <> W64.zero => i \ult (W64.of_int 2048))).
wp.  call (bn_mulm_leakages suf4).
wp. skip. progress.
pose suf5 :=  [LeakAddr []]  ++ mulm_t ++ suf4.
seq 3 : (M.leakages = mulm_t ++ suf5 /\ i_var = i + W64.one /\ W64.zero \ult i_var /\ (i + W64.one <> W64.zero => i \ult (W64.of_int 2048))).
wp.  call (bn_mulm_leakages suf5).
wp. skip. progress.
pose suf6 :=  [LeakAddr []]  ++ mulm_t ++ suf5.
seq 3 : (M.leakages = swapr_f 32 ++ suf6 /\ i_var = i + W64.one /\ W64.zero \ult i_var /\ (i + W64.one <> W64.zero => i \ult (W64.of_int 2048))).
wp.  call (swapr_leakages suf6).
wp. skip. progress.
wp.  skip. progress.
rewrite /suf6 /suf5 /suf4 /suf3 /suf2 /suf1.
rewrite (expm_stepSS (to_uint i{hr})).
split. smt(@W64). smt(@W64).
rewrite /expm_step_acc.
have ->: (W64.of_int (to_uint i{hr})) = i{hr}.
smt(@W64).
have -> :  (to_uint i{hr} + 1) = to_uint (i{hr} + W64.one). smt(@W64).
do ? rewrite  catA.
simplify.
pose xxx := swapr_f 32 ++ [LeakAddr []] ++ mulm_t ++ [LeakAddr []] ++ mulm_t.
pose yyy := xxx ++ [LeakAddr []] ++ copy_f 32 ++ [LeakAddr []] ++
swapr_f 32 ++ [LeakAddr []] ++ ith_bit_t (i{hr} + W64.one - W64.one).
pose www := expm_step (2048 - to_uint (i{hr} + W64.one)) .
congr. congr.
have ->: yyy ++ [LeakAddr []; LeakAddr []] ++ www
   = yyy ++ ([LeakAddr []; LeakAddr []] ++ www). rewrite catA. auto.
have ->: ([LeakAddr []; LeakAddr []] ++ www) = (LeakAddr [] :: LeakAddr [] :: www). smt(@List).
auto.
smt(@W64).
skip.
progress.
rewrite expm_step0. simplify. auto.
have : i0 = W64.zero.  smt(@W64).
progress.
rewrite /expm_t. auto.
qed.


lemma bn_expm_ll : islossless M(Syscall).bn_expm.
proc.
while (0 <= to_uint i) (to_uint i).
progress.
wp. call swapr_ll.
wp. call bn_mulm_ll.
wp. call bn_mulm_ll.
wp. call bn_copy_ll.
wp. call swapr_ll.
wp. call ith_bit_ll.
wp. skip. progress.
smt(@W64).
smt(@W64).
wp. call bn_copy_ll.
wp. call bn_copy_ll.
wp. call bn_set1_ll.
wp. skip. progress.
smt(@W64).
qed.



lemma bn_expm_leakages_ph start_l :
   phoare [ M(Syscall).bn_expm : M.leakages = start_l
     ==> M.leakages = expm_t ++ start_l ] = 1%r.
phoare split !  1%r 0%r. auto.
conseq bn_expm_ll. hoare. conseq (bn_expm_leakages start_l).
qed.

lemma bn_expm_ct &m l r a b n :  M.leakages{m} = l
 => Pr[ M(Syscall).bn_expm(r,a,b,n)@&m : M.leakages = expm_t ++ l ] = 1%r.
move => lh.
byphoare (_: (glob M) = (glob M){m} ==> _ ).
conseq (bn_expm_leakages_ph l).
auto. auto. auto.
qed.



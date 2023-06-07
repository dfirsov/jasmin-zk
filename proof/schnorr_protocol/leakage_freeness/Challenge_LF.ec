require import List Int AllCore Distr.

from Jasmin require import JModel.

require import AuxLemmas.
require import BigNum_LF.
require import Random_bit_LF.


require import W64_SchnorrExtract_ct.
module M1 = W64_SchnorrExtract_ct.M(W64_SchnorrExtract_ct.Syscall).


(* challenge LEAKAGES  *)
op challenge_t : leakages_t = uniform_binary_choice_t ++
 [LeakAddr []] ++ set1_f 32 ++ [LeakAddr []] ++ set0_f 32 ++ [LeakAddr []].

lemma challenge_leakages start_l : 
  hoare [ M(Syscall).challenge : M.leakages = start_l ==> M.leakages = challenge_t ++ start_l].
proc.
pose suf1 :=  [LeakAddr []] ++ start_l.
seq 6 : (M.leakages = set0_f 32 ++ suf1 ).
wp.  call (bn_set0_leakages suf1). simplify. wp. skip. progress. auto.
pose suf2 :=  [LeakAddr []] ++ set0_f 32 ++ suf1.
seq 3 : (M.leakages = set1_f 32 ++ suf2).
wp.  call (bn_set1_leakages suf2). wp. skip. progress.
pose suf3 :=  [LeakAddr []] ++ set1_f 32 ++ suf2.
seq 3 : (M.leakages = uniform_binary_choice_t ++ suf3).
call (uniform_binary_choice_leakages suf3). wp. skip. progress.
skip. progress.
rewrite /suf3 /suf2 /suf1. 
do? rewrite - catA. 
do? rewrite  catA.  auto.
qed.


lemma challenge_ll : 
  islossless M(Syscall).challenge.
proc. 
wp. call uniform_binary_choice_ll. 
wp. call bn_set1_ll.
wp. call bn_set0_ll.
auto.
qed.

lemma challenge_leakages_ph start_l : 
  phoare [ M(Syscall).challenge : M.leakages = start_l ==> M.leakages = challenge_t ++ start_l] = 1%r.
phoare split !  1%r 0%r. auto.
conseq challenge_ll. hoare. conseq (challenge_leakages start_l).
qed.


lemma challenge_leakages_ph0 start_l : 
  phoare [ M(Syscall).challenge : M.leakages = start_l ==> M.leakages <> challenge_t ++ start_l] = 0%r.
hoare. simplify.
apply challenge_leakages.
qed.


lemma chalenge_leakfree l a &m: (glob M1){m} = [] 
 =>  let v = Pr[ M1.challenge() @ &m : res = a  ] in 
     let w = Pr[ M1.challenge() @ &m : M1.leakages = l  /\ res = a  ] in 
  0%r < w => v/w 
  = 1%r.
case (l = challenge_t).
progress.
 have ->: Pr[M(Syscall).challenge() @ &m : res = a] 
  = Pr[M(Syscall).challenge() @ &m : res = a /\  M1.leakages = challenge_t ]
  + Pr[M(Syscall).challenge() @ &m : res = a /\  M1.leakages <> challenge_t ].
  rewrite Pr[mu_split (M1.leakages = challenge_t)]. auto.
 have ->: Pr[M(Syscall).challenge() @ &m : res = a /\  M1.leakages <> challenge_t ] = 0%r.
  have : Pr[M(Syscall).challenge() @ &m : res = a /\  M1.leakages <> challenge_t ]
   <= Pr[M(Syscall).challenge() @ &m :  M1.leakages <> challenge_t ].
   rewrite Pr[mu_sub]. smt(). auto.
   have ->: Pr[M(Syscall).challenge() @ &m :  M1.leakages <> challenge_t ] = 0%r.
   byphoare (_: M.leakages = [] ==> _). conseq (challenge_leakages_ph0 []). 
   progress. smt(@List).  smt(@List).  auto. auto.
   smt(@Distr). simplify. auto.
 have ->: Pr[M(Syscall).challenge() @ &m : res = a /\ M.leakages = challenge_t] 
   = Pr[M(Syscall).challenge() @ &m : M.leakages = challenge_t /\ res = a ]. rewrite Pr[mu_eq]. auto. auto.
 smt(@Real).
 progress.
 have fact1 : 
    Pr[M(Syscall).challenge() @ &m : M.leakages = l /\ res = a] = 
    Pr[M(Syscall).challenge() @ &m : M.leakages = l /\ res = a /\ M.leakages <> challenge_t].
 rewrite Pr[mu_eq]. smt(). auto.
 have fact2 : Pr[M(Syscall).challenge() @ &m : M.leakages = l /\ res = a /\ M.leakages <> challenge_t] = 0%r.
  byphoare (_: M.leakages = [] ==> _). proc*. call (challenge_leakages_ph0 []). skip. progress. 
  smt(@List). auto. auto. 
  smt().
qed.

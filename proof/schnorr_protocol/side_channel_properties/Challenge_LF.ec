require import List Int AllCore Distr.

from Jasmin require import JModel.

require import AuxLemmas.
require import Ops_LeakageFunctions.


require import W64_SchnorrExtract_ct.
module M1 = W64_SchnorrExtract_ct.M(W64_SchnorrExtract_ct.Syscall).


lemma challenge_leakages_ph start_l : 
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
   byphoare (_: M.leakages = [] ==> _). conseq (challenge_leakages_ph []). 
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
  byphoare (_: M.leakages = [] ==> _). proc*. call (challenge_leakages_ph []). skip. progress. 
  smt(@List). auto. auto. 
  smt().
qed.

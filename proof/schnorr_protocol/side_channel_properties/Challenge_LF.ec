require import List Int AllCore Distr.

from Jasmin require import JModel.

require import AuxLemmas.
require import Ops_LeakageFunctions.

(* SAMPLING LEAKAGES  *)
require import W64_SchnorrExtract_ct.
module M1 = W64_SchnorrExtract_ct.M(W64_SchnorrExtract_ct.Syscall).

require Constants.
op challenge_t i : leakages_t =  samp_t i ++ ([LeakAddr []] ++ bn_set_q_t ++ [LeakAddr []]).

lemma challenge_t_inj : injective challenge_t.
move => x y.
have : x <> y => challenge_t x <> challenge_t y.
move => xneqy.
rewrite /commitment_t.
have : samp_t x <> samp_t y. smt(samp_t_inj).
smt(@List).
smt().
qed.


lemma challenge_leakages2   &m : (glob M1){m} = [] =>
  Pr[ M1.challenge_indexed() @ &m : M1.leakages <> challenge_t res.`1 ] = 0%r.
progress. byphoare (_: glob M1 = [] ==> _).
hoare. simplify.
proc.
pose suf1 :=  [LeakAddr []].
seq 5 : (M.leakages = bn_set_q_t ++ suf1 ).
wp.  call (bn_set_q_leakages suf1). simplify. wp. skip. progress. 
pose suf2 := [LeakAddr []] ++ bn_set_q_t ++ suf1.
seq 4 : (M.leakages = samp_t i ++ suf2).
wp. call  (rsample_leakages suf2). wp.
skip. progress. skip. progress.
rewrite /challenge_t /suf2 /suf1.
auto. auto.
qed.


lemma challenge_leakages3 l x &m : (glob M1){m} = [] =>
  Pr[ M1.challenge_indexed() @ &m : M1.leakages = l  /\ res.`2 = x ]
  = Pr[ M1.challenge_indexed() @ &m : l = challenge_t res.`1 /\ res.`2 = x  ].
move => H.
have ->: Pr[ M1.challenge_indexed() @ &m : l = challenge_t res.`1 /\ res.`2 = x ]
 = Pr[ M1.challenge_indexed() @ &m : l = challenge_t res.`1 /\ res.`2 = x /\ M1.leakages = challenge_t res.`1  ].
  have -> : Pr[M1.challenge_indexed() @ &m : l = challenge_t res.`1 /\ res.`2 = x]
   = Pr[M1.challenge_indexed() @ &m : l = challenge_t res.`1 /\ res.`2 = x /\ M1.leakages = challenge_t res.`1]
   + Pr[M1.challenge_indexed() @ &m : l = challenge_t res.`1 /\ res.`2 = x /\ M1.leakages <> challenge_t res.`1].
   rewrite Pr[mu_split (M1.leakages = challenge_t res.`1)]. smt(). 
  have ->: Pr[M1.challenge_indexed() @ &m :
   l = challenge_t res.`1 /\ res.`2 = x /\ M1.leakages <> challenge_t res.`1] = 0%r.
    have : Pr[M1.challenge_indexed() @ &m :
       l = challenge_t res.`1 /\ res.`2 = x /\ M1.leakages <> challenge_t res.`1]
     <= Pr[ M1.challenge_indexed() @ &m : M1.leakages <> challenge_t res.`1 ]. smt(@Distr).
    rewrite (challenge_leakages2  &m). auto. smt(@Distr). 
auto.
have -> : Pr[ M1.challenge_indexed() @ &m : l = challenge_t res.`1 /\ res.`2 = x /\ M1.leakages = challenge_t res.`1  ]
 = Pr[ M1.challenge_indexed() @ &m : res.`2 = x /\  l = M1.leakages /\ M1.leakages = challenge_t res.`1  ].
rewrite Pr[mu_eq]. move => &hr. split.  smt().  smt(). auto.
have -> : Pr[ M1.challenge_indexed() @ &m : res.`2 = x /\ l = M1.leakages /\ M1.leakages = challenge_t res.`1  ]
 = Pr[ M1.challenge_indexed() @ &m :  l = M1.leakages /\ res.`2 = x ].
  have : Pr[ M1.challenge_indexed() @ &m :  l = M1.leakages /\ res.`2 = x ] 
   = Pr[ M1.challenge_indexed() @ &m :  l = M1.leakages /\ res.`2 = x /\ M1.leakages = challenge_t res.`1  ]
   + Pr[ M1.challenge_indexed() @ &m :  l = M1.leakages /\ res.`2 = x /\ M1.leakages <> challenge_t res.`1  ].
 rewrite Pr[mu_split (M1.leakages = challenge_t res.`1 )]. smt().
   have : Pr[ M1.challenge_indexed() @ &m :  l = M1.leakages /\ res.`2 = x /\ M1.leakages <> challenge_t res.`1  ]
    = 0%r.
     have : Pr[ M1.challenge_indexed() @ &m :  l = M1.leakages /\ res.`2 = x /\ M1.leakages <> challenge_t res.`1  ] 
         <= Pr[ M1.challenge_indexed() @ &m : M1.leakages <> challenge_t res.`1 ].
       rewrite Pr[mu_sub]. auto. auto.
    rewrite (challenge_leakages2 &m). auto. smt(@Distr).
    move => h. rewrite h. simplify. progress. rewrite H0.
rewrite Pr[mu_eq]. smt(). auto. 
rewrite Pr[mu_eq]. smt(). auto.
qed.


lemma challenge_leakages_inv x l &m : (glob M1){m} = [] 
 => Pr[ M1.challenge_indexed() @ &m : M1.leakages = l /\ res.`2 = x  ]
  = Pr[ M1.challenge_indexed() @ &m :  (inv (-1) challenge_t) l = res.`1  /\ res.`2 = x  ].
move => ic (* ic' *). rewrite  (challenge_leakages3 l x &m). auto. auto.
simplify. 
have -> : 
  Pr[M1.challenge_indexed() @ &m :
   l = challenge_t res.`1 /\ res.`2 = x]
  =   Pr[M1.challenge_indexed() @ &m :
   l = challenge_t res.`1 /\ res.`2 = x /\ 0 <= res.`1]. 
byequiv.
proc. inline M(Syscall).bn_rsample. wp.
while (0 <= i0{1} /\ ={i0,byte_p, byte_z}). wp.  simplify.
call (_: true).  wp. sim. wp. 
call (_:true). sim. wp. 
call (_:true).  sim. wp. 
skip. progress. smt(). wp.
call (_: true).  sim. wp.
call (_: true ).  sim. wp.
skip. progress. auto. auto.
have -> : Pr[M1.challenge_indexed() @ &m :
   inv (-1) challenge_t l = res.`1 /\ res.`2 = x] 
 = Pr[M1.challenge_indexed() @ &m :
   inv (-1) challenge_t l = res.`1 /\ res.`2 = x /\ 0 <= res.`1].
byequiv.
proc. inline M(Syscall).bn_rsample. wp.
while (0 <= i0{1} /\ ={i0,byte_p, byte_z}). wp.  simplify.
call (_: true).  wp. sim. wp. 
call (_:true). sim. wp. 
call (_:true).  sim. wp. 
skip. progress. smt(). wp.
call (_: true).  sim. wp.
call (_: true ).  sim. wp.
skip. progress. auto. auto.
rewrite Pr[mu_eq].
progress.
rewrite invP. apply challenge_t_inj. auto.  
have : exists z, (challenge_t z) = l.
apply (choiceEx (-1) challenge_t l res{hr}.`1) . apply H. smt().
elim. progress.
rewrite - H.
rewrite invP.
apply challenge_t_inj. auto.
auto.
qed.


require import W64_SchnorrExtract.
module M2 = W64_SchnorrExtract.M(W64_SchnorrExtract.Syscall).  

lemma M1_M2_challenge :
  equiv  [ M1.challenge_indexed ~ M2.challenge_indexed
    : true ==> ={res}  ].
proof. proc.
seq 6 3  : (={exp_order}).
wp. call(_:true). sim. wp. skip. progress.
seq 1 1 : (aux_0{1} = i{2} /\ aux{1} = challenge_0{2}).
sim.
call (_: ={arg} ==> ={res}). proc. sim.
call (_:true). wp.  while (={a,i}). wp.  skip. progress. wp. skip. progress.
wp.  skip. progress.
skip.  progress. wp.  auto.
qed.

require import Ring_ops_proof.
require import Ring_ops_spec.
require import UniformSampling_Abstract.
require import UniformSampling_Concrete.


equiv rsample_cspec_equiv:
 M1.challenge_indexed ~ CSpecFp.rsample:
   Constants.q = a{2}
  ==> W64xN.valR res{1}.`2 = res{2}.`2 /\ res{1}.`1 = res{2}.`1.
transitivity M2.challenge_indexed
 (={arg} ==> ={res})
 (Constants.q = a{2}
  ==> W64xN.valR res{1}.`2 = res{2}.`2 /\ res{1}.`1 = res{2}.`1).
progress. smt(). progress.
conseq M1_M2_challenge. 
proc*.
inline M2.challenge_indexed.
wp.
call rsample_cspec.
call {1} Constants.bn_set_q_correct.
wp. skip. progress.
qed.


lemma challenge_cspec_pr  i x &m : 
  Pr[ M1.challenge_indexed() @ &m : res = (i,x)  ]
   = Pr[ CSpecFp.rsample(Constants.q) @ &m : res = (i, W64xN.valR x)  ].
byequiv.
conseq rsample_cspec_equiv. progress. progress. smt().
smt(@W64xN). auto. auto.
qed.


lemma challenge_index_pos &m  : Pr[M1.challenge_indexed() @ &m : res.`1 <= 0 ] = 0%r.
byphoare (_: true ==> _);auto. hoare.
proc.  simplify.
inline W64_SchnorrExtract_ct.M(W64_SchnorrExtract_ct.Syscall).bn_rsample.
unroll 25. rcondt 25. wp. wp. 
call (_:true). wp. auto. wp. 
call (_:true). wp. auto. wp. skip. auto.
wp.
while (0 < i0). wp. call (_:true). auto. wp.  call (_:true). auto.  wp. 
inline*. wp. rnd. wp. skip. progress.  smt().
wp. call (_:true). auto.  wp.  
call (_:true). auto. wp. 
call (_:true). auto. wp. 
call (_:true). auto. wp. 
call (_:true). wp.  auto. wp.
skip. progress. smt().
qed.

import W64xN.


op g l : real 
 = if inv (-1) challenge_t l <= 0 then 0%r else 
     mu D (predC (RSP Constants.q)) ^ (inv (-1) challenge_t l - 1)
       * (1%r / Ring_ops_spec.M%r).

        
lemma leakfree1 &m x  l: (glob M1){m} = [] 
  => Pr[ M1.challenge_indexed() @ &m : M1.leakages = l  /\ res.`2 = x  ] = if (Constants.q <= valR x) then 0%r else (g  l).
      progress.
   rewrite  (challenge_leakages_inv x l &m);auto.
case (inv (-1) challenge_t l <= 0). 
move => q. rewrite /g. rewrite q.  simplify. 
  have : Pr[M1.challenge_indexed() @ &m :
   inv (-1) challenge_t l = res.`1 /\ res.`2 = x] 
    <= Pr[M1.challenge_indexed() @ &m : res.`1 <= 0 ]. simplify. rewrite Pr[mu_sub]. smt().
   auto. smt(challenge_index_pos @Distr).
move => q.
have -> : 
 Pr[M1.challenge_indexed() @ &m :
   inv (-1) challenge_t l = res.`1 /\ res.`2 = x]
  = Pr[M1.challenge_indexed() @ &m :
   res = (inv (-1) challenge_t l , x) ]. rewrite Pr[mu_eq]. smt(). auto.
case (valR x < Constants.q) => case1.
rewrite challenge_cspec_pr.
rewrite rsample_pr.   smt().
rewrite /RSP. auto.
rewrite /z. 
have ->: mu1 D (W64xN.valR x) = 1%r / Ring_ops_spec.M%r.
rewrite duniform1E_uniq. smt(@List).
 have f1 : 0 <= W64xN.valR x < Ring_ops_spec.M. smt(@W64xN).  smt(@Distr @List). 
rewrite /g.   smt().
have : Pr[M1.challenge_indexed() @ &m :
   res.`2 = x] = 0%r.
  have -> : Pr[M1.challenge_indexed() @ &m :
     res.`2 =  x] = Pr[ CSpecFp.rsample(Constants.q) @ &m : res.`2 =  W64xN.valR x ].
  byequiv. conseq rsample_cspec_equiv. auto. progress. rewrite H0.  auto.  smt(@W64xN). auto. auto.
  apply rsample_pr_out. auto.
smt(@Distr).
qed.


op h : real = 1%r/Constants.q%r. 

lemma leakfree2 &m x: 
 Pr[ M1.challenge_indexed() @ &m : res.`2 = x ] 
  = if (Constants.q <= valR x) then 0%r else h .    
proof. 
 have ->: Pr[ M1.challenge_indexed() @ &m : res.`2 = x ] =
  Pr[ CSpecFp.rsample(Constants.q) @ &m : res.`2 =  W64xN.valR x ].
  byequiv. conseq rsample_cspec_equiv. auto. 
progress. rewrite - H. auto. smt(@W64xN). auto. auto.
rewrite /h.
case: (Constants.q <= valR x). move => alx.
rewrite rsample_pr_out. smt(). auto.
move => a_less_x.
rewrite rsample_uni. auto. smt(@W64xN).
smt(). auto.
qed.

op f l = h / g l.

lemma rsample_leakfree_indexed l a &m: (glob M1){m} = [] 
 =>  let v = Pr[ M1.challenge_indexed() @ &m : res.`2 = a  ] in 
     let w = Pr[ M1.challenge_indexed() @ &m : M1.leakages = l  /\ res.`2 = a  ] in 
  0%r < w => v/w 
  = f  l.
move => l_empty v w f1.
have : (valR a < Constants.q).
 case (Constants.q <= valR a) => h.
 have : w <= 0%r.
 rewrite /w.  
 rewrite (leakfree1 &m a l _). auto.
 rewrite h. auto.
 smt(). 
 smt().
move => a_less_pin.
rewrite /f.
rewrite  (leakfree1 &m a l _). auto.
rewrite  (leakfree2 &m a ). auto. 
smt().
qed.


lemma rsample_leakfree l a &m: (glob M1){m} = [] 
 =>  let v = Pr[ M1.challenge() @ &m : res = a  ] in 
     let w = Pr[ M1.challenge() @ &m : M1.leakages = l  /\ res = a  ] in 
  0%r < w => v/w 
  = f  l.
move => ge v w .
have -> : Pr[ M1.challenge() @ &m : res = a  ] = Pr[ M1.challenge_indexed() @ &m : res.`2 = a  ].
byequiv. proc. wp.
wp. call (_:true). sim. 
wp. call (_:true). sim. 
wp.  skip. progress. auto. auto.

have -> : Pr[ M1.challenge() @ &m : M1.leakages = l /\ res = a  ] = Pr[ M1.challenge_indexed() @ &m : M1.leakages = l /\ res.`2 = a  ].
byequiv (_: ={M1.leakages} ==> _). proc. wp.
wp. call (_: ={M1.leakages}). sim. 
wp. call (_: ={M1.leakages}). sim. 
wp.  skip. progress. auto. auto.
apply (rsample_leakfree_indexed l a &m).
auto. 
qed.

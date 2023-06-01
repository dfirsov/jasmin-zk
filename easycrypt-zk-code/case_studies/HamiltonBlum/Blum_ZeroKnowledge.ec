pragma Goals:printall.
require import AllCore DBool Bool List Distr Int AuxResults DJoin.
require import Permutation Blum_Basics.
require Blum_Sim1Property.



require RewBasics.
clone import RewBasics as Rew with type sbits <- sbits.

op stat : hc_stat.
op wit : hc_wit.

clone import Blum_Sim1Property as BSP with op statProb <- stat,
                                           op statWit <- wit.


import OSS.
clone import ZK.SequentialComposition.



section.


declare axiom stat_wit : zk_relation stat wit.
declare module V <: RewMaliciousVerifier{-HP, -ZK.Hyb.HybOrcl,-ZK.Hyb.Count}.
declare module D <: ZKDistinguisher{-HP,-ZK.Hyb.HybOrcl,-ZK.Hyb.Count}.

declare axiom Sim1_run_ll : islossless Sim1(V).run.
declare axiom V_summitup_ll : islossless V.summitup. 
declare axiom V_challenge_ll : islossless V.challenge.
declare axiom D_guess_ll : islossless D.guess.
declare axiom P_response_ll : islossless HP.response.
declare axiom P_commitment_ll : islossless HP.commitment.
declare axiom simn_simulate_ll : forall (V0 <: RewMaliciousVerifier), islossless V0.challenge 
  => islossless V0.summitup => islossless SimN(Sim1, V0).simulate.
declare axiom D_guess_prop : equiv[ D.guess ~ D.guess : ={glob V, arg} ==> ={res} ].

declare axiom rewindable_V_plus :
        (exists (f : glob V -> sbits),
         injective f /\
         (forall &m, Pr[ V.getState() @ &m : (glob V) = ((glob V){m})
                                               /\ res = f ((glob V){m}) ] = 1%r) /\
         (forall &m b (x: glob V), b = f x =>
           Pr[V.setState(b) @ &m : glob V = x] = 1%r) /\
         islossless V.setState).

                                     

lemma hc_statistical_zk   &m:
        zk_relation stat wit => 
        let real_prob = Pr[ZKReal(HP, V, D).run(stat, wit) @ &m : res] in
        let ideal_prob = Pr[ZKIdeal(SimN(Sim1), V, D).run(stat, wit) @ &m : res] in
          `|ideal_prob - real_prob| <= (2%r * eps + 20%r * eps2) + 2%r * (1%r- (1%r/2%r - eps2)) ^ OSS.N.
proof.
progress.
apply (Statistical.statistical_zk (2%r * eps + 20%r * eps2) (1%r/2%r - eps2) _ HP Sim1 V D _ _ _ _ _  stat wit &m). smt(eps_ge0 eps2_ge0). apply Sim1_run_ll. apply V_summitup_ll. apply V_challenge_ll. 
apply D_guess_ll. 
proc*. call D_guess_prop. skip.  auto.
move => x.
conseq (sim1_rew_ph V _ _ _ _ _  x.`1).  auto. auto.
apply V_summitup_ll. apply V_challenge_ll. apply P_response_ll. apply P_commitment_ll.
apply (rewindable_A_plus V). apply rewindable_V_plus.
apply (sim1_error stat_wit V D  _ _  _ _ _  _ &m   _ );auto.   apply V_summitup_ll. 
apply D_guess_ll. apply V_summitup_ll. apply V_challenge_ll. 
conseq D_guess_prop. auto. apply (rewindable_A_plus V). apply rewindable_V_plus.  apply D_guess_ll. apply V_summitup_ll.
progress. 
apply (sim1_succ stat_wit V D _ _ _ _ _ _ &m  ).  apply V_summitup_ll. apply D_guess_ll. apply V_summitup_ll.
apply V_challenge_ll.
 progress.
conseq D_guess_prop. auto.
apply (rewindable_A_plus V). apply rewindable_V_plus.
auto.
qed.


lemma hc_statistical_zk_iter &m:
        zk_relation stat wit =>
        let real_prob = Pr[ZKRealAmp(HP, V, D).run(stat, wit) @ &m : res] in
        let ideal_prob = Pr[ZKIdeal(SimAmp(SimN(Sim1)), V, D).run(stat, wit) @ &m : res] in
          `|ideal_prob - real_prob| <= ZK.n%r * ((2%r * eps + 20%r * eps2) + 2%r * (1%r- (1%r/2%r - eps2)) ^ OSS.N).
progress.
apply (zk_seq HP (SimN(Sim1)) V D _ _ _ _ _ _ _ &m  ((2%r * eps + 20%r * eps2) + 2%r * (1%r- (1%r/2%r - eps2)) ^ OSS.N) stat wit). 
progress.  
apply (simn_simulate_ll V0). auto. auto.
apply V_summitup_ll. apply V_challenge_ll. apply P_response_ll.
apply P_commitment_ll. apply D_guess_ll.
apply D_guess_prop.
smt(eps2_ge0 eps_ge0 N_pos @RealExp).
progress.
apply (Statistical.statistical_zk (2%r * eps + 20%r * eps2) (1%r/2%r - eps2) _ HP Sim1  V (Di(D, SimN(Sim1), V))  _ _ _ _ _ stat wit &n ). smt(eps_ge0 eps2_ge0).
apply Sim1_run_ll.
apply V_summitup_ll. apply V_challenge_ll. 
proc. 
call D_guess_ll. sp.
while (true) (ZK.n - ZK.Hyb.HybOrcl.l). progress.
wp. call (simn_simulate_ll V). apply V_challenge_ll. apply V_summitup_ll.  skip. smt().
skip. smt().
proc. 
call D_guess_prop. sim.
progress.
proc*.  
call (sim1_rew_ph V _ _ _ _ _ x.`1).  apply V_summitup_ll.
apply V_challenge_ll. apply P_response_ll.
apply P_commitment_ll. 
apply (rewindable_A_plus V). apply rewindable_V_plus.  skip. auto. progress.
rewrite (sim1_error stat_wit V (Di(D, SimN(Sim1), V))).
apply V_summitup_ll.  
proc. 
call D_guess_ll. sp.
while (true) (ZK.n - ZK.Hyb.HybOrcl.l). progress.
wp. call (simn_simulate_ll V).  apply V_challenge_ll. apply V_summitup_ll. 
skip. smt(). skip. smt().
apply V_summitup_ll. apply V_challenge_ll. 
proc. call D_guess_prop. sim.  progress.
apply (rewindable_A_plus V). apply rewindable_V_plus.
proc. call D_guess_ll. sp.
while (true) (ZK.n - ZK.Hyb.HybOrcl.l). progress. wp. 
call (simn_simulate_ll V).  apply V_challenge_ll. apply V_summitup_ll.  skip. smt().
skip. smt(). apply V_summitup_ll. auto.
progress.
rewrite (sim1_succ stat_wit V D _ _ _ _  _  _ &n ). 
apply V_summitup_ll.
apply D_guess_ll. 
apply V_summitup_ll.
apply V_challenge_ll.
conseq D_guess_prop.  auto. 
apply (rewindable_A_plus V).
apply rewindable_V_plus. 
auto. 
qed.


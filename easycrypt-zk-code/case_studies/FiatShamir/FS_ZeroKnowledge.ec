pragma Goals:printall.
require import AllCore DBool Bool List Distr Int AuxResults DJoin.
require import FS_Basics FS_Sim1Property.
import OSS.

clone import ZK.SequentialComposition
proof*.

import Statistical.

(* (* importing statistical zero knowledge  *) *)
(* clone import Statistical with op epsilon <- 0%r,   (* conditional probability of indistinguishability *) *)
(*                               op sigma <- 1%r/2%r (* success-event *) *)
(* proof*. *)
(* realize epsilon_pos. auto. qed. *)

(* importing the rewinding framework *)
require  RewBasics.
clone import RewBasics as Rew with
  type sbits <- sbits,
  op pair_sbits <- FS_pair_sbits,
  op unpair <- FS_unpair
proof *.
realize ips. apply FS_ips. qed.
realize unpair_pair. apply FS_unpair_pair. qed.


section. (* modules and their losslessness assumptions  *)
declare module V <: RewMaliciousVerifier{-ZK.Hyb.HybOrcl,-ZK.Hyb.Count,-HP}.
declare module D <: ZKDistinguisher{-ZK.Hyb.HybOrcl,-ZK.Hyb.Count, -HP}.

declare axiom Sim1_run_ll : forall (V0 <: RewMaliciousVerifier), islossless V0.challenge 
  => islossless V0.summitup => islossless Sim1(V0).run.
declare axiom V_summitup_ll : islossless V.summitup. 
declare axiom V_challenge_ll : islossless V.challenge.
declare axiom D_guess_ll : islossless D.guess.
declare axiom P_response_ll : islossless HP.response.
declare axiom P_commitment_ll : islossless HP.commitment.
declare axiom simn_simulate_ll : forall (V0 <: RewMaliciousVerifier), islossless V0.challenge 
  => islossless V0.summitup => islossless SimN(Sim1, V0).simulate.
declare axiom D_guess_prop : equiv[ D.guess ~ D.guess : ={glob V, arg} ==> ={res} ].


(* rewindability assumption *)
declare axiom rewindable_V_plus :
        (exists (f : glob V -> sbits),
         injective f /\
         (forall &m, Pr[ V.getState() @ &m : (glob V) = ((glob V){m})
                                          /\ res = f ((glob V){m} ) ] = 1%r) /\
         (forall &m b (x: glob V), b = f x =>
           Pr[V.setState(b) @ &m : glob V = x] = 1%r) /\
         islossless V.setState).


(* one-round zero-knowledge *)

lemma qr_statistical_zk stat wit &m:
        zk_relation stat wit =>
        let real_prob = Pr[ZKReal(HP, V, D).run(stat, wit) @ &m : res] in
        let ideal_prob = Pr[ZKIdeal(SimN(Sim1), V, D).run(stat, wit) @ &m : res] in
          `|ideal_prob - real_prob| <= 2%r * (1%r / 2%r) ^ FS_Sim1Property.N.
proof.
  progress.
apply (statistical_zk 0%r (1%r/2%r) _ HP Sim1  V D _ _ _ _ _  stat wit &m);auto. apply Sim1_run_ll. apply V_summitup_ll. apply V_challenge_ll. 

apply D_guess_ll.  conseq  D_guess_prop. auto.
   apply (sim1_rew_ph V). 
 apply V_summitup_ll. apply V_challenge_ll.  apply (rewindable_A_plus V). 
apply rewindable_V_plus.
progress. 
rewrite (sim1_error V D _ _  _ _).  apply (rewindable_A_plus V).
apply rewindable_V_plus.
apply V_summitup_ll.
apply V_challenge_ll. apply D_guess_ll. 
conseq D_guess_prop. auto. auto. auto.
progress.
rewrite (sim1_succ V D _ _ _ _ _ &m stat). apply (rewindable_A_plus V).
apply rewindable_V_plus.
apply V_summitup_ll.
apply V_challenge_ll. apply D_guess_ll. conseq D_guess_prop. auto. auto. smt(). auto.
qed.


       
(* iterated zero-knowledge  *)
(* Note 1: The proof mostly consists of establishing "losslessness" of involved modules. *)
(* Note 2: ZK.n and OSS.N are abstract parameters which could be instantiated when cloning the ZK theory. The reason for them
being parameters is a restriction induced by HybridArgument formalization which uses global paremters instead of universally quantified    ones *)
lemma qr_statistical_zk_iter stat wit &m:
        zk_relation stat wit =>
        let real_prob = Pr[ZKRealAmp(HP, V, D).run(stat, wit) @ &m : res] in
        let ideal_prob = Pr[ZKIdeal(SimAmp(SimN(Sim1)), V, D).run(stat, wit) @ &m : res] in
          `|ideal_prob - real_prob| <= ZK.n%r * (2%r * (1%r / 2%r) ^  OSS.N).
progress.
apply (zk_seq HP (SimN(Sim1)) V D _ _ _ _ _ _ _ &m  (2%r * (1%r / 2%r) ^ FS_Sim1Property.N) stat wit). 
progress.  apply (simn_simulate_ll V0). auto. auto.
apply V_summitup_ll. apply V_challenge_ll. apply P_response_ll.
apply P_commitment_ll. apply D_guess_ll.  conseq D_guess_prop. 
smt(@RealExp). progress.
apply (statistical_zk 0%r (1%r/2%r) _ HP Sim1  V (Di(D, SimN(Sim1), V)) _ _ _ _ _ stat wit &n); auto.
apply Sim1_run_ll. apply V_summitup_ll. apply V_challenge_ll.
proc. 
call D_guess_ll. sp.
while (true) (FS_Sim1Property.n - ZK.Hyb.HybOrcl.l). progress.
wp. call (simn_simulate_ll V). apply V_challenge_ll. apply V_summitup_ll.  skip. smt().
skip. smt(). auto. auto. progress.
proc. 
call D_guess_prop. sim.
progress.
proc*.  
call (sim1_rew_ph V _ _ _ x).  apply V_summitup_ll.
apply V_challenge_ll. apply (rewindable_A_plus V).
apply rewindable_V_plus. skip. auto. progress.
rewrite (sim1_succ V (Di(D, SimN(Sim1), V))).
apply (rewindable_A_plus V). apply rewindable_V_plus.
apply V_summitup_ll. apply V_challenge_ll. 
proc. 
call D_guess_ll. sp.
while (true) (FS_Sim1Property.n - ZK.Hyb.HybOrcl.l). progress.
wp. call (simn_simulate_ll V).  apply V_challenge_ll. apply V_summitup_ll. 
skip. smt(). skip. smt().
auto. auto. progress.
proc. call D_guess_prop. sim. smt().
rewrite - (sim1_succ V D _ _ _ _  _ &n stat).
apply (rewindable_A_plus V). apply rewindable_V_plus. apply V_summitup_ll.
apply V_challenge_ll. apply D_guess_ll. 
conseq D_guess_prop. auto. smt().
rewrite   (sim1_error V (Di(D, SimN(Sim1), V)) _ _ _ _  _ &n stat wit). 
apply (rewindable_A_plus V).
apply rewindable_V_plus. apply V_summitup_ll.
apply V_challenge_ll. 
proc.
call D_guess_ll. sp.
while (true) (ZK.n - ZK.Hyb.HybOrcl.l). progress.
wp. call (simn_simulate_ll V). apply V_challenge_ll. apply V_summitup_ll.  skip. smt().
skip. smt(). proc. call D_guess_prop. sim. auto. 
progress.
rewrite (sim1_succ V D _ _ _ _  _ &n stat). apply (rewindable_A_plus V).
apply rewindable_V_plus. apply V_summitup_ll.
apply V_challenge_ll. apply D_guess_ll. 
proc*.
call D_guess_prop. skip. auto. smt().
auto. 
qed.


end section.

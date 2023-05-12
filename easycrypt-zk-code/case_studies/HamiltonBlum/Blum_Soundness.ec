pragma Goals:printall.
require import AllCore DBool Bool List Distr Int AuxResults DJoin RealExp.
require import  Blum_Basics.

require import Blum_SpecialSoundness.


section.
declare module P <: RewMaliciousProver {-HV}.

declare axiom P_response_ll : islossless P.response.
declare axiom P_commitment_ll : islossless P.commitment.
op ss : hc_stat.

declare axiom P_rewindable : exists (f : (glob P) -> sbits),
  injective f /\
  (forall &m0,
     Pr[P.getState() @ &m0 : (glob P) = (glob P){m0} /\ res = f (glob P){m0}] =
     1%r) /\
  (forall &m0 (b : sbits) (x : (glob P)),
     b = f x => Pr[P.setState(b) @ &m0 : (glob P) = x] = 1%r) /\
  islossless P.setState.


clone import SSB as SSB with op ss <- ss.

lemma hc_computational_soundness &m :
    ! in_language soundness_relation ss =>
     Pr[Soundness(P, HV).run(ss) @ &m : res]
     <= sqrt (Pr[BindingExperiment(SpecialSoundnessBinder(SpecialSoundnessAdversary(P))).main() @ &m : res]) + 1%r/2%r.
proof.  progress.
apply (Computational.computational_soundness P _ _ _ &m ss).  apply P_response_ll. apply P_commitment_ll.
apply P_rewindable. auto.
apply (hc_computational_special_soundness_binding (SpecialSoundnessAdversary(P)) &m).
qed.

end section.

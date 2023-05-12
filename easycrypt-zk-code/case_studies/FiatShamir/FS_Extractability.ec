pragma Goals:printall.
require import AllCore.
require import AuxResults FS_Basics List.

require import FS_SpecialSoundness.

section.
declare module P <: RewMaliciousProver {-HV}.
declare axiom P_response_ll : islossless P.response.
declare axiom P_commitment_ll : islossless P.commitment.

(* rewindability assumption *)
declare axiom rewindable_P_plus :
        (exists (f : glob P -> sbits),
         injective f /\
         (forall &m, Pr[ P.getState() @ &m : (glob P) = ((glob P){m})
                                          /\ res = f ((glob P){m} ) ] = 1%r) /\
         (forall &m b (x: glob P), b = f x =>
           Pr[P.setState(b) @ &m : glob P = x] = 1%r) /\
         islossless P.setState).


(* automatically implying proof-of-knowledge from special soundness  *)
lemma qr_statistical_PoK &m  s: 
  Pr[Extractor(P).extract(s) @ &m : soundness_relation s res ] >=
   (Pr[Soundness(P, HV).run(s) @ &m : res]^2
     - (1%r/2%r) * Pr[Soundness(P, HV).run(s) @ &m : res]).
apply (SpecialSoundness.Perfect.statistical_extractability P  _ _ _ _ &m s  ). apply rewindable_P_plus. apply P_response_ll. 
apply P_commitment_ll. 
apply qr_perfect_special_soundness.
qed.

end section.

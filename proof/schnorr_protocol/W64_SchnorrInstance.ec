require import AllCore Distr DInterval List Int IntDiv.

from Jasmin require import JModel JBigNum.
require import BigNum_spec.
import W64xN. 
require import W64_SchnorrProtocol.
require  W64_Zp_SchnorrCorrespondance.
require Constants.
require import ConstantsValidation.

(* the only undischarged assumptions *)
axiom p_prime : prime Constants.p.
axiom q_prime : prime Constants.q.

(* parameters for rewindability framework  *)
op pair_sbits : sbits * sbits -> sbits.
op unpair : sbits -> sbits * sbits.
axiom pair_sibts_inj : injective pair_sbits.
axiom unpair_pair: forall (x : sbits * sbits), unpair (pair_sbits x) = x.


clone W64_Zp_SchnorrCorrespondance as W64_Zp_Corr with
  op p <= Constants.p,
  op q <= Constants.q,
  op bp <= Constants.bp,
  op bq <= Constants.bq,
  op g <= Constants.g,
  op pair_sbits <= pair_sbits,
  op unpair  <= unpair,
  op ZpC.p <= Constants.p
proof*.
realize bn_glob_p_correct. apply Constants.bn_glob_p_correct. qed.
realize bn_glob_q_correct. apply Constants.bn_glob_q_correct. qed.
realize bn_glob_g_correct. apply Constants.bn_glob_g_correct. qed.
realize bn_glob_bp_correct. apply Constants.bn_glob_bp_correct. qed.
realize bn_glob_bq_correct. apply Constants.bn_glob_bq_correct. qed.
realize g_less_p. split. auto. auto. qed.
realize p_less_modulusR. split. auto. auto. qed.
realize q_val_prop1. move => x.
  have fact1 : valR x < modulusR. smt(@W64xN).
  have fact2 : modulusR < Constants.q * Constants.q. auto.
  smt(). qed.
realize q_less_p. split. auto. auto. qed.
realize q_prime. apply q_prime. qed.
realize p_prime. apply p_prime. qed.
realize bp_correct.
 have ->: 4 ^ (dnlimbs * nlimbs) = Constants.barrett_numerator. simplify. auto.
 have  -> : Constants.barrett_numerator = (Constants.p * Constants.barrett_numerator_div_p + Constants.barrett_numerator_mod_p). smt(pq_euclid).
  smt(@IntDiv). qed.
realize bq_correct.
 have ->: 4 ^ (dnlimbs * nlimbs) = Constants.barrett_numerator. simplify. auto.
 have  -> : Constants.barrett_numerator = (Constants.p * Constants.barrett_numerator_div_p + Constants.barrett_numerator_mod_p). smt(pq_euclid).
  smt(@IntDiv). qed.
realize pair_sibts_inj. apply pair_sibts_inj. qed.
realize unpair_pair. apply unpair_pair. qed.
realize g_correct. apply generator_is_valid. qed.


(* COMPLETENESS PROPERTY  *)
require W64_SchnorrCompleteness.
clone W64_SchnorrCompleteness as CompletenessTheory with theory Ind <- W64_Zp_Corr
proof*.

section Completeness.

lemma completeness_for_instance ss ww &m: W64_Zp_Corr.completeness_relationJ ss ww =>
 Pr[CompletenessJ(JProver,JVerifier).main(ss,ww)@&m : res] = 1%r.
apply CompletenessTheory.completenessJ. qed.

end section Completeness.
  

(* PROOF-OF-KNOWLEDGE (aka Extractability) PROPERTY  *)
require W64_SchnorrExtractability.
clone W64_SchnorrExtractability as ExtractabilityTheory with theory Ind <- W64_Zp_Corr
proof*.

section Extractability.

declare module P <: ZKRewindableMaliciousProverJ{-W64_Zp_Corr.ZPSP.LSP.HV}.
declare axiom P_response_ll : islossless P.response.
declare axiom P_commitment_ll : islossless P.commitment.

import ExtractabilityTheory.

(* rewindability assumption  *)
declare axiom P_rewindable : exists (f : (glob AWrapE(P)) -> sbits),
  injective f /\
  (forall &m0,
     Pr[AWrapE(P).getState() @ &m0 :
        (glob AWrapE(P)) = (glob AWrapE(P)){m0} /\
        res = f (glob AWrapE(P)){m0}] =
     1%r) /\
  (forall &m0 (b : sbits) (x : (glob AWrapE(P))),
     b = f x => Pr[AWrapE(P).setState(b) @ &m0 : (glob AWrapE(P)) = x] = 1%r) /\
  islossless AWrapE(P).setState.


lemma extractability_for_InstanceJ &m s: 
  Pr[ExtractorJ(P).extract(s)@&m: W64_Zp_Corr.completeness_relationJ  s res ] >=
   (Pr[SoundnessJ(P, JVerifier).main(s) @ &m : res] ^ 2
       - 1%r / 2%r
           * Pr[SoundnessJ(P, JVerifier).main(s) @ &m : res]).
apply (extractabilityJ P P_response_ll P_commitment_ll P_rewindable). 
qed.

end section Extractability.


(* ZERO-KNOWLEDGE PROPERTY *)
abstract theory ZeroKnowledge_for_Instance.

op N : int.                     (* number of tries for SimNJ *)
op n : int.                     (* number of rounds for iterated ZK *)

axiom n_pos : 1 <= n.
axiom N_pos : 0 <= N.

require W64_SchnorrZK.
clone W64_SchnorrZK as ZKTheory 
 with theory Ind <- W64_Zp_Corr,
      op  ZSZK.SZK.n <- n,
      op ZSZK.SZK.N <- N
proof*.
realize ZSZK.SZK.n_pos. apply n_pos. qed.
realize ZSZK.SZK.N_pos. apply N_pos. qed.


section ZeroKnowledge.

declare module V <: RewMaliciousVerifierJ{-W64_Zp_Corr.ZPSP.LSP.HP, -ZKTheory.ZSZK.SZK.ZK.Hyb.Count, -ZKTheory.ZSZK.SZK.ZK.Hyb.HybOrcl}.
declare module D <: ZKDistinguisherJ{-W64_Zp_Corr.ZPSP.LSP.HP, -ZKTheory.ZSZK.SZK.ZK.Hyb.Count, -ZKTheory.ZSZK.SZK.ZK.Hyb.HybOrcl}.

declare axiom V_summitup_ll : islossless V.summitup. 
declare axiom V_challenge_ll : islossless V.challenge.
declare axiom D_guess_ll : islossless D.guess.
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



lemma zero_knowledge_for_instanceJ &m stat wit :
  W64_Zp_Corr.zk_relationJ stat wit =>
  let ideal_prob = Pr[ZKIdealJ(ZKTheory.SimNJ, V, D).run(stat, wit)@&m : res] in
  let real_prob = Pr[ZKRealJ(JProver, V, D).run(stat, wit)@&m : res] in
 `|ideal_prob - real_prob| <= 2%r * ((1%r/2%r) ^ N).
progress.
have ->: inv 2%r = (1%r - 1%r / (size [0; 1])%r). smt(@Real).
apply (ZKTheory.zero_knowledgeJ V D V_summitup_ll V_challenge_ll 
   D_guess_ll D_guess_prop rewindable_V_plus stat wit &m H).
qed.

end section ZeroKnowledge.

end ZeroKnowledge_for_Instance.

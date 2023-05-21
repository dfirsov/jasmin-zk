require import AllCore Distr DInterval List Int IntDiv.

from Jasmin require import JModel JBigNum.
require import Array32 Array64 Array128.
require import Ring_ops_spec.
import W64xN. 
require import W64_SchnorrProtocol.
require  W64_Zp_SchnorrPropreties.
require Constants.
require import ConstantsValidation.

axiom p_prime : prime Constants.p.
axiom q_prime : prime Constants.q.

op pair_sbits : sbits * sbits -> sbits.
op unpair : sbits -> sbits * sbits.
axiom pair_sibts_inj : injective pair_sbits.
axiom unpair_pair: forall (x : sbits * sbits),
                             unpair (pair_sbits x) = x.


require ZModP.
clone import ZModP.ZModField as ZpC 
  with op p <= Constants.p
proof*.
realize prime_p. apply p_prime. qed.


lemma zp_mul (z1 z2 : zmod) : Sub.val (z1 * z2) = (Sub.val z1 * Sub.val z2) %% p. 
by smt(@ZpC). qed.


lemma exps' (s : zmod) : forall n, 0 <= n => Sub.val (ZModpField.exp s n) = (Sub.val s ^ n) %% p.
apply intind. progress. smt(@ZModpField @Sub).
progress.
rewrite exprSr. auto.
rewrite ZModpField.exprSr. auto.
rewrite zp_mul.
rewrite H0.
smt(@IntDiv). 
qed.

lemma zp_eq z1 z2 : (Sub.val z1 = Sub.val z2) = (z1 = z2). smt(@ZpC). qed.

clone import W64_Zp_SchnorrPropreties as W64_Zp_Props with 
  op Ind.p <- Constants.p,
  op Ind.q <- Constants.q,
  op Ind.bp <- Constants.bp,
  op Ind.bq <- Constants.bq,
  op Ind.g <- Constants.g,
  op Ind.pair_sbits <- pair_sbits,
  op Ind.unpair <- unpair,
  theory Ind.ZpC <= ZpC
proof*.
realize Ind.bn_set_p_correct. apply Constants.bn_set_p_correct. qed.
realize Ind.bn_set_q_correct. apply Constants.bn_set_q_correct. qed.
realize Ind.bn_set_bp_correct. apply Constants.bn_set_bp_correct. qed.
realize Ind.bn_set_bq_correct. apply Constants.bn_set_bq_correct. qed.
realize Ind.bn_set_g_correct. apply Constants.bn_set_g_correct. qed.
realize Ind.g_less_p. split. auto. auto. qed.
realize Ind.p_less_modulusR. split. auto. auto. qed.
realize Ind.q_val_prop1. move => x.
  have fact1 : valR x < modulusR. smt(@W64xN).
  have fact2 : modulusR < Constants.q * Constants.q. auto.
  smt(). qed.
realize Ind.q_less_p. split. auto. auto. qed.
realize Ind.q_prime. apply q_prime. qed.
realize Ind.p_prime. apply p_prime. qed.
realize Ind.bp_correct.

 have ->: 4 ^ (dnlimbs * nlimbs) = Constants.barrett_numerator. simplify. auto.
 have  -> : Constants.barrett_numerator = (Constants.p * Constants.barrett_numerator_div_p + Constants.barrett_numerator_mod_p). smt(pq_euclid).
  smt(@IntDiv). qed.
realize Ind.bq_correct.
 have ->: 4 ^ (dnlimbs * nlimbs) = Constants.barrett_numerator. simplify. auto.
 have  -> : Constants.barrett_numerator = (Constants.p * Constants.barrett_numerator_div_p + Constants.barrett_numerator_mod_p). smt(pq_euclid).
  smt(@IntDiv). qed.
realize Ind.pair_sibts_inj. apply pair_sibts_inj. qed.
realize Ind.unpair_pair. apply unpair_pair. qed.
realize Ind.g_correct. apply generator_is_valid. qed.



lemma completenessJ ss ww &m: W64_Zp_Props.Ind.completeness_relationJ ss ww =>
 Pr[CompletenessJ(JProver,JVerifier).main(ss,ww)@&m : res] = 1%r.
apply W64_Zp_Props.completenessJ. qed.

section.

declare module P <: ZKRewindableMaliciousProverJ{-Ind.ZPSP.LSP.HV}.
declare axiom P_response_ll : islossless P.response.
declare axiom P_commitment_ll : islossless P.commitment.

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


lemma extractabilityJ &m s: 
  Pr[ExtractorJ(P).extract(s)@&m: W64_Zp_Props.Ind.completeness_relationJ  s res ] >=
   (Pr[SoundnessJ(P, JVerifier).main(s) @ &m : res] ^ 2
       - 1%r / Constants.q%r
           * Pr[SoundnessJ(P, JVerifier).main(s) @ &m : res]).
have : Pr[ExtractorJ(P).extract(s)@&m: W64_Zp_Props.Ind.completeness_relationJ  s res ] >=
   (Pr[SoundnessJ(P, JVerifier).main(s) @ &m : res] ^ 2
       - 1%r / (size Ind.ZPSP.LSP.EG.DZmodP.Support.enum)%r
           * Pr[SoundnessJ(P, JVerifier).main(s) @ &m : res]).
apply (W64_Zp_Props.extractabilityJ P P_response_ll P_commitment_ll P_rewindable). 
have ->: (size Ind.ZPSP.LSP.EG.DZmodP.Support.enum) = Constants.q.
smt(@Ind.ZPSP.LSP.EG). auto.
qed.

end section.

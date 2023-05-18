require import AllCore Distr DInterval List Int IntDiv.

from Jasmin require import JModel JBigNum.
require import Array32 Array64 Array128.

require import W64_SchnorrProtocol.
require import Ring_ops_spec.
(* import Zp DZmodP  Sub . *)

import W64xN. 

require import W64_Zp_SchnorrIndistinguishability.
import ZPSP.
import Zp.

module CompletenessJ(P:ZKProverJ,V:ZKVerifierJ) = {
  proc main(s:W64.t Array32.t, w:W64.t Array32.t) = {
    var z, c, r,t,v;
    (z,r) <@ P.commitment();
    c <@ V.challenge();
    t <@ P.response(w,r,c);
    v <@ V.verify(s,z,c,t);
    return (v <> W64.zero);
  }
}.


lemma completeness_same ss ww &m:
 Pr[ CompletenessG(SchnorrProver,SchnorrVerifier).main(ZPSP.Zp.inzmod (W64xN.valR ss) , (W64xN.valR ww))@&m : res]
 = Pr[CompletenessJ(JProver,JVerifier).main(ss,ww)@&m : res].
proof.
byequiv.
proc.
call verify_eq.
call response_eq.
call challenge_eq.
call commitment_eq.
simplify. skip. progress.
smt. smt. rewrite H. 
have v : valR result_R.`1 < ZPSP.Zp.p. rewrite - H. smt(@Zp).
have : valR result_R.`1 %% ZPSP.Zp.p = valR result_R.`1. smt (@IntDiv @Zp).
smt().
rewrite - H2.
smt.
smt.
auto. auto.
qed.

import MLC.
lemma qqqq x : 0 <= x => (Constants.g ^ x %% Zp.p) <> 0.
move => xnonzero.
case ((Constants.g ^ x %% Zp.p = 0)).
move => q. simplify.
  have : unit (ZModpField.exp g x ).
  smt.
rewrite /unit. elim. 
move => y.
have : Sub.val (y * (ZModpField.exp g x) )= ((Sub.val y) * (Sub.val (ZModpField.exp g x)) %% Zp.p). 
smt.
have ->: (Sub.val ((ZModpField.exp g x))) = ((Sub.val g) ^ x) %% p.
 have -> : (ZModpField.exp g x) = g ^^ x. auto.
rewrite  - exps. assumption.
smt.
move => eq1 eq2.
have o1 : (Sub.val y) * ((Sub.val g) ^ x %% p) %% Zp.p = 0.
  have -> : (Sub.val g) = Constants.g. smt(@Sub). rewrite q. simplify. auto.
have o2 : (Sub.val y) * ((Sub.val g) ^ x %% p) %% Zp.p = 1.
 rewrite - eq1. rewrite eq2. smt(@Sub).
smt().
auto.
qed.


lemma completenessJ ss ww &m: completeness_relationJ ss ww =>
 Pr[CompletenessJ(JProver,JVerifier).main(ss,ww)@&m : res] = 1%r.
move => compl_rel.
rewrite - completeness_same.
apply  (ZPSP.completenessG (ZPSP.Zp.inzmod (W64xN.valR ss)) (W64xN.valR ww) &m).
rewrite - (completness_compat ss ww). auto. 
qed.

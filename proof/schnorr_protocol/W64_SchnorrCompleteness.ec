require import AllCore Distr DInterval List Int IntDiv.

from Jasmin require import JModel JBigNum.
from Jasmin require import Array32 Array64 Array128.

require import ZK_SchnorrBasics.
require import Zp_SchnorrProtocol.
require import W64_SchnorrProtocol.
require import W64_Zp_SchnorrIndistinguishability.
require import Ring_ops_spec.
import Zp DZmodP.
import W64xN Sub R. 

module CompletenessJ(P:ZKProverJ,V:ZKVerifierJ) = {
  proc main(s:W64xN, w:W64xN) = {
    var z, c, r,t,v;
    (z,r) <@ P.commitment();
    c <@ V.challenge();
    t <@ P.response(w,r,c);
    v <@ V.verify(s,z,c,t);
    return (v <> W64.zero);
  }
}.


lemma completeness ss ww &m:
 Pr[ CompletenessG(SchnorrProver,SchnorrVerifier).main(inzp (W64xN.valR ss) , (W64xN.valR ww))@&m : res]
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
have v : valR result_R.`1 < p. rewrite - H. smt(@Zp).
have : valR result_R.`1 %% p = valR result_R.`1. smt (@IntDiv @Zp).
smt().
rewrite - H2.
smt.
smt.
auto. auto.
qed.

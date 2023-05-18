require import AllCore Distr DInterval List Int IntDiv.
from Jasmin require import JModel JBigNum.
require import Array32 Array64 Array128.

require import W64_Zp_SchnorrIndistinguishability.
require import W64_SchnorrProtocol.
require import Ring_ops_spec.
import ZPSP.
import Zp.

import Zp DZmodP.
import W64xN Sub R. 

module SoundnessJ(P:ZKMaliciousProverJ, V:ZKVerifierJ) = {
  proc main(s:W64.t Array32.t) = {
    var z, c,t,v;
    z <@ P.commitment();
    c <@ V.challenge();
    t <@ P.response(c);
    v <@ V.verify(s,z,c,t);
    return (v <> W64.zero);
  }
}.

module  AWrap(A:ZKMaliciousProverJ) : ZKMaliciousProverG = {
  proc commitment() : commitment  = {
     var c;
     c <@ A.commitment();
     return (inzmod (valR c ));
  }
  proc response(c:challenge) : response = {
   var r;
   r <@ A.response(bn_ofint c);
   return (valR r);
  }  
}.


lemma soundness_same (s : W64.t Array32.t) &m : forall (A <: ZKMaliciousProverJ),
   Pr[ SoundnessJ(A,JVerifier).main(s)@&m : res]
   = Pr[ SoundnessG(AWrap(A),SchnorrVerifier).run(inzmod (W64xN.valR s))@&m : res].
move => A. byequiv. proc.
symmetry. call verify_eq.
inline AWrap(A).response.
wp. call (_:true).
wp. 
call challenge_eq.
inline AWrap(A).commitment.
wp. call (_:true). simplify. skip.
progress. smt. smt. smt. smt. auto. auto.
qed.

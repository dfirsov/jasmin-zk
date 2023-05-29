require import AllCore.
from Jasmin require import JModel.


require import W64_SchnorrExtract.
require import BigNum_spec.

module JProver = M(Syscall).
module JVerifier = M(Syscall).

module type ZKProverJ = {
  proc response (witness0: W64xN.R.t, secret_power:W64xN.R.t,
                 challenge:W64xN.R.t) : W64xN.R.t 
  proc commitment () : W64xN.R.t * W64xN.R.t  
}.


module type ZKMaliciousProverJ = {
  proc commitment() : W64xN.R.t 
  proc response(challenge:W64xN.R.t) : W64xN.R.t 
}.


module type ZKVerifierJ = {
   proc verify(statement : W64xN.R.t, commitment : W64xN.R.t, challenge_0 : W64xN.R.t, response : W64xN.R.t) :
    W64.t  
  proc challenge() : W64xN.R.t 
}.


module CompletenessJ(P:ZKProverJ,V:ZKVerifierJ) = {
  proc main(s:W64xN.R.t, w:W64xN.R.t) = {
    var z, c, r,t,v;
    (z,r) <@ P.commitment();
    c <@ V.challenge();
    t <@ P.response(w,r,c);
    v <@ V.verify(s,z,c,t);
    return (v <> W64.zero);
  }
}.



module SoundnessJ(P:ZKMaliciousProverJ, V:ZKVerifierJ) = {
  proc main(s:W64xN.R.t) = {
    var z, c,t,v;
    z <@ P.commitment();
    c <@ V.challenge();
    t <@ P.response(c);
    v <@ V.verify(s,z,c,t);
    return (v <> W64.zero);
  }
}.



type sbits.                     (* rewinding parameter type *)


module type ZKRewindableMaliciousProverJ = {
  proc response (challenge:W64xN.R.t) : W64xN.R.t
  proc commitment () : W64xN.R.t 
  (* rewinding interface *)
  proc getState() : sbits 
  proc setState(b : sbits) : unit 
}.


module type ExtractorJ(P: ZKRewindableMaliciousProverJ) = {
  proc extract(statement: W64xN.R.t): W64xN.R.t
}.


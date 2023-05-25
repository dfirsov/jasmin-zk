require import AllCore.
from Jasmin require import JModel.
require import Array32 Array64 Array128.


require import W64_SchnorrExtract.

module JProver = M(Syscall).
module JVerifier = M(Syscall).

module type ZKProverJ = {
  proc response (witness0:W64.t Array32.t, secret_power:W64.t Array32.t,
                 challenge:W64.t Array32.t) : W64.t Array32.t 
  proc commitment () : W64.t Array32.t * W64.t Array32.t  
}.


module type ZKMaliciousProverJ = {
  proc commitment() : W64.t Array32.t 
  proc response(challenge:W64.t Array32.t) : W64.t Array32.t 
}.


module type ZKVerifierJ = {
   proc verify(statement : W64.t Array32.t, commitment : W64.t Array32.t, challenge_0 : W64.t Array32.t, response : W64.t Array32.t) :
    W64.t  
  proc challenge() : W64.t Array32.t 
}.


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



type sbits.                     (* rewinding parameter type *)


module type ZKRewindableMaliciousProverJ = {
  proc response (challenge:W64.t Array32.t) : W64.t Array32.t
  proc commitment () : W64.t Array32.t 
  (* rewinding interface *)
  proc getState() : sbits 
  proc setState(b : sbits) : unit 
}.


module type ExtractorJ(P: ZKRewindableMaliciousProverJ) = {
  proc extract(statement: W64.t Array32.t): W64.t Array32.t
}.


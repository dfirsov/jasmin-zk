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




module type MaliciousVerifierJ = {
  proc challenge(s : W64xN.R.t, z : W64xN.R.t) : W64xN.R.t
  proc summitup(r : W64xN.R.t) : sbits
}.

module type ZKDistinguisherJ  = {
  proc guess(statement : W64xN.R.t, witness : W64xN.R.t, summary : sbits) : bool 
}.


module type RewMaliciousVerifierJ = {
  proc challenge(s : W64xN.R.t, z : W64xN.R.t) : W64xN.R.t
  proc summitup(r : W64xN.R.t) : sbits
  proc getState() : sbits 
  proc setState(b : sbits) : unit 
}.


module type SimulatorJ(V0 : RewMaliciousVerifierJ)  = {
  proc simulate(statement : W64xN.R.t) : sbits
}.


module ZKRealJ(P : ZKProverJ, V : MaliciousVerifierJ, D : ZKDistinguisherJ) = {
  proc run(statement : W64xN.R.t, witness : W64xN.R.t) : bool = {
    var commit, secret,  challenge, response, summary, guess;    
    (commit, secret) <@ P.commitment();
    challenge <@ V.challenge(statement, commit);
    response <@ P.response(witness, secret, challenge);
    summary <@ V.summitup(response);
    guess <@ D.guess(statement, witness, summary);
    return guess;
  }
}.


module ZKIdealJ(S : SimulatorJ, V0 : RewMaliciousVerifierJ,
               D0 : ZKDistinguisherJ) = {
  proc run(statement : W64xN.R.t, witness : W64xN.R.t) : bool = {
    var summary : sbits;
    var guess : bool;
    summary <@ S(V0).simulate(statement);
    guess <@ D0.guess(statement, witness, summary);
    return guess;
  }
}.

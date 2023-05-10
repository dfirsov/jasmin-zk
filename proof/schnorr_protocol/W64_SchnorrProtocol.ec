require import Int Real Distr.
from Jasmin require import JModel JBigNum.
require import Array32 Array64 Array128.
require import Ring_ops_proof ZK_SchnorrBasics.


require export W64_SchnorrProver W64_SchnorrVerifier.

type W64xN = W64.t Array32.t.

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



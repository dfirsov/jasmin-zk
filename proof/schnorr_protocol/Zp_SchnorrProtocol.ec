require import Int IntDiv.
require import Real.
require import Distr.
require import List.
require import StdOrder.
import Ring.IntID IntOrder.

require import ZK_SchnorrBasics.
require import ZK_SchnorrCompleteness.
require import ZK_SchnorrSpecialSoundness.
require import ZK_SchnorrExtractability.


require import Ring_ops_spec.
import Zp.

type statement = zp.
type witness   = int.
type commitment = zp.
type secret    = int.
type challenge = int.
type response  = int.


module type ZKProverG = {
  proc commitment() : commitment * secret
  proc response(w : witness, r : secret, c : challenge) : response
}.


module type ZKVerifierG = {
  proc challenge() : challenge
  proc verify(s : statement, z : commitment, c : challenge, t : response) :
    bool
}.

module SchnorrProver : ZKProverG = {
  proc commitment() : commitment * secret = {
    var r : secret;
    r <$ [0..p-2];
    return (g ^^ r, r);
  }
  proc response(w: witness, r:secret, c: challenge) : response = {
    return r + c * w;
  }
}.

module SchnorrVerifier : ZKVerifierG = {
  proc challenge() : challenge = {
    var c;
    c <$ [0..p-2];
    return c;
  }
  proc verify(s: statement, z: commitment, c: challenge, t: response) : bool = {
    return (z * (s ^^ c) = g ^^ t);
  }
}.


module CompletenessG(P : ZKProverG, V : ZKVerifierG) = {
  proc main(s:statement, w:witness) = {
    var z, c, r,t,v;
    (z,r) <@ P.commitment();
    c <@ V.challenge();
    t <@ P.response(w,r,c);
    v <@ V.verify(s,z,c,t);
    return v;
  }
}.


lemma completenessG (s : statement) (w : witness) &m: completeness_relation s w =>
  Pr[ CompletenessG(SchnorrProver, SchnorrVerifier).main(s,w)@&m : res] = 1%r.
proof. progress.
rewrite - (dl_completeness s w &m). auto.
byequiv (_: ={arg} ==> _). proc.
inline*. wp. 
rnd. wp. rnd.  wp. skip. progress. smt(@Distr @List).
smt. auto. auto.
qed.



(* Extractability  *)
import Rew.
op sec_to_sbits : secret -> sbits.
op sec_from_sbits : sbits -> secret.
axiom sec_enc x : x = sec_from_sbits (sec_to_sbits x).
axiom sec_inj : injective sec_to_sbits.

(* 
- remove secret from commitment and response

 *)
module type ZKMaliciousProverG = {
  proc commitment() : commitment
  proc response(c : challenge) : response
}.


module type ZKRewindableMaliciousProverG = {
  proc commitment() : commitment
  proc response(c : challenge) : response
  proc getState() : sbits 
  proc setState(b : sbits) : unit 
}.

module SoundnessG(P : ZKMaliciousProverG, V : ZKVerifierG) = {
  proc run(s:statement) = {
    var z, c,t,v;
    z <@ P.commitment();
    c <@ V.challenge();
    t <@ P.response(c);
    v <@ V.verify(s,z,c,t);
    return v;
  }
}.

module type ExtractorG(P: ZKRewindableMaliciousProverG) = {
  proc extract(statement: statement): witness
}.

module SpecialSoundnessAdversaryG(P : ZKRewindableMaliciousProverG)  = {
  proc attack(statement:statement):transcript * transcript = {
    var i,c1,c2,r1,r2,pstate;
    i <@ P.commitment();
    c1 <$ [0..p-2];
    pstate <@ P.getState();
    r1 <@ P.response(c1);
    c2 <$ [0..p-2];
    P.setState(pstate);
    r2 <@ P.response(c2);
    return ((i,c1,r1), (i,c2,r2));
  }
}.

op special_soundness_extractG (t1 t2 : commitment * challenge * response): witness = 
 (special_soundness_extract witness t1 t2).

module (ExtractorG : ExtractorG)(P : ZKRewindableMaliciousProverG) = {  
  module SA = SpecialSoundnessAdversaryG(P)
  proc extract(p : statement) : witness = {
    var t1,t2;
    (t1,t2) <@ SA.attack(p);
    return special_soundness_extractG t1 t2;
 }
}.


section.

declare module P <: ZKRewindableMaliciousProverG{-HV}.
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



local module P' = {
  proc commitment(s : dl_stat) : dl_com  = {
    var r;
    r <@ P.commitment();
    return r;
  }  
  proc response(challenge : dl_chal) : dl_resp  = {
    var r;
    r <@ P.response(challenge);
    return r;
  }  
  proc getState = P.getState
  proc setState = P.setState
}.


lemma extractabilityG &m s: 
  Pr[ExtractorG(P).extract(s) @ &m : soundness_relation s res ] >=
   (Pr[SoundnessG(P, SchnorrVerifier).run(s) @ &m : res] ^ 2
       - 1%r / (size (range 0 (p - 1)))%r
           * Pr[SoundnessG(P, SchnorrVerifier).run(s) @ &m : res]).
proof.
have -> : Pr[SoundnessG(P, SchnorrVerifier).run(s) @ &m : res]
 = Pr[Soundness(P', HV).run(s) @ &m : res].
byequiv (_: ={glob P, arg} ==> _).
proc. inline*. wp.  call(_:true). wp. 
rnd. wp.  call (_:true). wp.  skip. progress.
smt. smt. auto. auto. 
have -> : Pr[ExtractorG(P).extract(s) @ &m : soundness_relation s res] 
 = Pr[Extractor(P').extract(s) @ &m : soundness_relation s res].
byequiv (_: ={glob P, arg} ==> _). proc.
inline*. wp. call (_:true). wp. 
call (_:true). wp.  rnd. wp. call (_:true). wp.
call (_:true). rnd. wp.  call (_:true). wp.  skip. progress. auto. auto. 
apply (dl_statistical_PoK P' _ _ _ &m s).
proc. call P_response_ll. auto.
proc. call P_commitment_ll. auto.
apply rewindable_P_plus.
qed.

end section.

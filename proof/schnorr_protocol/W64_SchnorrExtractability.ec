require import AllCore Distr DInterval List Int IntDiv.

require import JModel JBigNum.
require import Array32 Array64 Array128.
require import ZK_SchnorrBasics.
require import W64_Zp_SchnorrIndistinguishability.
require import W64_SchnorrSoundness.
require import Zp_SchnorrProtocol.
require import W64_SchnorrProtocol.
require import Ring_ops_spec.
import Zp DZmodP.
import W64xN Sub R. 


module  AWrapE(A:ZKRewindableMaliciousProverJ) : ZKRewindableMaliciousProverG = {
  proc commitment() : commitment  = {
     var c;
     c <@ A.commitment();
     return (inzp (valR c ));
  }
  proc response(c:challenge) : response = {
   var r;
   r <@ A.response(bn_ofint c);
   return (valR r);
  }  

  proc getState = A.getState
  proc setState = A.setState
}.



module (ExtractorJ : ExtractorJ)(P : ZKRewindableMaliciousProverJ) = {
  module SA = SpecialSoundnessAdversaryG(AWrapE(P))
  proc extract(p : W64xN) : W64xN = {
    var t1,t2;
    (t1,t2) <@ SA.attack(inzp (valR p));
    return bn_ofint (special_soundness_extractG t1 t2);
 }
}.


lemma extractability_same : forall (P <:  ZKRewindableMaliciousProverJ) p &m,
  Pr[ ExtractorJ(P).extract(p) @&m: soundness_relation (inzp (valR p)) (valR res) ]
  = Pr[ ExtractorG(AWrapE(P)).extract((inzp (valR p))) @&m: soundness_relation (inzp (valR p)) res ].
progress. 
byequiv.
proc.
call (_: ={glob P}). sim. auto. progress.
have : (valR (bn_ofint (special_soundness_extractG result_R.`1 result_R.`2))) 
 = (special_soundness_extractG result_R.`1 result_R.`2).
rewrite bn_ofintK. rewrite /special_soundness_extractG.  
rewrite /special_soundness_extract.  smt.
move => q.
have <- : (valR (bn_ofint (special_soundness_extractG result_R.`1 result_R.`2))) 
 = (special_soundness_extractG result_R.`1 result_R.`2).
rewrite bn_ofintK. rewrite /special_soundness_extractG. 
rewrite /special_soundness_extract.
smt.
have -> : (valR (bn_ofint (special_soundness_extractG result_R.`1 result_R.`2))) 
 = (special_soundness_extractG result_R.`1 result_R.`2).
rewrite bn_ofintK. rewrite /special_soundness_extractG.  smt.
smt. 
have -> : (valR (bn_ofint (special_soundness_extractG result_R.`1 result_R.`2)))
 = (special_soundness_extractG result_R.`1 result_R.`2).
rewrite bn_ofintK. rewrite /special_soundness_extractG.   
rewrite /special_soundness_extract.  smt.
apply H. auto. auto.
qed.

section.

declare module P <: ZKRewindableMaliciousProverJ{-HV}.
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
  Pr[ExtractorJ(P).extract(s)@&m: soundness_relation (inzp (valR s)) (valR res) ] >=
   (Pr[SoundnessJ(P, JVerifier(Syscall)).main(s) @ &m : res] ^ 2
       - 1%r / (size (range 0 (p - 1)))%r
           * Pr[SoundnessJ(P, JVerifier(Syscall)).main(s) @ &m : res]).
proof. rewrite (extractability_same P).
rewrite (soundness_same s &m P).
have -> : Pr[SoundnessG(AWrap(P), SchnorrVerifier).run(inzp (valR s)) @ &m : res]
 = Pr[SoundnessG(AWrapE(P), SchnorrVerifier).run(inzp (valR s)) @ &m : res].
byequiv. proc.  sim. auto. auto.
apply (extractabilityG (AWrapE(P)) _ _ _ &m (inzp (valR s))).
proc. call P_response_ll. auto.
proc. call P_commitment_ll. auto.
apply P_rewindable.
qed.

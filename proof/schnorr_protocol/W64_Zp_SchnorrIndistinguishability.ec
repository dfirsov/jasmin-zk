require import AllCore Distr DInterval List Int IntDiv.

require import JModel JBigNum.
require import Array32 Array64 Array128.


require import W64_SchnorrProtocol.
require import Zp_SchnorrProtocol.

require import Ring_ops_spec.
import Zp DZmodP.
import W64xN Sub R. 




module PWrap = {
  module JProver = JProver(Syscall)
  proc commitment() : commitment * secret = {
    var c,s;
    (c, s)  <@ JProver.commitment();  
    return (inzp (W64xN.valR c), W64xN.valR s);
  }

  proc response(w: witness, r:secret, c: challenge) : response = {
    var resp;
    resp <@ JProver.response(W64xN.R.bn_ofint (w %% (p-1)), W64xN.R.bn_ofint (r %% (p-1)), W64xN.R.bn_ofint (c %% (p-1)));
    return (W64xN.valR resp);
  }  
}.


module VWrap = {
  module JVerifier = JVerifier(Syscall)
  proc challenge() : challenge = {
    var r;
    r <@ JVerifier.challenge();
    return (W64xN.valR r);
  }
  proc verify(s: statement, z: commitment, c: challenge, t: response) : bool = {
    var b;
    b <@ JVerifier.verify(W64xN.R.bn_ofint (Sub.val s), W64xN.R.bn_ofint (Sub.val z), W64xN.R.bn_ofint (c %% (p-1)), W64xN.R.bn_ofint (t %% (p-1)));
   return (b = W64.one);
  }  
}.


axiom pmoval:  p - 1 < modulusR.
axiom pval:  p < modulusR.
axiom inzpKK: forall (z : int), val (inzp z) = z %% p.


lemma commitment_eq : 
  equiv [ SchnorrProver.commitment ~ JProver(Syscall).commitment :
  true
  ==> (val res{1}.`1) = (valR res{2}.`1)
    /\ res{1}.`2 = (valR res{2}.`2) ].
admitted.


lemma challenge_eq : 
  equiv [ SchnorrVerifier.challenge ~ JVerifier(Syscall).challenge :
  true ==> res{1} = (valR res{2}) ].
admitted.


lemma response_eq : 
  equiv [ SchnorrProver.response ~ JProver(Syscall).response :
    w{1} %% (p-1)       = (valR (witness0{2}) )       %% (p-1)
    /\ r{1} %% (p-1)    = (valR secret_power{2})     %% (p-1)
    /\ c{1} %% (p-1)    = (valR challenge{2})        %% (p-1)
    ==> res{1}  = (valR res{2}) ].
admitted.


lemma verify_eq : 
  equiv [ SchnorrVerifier.verify ~ JVerifier(Syscall).verify :
       Sub.val(s{1}) = valR statement{2} %% p
       /\ Sub.val(z{1}) = valR commitment{2} %% p
       /\ c{1} %% (p-1) = (valR (challenge_0{2})) %% (p-1)
       /\ t{1} %% (p-1) = (valR response{2})  %% (p-1)
       ==> res{1} = (res{2} = W64.one)
].
admitted.


lemma response_mod_eq :
  equiv [ JProver(Syscall).response ~ JProver(Syscall).response :
    (valR witness{1})         %% (p-1) = (valR witness{2})      %% (p-1)
    /\ (valR secret_power{1}) %% (p-1) = (valR secret_power{2}) %% (p-1)
    /\ (valR challenge{1})    %% (p-1) = (valR challenge{2}) %% (p-1)
    ==> (valR res{1}) %% (p-1) = (valR res{2}) %% (p-1) ].
admitted.

  
lemma verify_mod_eq :
  equiv [ JVerifier(Syscall).verify ~ JVerifier(Syscall).verify :
       (valR statement{1})   %% p     = (valR statement{2})   %% p
    /\ (valR commitment{1})  %% p     = (valR commitment{2})  %% p
    /\ (valR challenge_0{1}) %% (p-1) = (valR challenge_0{2}) %% (p-1)
    /\ (valR response{1})    %% (p-1) = (valR response{2})    %% (p-1)
    ==> ={res} ].
admitted.


theory ZKDistinguisherTheory.

type zkin.
module type PDistinguisher(P : ZKProverG) = {
  proc distinguish(i : zkin) : bool
}.

module type VDistinguisher(V : ZKVerifierG) = {
  proc distinguish(i : zkin) : bool
}.



(*
 W64 -> zp
 W64 -> int

 int -> W64, includes "cleaning"
 int -> zp, includes "cleaning"

*)
lemma prover_ind:  forall (D <: PDistinguisher) &m i,
 Pr[D(SchnorrProver).distinguish(i)@&m: res]
  =  Pr[D(PWrap).distinguish(i)@&m: res].
proof. progress.
byequiv (_: ={glob D, arg} ==> _).
proc*.
call (_:true). simplify.
proc*. inline PWrap.commitment. wp.
call commitment_eq. skip. progress.
smt.
simplify.
proc*. simplify. inline PWrap.response. wp.
call response_eq. wp. simplify. skip. progress.
rewrite bnk_ofintK. auto. 
rewrite - bn_modulusE. smt(@Zp pmoval).
rewrite bnk_ofintK. auto. 
rewrite - bn_modulusE. smt(@Zp pmoval).
rewrite bnk_ofintK. auto. 
rewrite - bn_modulusE. smt(@Zp pmoval).
skip. progress. auto. auto.
qed.


lemma verifier_ind:  forall (D <: VDistinguisher) &m i,
 Pr[D(SchnorrVerifier).distinguish(i)@&m: res]
  =  Pr[D(VWrap).distinguish(i)@&m: res].
proof. progress.
byequiv (_: ={glob D, arg} ==> _).
proc*.
call (_:true). simplify.
proc*. inline VWrap.challenge. wp.
call challenge_eq. skip. progress.
simplify.
proc*. simplify. inline VWrap.verify. wp.
call verify_eq. wp. simplify. skip. progress.
rewrite bnk_ofintK. auto. 
rewrite - bn_modulusE. 
have v : val s{2} < p. smt(valP).
smt(@Zp pmoval).
rewrite bnk_ofintK. auto. 
have v : val z{2} < p. smt(valP).
rewrite - bn_modulusE. smt(@Zp pmoval).
rewrite bnk_ofintK. auto. 
rewrite - bn_modulusE. smt(@Zp pmoval).
rewrite bnk_ofintK. auto. 
rewrite - bn_modulusE. smt(@Zp pmoval).
skip. progress. auto. auto.
qed.

end ZKDistinguisherTheory. 


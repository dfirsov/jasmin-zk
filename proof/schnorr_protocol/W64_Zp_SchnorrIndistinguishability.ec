require import AllCore Distr DInterval List Int IntDiv.

require import JModel JBigNum.
require import Array32 Array64 Array128.


require import W64_SchnorrProtocol.
require import Zp_SchnorrProtocol.

require import Ring_ops_spec.
import Zp DZmodP.
import W64xN Sub R. 




module PWrap = {
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



import ZK_SchnorrBasics.
module ASpecFp_Schnorr = {
 proc commit(h : zp, w : R) : zp * int = {
   var r, q : int;
   var a : zp;    
   r <@ ASpecFp.rsample(p-1);
   a <@ ASpecFp.expm(g,r);
   return (a,  r);
  } 

  proc challenge() : int = {
   var r;
   r <@ ASpecFp.rsample(p-1);
   return r;
  }
}.


require import W64_SchnorrExtract.
require import Ring_ops_proof.

op Rip : int.
axiom Rip_def: Rip = 4 ^ (dnlimbs * nlimbs) %/ (P-1).

print Ri_def.    
lemma bn_set_bf_prop : 
  phoare[ M.bn_set_bf : true ==> W64x2N.valR res = Ri  ] = 1%r.
admitted.

lemma bn_set_go_prop : 
  phoare[ M.bn_set_go : true ==> valR res = p  ] = 1%r.
admitted.

lemma bn_set_eo_prop : 
  phoare[ M.bn_set_eo : true ==> valR res = p-1  ] = 1%r.
admitted.

lemma bn_set_eb_prop : 
  phoare[ M.bn_set_eb : true ==> W64x2N.valR res = Rip  ] = 1%r.
admitted.

lemma bn_set_gg_prop : 
  phoare[ M.bn_set_gg : true ==> valR res = val g  ] = 1%r.
admitted.

    
lemma commit_same1 : 
  equiv [ JProver.commitment ~ ASpecFp_Schnorr.commit 
          :   true
  ==> (val res{2}.`1) = (valR res{1}.`1)
    /\ res{2}.`2 = (valR res{1}.`2) ].
proc. 
symmetry. call expm_correct.
symmetry.
call usample_aspec. sp.
simplify.
call{1} bn_set_bf_prop.
call{1} bn_set_gg_prop.
call{1} bn_set_go_prop.
call{1} bn_set_eo_prop.
skip. move => &1 _ H r q r2 vr rr iz rp vri.
split. smt.
move => h1. move => rL rR. move => rzrlrr. 
split. 
split.  smt. split. smt. split.  smt. split.  smt. rewrite /R. rewrite - vri. smt(@W64x2N @R2).
move => qo. move => rl rrr ai. smt.
qed.


lemma commit_same : 
  equiv [ SchnorrProver.commitment ~ ASpecFp_Schnorr.commit 
          : true  ==> ={res} ].
proc. 
inline *. wp.  simplify. sp.
rnd.
skip. progress.  smt(@Distr).  rewrite /(^^). rewrite /(^). rewrite /(^). admit.
qed.

lemma commitment_eq : 
  equiv [ SchnorrProver.commitment ~ JProver.commitment :
  true
  ==> (val res{1}.`1) = (valR res{2}.`1)
    /\ res{1}.`2 = (valR res{2}.`2) ].
transitivity ASpecFp_Schnorr.commit
  (true ==> ={res})
  (true
  ==> (val res{1}.`1) = (valR res{2}.`1)
    /\ res{1}.`2 = (valR res{2}.`2)). auto. auto.
apply commit_same.
symmetry. apply commit_same1.
qed.



lemma challenge_same : 
  equiv [ SchnorrVerifier.challenge ~ ASpecFp_Schnorr.challenge
          : true  ==> ={res} ].
proc. inline*. wp. rnd. wp. skip.
progress.
qed.

lemma challenge_eq : 
  equiv [ SchnorrVerifier.challenge ~ JVerifier.challenge :
  true ==> res{1} = (valR res{2}) ].
transitivity ASpecFp_Schnorr.challenge
  (true ==> ={res})
  (true
  ==> (res{1}) = (valR res{2})). auto. auto.
apply challenge_same.
proc. 
symmetry. call usample_aspec.
call{1} bn_set_eo_prop. wp. skip. progress.
qed.



lemma response_eq : 
  equiv [ SchnorrProver.response ~ JProver.response :
    w{1} %% (p-1)       = (valR (witness0{2}) )      %% (p-1)
    /\ r{1} %% (p-1)    = (valR secret_power{2})     %% (p-1)
    /\ c{1} %% (p-1)    = (valR challenge_0{2})      %% (p-1)
    ==> res{1} %% (p-1)  = (valR res{2}) ].
proc. sp. simplify.
ecall {2} (bn_addm_correct secret_power{2} product{2} exp_order{2}). simplify. 
ecall {2} (bn_mulm_correct challenge_0{2} witness0{2} exp_order{2}). simplify.
ecall {2} (bnreduce_small_spec_ph challenge_0{2} exp_order{2}). simplify.
call{2} bn_set_eb_prop. simplify.
call{2} bn_set_eo_prop. simplify.
wp.
skip. 
progress. rewrite H3. rewrite Rip_def. rewrite ri_un. rewrite /ri. rewrite H2. smt().
smt. 
smt(@W64xN).
smt(@W64xN).
rewrite H2.  
admit.
smt.
smt.
smt(@W64xN).
smt.
smt(@W64xN).
rewrite H2. admit.
smt(@W64xN).
rewrite H2. admit.
smt(@W64xN).
smt.
smt(@W64xN).
admit.
rewrite - H24.
rewrite - H17.
rewrite H2.
admit.
qed.



lemma verify_eq : 
  equiv [ SchnorrVerifier.verify ~ JVerifier.verify :
       Sub.val(s{1}) = valR statement{2} %% p
       /\ Sub.val(z{1}) = valR commitment_0{2} %% p
       /\ c{1} %% (p-1) = (valR (challenge_0{2})) %% (p-1)
       /\ t{1} %% (p-1) = (valR response_0{2})  %% (p-1)
       ==> res{1} = (res{2} = W64.one) ].
admitted.


lemma response_mod_eq :
  equiv [ JProver.response ~ JProver.response :
    (valR witness{1})         %% (p-1) = (valR witness{2})      %% (p-1)
    /\ (valR secret_power{1}) %% (p-1) = (valR secret_power{2}) %% (p-1)
    /\ (valR challenge_0{1})    %% (p-1) = (valR challenge_0{2}) %% (p-1)
    ==> (valR res{1}) %% (p-1) = (valR res{2}) %% (p-1) ].
admitted.

  
lemma verify_mod_eq :
  equiv [ JVerifier.verify ~ JVerifier.verify :
       (valR statement{1})   %% p     = (valR statement{2})   %% p
    /\ (valR commitment_0{1})  %% p     = (valR commitment_0{2})  %% p
    /\ (valR challenge_0{1}) %% (p-1) = (valR challenge_0{2}) %% (p-1)
    /\ (valR response_0{1})    %% (p-1) = (valR response_0{2})    %% (p-1)
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
(* lemma prover_ind:  forall (D <: PDistinguisher) &m i, *)
(*  Pr[D(SchnorrProver).distinguish(i)@&m: res] *)
(*   =  Pr[D(PWrap).distinguish(i)@&m: res]. *)
(* proof. progress. *)
(* byequiv (_: ={glob D, arg} ==> _). *)
(* proc*. *)
(* call (_:true). simplify. *)
(* proc*. inline PWrap.commitment. wp. *)
(* call commitment_eq. skip. progress. *)
(* smt. *)
(* simplify. *)
(* proc*. simplify. inline PWrap.response. wp. *)
(* call response_eq. wp. simplify. skip. progress. *)
(* rewrite bnk_ofintK. auto.  *)
(* rewrite - bn_modulusE. smt(@Zp pmoval). *)
(* rewrite bnk_ofintK. auto.  *)
(* rewrite - bn_modulusE. smt(@Zp pmoval). *)
(* rewrite bnk_ofintK. auto.  *)
(* rewrite - bn_modulusE. smt(@Zp pmoval). *)
(* smt. skip. progress. auto. auto. *)
(* qed. *)


(* lemma verifier_ind:  forall (D <: VDistinguisher) &m i, *)
(*  Pr[D(SchnorrVerifier).distinguish(i)@&m: res] *)
(*   =  Pr[D(VWrap).distinguish(i)@&m: res]. *)
(* proof. progress. *)
(* byequiv (_: ={glob D, arg} ==> _). *)
(* proc*. *)
(* call (_:true). simplify. *)
(* proc*. inline VWrap.challenge. wp. *)
(* call challenge_eq. skip. progress. *)
(* simplify. *)
(* proc*. simplify. inline VWrap.verify. wp. *)
(* call verify_eq. wp. simplify. skip. progress. *)
(* rewrite bnk_ofintK. auto.  *)
(* rewrite - bn_modulusE.  *)
(* have v : val s{2} < p. smt(valP). *)
(* smt(@Zp pmoval). *)
(* rewrite bnk_ofintK. auto.  *)
(* have v : val z{2} < p. smt(valP). *)
(* rewrite - bn_modulusE. smt(@Zp pmoval). *)
(* rewrite bnk_ofintK. auto.  *)
(* rewrite - bn_modulusE. smt(@Zp pmoval). *)
(* rewrite bnk_ofintK. auto.  *)
(* rewrite - bn_modulusE. smt(@Zp pmoval). *)
(* skip. progress. auto. auto. *)
(* qed. *)

end ZKDistinguisherTheory. 


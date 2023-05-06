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

    

axiom p_val_prop1 x : W64xN.valR x < (p-1) * (p-1). 
axiom p_val_prop2 : 2*p < W64xN.modulusR. 

axiom exps s c : val (s ^^ c) = ((val s) ^ c) %% p.
lemma zp_eq z1 z2 : (val z1 = val z2) = (z1 = z2). smt(@Zp). qed.
lemma zp_mul (z1 z2 : zp) : val (z1 * z2) = (val z1 * val z2) %% p. smt(@Zp). qed.
axiom exp_pow x n : x ^^ n = x ^^ (n %% (p-1)).

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
skip. progress.  smt(@Distr).  
rewrite - zp_eq.
rewrite exps.
rewrite /(^).
rewrite inzpKK. congr. congr.
rewrite /asint. auto.
qed.

lemma commitment_eq : 
  equiv [ SchnorrProver.commitment ~ JProver.commitment :
  true
  ==> (val res{1}.`1) = (valR res{2}.`1)
    /\ res{1}.`2 = (valR res{2}.`2) ].
proc*.

transitivity ASpecFp_Schnorr.commit
  (true ==> ={res})
  (true
  ==> (val res{1}.`1) = (valR res{2}.`1)
    /\ res{1}.`2 = (valR res{2}.`2)). auto. auto.
apply commit_same.
symmetry. apply commit_same1.
qed.


lemma verify_eq : 
  equiv [ SchnorrVerifier.verify ~ JVerifier.verify :
       Sub.val(s{1}) = valR statement{2} %% p
       /\ Sub.val(z{1}) = valR commitment_0{2} %% p
       /\ c{1} %% (p-1) = (valR (challenge_0{2})) %% (p-1)
       /\ t{1} %% (p-1) = (valR response_0{2})  %% (p-1)
       ==> res{1} = (res{2} = W64.one) ].
proc. sp. simplify.
ecall {2} (bn_eq_correct v1{2} v2{2}). simplify. 
ecall {2} (bn_expm_correct group_barrett{2} group_order{2} group_generator{2} response_0{2}). simplify. 
ecall {2} (bn_mulm_correct commitment_0{2} tmp{2} group_order{2}). simplify.
ecall {2} (bn_expm_correct group_barrett{2} group_order{2} statement{2} challenge_0{2}). simplify. 
ecall {2} (bnreduce_small_spec_ph response_0{2} exp_order{2}). simplify.
ecall {2} (bnreduce_small_spec_ph challenge_0{2} exp_order{2}). simplify.
ecall {2} (bnreduce_small_spec_ph commitment_0{2} group_order{2}). simplify.
ecall {2} (bnreduce_small_spec_ph statement{2} group_order{2}). simplify.
call{2} bn_set_gg_prop.
call{2} bn_set_bf_prop.
call{2} bn_set_go_prop.
call{2} bn_set_eb_prop.
call{2} bn_set_eo_prop.
simplify.
skip. progress.
rewrite ri_un. rewrite H6. rewrite Ri_def. rewrite /ri. smt().
rewrite H5. smt(P_pos).
smt(@W64xN).
smt(@W64xN).
rewrite H5. 
smt.                            (* use p_val_prop1 *)
smt(P_pos).
smt(@W64xN).
smt(@W64xN).
rewrite H5. 
smt.
rewrite ri_un. rewrite H4. rewrite Rip_def. rewrite /ri. rewrite H3.
smt(). 
smt(P_pos).
smt.
smt(@W64xN).
smt.
smt(P_pos).
smt.
smt(@W64xN).
smt.
smt().
smt().
rewrite /R. smt.
smt(@W64xN).
smt().
smt(@W64xN).
smt().
smt(@Zp).
rewrite H52. rewrite - H48. rewrite H51.
rewrite H39.
rewrite H3. rewrite - H2.
rewrite H7.
rewrite H23.
rewrite H42.
rewrite H15.
rewrite H5.
rewrite - H.
rewrite - H0.
rewrite H31.
rewrite H3.
rewrite - H1.
rewrite - (zp_eq (z{1} * s{1} ^^ c{1}) (g ^^ t{1})).
rewrite (exps g t{1}).
rewrite (zp_mul).
congr.
congr.
congr.
congr.
rewrite /P.
rewrite - exps. smt(exp_pow). 
rewrite - exps.
rewrite /P. rewrite - exps. smt(exp_pow). 
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
ecall {2} (bnreduce_small_spec_ph witness0{2} exp_order{2}). simplify.
ecall {2} (bnreduce_small_spec_ph secret_power{2} exp_order{2}). simplify.
ecall {2} (bnreduce_small_spec_ph challenge_0{2} exp_order{2}). simplify.
call{2} bn_set_eb_prop. simplify.
call{2} bn_set_eo_prop. simplify.
wp.
skip. 
progress. rewrite H3. rewrite Rip_def. rewrite ri_un. rewrite /ri. rewrite H2. smt().
smt. 
smt(@W64xN).
smt(@W64xN).
rewrite H2.   smt (p_val_prop1).
smt.
smt.
smt(@W64xN).
smt.
smt(@W64xN).
rewrite H2. smt (p_val_prop1).
smt(@W64xN).
rewrite H2. smt.
smt(@W64xN).
smt.
smt(@W64xN).
rewrite H2. smt.
smt(@W64xN).
rewrite H2. smt.
smt(@W64xN).
rewrite H2. smt (p_val_prop2).
rewrite - H40.
rewrite - H33.
rewrite H2. 
have -> : (r{1} + c{1} * w{1}) %% (p - 1)
  = (r{1} %% (p - 1) + (c{1} * w{1}) %% (p - 1) ) %% (p - 1).
smt (modzDmr modzDml).
rewrite  H19 H2. rewrite - H0.
rewrite  H11 H2. rewrite - H1.
rewrite  H27 H2. rewrite - H.
search edivz.
rewrite modzMml.
rewrite modzMmr. done.
qed.








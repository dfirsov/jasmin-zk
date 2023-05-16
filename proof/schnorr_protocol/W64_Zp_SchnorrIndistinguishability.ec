require import AllCore Distr DInterval List Int IntDiv.

from Jasmin require import JModel JBigNum.
require import Array32 Array64 Array128.

require import W64_SchnorrProtocol.
require import Zp_SchnorrProtocol.
require import AuxLemmas.

require import Ring_ops_spec.
import Zp DZmodP.
import W64xN Sub R. 


require import W64_SchnorrExtract.
require import Ring_ops_proof.


(* TODO: proof constants to be correct  *)
(* lemma bn_set_gg_value :  *)
(*   phoare[ M.bn_set_gg : true ==> valR res =  1 ] = 1%r. *)
(* proc. wp. skip. progress. simplify. *)
(* search bnk. *)
(* rewrite R.bn2seq. *)
(* rewrite /to_list. rewrite /mkseq. *)
(* have -> : (map *)
(*      (fun (i : int) => *)
(*         (a{hr}.[0 <- W64.one].[1 <- W64.zero].[2 <- W64.zero].[3 <- W64.zero].[4 <- *)
(*            W64.zero].[5 <- W64.zero].[6 <- W64.zero].[7 <- W64.zero].[8 <- *)
(*            W64.zero].[9 <- W64.zero].[10 <- W64.zero].[11 <- W64.zero].[12 <- *)
(*            W64.zero].[13 <- W64.zero].[14 <- W64.zero].[15 <- W64.zero].[16 <- *)
(*            W64.zero].[17 <- W64.zero].[18 <- W64.zero].[19 <- W64.zero].[20 <- *)
(*            W64.zero].[21 <- W64.zero].[22 <- W64.zero].[23 <- W64.zero].[24 <- *)
(*            W64.zero].[25 <- W64.zero].[26 <- W64.zero].[27 <- W64.zero].[28 <- *)
(*            W64.zero].[29 <- W64.zero].[30 <- W64.zero].[31 <- W64.zero].[i])%Array32) *)
(*      (iota_ 0 nlimbs)) = [W64.one;W64.zero]. *)

(* admit. *)
(* rewrite /bn_seq. simplify. *)

axiom bn_set_gg_prop : 
  phoare[ M.bn_set_gg : true ==> valR res = Sub.val g  ] = 1%r.

axiom bn_set_go_prop : 
  phoare[ M.bn_set_go : true ==> valR res = p  ] = 1%r.
axiom bn_set_bf_prop : 
  phoare[ M.bn_set_bf : true ==> W64x2N.valR res = Ri  ] = 1%r.

axiom bn_set_eo_prop : 
  phoare[ M.bn_set_eo : true ==> valR res = q  ] = 1%r.
axiom bn_set_eb_prop : 
  phoare[ M.bn_set_eb : true ==> W64x2N.valR res = Rip  ] = 1%r.



lemma zp_eq z1 z2 : (val z1 = val z2) = (z1 = z2). smt(@Zp). qed.
lemma zp_mul (z1 z2 : zmod) : val (z1 * z2) = (val z1 * val z2) %% p. smt(@Zp). qed.
lemma inzpKK: forall (z : int), val (inzmod z) = z %% p. smt(@Zp). qed.

  
module ASpecFp_Schnorr = {
 proc commit(h : zmod, w : R) : zmod * int = {
   var r;
   var a : zmod;    
   r <@ ASpecFp.rsample(q);
   a <@ ASpecFp.expm(g,r);
   return (a,  r);
  } 

  proc challenge() : int = {
   var r;
   r <@ ASpecFp.rsample(q);
   return r;
  }
}.


require import UniformSampling_Concrete.
require import MontgomeryLadder_Concrete.

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
skip. move => &1 _ H r qe r2 vr rr iz rp vri.
split. rewrite qe. simplify. smt(q_prime).
move => h1. move => rL rR. move => rzrlrr. 
split. 
split.  smt. split. smt. split.  smt. split.  smt. rewrite /R. rewrite - vri. smt(@W64x2N @R2).
move => qo. move => rl rrr ai. smt.
qed.


lemma exps (x : zmod) : forall n, 0 <= n => (x ^ n)%Ring_ops_spec = (x ^^ n). 
apply intind. progress.
smt(@Zp @Ring).
progress.
have ->: (x ^ (i + 1))%Ring_ops_spec = x * (x^ i)%Ring_ops_spec. 
 rewrite /(^).
 have ->: asint x ^ (i + 1) = (asint x) * (asint x ^ i). smt.
 admit.
have ->: (x ^^ (i + 1)) = x * (x^^i). smt.
rewrite H0.
auto.
qed.


lemma commit_same : 
  equiv [ SchnorrProver.commitment ~ ASpecFp_Schnorr.commit 
          : true  ==> ={res} ].
proc. 
inline *. wp.  simplify. sp.
rnd.
skip. progress.  smt(@Distr).  
rewrite - zp_eq.
rewrite exps. smt(@DInterval).
rewrite /(^^) /(^).
auto.
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
smt.
qed.


require import ModularMultiplication_Concrete.
require import BarrettReduction_Concrete.

axiom q_less_p      : q < p.
axiom q_val_prop1 x : W64xN.valR x < q * q. 
axiom p_val_prop2   : 2*p < W64xN.modulusR. 

lemma p_val_prop1 x : W64xN.valR x < p * p.  by smt(q_less_p q_val_prop1 q_prime prime_p). qed.

lemma response_eq : 
  equiv [ SchnorrProver.response ~ JProver.response :
        w{1}   %% q  = (valR (witness0{2}) )  %% q
    /\  r{1}   %% q  = (valR secret_power{2}) %% q
    /\  c{1}   %% q  = (valR challenge_0{2})  %% q
    ==> res{1} %% q  = (valR res{2}) ].
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
rewrite H2.   smt (q_val_prop1).
smt.
smt.
smt(@W64xN).
smt.
smt(@W64xN).
rewrite H2. smt (q_val_prop1).
smt(@W64xN).
rewrite H2. smt.
smt(@W64xN).
smt.
smt(@W64xN).
rewrite H2. smt.
smt(@W64xN).
rewrite H2. smt.
smt(@W64xN).
rewrite H2. smt (p_val_prop2 q_less_p).
rewrite - H40.
rewrite - H33.
rewrite H2. 
have -> : (r{1} + c{1} * w{1}) %% q
  = (r{1} %% q + (c{1} * w{1}) %% q ) %% q.
smt (modzDmr modzDml).
rewrite  H19 H2. rewrite - H0.
rewrite  H11 H2. rewrite - H1.
rewrite  H27 H2. rewrite - H.
rewrite modzMml.
rewrite modzMmr. done.
qed.


lemma verify_eq : 
  equiv [ SchnorrVerifier.verify ~ JVerifier.verify :
       Sub.val(s{1}) = valR statement{2} %% p
       /\ Sub.val(z{1}) = valR commitment_0{2} %% p
       /\ c{1} %% q = (valR (challenge_0{2})) %% q
       /\ t{1} %% q = (valR response_0{2})  %% q
       ==> (res{1} = (res{2} = W64.one)) /\ (res{2} = W64.zero \/ res{2} = W64.one) ].
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
have  : valR statement{2} < q * q.
smt(q_val_prop1).
have : q * q < p * p. smt(q_less_p q_prime prime_p @StdOrder).
smt(p_val_prop1).
smt(P_pos).
smt(@W64xN).
smt(@W64xN).
rewrite H5. 
smt.
rewrite ri_un. rewrite H4. rewrite Rip_def. rewrite /ri. rewrite H3.
smt(). 
smt(q_prime).
smt.
smt(@W64xN).
smt.
smt(q_prime).
smt.
smt(@W64xN).
smt.
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
rewrite - (zp_eq (z{1} * s{1} ^^ c{1}) (Zp_SchnorrProtocol.g ^^ t{1})).
rewrite (exps Ring_ops_spec.g t{1}).
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

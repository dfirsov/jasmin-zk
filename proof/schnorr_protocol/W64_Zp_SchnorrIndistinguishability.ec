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






axiom bn_set_gg_prop : 
  phoare[ M.bn_set_g : true ==> valR res = Sub.val g  ] = 1%r.
axiom bn_set_go_prop : 
  phoare[ M.bn_set_p : true ==> valR res = p  ] = 1%r.
axiom bn_set_bf_prop : 
  phoare[ M.bn_set_bp : true ==> W64x2N.valR res = Ri  ] = 1%r.
axiom bn_set_eo_prop : 
  phoare[ M.bn_set_q : true ==> valR res = q  ] = 1%r.
axiom bn_set_eb_prop : 
  phoare[ M.bn_set_bq : true ==> W64x2N.valR res = Rip  ] = 1%r.



lemma zp_eq z1 z2 : (val z1 = val z2) = (z1 = z2). smt(@Zp). qed.
lemma zp_mul (z1 z2 : zmod) : val (z1 * z2) = (val z1 * val z2) %% p. 
by smt(@Zp). qed.
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

axiom q_less_p      : q < p.
axiom q_val_prop1 x : W64xN.valR x < q * q. 
axiom p_val_prop2   : 2*p < W64xN.modulusR. 

op g_int : int.

op completeness_relationJ (s: W64xN.R.t) (w:W64xN.R.t) = g_int ^ (W64xN.valR w) %% p = W64xN.valR s %% p.
op soundness_relationJ (s: W64xN.R.t) (w:W64xN.R.t) = g_int ^ (W64xN.valR w) %% p = W64xN.valR s %% p.





lemma p_val_prop1 x : W64xN.valR x < p * p.  
by smt(q_less_p q_val_prop1 q_prime prime_p). 
qed.


require import MontgomeryLadder_Concrete.
require import ModularMultiplication_Concrete.
require import BarrettReduction_Concrete.

lemma xxx:
  forall (a b : int), (inzmod a) = (inzmod b) <=> a %% p = b %% p.
smt(@Sub).
qed.


lemma w64_and (x y : W64.t) : (x = W64.one \/ x = W64.zero) 
 => (y = W64.one \/ y = W64.zero) => (x `&` y = W64.one) = (x = W64.one /\ y = W64.one). smt(@W64).
qed.


lemma w64_and_false (x y : W64.t) : (x = W64.one \/ x = W64.zero) 
 => (y = W64.one \/ y = W64.zero) => (x `&` y = W64.zero) = ((x = W64.one /\ y = W64.zero)  \/  (x = W64.zero /\ y = W64.one) \/ (x = W64.zero /\ y = W64.zero)). smt(@W64).
qed.

lemma exps_same (g : zmod) : ZModpField.exp g = ZModpRing.exp g.
rewrite /ZModpField.exp. rewrite /ZModpRing.exp. auto. qed.


lemma exps' (s : zmod) : forall n, 0 <= n => val (ZModpField.exp s n) = (val s ^ n) %% p.
apply intind. progress. smt(@Zp).
progress.
rewrite exprSr. auto.
rewrite ZModpField.exprSr. auto.
rewrite zp_mul.
rewrite H0.
smt(@IntDiv). 
qed.

lemma exps (x : zmod) : forall n, 0 <= n => (x ^ n)%Ring_ops_spec = (x ^^ n). 
apply intind. progress.
smt(@Zp @Ring).
progress.
have ->: (x ^ (i + 1))%Ring_ops_spec = x * (x^ i)%Ring_ops_spec. 
 rewrite /(^).
 have ->: asint x ^ (i + 1) = (asint x) * (asint x ^ i). smt.
 rewrite inzmodM. congr. rewrite asintK. auto.
have ->: (x ^^ (i + 1)) = x * (x^^i). smt.
rewrite H0.
auto.
qed.

lemma rels_compat s w : (valR s) %% p <> 0 =>
 soundness_relationJ s w 
 =  LSP.soundness_relation  (ZPS.Sub.insubd (inzmod (valR s))) (LSP.EG.inzmod (valR w)).
move => s_not_zero.
rewrite /soundness_relationJ /soundness_relation /IsDL.
 have by_def: g = (inzmod g_int). admit. 
rewrite by_def.
rewrite exp_lemma5. rewrite - by_def. apply g_unit. smt(@W64xN).
rewrite - by_def. rewrite g_q_assumption. auto.
rewrite  lll. rewrite - by_def. apply g_unit.
rewrite - bbb.
rewrite ZPS.Sub.insubdK. rewrite /P. rewrite - by_def. smt(g_unit @ZModpField).
rewrite ZPS.Sub.insubdK. rewrite /P. 
apply unitE. rewrite /Zp.zero. smt(@Zp).
have ->: (ZModpField.exp (inzmod g_int) (valR w)) = ((inzmod g_int) ^^ (valR w)). rewrite /(^^). auto.
rewrite - exps. smt(@W64xN).
rewrite /(^).
rewrite inzmodK.
have ->: (g_int %% p) = g_int. admit. (* by assumption *)
smt.
qed.


lemma verify_eq : 
  equiv [ SchnorrVerifier.verify ~ JVerifier.verify :
          Sub.val(s{1}) = valR statement{2}    %% p
       /\ Sub.val(z{1}) = valR commitment_0{2} %% p
       /\ c{1} %% q = (valR (challenge_0{2}))  %% q
       /\ t{1} %% q = (valR response_0{2})     %% q
       ==> (res{1} = (res{2} = W64.one)) /\ (res{2} = W64.zero \/ res{2} = W64.one) ].
proc. sp. simplify. wp.
ecall {2} (bn_eq_correct v3{2} v4{2}). simplify. 
ecall {2} (bn_set1_correct). simplify. 
ecall {2} (bn_expm_correct group_barrett{2} group_order{2} statement{2} exp_order{2}). simplify.      
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
rewrite H5. smt(prime_p).
smt(@W64xN).
smt(@W64xN).
rewrite H5. 
smt(p_val_prop1).
smt(prime_p).
smt(@W64xN).
smt(@W64xN).
rewrite H5. 
smt(p_val_prop1).
rewrite ri_un. rewrite H4. rewrite Rip_def. rewrite /ri. rewrite H3. smt().
smt(q_prime).
smt(@W64xN).
smt(@W64xN).
smt(q_val_prop1).
smt(q_prime).
smt(@W64xN).
smt(@W64xN).
smt(q_val_prop1).
smt().
rewrite /R. rewrite - H6.  
rewrite R2.bnK. auto.
smt(@W64xN).
smt().
smt(@W64xN).
smt().
smt(@Zp).
  have sq_fact: ((ZModpField.exp s{1} q) = ZPS.Zp.one)
            = (result15 = W64.one). 
  rewrite H58 H56 H15 H5 H3 H57 - H.
  have ->: (ZModpField.exp s{1} q) = s{1} ^^ q. 
    rewrite /(^^). smt(@ZModpField).
    rewrite - exps. smt(q_prime). rewrite /(^) /asint /ZPS.Zp.one xxx.  
    smt.
rewrite sq_fact.
have ->: (result12 `&` result15 = W64.one) 
  = (result12 = W64.one /\ result15 = W64.one). 
rewrite w64_and. smt(). smt(). auto.
rewrite  H52 - H48 H51 H39  H3 - H2 H7 H23 H42 H15 H5 - H - H0 H31 H3 - H1.
case (result15 = W64.one). progress. simplify.
rewrite - (zp_eq (g ^^ t{1}) (s{1} ^^ c{1} * z{1}) ). simplify.
 have ->: (val (g ^^ t{1}) = val (s{1} ^^ c{1} * z{1}))
  = (val (z{1} * s{1} ^^ c{1} ) = val (g ^^ t{1})). smt().
rewrite zp_mul.
congr.
congr.
congr.
congr.
rewrite /(^^).
have ->: (ZModpRing.exp s{1} c{1}) = (ZModpField.exp s{1} c{1}). 
rewrite exps_same. auto.
have  <- : (ZModpField.exp s{1} (c{1} %% q)) = (ZModpField.exp s{1} c{1}). 
rewrite (exp_mod s{1} c{1} q). rewrite sq_fact. auto. auto.
rewrite exps'. smt(@IntDiv).
auto.
rewrite /(^).
have ->: val (g ^^ t{1})  = val (g ^^ (t{1} %% q)).
rewrite /(^^). rewrite - exps_same.
rewrite (exp_mod g t{1} q). rewrite g_q_assumption. auto.
auto.
rewrite - exps'. smt(@IntDiv). rewrite /(^^). rewrite exps_same. auto.
progress.
rewrite (w64_and result12 result15). smt(). smt().
rewrite (w64_and_false result12 result15). 
smt(). smt().
smt().
qed.

require import UniformSampling_Concrete.

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

require import List Int AllCore Distr.

from Jasmin require import JModel.

require import AuxLemmas.
require import Ops_LeakageAnalysis.


(* SAMPLING LEAKAGES  *)
require import W64_SchnorrExtract_ct.
module M1 = W64_SchnorrExtract_ct.M(W64_SchnorrExtract_ct.Syscall).

op commitment_prefix : leakages_t.
op commitment_g (x : int) : leakages_t.
op commitment_step (i : int) : leakages_t.
 
axiom commitment_g_comp_1 x : x <= 0 => commitment_g x = [].
axiom commitment_g_comp_2 x : 0 <  x  => commitment_g x = commitment_step (x-1) ++ commitment_g (x - 1).

op commitment_suffix : leakages_t.

op commitment_f (x : int) : leakages_t = commitment_g x ++ commitment_prefix.
op commitment_t (x : int) : leakages_t = commitment_suffix ++ commitment_f (x - 1).

axiom commitment_t_inj : injective commitment_t.


lemma commitment_leakages1 :
  hoare [ M(Syscall).commitment_indexed : M.leakages = [] 
     ==> M.leakages = commitment_t res.`1].
admitted.

lemma commitment_leakages2 &m : (glob M1){m} = [] =>
  Pr[ M1.commitment_indexed() @ &m : M1.leakages <> commitment_t res.`1 ] = 0%r.
admitted.

lemma commitment_leakages3 l x &m : (glob M1){m} = [] =>
  Pr[ M1.commitment_indexed() @ &m : M1.leakages = l  /\ res.`2 = x ]
  = Pr[ M1.commitment_indexed() @ &m : l = commitment_t res.`1 /\ res.`2 = x ].
admitted.

lemma commitment_leakages_inv x l &m : (glob M1){m} = [] 
 => Pr[ M1.commitment_indexed() @ &m : M1.leakages = l /\ res.`2 = x  ]
  = Pr[ M1.commitment_indexed() @ &m :  (inv (-1) commitment_t) l = res.`1  /\ res.`2 = x  ].
admitted.

require import W64_SchnorrExtract.
module M2 = W64_SchnorrExtract.M(W64_SchnorrExtract.Syscall).  

lemma M1_M2_commitment :
  equiv  [ M1.commitment_indexed ~ M2.commitment_indexed
    : ={arg} ==> ={res}  ].
admitted.

require import Ring_ops_proof.
require import Ring_ops_spec.
require import UniformSampling_Abstract.
require import UniformSampling_Concrete.

require Constants.

require import IntDiv.
require MontgomeryLadder_Concrete.
require import ConstantsValidation.

clone import MontgomeryLadder_Concrete as MLC with op Zp.p <- Constants.p.

equiv commitment_rsample_equiv:
 M2.commitment_indexed ~ M2.rsample:
   Constants.q = W64xN.valR byte_z{2}
  ==> res{1}.`3 = res{2}.`2 /\ res{1}.`1 = res{2}.`1.
proc*.
inline M2.commitment_indexed. 
wp. call {1} (_:true ==> true).  admit.
seq 10 0 : ( exp_order{1} =  byte_z{2}). 
call {1} Constants.bn_set_bp_correct.
call {1} Constants.bn_set_g_correct.
call {1} Constants.bn_set_p_correct.
call {1} Constants.bn_set_q_correct.
wp. skip. progress. smt.
simplify.
call (_:true). sim. skip. auto.
qed.
equiv rsample_cspec_equiv:
 M1.commitment_indexed ~ CSpecFp.rsample:
   Constants.q = a{2}
  ==> W64xN.valR res{1}.`3 = res{2}.`2 /\ res{1}.`1 = res{2}.`1.
transitivity M2.commitment_indexed 
 (={arg} ==> ={res})
 (Constants.q = a{2}
  ==> W64xN.valR res{1}.`3 = res{2}.`2 /\ res{1}.`1 = res{2}.`1).
auto. auto.
conseq M1_M2_commitment. 
transitivity M2.rsample
  (Constants.q = W64xN.valR byte_z{2}
  ==> res{1}.`3 = res{2}.`2 /\ res{1}.`1 = res{2}.`1)
  (W64xN.valR byte_z{1} = a{2}
  ==> W64xN.valR res{1}.`2 = res{2}.`2 /\ res{1}.`1 = res{2}.`1).
progress. exists (W64xN.R.bn_ofint Constants.q).
split. 
rewrite W64xN.R.bnk_ofintK. auto. admit.
rewrite W64xN.R.bnk_ofintK. auto. admit.
smt().
conseq commitment_rsample_equiv. 
conseq rsample_cspec.
qed.


lemma commitment_cspec_pr1 (i  : int) x &m : 
  Pr[ M1.commitment_indexed() @ &m : res.`1 = i /\ res.`3 = x ]
   = Pr[ CSpecFp.rsample(Constants.q) @ &m : res = (i, W64xN.valR x)  ].
byequiv.
conseq rsample_cspec_equiv. progress. progress. smt().
smt(@W64xN). auto. auto.
smt(@W64xN).
auto. auto.
qed.


lemma val_congr a b :  
  W64xN.valR a = W64xN.valR b => a = b.
smt(@W64xN).
qed.


lemma val_congr2N a b :  
  W64x2N.valR a = W64x2N.valR b => a = b.
smt(@W64x2N).
qed.

lemma commitment_cspec_pr2 &m :
  Pr[ M1.commitment_indexed() @ &m : res.`2 <> W64xN.R.bn_ofint (Constants.g ^ (W64xN.valR res.`3) %% Constants.p) ] = 0%r.
have -> : Pr[ M1.commitment_indexed() @ &m : res.`2 <> W64xN.R.bn_ofint (Constants.g ^ (W64xN.valR res.`3) %% Constants.p) ] 
 = Pr[ M2.commitment_indexed() @ &m : res.`2 <> W64xN.R.bn_ofint (Constants.g ^ (W64xN.valR res.`3) %% Constants.p) ].
byequiv. conseq M1_M2_commitment. auto. auto.
byphoare. hoare.
simplify. proc.
simplify.
seq 11 : (W64xN.valR exp_order = Constants.q
       /\ W64xN.valR group_order = Constants.p
       /\ W64xN.valR group_generator = Constants.g
       /\ barrett_parameter = R).
call (_:true).  auto.
call Constants.bn_set_bp_correct_hoare.
call Constants.bn_set_g_correct_hoare.
call Constants.bn_set_p_correct_hoare.
call Constants.bn_set_q_correct_hoare.
wp. skip. progress. apply (val_congr2N result2 R). rewrite H2.
rewrite /R.
rewrite W64x2N.R.bn_ofintK.
rewrite /Ri. 
rewrite - bp_correct.
rewrite nasty_id.
have : Constants.bp < W64x2N.modulusR. auto.
smt(@IntDiv).
exists* barrett_parameter, group_order, group_generator, secret_power.
elim*. move => bp p g r.
call (bn_expm_correct_hoare bp p g r).
skip. progress. rewrite H1. auto.
apply val_congr.
rewrite H4. rewrite  H1.
rewrite W64xN.R.bn_ofintK.
pose x := Constants.g ^ (W64xN.valR secret_power{hr}).
have : 0 <= Constants.p < W64xN.modulusR. auto.
smt(@IntDiv). 
auto.
auto.
qed.

lemma commitment_cspec_pr3 i x &m :
  Pr[ M1.commitment_indexed() @ &m : res.`1 = i /\ (res.`2, res.`3) = (W64xN.R.bn_ofint (Constants.q ^ (W64xN.valR res.`3) %% Constants.p), x) ] 
   = Pr[ M1.commitment_indexed() @ &m : res.`1 = i /\ res.`3 = x ].
have -> : Pr[ M1.commitment_indexed() @ &m : res.`1 = i /\ res.`3 = x ]
 = Pr[ M1.commitment_indexed() @ &m : res.`1 = i /\ res.`3 = x 
    /\ res.`2 = W64xN.R.bn_ofint (Constants.q ^ (W64xN.valR res.`3) %% Constants.p) ] + Pr[ M1.commitment_indexed() @ &m : res.`1 = i /\ res.`3 = x 
    /\ res.`2 <> W64xN.R.bn_ofint (Constants.q ^ (W64xN.valR res.`3) %% Constants.p) ].
rewrite Pr[mu_split (res.`2 = W64xN.R.bn_ofint (Constants.q ^ (W64xN.valR res.`3) %% Constants.p))]. smt().
have ->:  Pr[ M1.commitment_indexed() @ &m : res.`1 = i /\ res.`3 = x 
    /\ res.`2 <> W64xN.R.bn_ofint (Constants.q ^ (W64xN.valR res.`3) %% Constants.p) ] = 0%r. 
   have : Pr[ M1.commitment_indexed() @ &m : res.`1 = i /\ res.`3 = x 
    /\ res.`2 <> W64xN.R.bn_ofint (Constants.q ^ (W64xN.valR res.`3) %% Constants.p) ] <= Pr[ M1.commitment_indexed() @ &m : res.`2 <> W64xN.R.bn_ofint (Constants.q ^ (W64xN.valR res.`3) %% Constants.p) ]. rewrite Pr[mu_sub]. smt(). auto.
  have ->: Pr[ M1.commitment_indexed() @ &m : res.`2 <> W64xN.R.bn_ofint (Constants.q ^ (W64xN.valR res.`3) %% Constants.p) ] = 0%r. rewrite commitment_cspec_pr2.
auto. smt(@Distr). 
simplify. rewrite Pr[mu_eq]. smt(). auto.
qed.

lemma commitment_cspec_pr i x &m :
  Pr[ M1.commitment_indexed() @ &m : res.`1 = i /\ 
   (res.`2, res.`3) = (W64xN.R.bn_ofint (Constants.q ^ (W64xN.valR res.`3) %% Constants.p), x)  ] 
   = Pr[ CSpecFp.rsample(Constants.q) @ &m : res = (i, W64xN.valR x) ].
rewrite commitment_cspec_pr3.
rewrite commitment_cspec_pr1. auto.
qed.

lemma commitment_index_pos &m  : Pr[M1.commitment_indexed() @ &m : res.`1 <= 0 ] = 0%r.
admitted.

import W64xN.

op g l : real 
 = if inv (-1) commitment_t l <= 0 then 0%r else 
     mu D (predC (RSP Constants.q)) ^ (inv (-1) commitment_t l - 1)
       * (1%r / Ring_ops_spec.M%r).

        
lemma leakfree1 &m x l: (glob M1){m} = [] 
  => Pr[ M1.commitment_indexed() @ &m : M1.leakages = l  /\ 
   (res.`2, res.`3) = (W64xN.R.bn_ofint (Constants.q ^ (W64xN.valR x) %% Constants.p), x) ] 
      = if W64xN.valR x < Constants.q then g l else 0%r.
admitted.


op h  : real = 1%r/Constants.q%r. 

lemma leakfree2 &m x: 
 Pr[ M1.commitment_indexed() @ &m : 
   (res.`2, res.`3) = (W64xN.R.bn_ofint (Constants.q ^ (W64xN.valR x) %% Constants.p), x)  ] = if W64xN.valR x < Constants.q then h else 0%r. 
admitted.

op f l = h / g l.

lemma commitment_indexed_leakfree l a &m: (glob M1){m} = [] 
 =>  let v = Pr[ M1.commitment_indexed() @ &m : (res.`2, res.`3) = a  ] in 
     let w = Pr[ M1.commitment_indexed() @ &m : M1.leakages = l  /\ (res.`2, res.`3) = a  ] in 
  0%r < w => v/w 
  = f  l.
move => l_empty v w f1.

pose a1_val := W64xN.R.bn_ofint (Constants.q ^ (W64xN.valR a.`2) %% Constants.p).  
  
have fact1 : a.`1 = a1_val.
admit.
have fact2 : valR a.`2 < Constants.q.
admit.

have -> : v = Pr[M1.commitment_indexed() @ &m : (res.`2, res.`3) = (a1_val, a.`2)].
rewrite  /v Pr[mu_eq]. smt(). auto.
have ->:  w = Pr[M1.commitment_indexed() @ &m :
           M1.leakages = l /\ (res.`2, res.`3) = (a1_val, a.`2)].
rewrite  /w Pr[mu_eq]. smt(). auto.

rewrite /a1_val.

rewrite (leakfree1 &m a.`2 l _).  auto.
rewrite  (leakfree2 &m a.`2 ).  auto.

rewrite fact2. simplify. auto.
qed.


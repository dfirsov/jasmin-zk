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
  Pr[ M1.commitment_indexed() @ &m : M1.leakages = l  /\ res.`3 = x ]
  = Pr[ M1.commitment_indexed() @ &m : l = commitment_t res.`1 /\ res.`3 = x ].
admitted.

lemma commitment_leakages_inv x l &m : (glob M1){m} = [] 
 => Pr[ M1.commitment_indexed() @ &m : M1.leakages = l /\ res.`3 = x  ]
  = Pr[ M1.commitment_indexed() @ &m :  (inv (-1) commitment_t) l = res.`1  /\ res.`3 = x  ].
admitted.

require import W64_SchnorrExtract.
module M2 = W64_SchnorrExtract.M(W64_SchnorrExtract.Syscall).  

lemma M1_M2_swapr :
  equiv  [ M1.swapr ~ M2.swapr
    : ={arg} ==> ={res}  ].
proc. sim.
wp. while (={i,y,x,mask}). wp. skip. progress. 
wp. skip. progress. 
qed.

lemma M1_M2_bn_shrink :
  equiv  [ M1.bn_shrink ~ M2.bn_shrink
    : ={arg} ==> ={res}  ].
proc. 
wp. while (={x,i,r}). wp. skip. progress. 
wp. skip. progress. 
qed.

lemma M1_M2_dcminusP :
  equiv  [ M1.dcminusP ~ M2.dcminusP
    : ={arg} ==> ={res}  ].
proc.  sim. qed.

lemma M1_M2_bn_expand :
  equiv  [ M1.bn_expand ~ M2.bn_expand
    : ={arg} ==> ={res}  ].
proc.  sim. 
while (={i,r,aux}). wp. skip. progress.
wp.  while (={x,i,r}). wp. skip. progress.
wp. skip. progress.
qed.


lemma M1_M2_dbn_subc :
  equiv  [ M1.dbn_subc ~ M2.dbn_subc
    : ={arg} ==> ={res}  ].
proc.  sim.  qed.

lemma M1_M2_bn_muln :
  equiv  [ M1.bn_muln ~ M2.bn_muln
    : ={arg} ==> ={res}  ].
proc.  sim.  qed.

lemma M1_M2_dbn_muln :
  equiv  [ M1.dbn_muln ~ M2.dbn_muln
    : ={arg} ==> ={res}  ].
proc.  sim.  qed.

lemma M1_M2_div2 :
  equiv  [ M1.div2 ~ M2.div2
    : ={arg} ==> ={res}  ].
proc. sim.  
while (={i,r,x,aux}). wp. skip. progress.
wp. skip. progress.
qed.

lemma M1_M2_bn_breduce :
  equiv  [ M1.bn_breduce ~ M2.bn_breduce
    : ={arg} ==> ={res}  ].
proc.
wp. 
wp. call M1_M2_bn_shrink.
wp. call M1_M2_dcminusP.
wp. call M1_M2_bn_expand.
wp. call M1_M2_dbn_subc.
wp. call M1_M2_bn_muln.
wp. call M1_M2_bn_shrink.
wp. call M1_M2_div2.
wp. call M1_M2_dbn_muln.
wp. skip. progress.
qed.


lemma M1_M2_mulm :
  equiv  [ M1.mulm ~ M2.mulm
    : ={arg} ==> ={res}  ].
proc. sim.  
wp. call M1_M2_bn_breduce.
wp. call M1_M2_bn_muln.
wp. skip. progress.
qed.


lemma M1_M2_bn_copy :
  equiv  [ M1.bn_copy ~ M2.bn_copy
    : ={arg} ==> ={res}  ].
proc.  sim.  qed.

lemma M1_M2_bn_set1 :
  equiv  [ M1.bn_set1 ~ M2.bn_set1
    : ={arg} ==> ={res}  ].
proc.  sim.  
while (={i,a}). wp. skip. progress.
wp. skip. progress.
qed.

lemma M1_M2_ith_bit :
  equiv  [ M1.ith_bit ~ M2.ith_bit
    : ={arg} ==> ={res}  ].
proc.  sim.  qed.

lemma M1_M2_expm :
  equiv  [ M1.expm ~ M2.expm
    : ={arg} ==> ={res}  ].
proc. 
while (={m,r,n,i,b,x1,x2,x11,b}). 
wp. call M1_M2_swapr.
wp. call M1_M2_mulm.
wp. call M1_M2_mulm.
wp. call M1_M2_bn_copy.
wp. call M1_M2_swapr.
wp. call M1_M2_ith_bit.
wp. skip. progress.
wp. 
wp. call M1_M2_bn_copy.
wp. call M1_M2_bn_copy.
wp. call M1_M2_bn_set1.
wp. skip. progress.
qed.

lemma M1_M2_rsample :
  equiv  [ M1.rsample ~ M2.rsample
    : ={arg} ==> ={res}  ].
proc. sim. call(_:true). wp. 
while(={i,a}). wp. skip. auto. wp. skip. auto.
wp. skip. auto. qed.

lemma M1_M2_commitment :
  equiv  [ M1.commitment_indexed ~ M2.commitment_indexed
    : ={arg} ==> ={res}  ].
proc.  
wp. call M1_M2_expm. simplify.
wp. call M1_M2_rsample.  
wp. call (_:true). sim. progress.
wp. call (_:true). sim. progress.
wp. call (_:true). sim. progress.
wp. call (_:true). sim. progress. 
wp. skip. progress. 
qed.

    
require import Ring_ops_proof.
require import Ring_ops_spec.
require import UniformSampling_Abstract.
require import UniformSampling_Concrete.

require Constants.

require import IntDiv.
require MontgomeryLadder_Concrete.
require import ConstantsValidation.

clone import MontgomeryLadder_Concrete as MLC with op Zp.p <- Constants.p.


lemma val_congr a b :  
  W64xN.valR a = W64xN.valR b => a = b.
smt(@W64xN).
qed.


lemma val_congr2N a b :  
  W64x2N.valR a = W64x2N.valR b => a = b.
smt(@W64x2N).
qed.


equiv commitment_rsample_equiv:
 M2.commitment_indexed ~ M2.rsample:
   Constants.q = W64xN.valR byte_z{2}
  ==> res{1}.`3 = res{2}.`2 /\ res{1}.`1 = res{2}.`1.
proc*.
inline M2.commitment_indexed. 
wp. 
seq 11 1 : (exp_order{1} =  byte_z{2}
 /\ W64x2N.valR barrett_parameter{1} = Constants.bp
 /\ W64xN.valR group_order{1} = Constants.p
 /\ W64xN.valR group_generator{1} = Constants.g
 /\ W64xN.valR exp_order{1} = Constants.q
 /\ (i, secret_power){1} = r{2}). 
call (_:true). sim. 
call {1} Constants.bn_set_bp_correct.
call {1} Constants.bn_set_g_correct.
call {1} Constants.bn_set_p_correct.
call {1} Constants.bn_set_q_correct.
wp. skip. progress. smt.  smt().
ecall {1} (bn_expm_correct barrett_parameter{1} group_order{1} group_generator{1} secret_power{1}). skip. progress.
rewrite H1. auto. rewrite /R /Ri. 
apply  val_congr2N. rewrite H.
rewrite nasty_id.
rewrite - bp_correct.
rewrite W64x2N.R.bn_ofintK.
have : Constants.bp < W64x2N.modulusR. auto.
smt(@IntDiv).
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
rewrite W64xN.R.bnk_ofintK. auto.
smt(@Ring @IntDiv).
rewrite W64xN.R.bnk_ofintK. auto. smt(@Ring @IntDiv).
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
  Pr[ M1.commitment_indexed() @ &m : res.`1 = i /\ (res.`2, res.`3) = (W64xN.R.bn_ofint (Constants.g ^ (W64xN.valR res.`3) %% Constants.p), x) ] 
   = Pr[ M1.commitment_indexed() @ &m : res.`1 = i /\ res.`3 = x ].
have -> : Pr[ M1.commitment_indexed() @ &m : res.`1 = i /\ res.`3 = x ]
 = Pr[ M1.commitment_indexed() @ &m : res.`1 = i /\ res.`3 = x 
    /\ res.`2 = W64xN.R.bn_ofint (Constants.g ^ (W64xN.valR res.`3) %% Constants.p) ] + Pr[ M1.commitment_indexed() @ &m : res.`1 = i /\ res.`3 = x 
    /\ res.`2 <> W64xN.R.bn_ofint (Constants.g ^ (W64xN.valR res.`3) %% Constants.p) ].
rewrite Pr[mu_split (res.`2 = W64xN.R.bn_ofint (Constants.g ^ (W64xN.valR res.`3) %% Constants.p))]. smt().
have ->:  Pr[ M1.commitment_indexed() @ &m : res.`1 = i /\ res.`3 = x 
    /\ res.`2 <> W64xN.R.bn_ofint (Constants.g ^ (W64xN.valR res.`3) %% Constants.p) ] = 0%r. 
   have : Pr[ M1.commitment_indexed() @ &m : res.`1 = i /\ res.`3 = x 
    /\ res.`2 <> W64xN.R.bn_ofint (Constants.g ^ (W64xN.valR res.`3) %% Constants.p) ] <= Pr[ M1.commitment_indexed() @ &m : res.`2 <> W64xN.R.bn_ofint (Constants.g ^ (W64xN.valR res.`3) %% Constants.p) ]. rewrite Pr[mu_sub]. smt(). auto.
  have ->: Pr[ M1.commitment_indexed() @ &m : res.`2 <> W64xN.R.bn_ofint (Constants.g ^ (W64xN.valR res.`3) %% Constants.p) ] = 0%r. 
apply  (commitment_cspec_pr2 &m).
auto. smt(@Distr). 
simplify. rewrite Pr[mu_eq]. smt(). auto.
qed.

lemma commitment_cspec_pr i x &m :
  Pr[ M1.commitment_indexed() @ &m : res.`1 = i /\ 
   (res.`2, res.`3) = (W64xN.R.bn_ofint (Constants.g ^ (W64xN.valR res.`3) %% Constants.p), x)  ] 
   = Pr[ CSpecFp.rsample(Constants.q) @ &m : res = (i, W64xN.valR x) ].
rewrite commitment_cspec_pr3.
rewrite commitment_cspec_pr1. auto.
qed.

lemma commitment_index_pos &m  : Pr[M1.commitment_indexed() @ &m : res.`1 <= 0 ] = 0%r.
byphoare (_: true ==> _);auto. hoare.
proc.  simplify.
wp. call (_:true). auto.
wp. seq 19 : (true). auto.
inline W64_SchnorrExtract_ct.M(W64_SchnorrExtract_ct.Syscall).rsample.
unroll 19. rcondt 19. wp. wp. 
call (_:true). wp. auto. wp. skip. auto.
wp. while (0 < i0). wp. call (_:true). auto. wp.  call (_:true). auto.  wp. 
inline*. wp. rnd. wp. skip. progress. 
smt(). wp. call (_:true). auto.  wp.  
call (_:true). auto. wp. 
call (_:true). auto. wp. 
call (_:true). auto. wp. skip. 
progress. smt().
qed.

import W64xN.

op g l : real 
 = if inv (-1) commitment_t l <= 0 then 0%r else 
     mu D (predC (RSP Constants.q)) ^ (inv (-1) commitment_t l - 1)
       * (1%r / Ring_ops_spec.M%r).

        
lemma leakfree1 &m x l: (glob M1){m} = [] 
  => Pr[ M1.commitment_indexed() @ &m : M1.leakages = l  /\ 
   (res.`2, res.`3) = (W64xN.R.bn_ofint (Constants.g ^ (W64xN.valR x) %% Constants.p), x) ] 
      = if W64xN.valR x < Constants.q then g l else 0%r.
have ->:
 Pr[M1.commitment_indexed() @ &m :
   M1.leakages = l /\
   (res.`2, res.`3) = ((R.bn_ofint (Constants.g ^ valR x %% Constants.p))%R, x)]
 = Pr[M1.commitment_indexed() @ &m :
   M1.leakages = l /\ res.`3 = x]. 
  have ->: Pr[M1.commitment_indexed() @ &m : M1.leakages = l /\ res.`3 = x] =
    Pr[M1.commitment_indexed() @ &m : M1.leakages = l /\ res.`3 = x /\ res.`2 = (R.bn_ofint (Constants.g ^ valR res.`3 %% Constants.p))]
   + Pr[M1.commitment_indexed() @ &m : M1.leakages = l /\ res.`3 = x /\ res.`2 <> (R.bn_ofint (Constants.g ^ valR res.`3 %% Constants.p))].
    rewrite Pr[mu_split ( res.`2 = (R.bn_ofint (Constants.g ^ valR x %% Constants.p))) ].
    smt().
   have ->: Pr[M1.commitment_indexed() @ &m :
   M1.leakages = l /\
   res.`3 = x /\ res.`2 <> (R.bn_ofint (Constants.g ^ valR res.`3 %% Constants.p))%R] = 0%r.
     have : Pr[M1.commitment_indexed() @ &m :
           res.`2 <> (R.bn_ofint (Constants.g ^ valR res.`3 %% Constants.p))%R]  = 0%r.
     apply (commitment_cspec_pr2 &m).
      smt(@Distr).
    simplify. progress. rewrite Pr[mu_eq]. smt(). auto. 
move => glob_empty. 
rewrite (commitment_leakages_inv x l &m glob_empty).
case (inv (-1) commitment_t l <= 0). 
move => q. rewrite /g. rewrite q.  simplify. 
  have : Pr[M1.commitment_indexed() @ &m :
   (inv (-1) commitment_t l = res.`1) /\ res.`3 = x] 
    <= Pr[M1.commitment_indexed() @ &m : res.`1 <= 0 ]. simplify. rewrite Pr[mu_sub]. smt().
   auto. smt(commitment_index_pos @Distr).
move => q.
rewrite /g.
have ->: (inv (-1) commitment_t l <= 0) = false. smt(). simplify.  
have ->: Pr[W64_SchnorrExtract_ct.M(W64_SchnorrExtract_ct.Syscall).commitment_indexed
   () @ &m : inv (-1) commitment_t l = res.`1 /\ res.`3 = x]
 = Pr[W64_SchnorrExtract_ct.M(W64_SchnorrExtract_ct.Syscall).commitment_indexed
   () @ &m : res.`1 = inv (-1) commitment_t l /\ res.`3 = x]. rewrite Pr[mu_eq]. smt(). auto.
rewrite commitment_cspec_pr1.
case (valR x < Constants.q) => case1.
rewrite rsample_pr. smt().
auto. 
have ->: mu1 D (W64xN.valR x) = 1%r / Ring_ops_spec.M%r.
rewrite duniform1E_uniq. smt(@List).
 have f1 : 0 <= W64xN.valR x < Ring_ops_spec.M. smt(@W64xN).  smt(@Distr @List). 
smt().
have : Pr[CSpecFp.rsample(Constants.q) @ &m :
                   res.`2 = valR x] = 0%r.
apply rsample_pr_out. smt().
smt(@Distr).
qed.


op h  : real = 1%r/Constants.q%r. 

lemma leakfree2 &m x: 
 Pr[ M1.commitment_indexed() @ &m : 
   (res.`2, res.`3) = (W64xN.R.bn_ofint (Constants.g ^ (W64xN.valR x) %% Constants.p), x)  ] = if W64xN.valR x < Constants.q then h else 0%r. 
proof. 
 have  : Pr[ M1.commitment_indexed() @ &m : res.`3 = x ] =
  Pr[ CSpecFp.rsample(Constants.q) @ &m : res.`2 =  W64xN.valR x ].
  byequiv. conseq rsample_cspec_equiv. auto. 
progress. rewrite - H. auto. smt(@W64xN). auto. auto.
 have -> : Pr[M1.commitment_indexed() @ &m : res.`3 = x] 
       = Pr[ M1.commitment_indexed() @ &m : 
   (res.`2, res.`3) = (W64xN.R.bn_ofint (Constants.g ^ (W64xN.valR x) %% Constants.p), x)  ]. 
have : Pr[M1.commitment_indexed() @ &m : res.`3 = x]
 = Pr[M1.commitment_indexed() @ &m : res.`3 = x /\ res.`2 = (R.bn_ofint (Constants.g ^ valR res.`3 %% Constants.p))%R]
 + Pr[M1.commitment_indexed() @ &m : res.`3 = x /\ res.`2 <> (R.bn_ofint (Constants.g ^ valR res.`3 %% Constants.p))%R].
rewrite Pr[mu_split (res.`2 = (R.bn_ofint (Constants.g ^ valR res.`3 %% Constants.p))%R) ]. auto.
  have -> : Pr[M1.commitment_indexed() @ &m : res.`3 = x /\ res.`2 <> (R.bn_ofint (Constants.g ^ valR res.`3 %% Constants.p))%R] = 0%r.
   have : Pr[M1.commitment_indexed() @ &m : res.`3 = x /\ res.`2 <> (R.bn_ofint (Constants.g ^ valR res.`3 %% Constants.p))%R] <= Pr[M1.commitment_indexed() @ &m :  res.`2 <> (R.bn_ofint (Constants.g ^ valR res.`3 %% Constants.p))%R]. rewrite Pr[mu_sub].
auto. auto. 
rewrite  (commitment_cspec_pr2 &m).
smt (@Distr). move => h. rewrite h.
simplify. smt(@Distr). 
move => f. rewrite f. clear f.
case (valR x < Constants.q). move => q.
rewrite rsample_uni. auto. smt(@W64xN).
auto. auto. move => q.
rewrite rsample_pr_out. 
smt().    auto.
qed.


op f l = h / g l.

lemma commitment_indexed_leakfree l a &m: (glob M1){m} = [] 
 =>  let v = Pr[ M1.commitment_indexed() @ &m : (res.`2, res.`3) = a  ] in 
     let w = Pr[ M1.commitment_indexed() @ &m : M1.leakages = l  /\ (res.`2, res.`3) = a  ] in 
  0%r < w => v/w 
  = f  l.
move => l_empty v w f1.
pose a1_val := W64xN.R.bn_ofint (Constants.g ^ (W64xN.valR a.`2) %% Constants.p).  
have fact1 : a.`1 = a1_val.
   case (a.`1 = a1_val). auto.
   move => q.
   have : Pr[M1.commitment_indexed() @ &m :
                 res.`2  = a.`1 /\ res.`3 = a.`2 ] = Pr[M1.commitment_indexed() @ &m :
                 res.`2  = a.`1 /\ res.`3 = a.`2 /\ res.`2 <> a1_val ].
   rewrite Pr[mu_eq]. smt(). auto.
   have : Pr[M1.commitment_indexed() @ &m : res.`2 = a.`1 /\ res.`3 = a.`2 /\ res.`2 <> a1_val] = 0%r.
     have : Pr[M1.commitment_indexed() @ &m : res.`2 = a.`1 /\ res.`3 = a.`2 /\ res.`2 <> a1_val] <=
             Pr[M1.commitment_indexed() @ &m : res.`2 <> a1_val /\ res.`3 = a.`2 ]. 
      rewrite Pr[mu_sub]. auto. auto.
     have : Pr[M1.commitment_indexed() @ &m : res.`2 <> a1_val /\ res.`3 = a.`2] = 0%r.
     rewrite /a1_val. 
     have : Pr[M1.commitment_indexed() @ &m :
   res.`2 <> (R.bn_ofint (Constants.g ^ valR a.`2 %% Constants.p))%R /\
   res.`3 = a.`2] <= Pr[M1.commitment_indexed() @ &m :
   res.`2 <> (R.bn_ofint (Constants.g ^ valR res.`3 %% Constants.p))%R ].
   rewrite Pr[mu_sub]. smt(). auto.
    rewrite  (commitment_cspec_pr2 &m). smt(@Distr). smt(@Distr).
    move => qq. rewrite qq. clear qq q.
    move => G1.
    have : w <= 0%r. rewrite - G1.
    rewrite /w. rewrite Pr[mu_sub]. smt(). auto.
smt().

have fact2 : valR a.`2 < Constants.q.
 have : v <= Pr[M1.commitment_indexed() @ &m : res.`3 = a.`2]. rewrite  /v Pr[mu_sub]. auto. auto.
 have -> : Pr[M1.commitment_indexed() @ &m : res.`3 = a.`2] = Pr[ CSpecFp.rsample(Constants.q) @ &m : res.`2 = valR a.`2 ].   byequiv. conseq rsample_cspec_equiv. auto. progress.
smt(). smt(@W64xN). auto. auto.
case (valR a.`2 < Constants.q). auto.
move => q.
rewrite rsample_pr_out.  smt().
have : 0%r < v. 
   have : w <= v. rewrite /v /w Pr[mu_sub]. smt(). auto. smt().
smt().
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


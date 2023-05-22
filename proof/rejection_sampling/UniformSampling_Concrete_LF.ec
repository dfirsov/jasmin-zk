require import List Int AllCore Distr.

from Jasmin require import JModel.

require import AuxLemmas.
require import Ops_LeakageAnalysis.


(* SAMPLING LEAKAGES  *)
require import W64_SchnorrExtract_ct.
module M1 = W64_SchnorrExtract_ct.M(W64_SchnorrExtract_ct.Syscall).

op samp_prefix : leakages_t = 
  LeakCond (! set0_64_.`2) :: LeakAddr [] :: LeakAddr [] :: (set0_f 32 ++
                                                           [LeakAddr [];
                                                              LeakAddr []]).
op samp_g (x : int) : leakages_t.
op samp_step (i : int) : leakages_t = LeakCond true :: LeakAddr [] :: LeakAddr [] :: (sub_f 32 ++
                                                LeakAddr [] :: (copy_f 32 ++
                                                                LeakAddr [] :: 
                                                                LeakAddr [] :: [])) .
 
axiom samp_g_comp_1 x : x <= 0 => samp_g x = [].
axiom samp_g_comp_2 x : 0 <  x  => samp_g x = samp_step (x-1) ++ samp_g (x - 1).

op samp_suffix : leakages_t = 
 LeakCond false :: LeakAddr [] :: LeakAddr [] 
   :: (sub_f 32 ++ LeakAddr [] :: 
      (copy_f 32 ++ LeakAddr [] :: LeakAddr [] :: [])).

op samp_f (x : int) : leakages_t = samp_g x ++ samp_prefix.
op samp_t (x : int) : leakages_t = samp_suffix ++ samp_f (x - 1).

axiom samp_t_inj : injective samp_t.


lemma rsample_leakages1 l :
  hoare [ M(Syscall).rsample : M.leakages = l 
     ==> M.leakages = samp_t res.`1 ++ l].
proc.
seq 17 :  (M.leakages = samp_prefix ++ l /\ i = 0  /\ cf = false ).
wp. ecall (bn_set0_leakages M.leakages). wp. skip. progress.  
rewrite /set0_64. rewrite /samp_prefix. simplify. smt(@List).
while (0 <= i /\ (cf = false => M.leakages = samp_f i ++ l) 
              /\ (cf = true => M.leakages = samp_t i ++ l)).
wp.  ecall (bn_subc_leakages M.leakages). simplify.
wp.  ecall (bn_copy_leakages M.leakages). simplify.
wp. inline Syscall.randombytes_256. wp. rnd.  wp.
skip. progress. smt().  rewrite H4.  rewrite H0. rewrite H2. auto. simplify.
rewrite /samp_f. rewrite (samp_g_comp_2 (i{hr} + 1)). smt().
simplify.
rewrite /samp_step. simplify. 
have ->: (copy_f 32 ++
                LeakAddr [] :: LeakAddr [] :: (samp_g i{hr} ++ samp_prefix ++
                                               l))
 = (copy_f 32 ++ [LeakAddr []; LeakAddr []]) ++
samp_g i{hr} ++ samp_prefix ++ l.
smt(@List). smt(@List).
rewrite /samp_t. simplify.
rewrite /samp_suffix.  simplify.  split. rewrite H4. auto.
rewrite H0. rewrite H2. auto. smt(@List).
skip. progress. rewrite /samp_prefix. rewrite /samp_f. rewrite samp_g_comp_1.
auto. rewrite /samp_prefix. auto.
rewrite H2. rewrite H. auto.
auto.
qed.


lemma rsample_leakages2 a  &m : (glob M1){m} = [] =>
  Pr[ M1.rsample(a) @ &m : M1.leakages <> samp_t res.`1 ] = 0%r.
progress. byphoare (_: glob M1 = [] ==> _).
hoare. simplify.
conseq (rsample_leakages1 []). auto. smt(@List).  auto. auto.
qed.


lemma rsample_leakages3 a l x &m : (glob M1){m} = [] =>
  Pr[ M1.rsample(a) @ &m : M1.leakages = l  /\ res.`2 = x ]
  = Pr[ M1.rsample(a) @ &m : l = samp_t res.`1 /\ res.`2 = x  ].
move => H.
have ->: Pr[ M1.rsample(a) @ &m : l = samp_t res.`1 /\ res.`2 = x ]
 = Pr[ M1.rsample(a) @ &m : l = samp_t res.`1 /\ res.`2 = x /\ M1.leakages = samp_t res.`1  ].
  have -> : Pr[M1.rsample(a) @ &m : l = samp_t res.`1 /\ res.`2 = x]
   = Pr[M1.rsample(a) @ &m : l = samp_t res.`1 /\ res.`2 = x /\ M1.leakages = samp_t res.`1]
   + Pr[M1.rsample(a) @ &m : l = samp_t res.`1 /\ res.`2 = x /\ M1.leakages <> samp_t res.`1].
   rewrite Pr[mu_split (M1.leakages = samp_t res.`1)]. smt(). 
  have ->: Pr[M1.rsample(a) @ &m :
   l = samp_t res.`1 /\ res.`2 = x /\ M1.leakages <> samp_t res.`1] = 0%r.
    have : Pr[M1.rsample(a) @ &m :
       l = samp_t res.`1 /\ res.`2 = x /\ M1.leakages <> samp_t res.`1]
     <= Pr[ M1.rsample(a) @ &m : M1.leakages <> samp_t res.`1 ]. smt(@Distr).
    rewrite (rsample_leakages2 a &m). auto. smt(@Distr). 
auto.
have -> : Pr[ M1.rsample(a) @ &m : l = samp_t res.`1 /\ res.`2 = x /\ M1.leakages = samp_t res.`1  ]
 = Pr[ M1.rsample(a) @ &m : res.`2 = x /\  l = M1.leakages /\ M1.leakages = samp_t res.`1  ].
rewrite Pr[mu_eq]. move => &hr. split.  smt().  smt(). auto.
have -> : Pr[ M1.rsample(a) @ &m : res.`2 = x /\ l = M1.leakages /\ M1.leakages = samp_t res.`1  ]
 = Pr[ M1.rsample(a) @ &m :  l = M1.leakages /\ res.`2 = x ].
  have : Pr[ M1.rsample(a) @ &m :  l = M1.leakages /\ res.`2 = x ] 
   = Pr[ M1.rsample(a) @ &m :  l = M1.leakages /\ res.`2 = x /\ M1.leakages = samp_t res.`1  ]
   + Pr[ M1.rsample(a) @ &m :  l = M1.leakages /\ res.`2 = x /\ M1.leakages <> samp_t res.`1  ].
 rewrite Pr[mu_split (M1.leakages = samp_t res.`1 )]. smt().
   have : Pr[ M1.rsample(a) @ &m :  l = M1.leakages /\ res.`2 = x /\ M1.leakages <> samp_t res.`1  ]
    = 0%r.
     have : Pr[ M1.rsample(a) @ &m :  l = M1.leakages /\ res.`2 = x /\ M1.leakages <> samp_t res.`1  ] 
         <= Pr[ M1.rsample(a) @ &m : M1.leakages <> samp_t res.`1 ].
       rewrite Pr[mu_sub]. auto. auto.
    rewrite (rsample_leakages2 a &m). auto. smt(@Distr).
    move => h. rewrite h. simplify. progress. rewrite H0.
rewrite Pr[mu_eq]. smt(). auto. 
rewrite Pr[mu_eq]. smt(). auto.
qed.


lemma rsample_leakages_inv a x l &m : (glob M1){m} = [] 
 => Pr[ M1.rsample(a) @ &m : M1.leakages = l /\ res.`2 = x  ]
  = Pr[ M1.rsample(a) @ &m :  (inv (-1) samp_t) l = res.`1  /\ res.`2 = x  ].
move => ic (* ic' *). rewrite  (rsample_leakages3 a l x &m). auto. auto.
simplify. 
have -> : 
  Pr[M1.rsample(a) @ &m :
   l = samp_t res.`1 /\ res.`2 = x]
  =   Pr[M1.rsample(a) @ &m :
   l = samp_t res.`1 /\ res.`2 = x /\ 0 <= res.`1]. byequiv.
proc. wp. simplify. 
while (0 <= i{1} /\ ={i,byte_p, byte_z}). wp.  simplify.
call (_:true). wp. sim. wp. 
call (_:true). wp. sim. wp. 
call (_:true). wp. sim. wp. 
skip. progress. smt(). wp. 
call (_:true). wp. sim. wp.  skip. progress.
auto. auto.
have -> : Pr[M1.rsample(a) @ &m :
   inv (-1) samp_t l = res.`1 /\ res.`2 = x] 
 = Pr[M1.rsample(a) @ &m :
   inv (-1) samp_t l = res.`1 /\ res.`2 = x /\ 0 <= res.`1].
 byequiv.
proc. wp. simplify.
while (0 <= i{1} /\ ={i,byte_p, byte_z}). wp.  simplify.
call (_:true). wp. sim. wp. 
call (_:true). wp. sim. wp. 
call (_:true). wp. sim. wp. 
skip. progress. smt(). wp. 
call (_:true). wp. sim. wp.  skip. progress.
auto. auto.
rewrite Pr[mu_eq].
progress.
rewrite invP. apply samp_t_inj. auto.  
have : exists z, (samp_t z) = l.
apply (choiceEx (-1) samp_t l res{hr}.`1) . apply H. smt().
elim. progress.
rewrite - H.
rewrite invP.
apply samp_t_inj. auto.
auto.
qed.


require import W64_SchnorrExtract.
module M2 = W64_SchnorrExtract.M(W64_SchnorrExtract.Syscall).  

lemma M1_M2_rsample :
  equiv  [ M1.rsample ~ M2.rsample 
    : ={arg} ==> ={res}  ].
proof. proc.  sim. 
call (_:true). 
wp. while (={a,i}). wp.  skip. progress. wp. skip. progress.
wp.  skip. progress. qed.


require import Ring_ops_proof.
require import Ring_ops_spec.
require import UniformSampling_Abstract.
require import UniformSampling_Concrete.


equiv rsample_cspec_equiv:
 M1.rsample ~ CSpecFp.rsample:
  W64xN.valR byte_z{1} = a{2}
  ==> W64xN.valR res{1}.`2 = res{2}.`2 /\ res{1}.`1 = res{2}.`1.
transitivity M2.rsample 
 (={arg} ==> ={res})
 (W64xN.valR byte_z{1} = a{2}
  ==> W64xN.valR res{1}.`2 = res{2}.`2 /\ res{1}.`1 = res{2}.`1).
progress. smt(). progress.
conseq M1_M2_rsample. 
conseq rsample_cspec.
qed.


lemma rsample_cspec_pr a i x &m : 
  Pr[ M1.rsample(a) @ &m : res = (i,x)  ]
   = Pr[ CSpecFp.rsample(W64xN.valR a) @ &m : res = (i, W64xN.valR x)  ].
byequiv.
conseq rsample_cspec_equiv. progress. progress. smt().
smt(@W64xN). auto. auto.
qed.


lemma rsample_index_pos &m a : Pr[M1.rsample(a) @ &m : res.`1 <= 0 ] = 0%r.
byphoare (_: arg = a ==> _);auto. hoare.
proc.  simplify.
unroll 18. rcondt 18. wp. wp. 
call (_:true). wp. auto. wp. skip. auto.
while (0 < i). wp. call (_:true). auto. wp.  call (_:true). auto.  wp. 
inline*. wp. rnd. wp. skip. progress. smt().
wp. call (_:true). auto.  wp.  
call (_:true). auto. wp. 
call (_:true). auto. wp. 
call (_:true). auto. wp. skip. smt().
qed.

import W64xN.


op g a l : real 
 = if inv (-1) samp_t l <= 0 then 0%r else 
     mu D (predC (RSP (valR a))) ^ (inv (-1) samp_t l - 1)
       * (1%r / Ring_ops_spec.M%r).

        
lemma leakfree1 &m x a l: (glob M1){m} = [] 
  => Pr[ M1.rsample(a) @ &m : M1.leakages = l  /\ res.`2 = x  ] = if (valR a <= valR x) then 0%r else (g a l).
      progress.
   rewrite  (rsample_leakages_inv a x l &m);auto.
case (inv (-1) samp_t l <= 0). 
move => q. rewrite /g. rewrite q.  simplify. 
  have : Pr[M1.rsample(a) @ &m :
   inv (-1) samp_t l = res.`1 /\ res.`2 = x] 
    <= Pr[M1.rsample(a) @ &m : res.`1 <= 0 ]. simplify. rewrite Pr[mu_sub]. smt().
   auto. smt(rsample_index_pos @Distr).
move => q.
have -> : 
 Pr[M1.rsample(a) @ &m :
   inv (-1) samp_t l = res.`1 /\ res.`2 = x]
  = Pr[M1.rsample(a) @ &m :
   res = (inv (-1) samp_t l , x) ]. rewrite Pr[mu_eq]. smt(). auto.
case (valR x < valR a) => case1.
rewrite rsample_cspec_pr.
rewrite rsample_pr.   smt().
rewrite /RSP. auto.
rewrite /z. 
have ->: mu1 D (W64xN.valR x) = 1%r / Ring_ops_spec.M%r.
rewrite duniform1E_uniq. smt(@List).
 have f1 : 0 <= W64xN.valR x < Ring_ops_spec.M. smt(@W64xN).  smt(@Distr @List). 
rewrite /g.   smt().
have : Pr[W64_SchnorrExtract_ct.M(W64_SchnorrExtract_ct.Syscall).rsample(a) @ &m :
   res.`2 = x] = 0%r.
  have -> : Pr[W64_SchnorrExtract_ct.M(W64_SchnorrExtract_ct.Syscall).rsample(a) @ &m :
     res.`2 =  x] = Pr[ CSpecFp.rsample(W64xN.valR a) @ &m : res.`2 =  W64xN.valR x ].
  byequiv. conseq rsample_cspec_equiv. auto. progress. rewrite H0.  auto.  smt(@W64xN). auto. auto.
  apply rsample_pr_out. auto.
smt(@Distr).
qed.

op h a : real = 1%r/(valR a)%r. 

lemma leakfree2 &m x a: 
 Pr[ M1.rsample(a) @ &m : res.`2 = x ] 
  = if (valR a <= valR x) then 0%r else h a.    
proof. 
 have ->: Pr[ M1.rsample(a) @ &m : res.`2 = x ] =
  Pr[ CSpecFp.rsample(W64xN.valR a) @ &m : res.`2 =  W64xN.valR x ].
  byequiv. conseq rsample_cspec_equiv. auto. 
progress. rewrite - H. auto. smt(@W64xN). auto. auto.
rewrite /h.
case: (valR a <= valR x). move => alx.
rewrite rsample_pr_out. smt(). auto.
move => a_less_x.
rewrite rsample_uni. smt(@W64xN).
smt(@W64xN). smt(). auto.
qed.

op f a l = h a / g a l.

lemma rsample_leakfree pin l a &m: (glob M1){m} = [] 
 =>  let v = Pr[ M1.rsample(pin) @ &m : res.`2 = a  ] in 
     let w = Pr[ M1.rsample(pin) @ &m : M1.leakages = l  /\ res.`2 = a  ] in 
  0%r < w => v/w 
  = f pin l.
move => l_empty v w f1.
have : (valR a < valR pin).
 case (valR pin <= valR a) => h.
 have : w <= 0%r.
 rewrite /w.  
 rewrite (leakfree1 &m a pin l _). auto.
 rewrite h. auto.
 smt(). 
 smt().
move => a_less_pin.
rewrite /f.
rewrite  (leakfree1 &m a pin l _). auto.
rewrite  (leakfree2 &m a pin ). auto. 
smt().
qed.


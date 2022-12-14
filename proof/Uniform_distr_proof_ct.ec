
require import Ring_ops_extract_ct.
require import JModel List Int AllCore.


require import Array1.
require import WArray1.

(* SUBTRACTION LEAKAGES  *)
op sub_prefix : leakages_t = 
  [LeakFor (1, 32); LeakAddr []; LeakAddr [0]; LeakAddr []; 
    LeakAddr []; LeakAddr [0]; LeakAddr [0]].

op sub_step (i : int) : leakages_t = 
  [LeakAddr [i] ; LeakAddr [] ; LeakAddr [] ; LeakAddr [i] ; 
    LeakAddr [i] ].


op sub_g (x : int) : leakages_t.
axiom sub_g_comp_1 x : 1 <= x  => sub_g x = [].
axiom sub_g_comp_2 x : 1 < x => sub_g x = sub_step (x-1) ++ sub_g (x - 1).

op sub_f (x : int) : leakages_t = sub_g x ++ sub_prefix.

lemma bn_subc_leakages start_l :
   hoare [ M(Syscall).bn_subc : M.leakages = start_l ==> M.leakages = sub_f 32 ++ start_l ].
proof. 
proc.
sp.  elim*. progress.
conseq (_: M.leakages = sub_prefix ++ start_l /\ i = 1 ==> _).
progress.
while (0 < i /\ i <= 32 /\ M.leakages = sub_f i ++ start_l).
wp.  skip.  progress. 
simplify. smt(). smt(). rewrite /sub_f. rewrite (sub_g_comp_2 (i{hr} +1)).  smt(). simplify. rewrite /sub_step. simplify. auto.
skip. progress. rewrite /sub_f.  rewrite sub_g_comp_1. auto. auto.
smt().
qed.


(* COPY LEAKAGES  *)
op copy_prefix : leakages_t = LeakFor (0, 32) :: LeakAddr [] ::[].
op copy_step (i : int) : leakages_t = LeakAddr [i] :: LeakAddr [] :: LeakAddr [i] :: [].

op copy_g (x : int) : leakages_t.
axiom copy_g_comp_1 x : 0 <= x  => copy_g x = [].
axiom copy_g_comp_2 x : 0 < x => copy_g x = copy_step (x-1) ++ copy_g (x - 1).

op copy_f (x : int) : leakages_t = copy_g x ++ copy_prefix.

lemma bn_copy_leakages start_l :
   hoare [ M(Syscall).bn_copy : M.leakages = start_l ==> M.leakages = copy_f 32 ++ start_l ].
proof. 
proc.
sp.  elim*. progress.
conseq (_: M.leakages = copy_prefix ++ start_l /\ i = 0 ==> _).
progress.
while (0 <= i /\ i <= 32 /\ M.leakages = copy_f i ++ start_l).
wp.  skip.  progress. 
simplify. smt(). smt(). rewrite /copy_f. rewrite (copy_g_comp_2 (i{hr} +1)).  smt(). simplify. rewrite /copy_step. simplify. auto.
skip. progress. rewrite /copy_f.  rewrite copy_g_comp_1. auto. auto. 
smt().
qed.




(* set0 LEAKAGES  *)
op set0_prefix : leakages_t = LeakFor (0, 32) :: LeakAddr [] :: [].
op set0_step (i : int) : leakages_t = LeakAddr [i] :: LeakAddr [] :: [].

op set0_g (x : int) : leakages_t.
axiom set0_g_comp_1 x : 0 <= x  => set0_g x = [].
axiom set0_g_comp_2 x : 0 < x => set0_g x = set0_step (x-1) ++ set0_g (x - 1).

op set0_f (x : int) : leakages_t = set0_g x ++ set0_prefix.

lemma bn_set0_leakages start_l :
   hoare [ M(Syscall).bn_set0 : M.leakages = start_l ==> M.leakages = set0_f 32 ++ start_l ].
proof. 
proc.
sp.  elim*. progress.
conseq (_: M.leakages = set0_prefix ++ start_l /\ i = 0 ==> _).
progress. rewrite /set0_prefix.
while (0 <= i /\ i <= 32 /\ M.leakages = set0_f i ++ start_l).
wp.  skip.  progress. 
simplify. smt(). smt(). rewrite /set0_f. rewrite (set0_g_comp_2 (i{hr} +1)).  smt(). simplify. rewrite /set0_step. simplify. auto.
skip. progress. rewrite /set0_f.  rewrite set0_g_comp_1. auto. auto. 
smt().
qed.



(* SAMPLING LEAKAGES  *)
op samp_prefix : leakages_t = 
  LeakCond true :: LeakAddr [] :: LeakAddr [] :: LeakAddr [] :: LeakAddr [] :: 
   LeakAddr [] :: (set0_f 32 ++ [LeakAddr []]).

op samp_g (x : int) : leakages_t.
op samp_step (i : int) : leakages_t = LeakCond true :: LeakAddr [] :: LeakAddr [] :: LeakAddr [] :: LeakAddr [] :: (
sub_f 32 ++
LeakAddr [] :: (copy_f 32 ++
                LeakAddr [] :: LeakAddr [] :: [])) .

  

axiom samp_g_comp_1 x : 0 <= x  => samp_g x = [].
axiom samp_g_comp_2 x : 0 < x => samp_g x = samp_step (x-1) ++ samp_g (x - 1).


op samp_suffix : leakages_t = 
 LeakCond false :: LeakAddr [] :: LeakAddr [] :: LeakAddr [] :: LeakAddr [] :: (
sub_f 32 ++
LeakAddr [] :: (copy_f 32 ++ LeakAddr [] :: LeakAddr [] :: [])).

op samp_f (x : int) : leakages_t = samp_g x ++ samp_prefix.
op samp_t (x : int) : leakages_t = samp_suffix ++ samp_f (x - 1).

axiom samp_t_inj : injective samp_t.


lemma rsample_leakages :
   hoare [ M(Syscall).rsample : M.leakages = [] ==> M.leakages = samp_t res.`1].
proc.
seq 18 :  (M.leakages = samp_prefix /\ i = 0  /\ z = true ).
wp. ecall (bn_set0_leakages M.leakages). wp. skip. progress. 

while (0 <= i /\ (z = true => M.leakages = samp_f i) 
              /\ (z = false => M.leakages = samp_t i)).
wp. 
ecall (bn_subc_leakages M.leakages). wp. ecall (bn_copy_leakages M.leakages). wp.  inline*. wp. rnd. wp.  skip. progress.
smt().  rewrite H4.  rewrite H0. rewrite H2. auto.
rewrite /samp_f. rewrite (samp_g_comp_2 (i{hr} + 1)). smt().
simplify.
 rewrite /samp_step.   
smt(@List). rewrite H4. rewrite H0. rewrite H2. auto.
rewrite /samp_t. simplify.
rewrite /samp_suffix. smt(@List).
skip. progress. rewrite /samp_prefix. rewrite /samp_f. rewrite samp_g_comp_1.
auto. rewrite /samp_prefix. auto.
rewrite H2. rewrite H. auto.
auto.
qed.
    
require Ring_ops_extract.
import Ring_ops_extract.

module M1 = Ring_ops_extract_ct.M(Ring_ops_extract_ct.Syscall).
module M2 = Ring_ops_extract.M(Ring_ops_extract.Syscall).

lemma aaaa :
  equiv  [ M1.bn_set0 ~ M2.bn_set0 
    : ={arg} ==> ={res}  ].
proc. 
while (={a,i}). wp. skip. progress. wp.  skip. progress. qed.

  
lemma aaa :
  equiv  [ M1.rsample ~ M2.rsample 
    : ={arg} ==> ={res}  ].
proof. proc.  sim. call aaaa. wp.  skip. progress. qed.

require import Ring_ops_proof.
require import Ring_ops_spec.


equiv rsample_cspec2:
 M1.rsample ~ CSpecFp.rsample:
  W64xN.valR byte_z{1} = a{2}
  ==> W64xN.valR res{1}.`2 = res{2}.`2 /\ res{1}.`1 = res{2}.`1.
transitivity M2.rsample 
 (={arg} ==> ={res})
 (W64xN.valR byte_z{1} = a{2}
  ==> W64xN.valR res{1}.`2 = res{2}.`2 /\ res{1}.`1 = res{2}.`1).
progress. smt(). progress.
conseq aaa. 
conseq rsample_cspec.
qed.

import W64xN.
require import Distr.

lemma samew a &m : 0%r < mu D (RSP (valR a)) =>
  Pr[ M1.rsample(a) @ &m : true  ] = 1%r.
progress.
rewrite - (rsample_lossless (W64xN.valR a) &m _). auto. 
byequiv.
conseq rsample_cspec2. progress. progress. smt().
qed.


lemma zzz a i x &m : 
  Pr[ M1.rsample(a) @ &m : res = (i,x)  ]
   =   Pr[ CSpecFp.rsample(W64xN.valR a) @ &m : res = (i, W64xN.valR x)  ].
byequiv.
conseq rsample_cspec2. progress. progress. smt().
smt(@W64xN). auto. auto.
qed.


lemma qq' a  &m : (glob M1){m} = [] =>
  Pr[ M1.rsample(a) @ &m : M1.leakages <> samp_t res.`1 ] = 0%r.
progress. byphoare (_: glob M1 = [] ==> _).
hoare. simplify.
conseq rsample_leakages. auto. auto. auto.
qed.

lemma qq a l x &m : (glob M1){m} = [] => 0%r < mu D (RSP (valR a)) =>
  Pr[ M1.rsample(a) @ &m : M1.leakages = l  /\ res.`2 = x ]
  = Pr[ M1.rsample(a) @ &m : l = samp_t res.`1 /\ res.`2 = x  ].
move => m1p m2p.
have pr1 :  Pr[ M1.rsample(a) @ &m : M1.leakages = samp_t res.`1   ] = 1%r.
rewrite - (samew a &m).   auto.
  have ->: Pr[Ring_ops_extract_ct.M(Ring_ops_extract_ct.Syscall).rsample(a) @ &m : true] 
   = Pr[Ring_ops_extract_ct.M(Ring_ops_extract_ct.Syscall).rsample(a) @ &m : M1.leakages = samp_t res.`1 ] + Pr[Ring_ops_extract_ct.M(Ring_ops_extract_ct.Syscall).rsample(a) @ &m : M1.leakages <> samp_t res.`1  ]. rewrite Pr[mu_split (M1.leakages = samp_t res.`1) ]. simplify. auto. rewrite (qq' a &m). auto.
simplify. auto.
have pr2 :  Pr[ M1.rsample(a) @ &m : M1.leakages <> samp_t res.`1   ] = 0%r.
byphoare (_:(glob M1){m} = (glob M1) ==> _). 
hoare. simplify.
conseq rsample_leakages. smt(). progress. auto.
have -> :   Pr[ M1.rsample(a) @ &m : M1.leakages = l /\ res.`2 = x  ]
 = Pr[ M1.rsample(a) @ &m : M1.leakages = samp_t res.`1 /\ M1.leakages = l /\ res.`2 = x ].
rewrite Pr[mu_split (M1.leakages = samp_t res.`1) ].
  have -> : Pr[M1.rsample(a) @ &m :
   (M1.leakages = l /\ res.`2 = x) /\ M1.leakages <> samp_t res.`1] = 0%r. smt(@Distr). 
   simplify. rewrite Pr[mu_eq]. progress. auto. 
have -> : Pr[M1.rsample(a) @ &m : l = samp_t res.`1 /\ res.`2 = x] 
  = Pr[M1.rsample(a) @ &m : l = samp_t res.`1 /\ M1.leakages = samp_t res.`1 /\ res.`2 = x  ].
rewrite Pr[mu_split (M1.leakages = samp_t res.`1) ].
  have -> : Pr[M1.rsample(a) @ &m :
   (l = samp_t res.`1 /\ res.`2 = x) /\ M1.leakages <> samp_t res.`1] = 0%r. smt(@Distr).  auto. 
   simplify. rewrite Pr[mu_eq]. progress. auto. 
rewrite Pr[mu_eq]. progress. auto.
qed.

require import InvFun.




    
lemma qqq a x l &m : (glob M1){m} = [] => 0%r < mu D (RSP (valR a)) =>
  Pr[ M1.rsample(a) @ &m : M1.leakages = l  /\ res.`2 = x  ]
  = Pr[ M1.rsample(a) @ &m :  (inv (-1) samp_t) l = res.`1  /\ res.`2 = x  ].
move => ic ic'. rewrite  (qq a  l x &m). auto. auto.
simplify. 
have -> : 
  Pr[Ring_ops_extract_ct.M(Ring_ops_extract_ct.Syscall).rsample(a) @ &m :
   l = samp_t res.`1 /\ res.`2 = x]
  =   Pr[Ring_ops_extract_ct.M(Ring_ops_extract_ct.Syscall).rsample(a) @ &m :
   l = samp_t res.`1 /\ res.`2 = x /\ 0 <= res.`1]. byequiv.
proc. wp. simplify.
while (0 <= i{1} /\ ={i,byte_p, byte_z, q0, q1}). wp.  simplify.
call (_:true). wp. sim. wp. 
call (_:true). wp. sim. wp. 
call (_:true). wp. sim. wp. 
skip. progress. smt(). wp. 
call (_:true). wp. sim. wp.  skip. progress.
auto. auto.
have -> : Pr[Ring_ops_extract_ct.M(Ring_ops_extract_ct.Syscall).rsample(a) @ &m :
   inv (-1) samp_t l = res.`1 /\ res.`2 = x] 
 = Pr[Ring_ops_extract_ct.M(Ring_ops_extract_ct.Syscall).rsample(a) @ &m :
   inv (-1) samp_t l = res.`1 /\ res.`2 = x /\ 0 <= res.`1].
 byequiv.
proc. wp. simplify.
while (0 <= i{1} /\ ={i,byte_p, byte_z, q0, q1}). wp.  simplify.
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




lemma ph_l5''_var &m a : Pr[M1.rsample(a) @ &m : res.`1 <= 0 ] = 0%r.
byphoare (_: arg = a ==> _);auto. hoare.
proc.  simplify.
unroll 19. rcondt 19. wp. wp. 
call (_:true). wp. auto. wp. skip. auto.
while (0 < i). wp. call (_:true). auto. wp.  call (_:true). auto.  wp. 
inline*. wp. rnd. wp. skip. progress. smt().
wp. call (_:true). auto.  wp.  
call (_:true). auto. wp. 
call (_:true). auto. wp. 
call (_:true). auto. wp. skip. smt().
qed.



op g a x l : real 
 = if inv (-1) samp_t l <= 0 then 0%r else mu D (predC (RSP ((valR a)))) ^ (inv (-1) samp_t l - 1) *
        (mu1 D ((valR x))).

        
lemma leakfree &m x a l: (glob M1){m} = [] => valR x < valR a => 0%r < mu D (RSP (valR a)) =>
  Pr[ M1.rsample(a) @ &m : M1.leakages = l  /\ res.`2 = x  ]
    = g a x l.
      progress.
   rewrite  (qqq a x l &m);auto.
case (inv (-1) samp_t l <= 0). 
move => q. rewrite /g. rewrite q.  simplify. 
  have : Pr[Ring_ops_extract_ct.M(Ring_ops_extract_ct.Syscall).rsample(a) @ &m :
   inv (-1) samp_t l = res.`1 /\ res.`2 = x] 
    <= Pr[M1.rsample(a) @ &m : res.`1 <= 0 ]. simplify. rewrite Pr[mu_sub]. smt().
   auto. smt(ph_l5''_var @Distr).
move => q.
have -> : 
 Pr[Ring_ops_extract_ct.M(Ring_ops_extract_ct.Syscall).rsample(a) @ &m :
   inv (-1) samp_t l = res.`1 /\ res.`2 = x]
  = Pr[Ring_ops_extract_ct.M(Ring_ops_extract_ct.Syscall).rsample(a) @ &m :
   res = (inv (-1) samp_t l , x) ]. rewrite Pr[mu_eq]. smt(). auto.
rewrite zzz.
rewrite rsample_pr.   smt().
rewrite /RSP. auto.
rewrite /z. smt().
qed.

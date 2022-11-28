require import Ring_ops_extract_ct.
require import JModel List Int AllCore.


require import Array1.
require import WArray1.

require import Uniform_distr_extract_ct.

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



lemma jj start_l :
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


op samp_prefix : leakages_t = 
  LeakCond true :: LeakAddr [] :: LeakAddr [] :: LeakAddr [] :: LeakAddr [] :: 
  LeakAddr [] :: [].
op samp_g (x : int) : leakages_t.
op samp_step (i : int) : leakages_t = LeakCond true :: LeakAddr [] :: LeakAddr [] :: LeakAddr [] :: LeakAddr [] :: (
sub_f 32 ++ LeakAddr [] :: LeakAddr [] :: []).

  

axiom samp_g_comp_1 x : 0 <= x  => samp_g x = [].
axiom samp_g_comp_2 x : 0 < x => samp_g x = samp_step (x-1) ++ samp_g (x - 1).

op samp_suffix : leakages_t = 
 LeakCond false :: LeakAddr [] :: LeakAddr [] :: LeakAddr [] :: LeakAddr [] :: 
sub_f 32 ++ LeakAddr [] :: LeakAddr [] :: [].

op samp_f (x : int) : leakages_t = samp_g x ++ samp_prefix.
op samp_t (x : int) : leakages_t = samp_suffix ++ samp_f (x - 1).



lemma ii :
   hoare [ M(Syscall).rsample : M.leakages = [] ==> M.leakages = samp_t res.`1].
proc.
sp. elim*. progress.
conseq (_: M.leakages = samp_prefix /\ i = 0  /\ z = true ==> _).
progress.
while (0 <= i /\ (z = true => M.leakages = samp_f i) 
              /\ (z = false => M.leakages = samp_t i)).
wp. 
ecall (jj M.leakages). wp. inline*. wp. rnd. wp.  skip. progress.
smt().  rewrite H4.  rewrite H0. rewrite H2. auto.
rewrite /samp_f. rewrite (samp_g_comp_2 (i{hr} + 1)). smt().
simplify. rewrite /samp_step.   
smt(@List). rewrite H4. rewrite H0. rewrite H2. auto.
rewrite /samp_t. simplify.
rewrite /samp_suffix. smt(@List).
skip. progress. rewrite /samp_prefix. rewrite /samp_f. rewrite samp_g_comp_1.
auto. rewrite /samp_prefix. auto.
rewrite H2. rewrite H. auto.
auto.
qed.
    

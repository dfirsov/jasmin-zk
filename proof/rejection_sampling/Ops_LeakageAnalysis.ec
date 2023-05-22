require import W64_SchnorrExtract_ct.
require import List Int AllCore.

from Jasmin require import JModel.

(* SUBTRACTION LEAKAGES  *)
op sub_prefix : leakages_t = 
  [LeakFor (1, 32); LeakAddr []; LeakAddr [0]; LeakAddr []; 
    LeakAddr []; LeakAddr [0]; LeakAddr [0]].

op sub_step (i : int) : leakages_t = 
  [LeakAddr [i] ; LeakAddr [] ; LeakAddr [] ; LeakAddr [i] ; 
    LeakAddr [i] ].


op sub_g (x : int) : leakages_t.
axiom sub_g_comp_1 x : x <= 1 => sub_g x = [].
axiom sub_g_comp_2 x : 1 <  x => sub_g x = sub_step (x-1) ++ sub_g (x - 1).

op sub_f (x : int) : leakages_t = sub_g x ++ sub_prefix.


lemma bn_subc_leakages start_l :
  hoare [ M(Syscall).bn_subc : M.leakages = start_l 
            ==> M.leakages = sub_f 32 ++ start_l ].
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
axiom copy_g_comp_1 x : x <= 0 => copy_g x = [].
axiom copy_g_comp_2 x : 0 <  x => copy_g x = copy_step (x-1) ++ copy_g (x - 1).

op copy_f (x : int) : leakages_t = copy_g x ++ copy_prefix.

lemma bn_copy_leakages start_l :
   hoare [ M(Syscall).bn_copy : M.leakages = start_l 
     ==> M.leakages = copy_f 32 ++ start_l ].
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
axiom set0_g_comp_1 x : x <= 0 => set0_g x = [].
axiom set0_g_comp_2 x : 0 <  x => set0_g x = set0_step (x-1) ++ set0_g (x - 1).

op set0_f (x : int) : leakages_t = set0_g x ++ set0_prefix.

lemma bn_set0_leakages start_l :
   hoare [ M(Syscall).bn_set0 : M.leakages = start_l 
                ==> M.leakages = set0_f 32 ++ start_l ].
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


(* set1 LEAKAGES  *)
op set1_prefix : leakages_t = LeakFor (1, 32) :: LeakAddr [] :: LeakAddr [0] :: LeakAddr [] :: [].
op set1_step (i : int) : leakages_t = LeakAddr [i] :: LeakAddr [] :: [].

op set1_g (x : int) : leakages_t.
axiom set1_g_comp_1 x : x <= 1 => set1_g x = [].
axiom set1_g_comp_2 x : 1 <  x => set1_g x = set1_step (x-1) ++ set1_g (x - 1).

op set1_f (x : int) : leakages_t = set1_g x ++ set1_prefix.

lemma bn_set1_leakages start_l :
   hoare [ M(Syscall).bn_set1 : M.leakages = start_l 
                ==> M.leakages = set1_f 32 ++ start_l ].
proof. 
proc.
sp.  elim*. progress.
conseq (_: M.leakages = set1_prefix ++ start_l /\ i = 1 ==> _).
progress. rewrite /set1_prefix.
while (1 <= i /\ i <= 32 /\ M.leakages = set1_f i ++ start_l).
wp.  skip.  progress. 
simplify. smt(). smt(). rewrite /set1_f.  simplify. rewrite (set1_g_comp_2 (i{hr} + 1)).  smt(). simplify. rewrite /set1_step. simplify. auto.
skip. 
progress.  rewrite /set1_f.  rewrite set1_g_comp_1. auto. auto. 
smt().
qed.

(* ith_bit64 leakages  *)
op ith_bit64_t : leakages_t = LeakAddr [] :: LeakAddr [] :: LeakAddr [] :: LeakAddr [] :: LeakAddr [] :: [].

lemma ith_bit64_leakages start_l :
   hoare [ M(Syscall).ith_bit64 : M.leakages = start_l 
                ==> M.leakages = ith_bit64_t ++ start_l ].
proc. wp. skip. progress. qed.

(* ith_bit LEAKAGES  *)
op ith_bit_t (x : W64.t) :  leakages_t = 
 ith_bit64_t ++ LeakAddr [] :: LeakAddr [to_uint (x `>>` (of_int 6)%W8)] :: LeakAddr [] ::  LeakAddr [] :: LeakAddr [] :: LeakAddr [] :: [].

lemma ith_bit_leakages start_l c :
   hoare [ M(Syscall).ith_bit : M.leakages = start_l /\ c = ctr 
                ==> M.leakages = ith_bit_t c ++ start_l ].
proof. 
proc.
wp. 
sp. elim*. progress. 
exists* c1. elim*. move => c1_var.
call (ith_bit64_leakages (LeakAddr [] :: LeakAddr [to_uint  c1_var   ] :: LeakAddr [] :: LeakAddr [] :: 
  LeakAddr [] :: LeakAddr [] :: start_l)).
skip. progress. 
qed.


(* swapr LEAKAGES  *)
op swapr_prefix : leakages_t = LeakFor (0, 32) :: LeakAddr [] :: LeakAddr [] :: [].
op swapr_step (x : int) : leakages_t = LeakAddr [x] :: LeakAddr [] :: LeakAddr [] :: LeakAddr [x] :: 
LeakAddr [x] :: LeakAddr [x] :: LeakAddr [] :: LeakAddr [x] :: 
LeakAddr [x] :: [].

op swapr_g (x : int) : leakages_t.
axiom swapr_g_comp_1 x : x = 0 => swapr_g x = [].
axiom swapr_g_comp_2 x : 0 <  x => swapr_g x = swapr_step (x-1) ++ swapr_g (x - 1).

op swapr_f (x : int) : leakages_t = swapr_g x ++ swapr_prefix.

lemma swapr_leakages start_l :
   hoare [ M(Syscall).swapr : M.leakages = start_l 
     ==> M.leakages = swapr_f 32 ++ start_l ].
proof. 
proc.
sp.  elim*. progress.
conseq (_: M.leakages = swapr_prefix ++ start_l /\ i = 0 ==> _).
progress.
while (0 <= i /\ i <= 32 /\ M.leakages = swapr_f i ++ start_l).
wp.  skip.  progress. 
smt(). smt(). 
rewrite /swapr_f. rewrite (swapr_g_comp_2 (i{hr} +1)).  smt(). simplify. rewrite /swapr_step. simplify. auto.
skip. progress. rewrite /swapr_f.  rewrite swapr_g_comp_1. auto. auto. 
smt().
qed.


(* mulm LEAKAGES  *)
op mulm_t :  leakages_t.

lemma mulm_leakages start_l :
   hoare [ M(Syscall).mulm : M.leakages = start_l 
                ==> M.leakages = mulm_t ++ start_l ].
admitted.


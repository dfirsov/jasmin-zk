require import List Int AllCore Distr.

from Jasmin require import JModel.

require import AuxLemmas.
require import W64_SchnorrExtract_ct.


(* SUBTRACTION LEAKAGES  *)
op sub_prefix : leakages_t = 
  [LeakFor (1, 32); LeakAddr []; LeakAddr [0]; LeakAddr []; 
    LeakAddr []; LeakAddr [0]; LeakAddr [0]].

op sub_step (i : int) : leakages_t = 
  [LeakAddr [i] ; LeakAddr [] ; LeakAddr [] ; LeakAddr [i] ; 
    LeakAddr [i] ].


op sub_g (x : int) : leakages_t = iteri (x - 1) (fun i r => sub_step (i + 1) ++ r) [].
lemma sub_g_comp_1 x : x <= 1 => sub_g x = []. by smt(@Int). qed.

lemma sub_g_comp_2 x : 1 <  x => sub_g x = sub_step (x-1) ++ sub_g (x - 1). progress. rewrite /sub_g. smt(@Int). qed.

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

op copy_g (x : int) : leakages_t = iteri x (fun i r => copy_step i ++ r) [].

lemma copy_g_comp_1 x : x <= 0 => copy_g x = [].
progress. rewrite /copy_g. smt(@Int). qed.

lemma copy_g_comp_2 x : 0 <  x => copy_g x = copy_step (x-1) ++ copy_g (x - 1).
progress. rewrite /copy_g. smt(@Int). qed.

op [opaque] copy_f (x : int) : leakages_t = copy_g x ++ copy_prefix.

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

(* DCOPY LEAKAGES  *)
op dcopy_prefix : leakages_t = LeakFor (0, 64) :: LeakAddr [] ::[].
op dcopy_step (i : int) : leakages_t = LeakAddr [i] :: LeakAddr [] :: LeakAddr [i] :: [].


op dcopy_g (x : int) : leakages_t = iteri x (fun i r => dcopy_step i ++ r) [].
lemma dcopy_g_comp_1 x : x <= 0 => dcopy_g x = []. by smt(@Int). qed.
lemma dcopy_g_comp_2 x : 0 <  x => dcopy_g x = dcopy_step (x-1) ++ dcopy_g (x - 1). by smt(@Int). qed.

op dcopy_f (x : int) : leakages_t = dcopy_g x ++ dcopy_prefix.

lemma dbn_copy_leakages start_l :
   hoare [ M(Syscall).dbn_copy : M.leakages = start_l 
     ==> M.leakages = dcopy_f 64 ++ start_l ].
proof. 
proc.
sp.  elim*. progress.
conseq (_: M.leakages = dcopy_prefix ++ start_l /\ i = 0 /\ aux = 64 ==> _).
progress.
while (aux = 64 /\ 0 <= i /\ i <= 64 /\ M.leakages = dcopy_f i ++ start_l).
wp.  skip.  progress. 
simplify. smt(). smt(). rewrite /dcopy_f. rewrite (dcopy_g_comp_2 (i{hr} +1)).  smt(). simplify. rewrite /dcopy_step. simplify. auto.
skip. progress. rewrite /dcopy_f.  rewrite dcopy_g_comp_1. auto. auto. 
smt().
qed.



(* set0 LEAKAGES  *)
op set0_prefix : leakages_t = LeakFor (0, 32) :: LeakAddr [] :: [].
op set0_step (i : int) : leakages_t = LeakAddr [i] :: LeakAddr [] :: [].

op set0_g (x : int) : leakages_t = iteri x (fun i r => set0_step i ++ r) [].
lemma set0_g_comp_1 x : x <= 0 => set0_g x = []. by smt(@Int). qed.
lemma set0_g_comp_2 x : 0 <  x => set0_g x = set0_step (x-1) ++ set0_g (x - 1). by smt(@Int). qed.

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

op set1_g (x : int) : leakages_t = iteri (x-1) (fun i r => set1_step (i+1) ++ r) [].
lemma set1_g_comp_1 x : x <= 1 => set1_g x = []. by smt(@Int). qed.
lemma set1_g_comp_2 x : 1 <  x => set1_g x = set1_step (x-1) ++ set1_g (x - 1). rewrite /set1_g. by smt(@Int). qed.

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
op [opaque] ith_bit_t (x : W64.t) :  leakages_t = 
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
skip. rewrite /ith_bit_t. progress.  
qed.


(* swapr LEAKAGES  *)
op swapr_prefix : leakages_t = LeakFor (0, 32) :: LeakAddr [] :: LeakAddr [] :: [].
op swapr_step (x : int) : leakages_t = LeakAddr [x] :: LeakAddr [] :: LeakAddr [] :: LeakAddr [x] :: 
LeakAddr [x] :: LeakAddr [x] :: LeakAddr [] :: LeakAddr [x] :: 
LeakAddr [x] :: [].

op swapr_g (x : int) : leakages_t = iteri x (fun i r => swapr_step i ++ r) [].
lemma swapr_g_comp_1 x : x = 0 => swapr_g x = []. by smt(@Int). qed.
lemma swapr_g_comp_2 x : 0 <  x => swapr_g x = swapr_step (x-1) ++ swapr_g (x - 1). by smt(@Int). qed.

op [opaque] swapr_f (x : int) : leakages_t = swapr_g x ++ swapr_prefix.

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



(* mul1 LEAKAGES  *)
op mul1_prefix : leakages_t = LeakFor (1, 32) :: LeakAddr [] :: LeakAddr [0] :: LeakAddr [] :: LeakAddr [1] :: 
LeakAddr [] :: LeakAddr [] :: LeakAddr [0] :: LeakAddr [] :: LeakAddr [] :: [].
op mul1_step (x : int) : leakages_t = LeakAddr [x] :: LeakAddr [] :: LeakAddr [] :: LeakAddr [] :: LeakAddr
                                                                   [x] :: 
LeakAddr [] :: LeakAddr [x + 1] :: LeakAddr [] :: LeakAddr [] :: 
LeakAddr [x] :: LeakAddr [] :: [].

op mul1_suffix : leakages_t = LeakAddr [32] :: LeakAddr [] :: LeakAddr [] :: LeakAddr [32] :: [].

op mul1_g (x : int) : leakages_t  = iteri (x-1) (fun i r => mul1_step (i+1) ++ r) [].
lemma mul1_g_comp_1 x : x = 1 => mul1_g x = []. by smt(@Int). qed.
lemma mul1_g_comp_2 x : 1 <  x => mul1_g x = mul1_step (x-1) ++ mul1_g (x - 1). rewrite /mul1_g. smt(@Int). qed.

op mul1_f (x : int) : leakages_t = mul1_suffix ++ mul1_g x ++ mul1_prefix.

lemma mul1_leakages start_l :
   hoare [ M(Syscall).mul1 : M.leakages = start_l 
     ==> M.leakages = mul1_f 32 ++ start_l ].
proof. 
proc.
sp.  elim*. progress.
conseq (_: M.leakages = mul1_prefix ++ start_l /\ i = 1 ==> _).
progress. wp.
while (1 <= i /\ i <= 32 /\ M.leakages = mul1_g i ++ mul1_prefix ++ start_l).
wp.  skip.  progress. 
smt(). smt(). 
rewrite /mul1_f. rewrite (mul1_g_comp_2 (i{hr} +1)).  smt(). simplify. rewrite /mul1_step. simplify. auto.
skip. progress. rewrite /mul1_f.  rewrite mul1_g_comp_1. auto. auto. 
smt().
qed.

(* dmul1 LEAKAGES  *)
op dmul1_prefix : leakages_t = LeakFor (1, 64) :: LeakAddr [] :: LeakAddr [0] :: LeakAddr [] :: LeakAddr [1] :: 
LeakAddr [] :: LeakAddr [] :: LeakAddr [0] :: LeakAddr [] :: LeakAddr [] :: [].
op dmul1_step (x : int) : leakages_t = LeakAddr [x] :: LeakAddr [] :: LeakAddr [] :: LeakAddr [] :: LeakAddr
                                                                   [x] :: 
LeakAddr [] :: LeakAddr [x + 1] :: LeakAddr [] :: LeakAddr [] :: 
LeakAddr [x] :: LeakAddr [] :: [].

op dmul1_suffix : leakages_t = LeakAddr [64] :: LeakAddr [] :: LeakAddr [] :: LeakAddr [64] :: [].

op dmul1_g (x : int) : leakages_t = iteri (x-1) (fun i r => dmul1_step (i+1) ++ r) [].
lemma dmul1_g_comp_1 x : x = 1 => dmul1_g x = []. by smt(@Int). qed.
lemma dmul1_g_comp_2 x : 1 <  x => dmul1_g x = dmul1_step (x-1) ++ dmul1_g (x - 1). rewrite /dmul1_g. by smt(@Int). qed.

op dmul1_f (x : int) : leakages_t = dmul1_suffix ++ dmul1_g x ++ dmul1_prefix.

lemma dmul1_leakages start_l :
   hoare [ M(Syscall).dmul1 : M.leakages = start_l 
     ==> M.leakages = dmul1_f 64 ++ start_l ].
proof. 
proc.
sp.  elim*. progress.
conseq (_: aux_6 = 64 /\ M.leakages = dmul1_prefix ++ start_l /\ i = 1 ==> _).
progress. wp.
while (aux_6 = 64 /\ 1 <= i /\ i <= 64 /\ M.leakages = dmul1_g i ++ dmul1_prefix ++ start_l).
wp.  skip.  progress. 
smt(). smt(). 
rewrite /dmul1_f. rewrite (dmul1_g_comp_2 (i{hr} +1)).  smt(). simplify. rewrite /dmul1_step. simplify. auto.
skip. progress. rewrite /dmul1_f.  rewrite dmul1_g_comp_1. auto. auto. 
rewrite /dmul1_f.
have ->: i0 = 64. smt().
smt().
qed.




(* mul1acc LEAKAGES  *)
op mul1acc_prefix  : leakages_t = LeakFor (0, 31) :: LeakAddr [] :: LeakAddr [] :: [].

op mul1acc_suffix (kkk : int) : leakages_t =  LeakAddr [32 +  kkk] :: LeakAddr [] :: LeakAddr [] :: LeakAddr
                                                               [32 +
                                                                 kkk] :: 
LeakAddr [32 +  kkk] :: LeakAddr [] :: LeakAddr [] :: LeakAddr
                                                               [32 +
                                                                 kkk] :: 
LeakAddr [31 +  kkk] :: LeakAddr [] :: LeakAddr [] :: LeakAddr
                                                               [31 +
                                                                 kkk] :: 
LeakAddr [] :: LeakAddr [32 +  kkk] :: LeakAddr [] :: LeakAddr [] :: 
LeakAddr [31] :: LeakAddr [] :: [].

op mul1acc_step (kk i : int) : leakages_t = LeakAddr [kk + i + 1] :: LeakAddr [] :: LeakAddr [] :: LeakAddr
                                                                 [kk +
                                                                  i + 1] :: 
LeakAddr [kk + i] :: LeakAddr [] :: LeakAddr [] :: LeakAddr
                                                             [kk + i] :: 
LeakAddr [] :: LeakAddr [] :: LeakAddr [] :: LeakAddr [i] :: LeakAddr [] :: [].


op mul1acc_g (kk x : int) : leakages_t =  iteri (x) (fun i r => mul1acc_step kk i ++ r) [].
lemma mul1acc_g_comp_1 kk x : x = 0 => mul1acc_g kk x = []. smt(@Int). qed.
lemma mul1acc_g_comp_2 kk x : 0 < x => mul1acc_g kk x = mul1acc_step kk (x-1) ++ mul1acc_g kk (x - 1). smt(@Int). qed.

op mul1acc_f (kk x : int) : leakages_t = mul1acc_suffix kk ++ mul1acc_g kk x ++ mul1acc_prefix.

lemma mul1acc_leakages start_l kkk :
   hoare [ M(Syscall).mul1acc : M.leakages = start_l  /\ k = kkk
     ==> M.leakages = mul1acc_f (to_uint kkk) 31 ++ start_l ].
proof. 
proc.
sp.  elim*. progress.
conseq (_: M.leakages = mul1acc_prefix ++ start_l /\ i = 0 /\ aux = 31 /\ (to_uint kkk) = kk ==> _).
progress. wp.
while (aux = 31 /\ 0 <= i /\ i <= 31 /\ M.leakages = mul1acc_g kk i ++ mul1acc_prefix ++ start_l /\ kk = (to_uint kkk)).
wp.  skip.  progress. 
smt(). smt(). 
rewrite (mul1acc_g_comp_2 (to_uint kkk) (i{hr}+1)).  smt(). simplify. rewrite /mul1acc_step. simplify. auto.
skip. progress. rewrite mul1acc_g_comp_1. auto. auto. 
simplify.
have -> : i0 = 31. smt().
rewrite /mul1acc_f. 
rewrite /mul1acc_suffix. simplify. auto.
qed.



(* dmul1acc LEAKAGES  *)
op dmul1acc_prefix  : leakages_t = LeakFor (0, 63) :: LeakAddr [] :: LeakAddr [] :: [].

op dmul1acc_suffix (kkk : int) : leakages_t =  LeakAddr [64 +  kkk] :: LeakAddr [] :: LeakAddr [] :: LeakAddr
                                                               [64 +
                                                                 kkk] :: 
LeakAddr [64 +  kkk] :: LeakAddr [] :: LeakAddr [] :: LeakAddr
                                                               [64 +
                                                                 kkk] :: 
LeakAddr [63 +  kkk] :: LeakAddr [] :: LeakAddr [] :: LeakAddr
                                                               [63 +
                                                                 kkk] :: 
LeakAddr [] :: LeakAddr [64 +  kkk] :: LeakAddr [] :: LeakAddr [] :: 
LeakAddr [63] :: LeakAddr [] :: [].

op dmul1acc_step (kk i : int) : leakages_t = LeakAddr [kk + i + 1] :: LeakAddr [] :: LeakAddr [] :: LeakAddr
                                                                 [kk +
                                                                  i + 1] :: 
LeakAddr [kk + i] :: LeakAddr [] :: LeakAddr [] :: LeakAddr
                                                             [kk + i] :: 
LeakAddr [] :: LeakAddr [] :: LeakAddr [] :: LeakAddr [i] :: LeakAddr [] :: [].


op dmul1acc_g (kk x : int) : leakages_t =  iteri (x) (fun i r => dmul1acc_step kk i ++ r) [].
lemma dmul1acc_g_comp_1 kk x : x = 0 => dmul1acc_g kk x = []. smt(@Int). qed.
lemma dmul1acc_g_comp_2 kk x : 0 < x => dmul1acc_g kk x = dmul1acc_step kk (x-1) ++ dmul1acc_g kk (x - 1). smt(@Int). qed.

op dmul1acc_f (kk x : int) : leakages_t = dmul1acc_suffix kk ++ dmul1acc_g kk x ++ dmul1acc_prefix.

lemma dmul1acc_leakages start_l kkk :
   hoare [ M(Syscall).dmul1acc : M.leakages = start_l  /\ k = kkk
     ==> M.leakages = dmul1acc_f (to_uint kkk) 63 ++ start_l ].
proof. 
proc.
sp.  elim*. progress.
conseq (_: M.leakages = dmul1acc_prefix ++ start_l /\ i = 0 /\ aux = 63 /\ (to_uint kkk) = kk ==> _).
progress. wp.
while (aux = 63 /\ 0 <= i /\ i <= 63 /\ M.leakages = dmul1acc_g kk i ++ dmul1acc_prefix ++ start_l /\ kk = (to_uint kkk)).
wp.  skip.  progress. 
smt(). smt(). 
rewrite (dmul1acc_g_comp_2 (to_uint kkk) (i{hr}+1)).  smt(). simplify. rewrite /dmul1acc_step. simplify. auto.
skip. progress. rewrite dmul1acc_g_comp_1. auto. auto. 
simplify.
have -> : i0 = 63. smt().
rewrite /dmul1acc_f. 
rewrite /dmul1acc_suffix. simplify. auto.
qed.




(* bn_muln LEAKAGES  *)
op bn_muln_prefix : leakages_t =  LeakFor (1, 32) :: LeakAddr [] :: LeakAddr [] :: LeakAddr [] ::  (mul1_f 32 ++ [LeakAddr []; LeakAddr [0]]).
op bn_muln_step (i : int) : leakages_t = mul1acc_f (to_uint ((of_int i))%W64) 31 ++
 [LeakAddr [] ; LeakAddr [] ; LeakAddr [i]] .

op bn_muln_g (x : int) : leakages_t =  iteri (x-1) (fun i r => bn_muln_step  (i+1) ++ r) [].
lemma bn_muln_g_comp_1 x : x = 1 => bn_muln_g x = []. smt(@Int). qed.
lemma bn_muln_g_comp_2 x : 1 <  x => bn_muln_g x = bn_muln_step (x-1) ++ bn_muln_g (x - 1). rewrite /bn_muln_g. smt(@Int). qed.

op bn_muln_f (x : int) : leakages_t = LeakAddr [] :: bn_muln_g x ++ bn_muln_prefix.

lemma bn_muln_leakages start_l :
   hoare [ M(Syscall).bn_muln : M.leakages = start_l 
     ==> M.leakages = bn_muln_f 32 ++ start_l ].
proof. 
proc.
seq 20 : (i = 1 /\ M.leakages = [ LeakFor (1, 32) ;  LeakAddr []; LeakAddr []; LeakAddr []] ++  mul1_f 32 ++ [LeakAddr []; LeakAddr [0]] ++ start_l).
wp. sp. elim*. progress.
call (mul1_leakages ([LeakAddr [] ; LeakAddr [0] ] ++ start_l)).
skip. progress. smt(@List). wp.
while (1 <= i /\ i <= 32 /\ M.leakages = bn_muln_g i ++ bn_muln_prefix ++ start_l).
wp.  
sp. elim*. progress.
exists* i. elim*. move => i_var.
call (mul1acc_leakages ([LeakAddr [] ; LeakAddr [] ; LeakAddr [i_var]] ++ leakages) (W64.of_int i_var)).
skip. progress.
smt().
smt().
rewrite (bn_muln_g_comp_2 (i{hr}+1)). smt(). simplify. rewrite /bn_muln_step.
pose xxx := mul1acc_f (to_uint ((of_int i{hr}))%W64) 31.
do ? rewrite - catA.
congr.
congr. congr. 
smt(@List).
skip.
progress.
rewrite bn_muln_g_comp_1. auto. simplify.
rewrite /bn_muln_prefix. auto.
smt().
qed.

(* bn_muln LEAKAGES  *)
op dbn_muln_prefix : leakages_t =  LeakFor (1, 64) :: LeakAddr [] :: LeakAddr [] :: LeakAddr [] ::  (dmul1_f 64 ++ [LeakAddr []; LeakAddr [0]]).
op dbn_muln_step (i : int) : leakages_t = dmul1acc_f (to_uint ((of_int i))%W64) 63 ++
 [LeakAddr [] ; LeakAddr [] ; LeakAddr [i]] .

op dbn_muln_g (x : int) : leakages_t =  iteri (x-1) (fun i r => dbn_muln_step  (i+1) ++ r) [].
lemma dbn_muln_g_comp_1 x : x = 1 => dbn_muln_g x = []. smt(@Int). qed.
lemma dbn_muln_g_comp_2 x : 1 <  x => dbn_muln_g x = dbn_muln_step (x-1) ++ dbn_muln_g (x - 1). rewrite /dbn_muln_g. smt(@Int). qed.

op dbn_muln_f (x : int) : leakages_t = LeakAddr [] :: dbn_muln_g x ++ dbn_muln_prefix.

lemma dbn_muln_leakages start_l :
   hoare [ M(Syscall).dbn_muln : M.leakages = start_l 
     ==> M.leakages = dbn_muln_f 64 ++ start_l ].
proof. 
proc.
seq 21 : (aux_4 = 64 /\ i = 1 /\ M.leakages = [ LeakFor (1, 64) ;  LeakAddr []; LeakAddr []; LeakAddr []] ++  dmul1_f 64 ++ [LeakAddr []; LeakAddr [0]] ++ start_l).
wp. sp. elim*. progress.
call (dmul1_leakages ([LeakAddr [] ; LeakAddr [0] ] ++ start_l)).
skip. progress. smt(@List). wp.
while (aux_4 = 64 /\ 1 <= i /\ i <= 64 /\ M.leakages = dbn_muln_g i ++ dbn_muln_prefix ++ start_l).
wp.  
sp. elim*. progress.
exists* i. elim*. move => i_var.
call (dmul1acc_leakages ([LeakAddr [] ; LeakAddr [] ; LeakAddr [i_var]] ++ leakages) (W64.of_int i_var)).
skip. progress.
smt().
smt().
rewrite (dbn_muln_g_comp_2 (i{hr}+1)). smt(). simplify. rewrite /dbn_muln_step.
pose xxx := dmul1acc_f (to_uint ((of_int i{hr}))%W64) 63.
do ? rewrite - catA.
congr.
congr. congr. 
smt(@List).
skip.
progress.
rewrite dbn_muln_g_comp_1. auto. simplify.
rewrite /dbn_muln_prefix. auto.
smt().
qed.


(* div2 LEAKAGES  *)
op div2_prefix (k : int) : leakages_t = LeakFor (0, k) :: LeakAddr [] :: [].
op div2_step (i : int) : leakages_t = LeakAddr [i] :: LeakAddr [64 + i] :: [].

op div2_g (x : int) : leakages_t   =  iteri x (fun i r => div2_step  i ++ r) [].
lemma div2_g_comp_1 x : x = 0 => div2_g x = []. smt(@Int). qed.
lemma div2_g_comp_2 x : 0 <  x => div2_g x = div2_step (x-1) ++ div2_g (x - 1). smt(@Int). qed.

op div2_f (x k : int) : leakages_t = div2_g x ++ div2_prefix k.

lemma div2_leakages start_l kk :
   hoare [ M(Syscall).div2 : M.leakages = start_l  /\ kk = k /\ 0 <= k
     ==> M.leakages = div2_f kk kk ++ start_l ].
proof. 
proc.
sp.  elim*. progress.
conseq (_: 0 <= k /\ aux = k /\ M.leakages = div2_prefix k ++ start_l /\ i = 0 /\ k = kk ==> _).
progress.
while (aux = k /\ 0 <= i /\ i <= k /\ M.leakages = div2_f i k ++ start_l /\ k = kk).
wp.  skip.  progress. 
smt(). smt(). 
rewrite /div2_f. rewrite (div2_g_comp_2 (i{hr}+1)).  smt(). simplify. rewrite /div2_step. simplify. auto.
skip. progress.  rewrite /div2_f. rewrite div2_g_comp_1. auto. auto. 
have -> : i0 = k{hr}. smt(). auto.
qed.



(* bn_shrink LEAKAGES  *)
op bn_shrink_prefix : leakages_t = LeakFor (0, 32) :: LeakAddr [] :: [].
op bn_shrink_step (i : int) : leakages_t = LeakAddr [i] :: LeakAddr [i] :: [].

op bn_shrink_g (x : int) : leakages_t =  iteri x (fun i r => bn_shrink_step i ++ r) [].
lemma bn_shrink_g_comp_1 x : x = 0 => bn_shrink_g x = []. smt(@Int). qed.
lemma bn_shrink_g_comp_2 x : 0 <  x => bn_shrink_g x = bn_shrink_step (x-1) ++ bn_shrink_g (x - 1). smt(@Int). qed.

op bn_shrink_f (x : int) : leakages_t = bn_shrink_g x ++ bn_shrink_prefix.

lemma bn_shrink_leakages start_l :
   hoare [ M(Syscall).bn_shrink : M.leakages = start_l 
     ==> M.leakages = bn_shrink_f 32 ++ start_l ].
proof. 
proc.
sp.  elim*. progress.
conseq (_: M.leakages = bn_shrink_prefix ++ start_l /\ i = 0 ==> _).
progress.
while (0 <= i /\ i <= 32 /\ M.leakages = bn_shrink_f i ++ start_l).
wp.  skip.  progress. 
smt(). smt(). 
rewrite /bn_shrink_f. rewrite (bn_shrink_g_comp_2 (i{hr} +1)).  smt(). simplify. rewrite /bn_shrink_step. simplify. auto.
skip. progress. rewrite /bn_shrink_f.  rewrite bn_shrink_g_comp_1. auto. auto. 
smt().
qed.



(* SUBTRACTION LEAKAGES  *)
op dsub_prefix : leakages_t = 
  [LeakFor (1, 64); LeakAddr []; LeakAddr [0]; LeakAddr []; 
    LeakAddr []; LeakAddr [0]; LeakAddr [0]].

op dsub_step (i : int) : leakages_t = 
  [LeakAddr [i] ; LeakAddr [] ; LeakAddr [] ; LeakAddr [i] ; 
    LeakAddr [i] ].


op dsub_g (x : int) : leakages_t =  iteri (x-1) (fun i r => dsub_step  (i+1) ++ r) [].
lemma dsub_g_comp_1 x : x <= 1 => dsub_g x = []. smt(@Int). qed.
lemma dsub_g_comp_2 x : 1 <  x => dsub_g x = dsub_step (x-1) ++ dsub_g (x - 1). rewrite /dsub_g. smt(@Int). qed.

op dsub_f (x : int) : leakages_t = dsub_g x ++ dsub_prefix.


lemma dbn_subc_leakages start_l :
  hoare [ M(Syscall).dbn_subc : M.leakages = start_l 
            ==> M.leakages = dsub_f 64 ++ start_l ].
proof. 
proc.
sp.  elim*. progress.
conseq (_: M.leakages = dsub_prefix ++ start_l /\ i = 1 /\ aux_1 = 64 ==> _).
progress.
while (aux_1 = 64 /\ 0 < i /\ i <= 64 /\ M.leakages = dsub_f i ++ start_l).
wp.  skip.  progress. 
simplify. smt(). smt(). rewrite /dsub_f. rewrite (dsub_g_comp_2 (i{hr} +1)).  smt(). simplify. rewrite /dsub_step. simplify. auto.
skip. progress. rewrite /dsub_f.  rewrite dsub_g_comp_1. auto. auto.
smt().
qed.



(* bn_expand LEAKAGES  *)
op bn_expand_prefix : leakages_t = LeakFor (0, 32) :: LeakAddr [] :: [].
op bn_expand_step (i : int) : leakages_t = LeakAddr [i] :: LeakAddr [i] :: [].
op bn_expand_step2 (i : int) : leakages_t = LeakAddr [i] :: LeakAddr [] :: [].

op bn_expand_g (x : int) : leakages_t = iteri x (fun i r => bn_expand_step  i ++ r) [].
lemma bn_expand_g_comp_1 x : x = 0 => bn_expand_g x = []. smt(@Int). qed.
lemma bn_expand_g_comp_2 x : 0 <  x => bn_expand_g x = bn_expand_step (x-1) ++ bn_expand_g (x - 1). smt(@Int). qed.

op bn_expand_h (x : int) : leakages_t = iteri (x-32) (fun i r => bn_expand_step2 (i + 32) ++ r) [].
lemma bn_expand_h_comp_1 x : x = 32 => bn_expand_h x = []. smt(@Int). qed.
lemma bn_expand_h_comp_2 x : 32 < x => bn_expand_h x = bn_expand_step2 (x-1) ++ bn_expand_h (x - 1). rewrite /bn_expand_h. smt(@Int). qed.


op bn_expand_f (x : int) : leakages_t = bn_expand_h (2 * x) ++ [LeakFor (32, 64) ; LeakAddr [] ] ++ bn_expand_g x ++ bn_expand_prefix.

lemma bn_expand_leakages start_l :
   hoare [ M(Syscall).bn_expand : M.leakages = start_l 
     ==> M.leakages = bn_expand_f 32 ++ start_l ].
proof. 
proc.
seq 4 : (M.leakages =  bn_expand_g 32 ++ bn_expand_prefix ++ start_l).
sp.  elim*. progress.
conseq (_: M.leakages = bn_expand_prefix ++ start_l /\ i = 0 ==> _).
progress.
while (0 <= i /\ i <= 32 /\ M.leakages = bn_expand_g i ++ bn_expand_prefix ++ start_l).
wp.  skip.  progress. 
smt(). smt(). 
rewrite (bn_expand_g_comp_2 (i{hr} +1)).  smt(). simplify. rewrite /bn_expand_step. simplify. auto.
skip. progress.  rewrite bn_expand_g_comp_1. auto. auto. 
smt().
sp. elim*. progress.
rewrite /bn_expand_f. simplify.
conseq (_: i = 32 /\ aux = 64 /\ M.leakages = LeakFor (32, 64) :: LeakAddr [] :: bn_expand_g 32 ++ bn_expand_prefix ++ start_l ==> _).
progress.
while (aux = 64 /\ 32 <= i /\ i <= 64 
  /\ M.leakages = (bn_expand_h i ++ LeakFor (32, 64) :: LeakAddr [] :: 
                   bn_expand_g 32 ++ bn_expand_prefix ++ start_l)).
wp.  skip.  progress. 
smt(). smt(). 
rewrite (bn_expand_h_comp_2 (i{hr} +1)).  smt(). simplify.
 rewrite /bn_expand_step2. simplify. auto.
skip. progress. simplify.
rewrite bn_expand_h_comp_1. auto. 
simplify. auto. smt(@List).
qed.


(* dbn_cmov LEAKAGES  *)
op dbn_cmov_prefix : leakages_t = LeakFor (0, 64) :: LeakAddr [] :: [].
op dbn_cmov_step (i : int) : leakages_t = LeakAddr [i] :: LeakAddr [] :: LeakAddr [] :: LeakAddr [i] :: 
LeakAddr [i] :: [].

op dbn_cmov_g (x : int) : leakages_t = iteri (x) (fun i r => dbn_cmov_step (i) ++ r) [].
lemma dbn_cmov_g_comp_1 x : x = 0 => dbn_cmov_g x = []. smt(@Int). qed.
lemma dbn_cmov_g_comp_2 x : 0 <  x => dbn_cmov_g x = dbn_cmov_step (x-1) ++ dbn_cmov_g (x - 1). smt(@Int). qed.

op dbn_cmov_f (x : int) : leakages_t = dbn_cmov_g x ++ dbn_cmov_prefix.

lemma dbn_cmov_leakages start_l :
   hoare [ M(Syscall).dbn_cmov : M.leakages = start_l 
     ==> M.leakages = dbn_cmov_f 64 ++ start_l ].
proof. 
proc.
sp.  elim*. progress.
conseq (_: M.leakages = dbn_cmov_prefix ++ start_l /\ i = 0 /\ aux = 64 ==> _).
progress.
while (0 <= i /\ i <= 64 /\ aux = 64 /\ M.leakages = dbn_cmov_f i ++ start_l).
wp.  skip.  progress. 
smt(). smt(). 
rewrite /dbn_cmov_f. rewrite (dbn_cmov_g_comp_2 (i{hr} +1)).  smt(). simplify. rewrite /dbn_cmov_step.
progress. skip. progress.  rewrite /dbn_cmov_f. rewrite dbn_cmov_g_comp_1. auto. auto. 
smt().
qed.

(* dcminusP LEAKAGES  *)
op dcminusP_f  : leakages_t =  
 dbn_cmov_f 64 ++ [LeakAddr []] ++ dsub_g 64 ++ dsub_prefix ++ [LeakAddr []; LeakAddr []; LeakAddr []] ++
dcopy_g 64 ++ dcopy_prefix ++ [LeakAddr []] .

lemma dcminusP_leakages start_l :
   hoare [ M(Syscall).dcminusP : M.leakages = start_l 
     ==> M.leakages = dcminusP_f  ++ start_l ].
proof. 
proc.
pose suf1 :=  [LeakAddr []] ++ start_l.
seq 6 : (M.leakages = dcopy_f 64 ++ suf1 ).
wp.  call (dbn_copy_leakages suf1). simplify. wp. skip. progress. auto.

pose suf2 :=  [LeakAddr [];LeakAddr [];LeakAddr []] ++ dcopy_f 64 ++ suf1.
seq 8 : (M.leakages = dsub_f 64 ++ suf2).
wp.  call (dbn_subc_leakages suf2). wp. skip. progress.

pose suf3 :=  [LeakAddr []] ++ dsub_f 64 ++ suf2.
seq 5 : (M.leakages = dbn_cmov_f 64 ++ suf3).
wp.  call (dbn_cmov_leakages suf3). wp. skip. progress.
skip.
progress. rewrite /suf3 /suf2 /suf1.
do ? rewrite catA. rewrite /dcminusP_f.
auto.
qed.

(* bn_breduce LEAKAGES  *)
op bn_breduce_f : leakages_t = bn_shrink_f 32 ++
[LeakAddr []] ++ dcminusP_f ++
[LeakAddr []] ++ bn_expand_f 32 ++
[LeakAddr []] ++ dsub_f 64 ++
[LeakAddr []; LeakAddr []; LeakAddr []] ++ bn_muln_f 32 ++
[LeakAddr []; LeakAddr []] ++ bn_shrink_f 32 ++
[LeakAddr []] ++ div2_f 64 64 ++
[LeakAddr []] ++ dbn_muln_f 64 ++ [LeakAddr []; LeakAddr []].

lemma bn_breduce_leakages start_l :
   hoare [ M(Syscall).bn_breduce : M.leakages = start_l 
     ==> M.leakages = bn_breduce_f ++ start_l ].
proof. 
proc. 
pose suf1 :=  [LeakAddr []; LeakAddr []] ++ start_l.
seq 16 : (M.leakages = dbn_muln_f 64 ++ suf1 ).
wp.  call (dbn_muln_leakages suf1). simplify. wp. skip. progress. 

pose suf2 :=  [LeakAddr []] ++ dbn_muln_f 64 ++ suf1.
seq 6 : (M.leakages = div2_f 64 64 ++ suf2).
wp.  call (div2_leakages suf2 64). simplify. wp. skip. progress. 

pose suf3 :=  [LeakAddr []] ++ div2_f 64 64 ++ suf2.
seq 3 : (M.leakages = bn_shrink_f 32 ++ suf3).
wp.  call (bn_shrink_leakages suf3). simplify. wp. skip. progress. 

pose suf4 :=  [LeakAddr [] ;  LeakAddr []] ++ bn_shrink_f 32 ++ suf3.
seq 9 : (M.leakages = bn_muln_f 32 ++ suf4).
wp.  call (bn_muln_leakages suf4). simplify. wp. skip. progress.  rewrite /suf4.

pose suf5 :=  [LeakAddr [];LeakAddr [];LeakAddr []] ++ bn_muln_f 32 ++ suf4.
seq 9 : (M.leakages = dsub_f 64  ++ suf5).
wp.  call (dbn_subc_leakages suf5). simplify. wp. skip. progress. 

pose suf6 :=  [LeakAddr []] ++ dsub_f 64 ++ suf5.
seq 4 : (M.leakages = bn_expand_f 32  ++ suf6).
wp. call (bn_expand_leakages suf6). simplify. wp. skip. progress. 

pose suf7 :=  [LeakAddr []] ++ bn_expand_f 32 ++ suf6.
seq 3 : (M.leakages = dcminusP_f   ++ suf7).
wp. call (dcminusP_leakages suf7). simplify. wp. skip. progress. 

pose suf8 :=  [LeakAddr []] ++ dcminusP_f ++ suf7.
seq 4 : (M.leakages = bn_shrink_f 32   ++ suf8).
wp. call (bn_shrink_leakages suf8). wp. skip.
progress.
skip. progress.
rewrite /suf8 /suf7 /suf6 /suf5 /suf4 /suf3 /suf2 /suf1.
rewrite /bn_breduce_f. 
do ? rewrite catA. auto.
qed.

(* mulm LEAKAGES  *)
op [opaque] mulm_t : leakages_t = bn_breduce_f ++ [LeakAddr []] ++ bn_muln_f 32  ++
[LeakAddr []; LeakAddr [] ; LeakAddr []] .
lemma mulm_leakages start_l : 
   hoare [ M(Syscall).bn_mulm : M.leakages = start_l 
                ==> M.leakages = mulm_t ++ start_l ].
proof. proc.
pose suf1 :=  [LeakAddr [];LeakAddr []; LeakAddr []] ++ start_l.
seq 11 : (M.leakages = bn_muln_f 32 ++ suf1 ).
wp. call (bn_muln_leakages suf1). simplify. wp. skip. progress. 

pose suf2 :=  [LeakAddr []] ++ bn_muln_f 32 ++ suf1.
seq 7 : (M.leakages = bn_breduce_f ++ suf2).
wp. call (bn_breduce_leakages suf2). simplify. wp. skip. progress. 
skip. auto.
progress.
rewrite /suf2 /suf1.
rewrite /mulm_t /bn_muln_f.
do? rewrite catA. auto.
qed.


op bn_set_q_t : leakages_t = LeakAddr [31] :: LeakAddr [] :: LeakAddr [] :: LeakAddr [30] :: LeakAddr [] :: 
LeakAddr [] :: LeakAddr [29] :: LeakAddr [] :: LeakAddr [] :: LeakAddr [28] :: 
LeakAddr [] :: LeakAddr [] :: LeakAddr [27] :: LeakAddr [] :: LeakAddr [] :: 
LeakAddr [26] :: LeakAddr [] :: LeakAddr [] :: LeakAddr [25] :: LeakAddr [] :: 
LeakAddr [] :: LeakAddr [24] :: LeakAddr [] :: LeakAddr [] :: LeakAddr [23] :: 
LeakAddr [] :: LeakAddr [] :: LeakAddr [22] :: LeakAddr [] :: LeakAddr [] :: 
LeakAddr [21] :: LeakAddr [] :: LeakAddr [] :: LeakAddr [20] :: LeakAddr [] :: 
LeakAddr [] :: LeakAddr [19] :: LeakAddr [] :: LeakAddr [] :: LeakAddr [18] :: 
LeakAddr [] :: LeakAddr [] :: LeakAddr [17] :: LeakAddr [] :: LeakAddr [] :: 
LeakAddr [16] :: LeakAddr [] :: LeakAddr [] :: LeakAddr [15] :: LeakAddr [] :: 
LeakAddr [] :: LeakAddr [14] :: LeakAddr [] :: LeakAddr [] :: LeakAddr [13] :: 
LeakAddr [] :: LeakAddr [] :: LeakAddr [12] :: LeakAddr [] :: LeakAddr [] :: 
LeakAddr [11] :: LeakAddr [] :: LeakAddr [] :: LeakAddr [10] :: LeakAddr [] :: 
LeakAddr [] :: LeakAddr [9] :: LeakAddr [] :: LeakAddr [] :: LeakAddr [8] :: 
LeakAddr [] :: LeakAddr [] :: LeakAddr [7] :: LeakAddr [] :: LeakAddr [] :: 
LeakAddr [6] :: LeakAddr [] :: LeakAddr [] :: LeakAddr [5] :: LeakAddr [] :: 
LeakAddr [] :: LeakAddr [4] :: LeakAddr [] :: LeakAddr [] :: LeakAddr [3] :: 
LeakAddr [] :: LeakAddr [] :: LeakAddr [2] :: LeakAddr [] :: LeakAddr [] :: 
LeakAddr [1] :: LeakAddr [] :: LeakAddr [] :: LeakAddr [0] :: LeakAddr [] :: 
LeakAddr [] :: [].
lemma bn_set_q_leakages l :
  hoare [ M(Syscall).bn_set_q : M.leakages = l
     ==> M.leakages = bn_set_q_t ++ l].
proc. wp. skip. progress. qed.


op bn_set_p_t : leakages_t = bn_set_q_t.
lemma bn_set_p_leakages l :
  hoare [ M(Syscall).bn_set_p : M.leakages = l
     ==> M.leakages = bn_set_p_t ++ l].
proc. wp. skip. progress. qed.


op bn_set_g_t : leakages_t = bn_set_q_t.
lemma bn_set_g_leakages l :
  hoare [ M(Syscall).bn_set_g : M.leakages = l
     ==> M.leakages = bn_set_g_t ++ l].
proc. wp. skip. progress. qed.


op bn_set_bp_t : leakages_t = LeakAddr [63] :: LeakAddr [] :: LeakAddr [] :: LeakAddr [62] :: LeakAddr [] :: 
LeakAddr [] :: LeakAddr [61] :: LeakAddr [] :: LeakAddr [] :: LeakAddr [60] :: 
LeakAddr [] :: LeakAddr [] :: LeakAddr [59] :: LeakAddr [] :: LeakAddr [] :: 
LeakAddr [58] :: LeakAddr [] :: LeakAddr [] :: LeakAddr [57] :: LeakAddr [] :: 
LeakAddr [] :: LeakAddr [56] :: LeakAddr [] :: LeakAddr [] :: LeakAddr [55] :: 
LeakAddr [] :: LeakAddr [] :: LeakAddr [54] :: LeakAddr [] :: LeakAddr [] :: 
LeakAddr [53] :: LeakAddr [] :: LeakAddr [] :: LeakAddr [52] :: LeakAddr [] :: 
LeakAddr [] :: LeakAddr [51] :: LeakAddr [] :: LeakAddr [] :: LeakAddr [50] :: 
LeakAddr [] :: LeakAddr [] :: LeakAddr [49] :: LeakAddr [] :: LeakAddr [] :: 
LeakAddr [48] :: LeakAddr [] :: LeakAddr [] :: LeakAddr [47] :: LeakAddr [] :: 
LeakAddr [] :: LeakAddr [46] :: LeakAddr [] :: LeakAddr [] :: LeakAddr [45] :: 
LeakAddr [] :: LeakAddr [] :: LeakAddr [44] :: LeakAddr [] :: LeakAddr [] :: 
LeakAddr [43] :: LeakAddr [] :: LeakAddr [] :: LeakAddr [42] :: LeakAddr [] :: 
LeakAddr [] :: LeakAddr [41] :: LeakAddr [] :: LeakAddr [] :: LeakAddr [40] :: 
LeakAddr [] :: LeakAddr [] :: LeakAddr [39] :: LeakAddr [] :: LeakAddr [] :: 
LeakAddr [38] :: LeakAddr [] :: LeakAddr [] :: LeakAddr [37] :: LeakAddr [] :: 
LeakAddr [] :: LeakAddr [36] :: LeakAddr [] :: LeakAddr [] :: LeakAddr [35] :: 
LeakAddr [] :: LeakAddr [] :: LeakAddr [34] :: LeakAddr [] :: LeakAddr [] :: 
LeakAddr [33] :: LeakAddr [] :: LeakAddr [] :: LeakAddr [32] :: LeakAddr [] :: 
LeakAddr [] :: LeakAddr [31] :: LeakAddr [] :: LeakAddr [] :: LeakAddr [30] :: 
LeakAddr [] :: LeakAddr [] :: LeakAddr [29] :: LeakAddr [] :: LeakAddr [] :: 
LeakAddr [28] :: LeakAddr [] :: LeakAddr [] :: LeakAddr [27] :: LeakAddr [] :: 
LeakAddr [] :: LeakAddr [26] :: LeakAddr [] :: LeakAddr [] :: LeakAddr [25] :: 
LeakAddr [] :: LeakAddr [] :: LeakAddr [24] :: LeakAddr [] :: LeakAddr [] :: 
LeakAddr [23] :: LeakAddr [] :: LeakAddr [] :: LeakAddr [22] :: LeakAddr [] :: 
LeakAddr [] :: LeakAddr [21] :: LeakAddr [] :: LeakAddr [] :: LeakAddr [20] :: 
LeakAddr [] :: LeakAddr [] :: LeakAddr [19] :: LeakAddr [] :: LeakAddr [] :: 
LeakAddr [18] :: LeakAddr [] :: LeakAddr [] :: LeakAddr [17] :: LeakAddr [] :: 
LeakAddr [] :: LeakAddr [16] :: LeakAddr [] :: LeakAddr [] :: LeakAddr [15] :: 
LeakAddr [] :: LeakAddr [] :: LeakAddr [14] :: LeakAddr [] :: LeakAddr [] :: 
LeakAddr [13] :: LeakAddr [] :: LeakAddr [] :: LeakAddr [12] :: LeakAddr [] :: 
LeakAddr [] :: LeakAddr [11] :: LeakAddr [] :: LeakAddr [] :: LeakAddr [10] :: 
LeakAddr [] :: LeakAddr [] :: LeakAddr [9] :: LeakAddr [] :: LeakAddr [] :: 
LeakAddr [8] :: LeakAddr [] :: LeakAddr [] :: LeakAddr [7] :: LeakAddr [] :: 
LeakAddr [] :: LeakAddr [6] :: LeakAddr [] :: LeakAddr [] :: LeakAddr [5] :: 
LeakAddr [] :: LeakAddr [] :: LeakAddr [4] :: LeakAddr [] :: LeakAddr [] :: 
LeakAddr [3] :: LeakAddr [] :: LeakAddr [] :: LeakAddr [2] :: LeakAddr [] :: 
LeakAddr [] :: LeakAddr [1] :: LeakAddr [] :: LeakAddr [] :: LeakAddr [0] :: 
LeakAddr [] :: LeakAddr [] :: [].
lemma bn_set_bp_leakages l :
  hoare [ M(Syscall).bn_set_bp : M.leakages = l
     ==> M.leakages = bn_set_bp_t ++ l].
proc. wp. skip. progress. qed.

op bn_set_bq_t = bn_set_bp_t.
lemma bn_set_bq_leakages l :
  hoare [ M(Syscall).bn_set_bq : M.leakages = l
     ==> M.leakages = bn_set_bq_t ++ l].
proc. wp. skip. progress. qed.


 
op samp_prefix : leakages_t = 
  LeakCond (! set0_64_.`2) :: LeakAddr [] :: LeakAddr [] :: (set0_f 32 ++
                                                           [LeakAddr [];
                                                              LeakAddr []]).
op samp_step  : leakages_t = LeakCond true :: LeakAddr [] :: LeakAddr [] :: (sub_f 32 ++
                                                LeakAddr [] :: (copy_f 32 ++
                                                                LeakAddr [] :: LeakAddr [] :: 
                                                                LeakAddr [] :: [])) .


op samp_g (x : int) : leakages_t = if (x < 0) then [(LeakAddr [x])] else iteri x (fun i r => samp_step  ++ r) []. 
lemma samp_g_comp_1 x : x = 0 => samp_g x = [].  rewrite /samp_g.
smt(@Int). qed.
lemma samp_g_comp_2 x : 0 <  x  => samp_g x = samp_step  ++ samp_g (x - 1). 
rewrite /samp_g. move => q.
have ->: x < 0 = false. smt().
have ->: x - 1 < 0 = false. smt(). simplify.
smt(@Int). qed.


op samp_suffix : leakages_t = 
 LeakCond false :: LeakAddr [] :: LeakAddr [] 
   :: (sub_f 32 ++ LeakAddr [] :: 
      (copy_f 32 ++ LeakAddr [] :: LeakAddr [] :: LeakAddr [] :: [])).

op samp_f (x : int) : leakages_t = samp_g x ++ samp_prefix.
op samp_t (x : int) : leakages_t = samp_suffix ++ samp_f (x - 1).

lemma samp_t_inj : injective samp_t.

 have fact1 : size (samp_t 1)  = size samp_suffix + size samp_prefix.
  rewrite /samp_t. rewrite /samp_f. simplify. rewrite samp_g_comp_1.   auto. simplify.
  rewrite size_cat. simplify. 
  smt(@Int).

 have fact2 : forall x, x <= 0 => size (samp_t x) = 1 + size samp_suffix + size samp_prefix.
  progress.  rewrite /samp_t. 
  rewrite /samp_f /samp_g.
  have ->: x - 1 < 0. smt(). simplify.
  rewrite size_cat. simplify.
   smt(@Int).
  

 have fact3 : forall x, 0 <= x => size (samp_g x) = x * (size samp_step).
   apply intind. progress.
    rewrite /samp_f /samp_prefix. rewrite samp_g_comp_1. auto. auto.
   progress.
    rewrite samp_g_comp_2. smt(). 
    rewrite size_cat. simplify. smt(@Int).
 
 have fact4: forall x, 1 <= x => size (samp_t x) = (x - 1) * (size samp_step) + size samp_suffix + size samp_prefix . progress. rewrite /samp_t. rewrite size_cat. rewrite /samp_f.
   rewrite size_cat. rewrite fact3. smt(). smt(@Int).

 have fact5 : 1 <= size samp_step. rewrite /samp_step. simplify. smt(@List).
 clear fact3.
    
 have fact6 : forall x y, x <> y => samp_t x <> samp_t y. 
  move => x y xneqy. 
    case (x <= 0) => xh.
    case (y <= 0) => yh.  
    rewrite /samp_t. rewrite /samp_f.  rewrite /samp_f. rewrite /samp_g.
     have ->: x - 1 < 0 = true. smt().
     have ->: y - 1 < 0 = true. smt(). 
    simplify. 
     smt(@List).

  rewrite /samp_t. rewrite /samp_f. rewrite /samp_g.
     have ->: x - 1 < 0 = true. smt().
     have ->: y - 1 < 0 = false. smt(). simplify.
     case (y - 1 = 0) => y0. rewrite iteri0. smt(). simplify. smt(@List).
     rewrite iteri_red. smt(). simplify. rewrite /samp_step. smt(@List).

  case (y <= 0) => yh.  
  rewrite /samp_t. rewrite /samp_f. rewrite /samp_g.
     have ->: x - 1 < 0 = false. smt().
     have ->: y - 1 < 0 = true. smt(). simplify.
     case (x - 1 = 0) => x0. rewrite iteri0. smt(). simplify. smt(@List).
     rewrite iteri_red. smt(). simplify. rewrite /samp_step. smt(@List).

  have : size (samp_t x) <> size (samp_t y).
   rewrite fact4. smt().
   rewrite fact4. smt().
  smt(@Int).
  smt().
smt().
qed.
 



lemma rsample_leakages l :
  hoare [ M(Syscall).bn_rsample : M.leakages = l 
     ==> M.leakages = samp_t res.`1 ++ l].
proc.
seq 18 :  (M.leakages = samp_prefix ++ l /\ i = 0  /\ cf = false ).
wp. ecall (bn_set0_leakages M.leakages). wp. skip. progress.
rewrite /samp_prefix. simplify. smt(@List).
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
                LeakAddr [] :: LeakAddr [] :: LeakAddr [] :: (samp_g i{hr} ++ samp_prefix ++
                                               l))
 = (copy_f 32 ++ [LeakAddr [] ; LeakAddr []; LeakAddr []]) ++
samp_g i{hr} ++ samp_prefix ++ l.
do ? rewrite - catA. simplify. auto. 


smt(@List).
rewrite /samp_t. simplify.
rewrite /samp_suffix.  simplify.  split. rewrite H4. auto.
rewrite H0. rewrite H2. auto. 
do ? rewrite - catA. simplify.
congr. congr. congr. 
do ? rewrite - catA. congr. simplify. auto.
skip. progress. rewrite /samp_prefix. rewrite /samp_f. rewrite samp_g_comp_1.
auto. rewrite /samp_prefix. auto.
rewrite H2. rewrite H. auto.
auto.
qed.



op expm_t_prefix : leakages_t = LeakCond true :: LeakAddr [] :: LeakAddr [] :: LeakAddr [] :: (copy_f 32 ++
                                                               [LeakAddr []] ++
                                                               copy_g 32 ++
                                                               copy_prefix ++
                                                               [LeakAddr []] ++
                                                               set1_g 32 ++
                                                               set1_prefix ++
                                                               [LeakAddr []]).
op expm_step_acc i = 
  LeakCond (W64.zero \ult i) :: LeakAddr [] :: (swapr_f 32 ++
                                                  ([LeakAddr []] ++ mulm_t ++
                                                   ([LeakAddr []] ++ mulm_t ++
                                                    ([LeakAddr []] ++
                                                     copy_f 32 ++
                                                     ([LeakAddr []] ++
                                                      swapr_f 32 ++
                                                      ([LeakAddr []] ++
                                                       ith_bit_t
                                                         (i + W64.one -
                                                          W64.one) ++
                                                       (LeakAddr [] ::
                                                        LeakAddr [] ::
                                                        []))))))).


op [opaque] expm_step (i : int) : leakages_t = iteri i (fun i r => expm_step_acc (W64.of_int (2048 - (i + 1))) ++ r) []. 

lemma expm_step0 : expm_step 0 = []. smt(@Int). qed.
lemma expm_stepS i : 0 < i =>  expm_step i 
 =  expm_step_acc (W64.of_int (2048 - i))
    ++ expm_step (i-1). rewrite /expm_step. 
progress. 
search iteri.
have ->: i = (i-1)+1. smt().
rewrite iteriS. smt(). simplify. auto. qed.

lemma expm_stepSS i : 0 <= i < 2048 =>  expm_step (2048 -  i)
  = expm_step_acc (W64.of_int i) ++ expm_step (2048 - (i + 1)).
progress.
case ((2048 - i) = 0).
progress.
have : i = 0. smt().
progress. rewrite expm_stepS. auto. simplify. auto.
move => q.
rewrite expm_stepS. smt().
simplify. smt().
qed.
  

op [opaque] expm_t : leakages_t = expm_step 2048 ++ expm_t_prefix.

lemma expm_leakages l :
  hoare [ M(Syscall).bn_expm : M.leakages = l 
     ==> M.leakages = expm_t ++ l].
proc.
seq 19 : (M.leakages = expm_t_prefix ++ l /\ i = (W64.of_int (32 * 64)) ). 

pose suf1 :=  [LeakAddr []] ++ l.
seq 6 : (M.leakages = set1_f 32 ++ suf1 ).
wp.  call (bn_set1_leakages suf1). simplify. wp. skip. progress.

pose suf2 :=  [LeakAddr []] ++ set1_f 32 ++ suf1.
seq 3 : (M.leakages = copy_f 32 ++ suf2).
wp.  call (bn_copy_leakages suf2). simplify. wp. skip. progress.

pose suf3 :=  [LeakAddr []] ++ copy_f 32 ++ suf2.
seq 3 : (M.leakages = copy_f 32 ++ suf3).
wp.  call (bn_copy_leakages suf3). simplify. wp. skip. progress.
wp. skip. progress.
rewrite /suf3 /suf2 /suf1.
rewrite /expm_t_prefix.
do ? rewrite catA. simplify. smt(@List).
while (W64.zero \ult (i + W64.one) /\ ( M.leakages = expm_step (2048 - (to_uint i)) ++ expm_t_prefix ++ l)  /\ (i <> W64.zero => (i - W64.one) \ult (W64.of_int 2048))  ).
exists* i. elim*. move => i_var.
pose suf1 :=  LeakAddr [] :: LeakAddr [] ::  expm_step (2048 - to_uint (i_var)) ++ expm_t_prefix ++ l.
seq 6 : (M.leakages = (ith_bit_t (i_var - W64.one)) ++ suf1 /\ i_var = i + W64.one /\ W64.zero \ult i_var /\ (i + W64.one <> W64.zero => i \ult (W64.of_int 2048))).
wp.  call (ith_bit_leakages suf1 (i_var - W64.one)). simplify.
wp. skip. progress. smt(@W64).  smt(@W64).
pose suf2 :=  [LeakAddr []]  ++ ith_bit_t (i_var - W64.one) ++ suf1.
seq 4 : (M.leakages = (swapr_f 32) ++ suf2 /\ i_var = i + W64.one /\ W64.zero \ult i_var /\ (i + W64.one <> W64.zero => i \ult (W64.of_int 2048))).
wp.  call (swapr_leakages suf2). 
wp. skip. progress. 
pose suf3 :=  [LeakAddr []]  ++ swapr_f 32 ++ suf2.
seq 3 : (M.leakages = copy_f 32 ++ suf3 /\ i_var = i + W64.one /\ W64.zero \ult i_var /\ (i + W64.one <> W64.zero => i \ult (W64.of_int 2048))).
wp.  call (bn_copy_leakages suf3). 
wp. skip. progress. 
pose suf4 :=  [LeakAddr []]  ++ copy_f 32 ++ suf3.
seq 3 : (M.leakages = mulm_t ++ suf4 /\ i_var = i + W64.one /\ W64.zero \ult i_var /\ (i + W64.one <> W64.zero => i \ult (W64.of_int 2048))).
wp.  call (mulm_leakages suf4). 
wp. skip. progress.    
pose suf5 :=  [LeakAddr []]  ++ mulm_t ++ suf4.
seq 3 : (M.leakages = mulm_t ++ suf5 /\ i_var = i + W64.one /\ W64.zero \ult i_var /\ (i + W64.one <> W64.zero => i \ult (W64.of_int 2048))).
wp.  call (mulm_leakages suf5). 
wp. skip. progress.    
pose suf6 :=  [LeakAddr []]  ++ mulm_t ++ suf5.
seq 3 : (M.leakages = swapr_f 32 ++ suf6 /\ i_var = i + W64.one /\ W64.zero \ult i_var /\ (i + W64.one <> W64.zero => i \ult (W64.of_int 2048))).
wp.  call (swapr_leakages suf6). 
wp. skip. progress.    
wp.  skip. progress.
rewrite /suf6 /suf5 /suf4 /suf3 /suf2 /suf1. 
rewrite (expm_stepSS (to_uint i{hr})). 
split. smt(@W64). smt(@W64).
rewrite /expm_step_acc.
have ->: (W64.of_int (to_uint i{hr})) = i{hr}. 
smt(@W64).
have -> :  (to_uint i{hr} + 1) = to_uint (i{hr} + W64.one). smt(@W64).
do ? rewrite  catA.
simplify.
pose xxx := swapr_f 32 ++ [LeakAddr []] ++ mulm_t ++ [LeakAddr []] ++ mulm_t.
pose yyy := xxx ++ [LeakAddr []] ++ copy_f 32 ++ [LeakAddr []] ++
swapr_f 32 ++ [LeakAddr []] ++ ith_bit_t (i{hr} + W64.one - W64.one).
pose www := expm_step (2048 - to_uint (i{hr} + W64.one)) .
congr. congr. 
have ->: yyy ++ [LeakAddr []; LeakAddr []] ++ www
   = yyy ++ ([LeakAddr []; LeakAddr []] ++ www). rewrite catA. auto.
have ->: ([LeakAddr []; LeakAddr []] ++ www) = (LeakAddr [] :: LeakAddr [] :: www). smt(@List).
auto.
smt(@W64).
skip.
progress.
rewrite expm_step0. simplify. auto.
have : i0 = W64.zero.  smt(@W64).
progress.
rewrite /expm_t. auto.
qed.

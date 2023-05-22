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

op swapr_g (x : int) : leakages_t = iteri x (fun i r => swapr_step i ++ r) [].
lemma swapr_g_comp_1 x : x = 0 => swapr_g x = []. by smt(@Int). qed.
lemma swapr_g_comp_2 x : 0 <  x => swapr_g x = swapr_step (x-1) ++ swapr_g (x - 1). by smt(@Int). qed.

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
op bn_muln_prefix : leakages_t = LeakFor (1, 32) :: LeakAddr [] :: (mul1_f 32 ++ [LeakAddr []; LeakAddr [0]]).
op bn_muln_step (i : int) : leakages_t = mul1acc_f (to_uint ((of_int i))%W64) 31 ++
 [LeakAddr [] ; LeakAddr [] ; LeakAddr [i]] .

op bn_muln_g (x : int) : leakages_t =  iteri (x-1) (fun i r => bn_muln_step  (i+1) ++ r) [].
lemma bn_muln_g_comp_1 x : x = 1 => bn_muln_g x = []. smt(@Int). qed.
lemma bn_muln_g_comp_2 x : 1 <  x => bn_muln_g x = bn_muln_step (x-1) ++ bn_muln_g (x - 1). rewrite /bn_muln_g. smt(@Int). qed.

op bn_muln_f (x : int) : leakages_t = bn_muln_g x ++ bn_muln_prefix.

lemma bn_muln_leakages start_l :
   hoare [ M(Syscall).bn_muln : M.leakages = start_l 
     ==> M.leakages = bn_muln_f 32 ++ start_l ].
proof. 
proc.
seq 12 : (i = 1 /\ M.leakages = [LeakFor (1, 32) ; LeakAddr [] ] ++ mul1_f 32 ++ [LeakAddr []; LeakAddr [0]] ++ start_l).
wp. sp. elim*. progress.
call (mul1_leakages ([LeakAddr [] ; LeakAddr [0] ] ++ start_l)).
skip. progress. smt(@List).
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


(* dbn_muln LEAKAGES  *)
op dbn_muln_prefix : leakages_t = LeakFor (1, 64) :: LeakAddr [] :: (dmul1_f 64 ++ [LeakAddr []; LeakAddr [0]]).
op dbn_muln_step (i : int) : leakages_t = dmul1acc_f (to_uint ((of_int i))%W64) 63 ++
 [LeakAddr [] ; LeakAddr [] ; LeakAddr [i]] .

op dbn_muln_g (x : int) : leakages_t  =  iteri (x-1) (fun i r => dbn_muln_step  (i+1) ++ r) [].
lemma dbn_muln_g_comp_1 x : x = 1 => dbn_muln_g x = []. smt(@Int). qed.
lemma dbn_muln_g_comp_2 x : 1 <  x => dbn_muln_g x = dbn_muln_step (x-1) ++ dbn_muln_g (x - 1). rewrite /dbn_muln_g. smt(@Int). qed.

op dbn_muln_f (x : int) : leakages_t = dbn_muln_g x ++ dbn_muln_prefix.

lemma dbn_muln_leakages start_l :
   hoare [ M(Syscall).dbn_muln : M.leakages = start_l 
     ==> M.leakages = dbn_muln_f 64 ++ start_l ].
proof. 
proc.
seq 13 : (aux_3 = 64 /\ i = 1 /\ M.leakages = [LeakFor (1, 64) ; LeakAddr [] ] ++ dmul1_f 64 ++ [LeakAddr []; LeakAddr [0]] ++ start_l).
wp. sp. elim*. progress.
call (dmul1_leakages ([LeakAddr [] ; LeakAddr [0] ] ++ start_l)).
skip. progress. smt(@List).
while (aux_3 = 64 /\  1 <= i /\ i <= 64 /\ M.leakages = dbn_muln_g i ++ dbn_muln_prefix ++ start_l).
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
 dbn_cmov_f 64 ++ [LeakAddr []] ++ dsub_g 64 ++ dsub_prefix ++ [LeakAddr []] ++
dcopy_g 64 ++ dcopy_prefix ++ [LeakAddr []] .

lemma dcminusP_leakages start_l :
   hoare [ M(Syscall).dcminusP : M.leakages = start_l 
     ==> M.leakages = dcminusP_f  ++ start_l ].
proof. 
proc.
pose suf1 :=  [LeakAddr []] ++ start_l.
seq 4 : (M.leakages = dcopy_f 64 ++ suf1 ).
wp.  call (dbn_copy_leakages suf1). simplify. wp. skip. progress. auto.

pose suf2 :=  [LeakAddr []] ++ dcopy_f 64 ++ suf1.
seq 3 : (M.leakages = dsub_f 64 ++ suf2).
wp.  call (dbn_subc_leakages suf2). wp. skip. progress.

pose suf3 :=  [LeakAddr []] ++ dsub_f 64 ++ suf2.
seq 3 : (M.leakages = dbn_cmov_f 64 ++ suf3).
wp.  call (dbn_cmov_leakages suf3). wp. skip. progress.
skip.
progress. rewrite /suf3 /suf2 /suf1.
do ? rewrite catA. rewrite /dcminusP_f.
auto.
qed.

(* bn_breduce LEAKAGES  *)
op bn_breduce_f : leakages_t = bn_shrink_f 32 ++ [LeakAddr []] ++ dbn_cmov_g 64 ++ dbn_cmov_prefix ++
[LeakAddr []] ++ dsub_g 64 ++ dsub_prefix ++ [LeakAddr []] ++ dcopy_g 64 ++
dcopy_prefix ++ [LeakAddr []] ++ [LeakAddr []] ++ bn_expand_h (2 * 32) ++
[LeakFor (32, 64); LeakAddr []] ++ bn_expand_g 32 ++ bn_expand_prefix ++
[LeakAddr []] ++ dsub_g 64 ++ dsub_prefix ++ [LeakAddr []] ++ bn_muln_g 32 ++
bn_muln_prefix ++ [LeakAddr []] ++ bn_shrink_g 32 ++ bn_shrink_prefix ++
[LeakAddr []] ++ div2_g 64 ++ div2_prefix 64 ++ [LeakAddr []] ++
dbn_muln_g 64 ++ dbn_muln_prefix ++ [LeakAddr []].

lemma bn_breduce_leakages start_l :
   hoare [ M(Syscall).bn_breduce : M.leakages = start_l 
     ==> M.leakages = bn_breduce_f ++ start_l ].
proof. 
proc. 
pose suf1 :=  [LeakAddr []] ++ start_l.
seq 13 : (M.leakages = dbn_muln_f 64 ++ suf1 ).
wp.  call (dbn_muln_leakages suf1). simplify. wp. skip. progress. 

pose suf2 :=  [LeakAddr []] ++ dbn_muln_f 64 ++ suf1.
seq 3 : (M.leakages = div2_f 64 64 ++ suf2).
wp.  call (div2_leakages suf2 64). simplify. wp. skip. progress. 

pose suf3 :=  [LeakAddr []] ++ div2_f 64 64 ++ suf2.
seq 3 : (M.leakages = bn_shrink_f 32 ++ suf3).
wp.  call (bn_shrink_leakages suf3). simplify. wp. skip. progress. 

pose suf4 :=  [LeakAddr []] ++ bn_shrink_f 32 ++ suf3.
seq 3 : (M.leakages = bn_muln_f 32 ++ suf4).
wp.  call (bn_muln_leakages suf4). simplify. wp. skip. progress. 

pose suf5 :=  [LeakAddr []] ++ bn_muln_f 32 ++ suf4.
seq 7 : (M.leakages = dsub_f 64  ++ suf5).
wp.  call (dbn_subc_leakages suf5). simplify. wp. skip. progress. 

pose suf6 :=  [LeakAddr []] ++ dsub_f 64 ++ suf5.
seq 3 : (M.leakages = bn_expand_f 32  ++ suf6).
wp. call (bn_expand_leakages suf6). simplify. wp. skip. progress. 

pose suf7 :=  [LeakAddr []] ++ bn_expand_f 32 ++ suf6.
seq 3 : (M.leakages = dcminusP_f   ++ suf7).
wp. call (dcminusP_leakages suf7). simplify. wp. skip. progress. 

pose suf8 :=  [LeakAddr []] ++ dcminusP_f ++ suf7.
seq 3 : (M.leakages = bn_shrink_f 32   ++ suf8).
wp. call (bn_shrink_leakages suf8). wp. skip.
progress.
skip. progress.
rewrite /suf8 /suf7 /suf6 /suf5 /suf4 /suf3 /suf2 /suf1.
do? rewrite catA.
auto.
qed.

(* mulm LEAKAGES  *)
op mulm_t : leakages_t = bn_breduce_f ++ [LeakAddr []] ++ bn_muln_g 32 ++ bn_muln_prefix ++
[LeakAddr []] .
lemma mulm_leakages start_l : 
   hoare [ M(Syscall).mulm : M.leakages = start_l 
                ==> M.leakages = mulm_t ++ start_l ].
proof. proc.
pose suf1 :=  [LeakAddr []] ++ start_l.
seq 7 : (M.leakages = bn_muln_f 32 ++ suf1 ).
wp. call (bn_muln_leakages suf1). simplify. wp. skip. progress. 

pose suf2 :=  [LeakAddr []] ++ bn_muln_f 32 ++ suf1.
seq 3 : (M.leakages = bn_breduce_f ++ suf2).
wp. call (bn_breduce_leakages suf2). simplify. wp. skip. progress. 
skip. auto.
progress.
rewrite /suf2 /suf1.
do? rewrite catA.
auto.
qed.

require import List Int AllCore. 
require import W64_SchnorrExtract_ct.
from Jasmin require import JModel.

require import BigNum_LF.


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

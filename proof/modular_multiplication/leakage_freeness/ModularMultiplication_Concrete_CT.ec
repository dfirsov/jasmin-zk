require import List Int AllCore. 
require import W64_SchnorrExtract_ct.
from Jasmin require import JModel.

require import BigNum_LF.
require import BarretReduction_Concrete_CT.

(* mulm LEAKAGES  *)
op [opaque] mulm_t : leakages_t = bn_breduce_f ++ [LeakAddr []] ++ bn_muln_f 32  ++
[LeakAddr []; LeakAddr [] ; LeakAddr []] .
lemma bn_mulm_leakages start_l :
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

lemma bn_mulm_ll : islossless M(Syscall).bn_mulm.
proc.
wp. call bn_breduce_ll.
wp. call bn_muln_ll.
wp. auto.
qed.


lemma bn_mulm_leakages_ph start_l :
   phoare [ M(Syscall).bn_mulm : M.leakages = start_l
     ==> M.leakages = mulm_t ++ start_l ] = 1%r.
phoare split !  1%r 0%r. auto.
conseq bn_mulm_ll. hoare. conseq (bn_mulm_leakages start_l).
qed.

lemma bn_mulm_ct &m l r a b n :  M.leakages{m} = l
 => Pr[ M(Syscall).bn_mulm(r,a,b,n)@&m : M.leakages = mulm_t ++ l ] = 1%r.
move => lh.
byphoare (_: (glob M) = (glob M){m} ==> _ ).
conseq (bn_mulm_leakages_ph l).
auto. auto. auto.
qed.


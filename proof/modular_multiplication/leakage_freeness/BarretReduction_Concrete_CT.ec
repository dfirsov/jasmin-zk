require import List Int AllCore. 
require import W64_SchnorrExtract_ct.
from Jasmin require import JModel.

require import BigNum_LF.

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


lemma bn_breduce_ll : islossless M(Syscall).bn_breduce.
proc.
wp. call bn_shrink_ll.
wp. call dcminusP_ll. 
wp. call bn_expand_ll.
wp. call dbn_subc_ll.
wp. call bn_muln_ll.
wp. call bn_shrink_ll.
wp. call div2_ll. simplify.
wp. call dbn_muln_ll.
wp. auto.
qed.


lemma bn_breduce_leakages_ph start_l :
   phoare [ M(Syscall).bn_breduce : M.leakages = start_l 
     ==> M.leakages = bn_breduce_f ++ start_l ] = 1%r.
phoare split !  1%r 0%r. auto.
conseq bn_breduce_ll. hoare. conseq (bn_breduce_leakages start_l).
qed.


lemma bn_breduce_ct &m l r x n :  M.leakages{m} = l
 => Pr[ M(Syscall).bn_breduce(r,x,n)@&m : M.leakages = bn_breduce_f ++ l ] = 1%r.
move => lh.
byphoare (_: (glob M) = (glob M){m} ==> _ ).
conseq (bn_breduce_leakages_ph l).
auto. auto. auto.
qed.


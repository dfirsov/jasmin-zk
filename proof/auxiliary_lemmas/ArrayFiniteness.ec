require import AllCore List.


require import WArray256.
from Jasmin require import JModel.

op all_8lists = alltuples 8 [true;false]. 

lemma all_8lists_full (l : bool list) : size l = 8
 => l \in all_8lists. 
rewrite /all_8lists.
move => q.
apply (alltuplesP 8 l [true;false]).
split. auto. smt(@List).
qed.


lemma all_8lists_size  : 
 size all_8lists = 2 ^ 8.
rewrite /all_8lists. rewrite size_alltuples.
simplify. rewrite /max. simplify. auto.
qed.


lemma all_8lists_uniq  : 
 uniq all_8lists.
smt(@List).
qed.

op all_8words = map W8.bits2w all_8lists.

lemma all_8words_full (w : W8.t) : 
  w \in all_8words.
rewrite /all_8words.
have : (W8.w2bits w) \in all_8lists. apply all_8lists_full.
smt(@W8).
move => h.
have : W8.bits2w (W8.w2bits w) \in all_8words. rewrite /all_8words.
apply map_f. auto.
rewrite /all_8words.
smt(@W8).
qed.

lemma all_8words_size : size all_8words = 2 ^ 8.
rewrite /all_8words. rewrite - all_8lists_size.
smt(@List).
qed.
  

lemma all_8words_uniq : uniq all_8words.
rewrite /all_8words.
apply map_inj_in_uniq. 
progress. 
have  : w2bits(bits2w x)%W8 = w2bits(bits2w y)%W8. smt().
rewrite  bits2wK. 
have -: x \in all_8lists.  auto. 
clear H. rewrite /all_8lists. smt(@List).
rewrite  bits2wK. smt(@List).
auto.
apply all_8lists_uniq.
qed.




op all_256lists = alltuples 256 all_8words. 

lemma all_256lists_full (l : W8.t list) : size l = 256
 => l \in all_256lists. 
rewrite /all_8lists.
move => q.
apply (alltuplesP 256 l all_8words).
split. auto. 
apply List.allP.
smt(all_8words_full).
qed.


lemma all_256lists_size  : 
 size all_256lists = 256 ^ 256.
rewrite /all_256lists. rewrite size_alltuples.
simplify. rewrite /max.
rewrite all_8words_size. simplify.
auto.
qed.

lemma all_256lists_uniq  : 
 uniq all_256lists.
smt(@List all_8words_uniq).
qed.


op all_256words = map WArray256.of_list all_256lists.



lemma all_256words_uniq : uniq all_256words.
rewrite /all_256words.
apply map_inj_in_uniq. 
progress. 
have  : to_list(of_list x)%WArray256 = to_list(of_list y)%WArray256. smt().
rewrite of_listK.
rewrite /all_256lists. smt(@List).
rewrite  of_listK. smt(@List).
rewrite /all_256lists. smt(@List).
apply all_256lists_uniq.
qed.

lemma all_256words_full (w : WArray256.t) : 
  w \in all_256words.
rewrite /all_256words.
have : (WArray256.to_list w) \in all_256lists. apply all_256lists_full.
smt(@WArray256).
move => h.
have : WArray256.of_list (WArray256.to_list w) \in all_256words. rewrite /all_256words.
apply map_f. auto.
rewrite /all_256words.
smt(@WArray256).
qed.

lemma all_256words_size : size all_256words = 256 ^ 256.
rewrite /all_256words. rewrite - all_256lists_size.
smt(@List).
qed.


    (* WArray1 *)
require import WArray1.

op all_256lists1 = alltuples 1 all_8words. 

lemma all_256lists1_full (l : W8.t list) : size l = 1
 => l \in all_256lists1. 
rewrite /all_8lists.
move => q.
apply (alltuplesP 1 l all_8words).
split. auto. 
apply List.allP.
smt(all_8words_full).
qed.


lemma all_256lists1_size  : 
 size all_256lists1 = 256 ^ 1.
rewrite /all_256lists1. rewrite size_alltuples.
simplify. rewrite /max.
rewrite all_8words_size. simplify.
auto.
qed.

lemma all_256lists1_uniq  : 
 uniq all_256lists1.
smt(@List all_8words_uniq).
qed.

require import Array1.

op all_256words1 = map (fun x => (Array1.init (fun i => x))) all_8words.

lemma all_256words1_uniq : uniq all_256words1.
rewrite /all_256words1.
apply map_inj_in_uniq. 
progress.  smt(@Array1).
apply all_8words_uniq.
qed.


lemma all_256words1_full (w : W8.t Array1.t ) : 
  w \in all_256words1.
have s : size (Array1.to_list w) = 1. smt(@Array1).

have q : (head witness (Array1.to_list w)) \in all_8words. 
apply all_8words_full.

rewrite /all_256words1.
have <- : (fun (x : W8.t) => Array1.init (fun (_ : int) => x)) (head witness (to_list w)) = w.
smt(@Array1). 
apply map_f. auto.
qed.

lemma all_256words1_size : size all_256words1 = 256 ^ 1.
rewrite /all_256words1. rewrite - all_256lists1_size.
smt(@List).
qed.



require import BigNum_spec.
require import AllCore List.

import W64xN.
import R.
op all_w64xN : R.t list  = map R.bn_ofint (range 0 modulusR).

lemma all_w64xN_uniq : uniq (all_w64xN).
apply map_inj_in_uniq. move => x y.
move => xi yi.
have f0 : 0 < modulusR. auto.
have f1 : 0 <= x < modulusR. split. smt(@List). move => _.
smt(@List).
have f2 : 0 <= y < modulusR. split. smt(@List). move => _.
smt(@List).
clear xi yi. 
move => ass.
have : valR (R.bn_ofint x) = valR (R.bn_ofint y).
smt().
rewrite R.bn_ofintK.
rewrite R.bn_ofintK. smt(@IntDiv).
smt(@List).
qed.

lemma modulusR_pos : 0 < modulusR. auto.
qed.


lemma all_w64xN_size : size (all_w64xN) = modulusR.
rewrite /all_w64xN.  smt(@List modulusR_pos).
qed.


lemma all_ints x : 0 <= x < modulusR => (R.bn_ofint x) \in all_w64xN.
progress. rewrite /all_w64xN. smt(@List).
qed.


lemma all_w64xN_full x : x \in all_w64xN.
 have f1 : R.bn_ofint (valR x) \in all_w64xN.
 apply all_ints.  split. smt(@W64xN). move => _. 
have f2 : 0 <= valR x < W64x2N.M ^ nlimbs.  rewrite /valR. apply R.bnk_cmp. smt().
smt (bnK).
qed.




    


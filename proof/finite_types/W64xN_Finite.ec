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
smt.
have f2 : 0 <= y < modulusR. split. smt(@List). move => _.
smt.
clear xi yi.
move => ass.
have : valR (R.bn_ofint x) = valR (R.bn_ofint y).
smt().
rewrite R.bn_ofintK.
rewrite R.bn_ofintK. smt.
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

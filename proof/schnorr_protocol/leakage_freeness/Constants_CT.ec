require import List Int AllCore. 
require import W64_SchnorrExtract_ct.
from Jasmin require import JModel.



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

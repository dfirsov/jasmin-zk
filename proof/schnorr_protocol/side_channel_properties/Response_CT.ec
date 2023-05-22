require import List Int AllCore Distr.

from Jasmin require import JModel.


require import W64_SchnorrExtract_ct.

(* only makes sense if response is not probabilitystic  *)
lemma response_ct : equiv [M(Syscall).response ~ M(Syscall).response : ={M.leakages} ==> ={M.leakages} ].
proof.  proc. progress. inline*. sim. qed.



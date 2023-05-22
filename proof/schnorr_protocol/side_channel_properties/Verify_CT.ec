require import List Int AllCore Distr.

from Jasmin require import JModel.


require import W64_SchnorrExtract_ct.

(* only makes sense if verify is not probabilitystic  *)
lemma verify_ct : equiv [M(Syscall).verify ~ M(Syscall).verify : ={M.leakages} ==> ={M.leakages} ].
proof.  proc. progress. inline*. sim. qed.



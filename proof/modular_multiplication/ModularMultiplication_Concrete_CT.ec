require import List Int AllCore. 
require import W64_SchnorrExtract_ct.
from Jasmin require import JModel.


equiv mulm_ct :
  M(Syscall).mulm ~ M(Syscall).mulm :
  ={M.leakages} ==> ={M.leakages}.
proof.  proc. progress. inline*. sim. qed.

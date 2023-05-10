require import List Int AllCore. 
require import W64_SchnorrExtract_ct.
from Jasmin require import JModel.


equiv expm_ct :
  M(Syscall).expm ~ M(Syscall).expm :
  ={M.leakages, glob M} ==> ={M.leakages}.
proof.  proc. progress. inline*. sim. qed.

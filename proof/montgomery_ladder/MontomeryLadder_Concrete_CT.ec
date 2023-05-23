require import List Int AllCore. 
require import W64_SchnorrExtract_ct.
from Jasmin require import JModel.


equiv expm_ct :
  M(Syscall).bn_expm ~ M(Syscall).bn_expm :
  ={M.leakages, glob M} ==> ={M.leakages}.
proof.  proc. progress. inline*. sim. qed.

lemma bn_expm_ct &m r1 r2 x1 x2 n1 n2 m1 m2 l:
  Pr[ M(Syscall).bn_expm(r1,m1,x1,n1)@&m: M.leakages = l ]
   = Pr[ M(Syscall).bn_expm(r2,m2,x2,n2)@&m: M.leakages = l ].
proof. byequiv;auto. conseq expm_ct;auto. qed.

require import List Int AllCore. 
require import W64_SchnorrExtract_ct.
from Jasmin require import JModel.


equiv bn_mulm_ct_equiv :
  M(Syscall).bn_mulm ~ M(Syscall).bn_mulm :
  ={M.leakages} ==> ={M.leakages}.
proof.  proc. progress. inline*. sim. qed.

lemma bn_mulm_ct &m r1 r2 a1 a2 b1 b2 p1 p2 l:
  Pr[ M(Syscall).bn_mulm(r1,p1,a1,b1)@&m: M.leakages = l ]
    = Pr[ M(Syscall).bn_mulm(r2,p2,a2,b2)@&m: M.leakages = l ].
byequiv. conseq bn_mulm_ct_equiv. auto. auto. auto. auto.
qed.



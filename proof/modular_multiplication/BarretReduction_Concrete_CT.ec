require import List Int AllCore. 
require import W64_SchnorrExtract_ct.
from Jasmin require import JModel.


equiv bn_breduce_ct_equiv :
  M(Syscall).bn_breduce ~ M(Syscall).bn_breduce :
  ={M.leakages} ==> ={M.leakages}.
proof.  proc. progress. inline*. sim. qed.

lemma bn_breduce_ct &m r1 r2 a1 a2 p1 p2 l:
  Pr[ M(Syscall).bn_breduce(r1,p1,a1)@&m: M.leakages = l ]
    = Pr[ M(Syscall).bn_breduce(r2,p2,a2)@&m: M.leakages = l ].
byequiv. conseq bn_breduce_ct_equiv. auto. auto. auto. auto.
qed.



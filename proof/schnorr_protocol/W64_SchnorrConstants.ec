require import AllCore Distr DInterval List Int IntDiv.

from Jasmin require import JModel JBigNum.
require import Array32 Array64 Array128.

require import Ring_ops_spec.
import Zp.
import W64xN Sub R. 

require import ConstantsExtract.


print ConstantsExtract.M.

op g = 2.

lemma bn_set_gg_prop :
  phoare[ ConstantsExtract.M.bn_set_g : true ==> W64xN.valR res = g ] = 1%r.
proof.
proc.
wp.
skip.

have H: 32 = 31 + 1. by trivial.
rewrite H.
clear H.
rewrite bnkS; 1: trivial.
rewrite /dig.
simplify.

have H: 31 = 30 + 1. by trivial.
rewrite H.
clear H.
rewrite bnkS; 1: trivial.
rewrite /dig.
simplify.



rewrite bnkS; 1: trivial.
progress (rewrite bnkS).
rewrite bnkS.
by trivial.

print valR.
search bnk.
print bnk.


simplify.

axiom bn_set_go_prop : 
  phoare[ M(Syscall).bn_set_go : true ==> W64xN.valR res = p  ] = 1%r.
axiom bn_set_bf_prop : 
  phoare[ M(Syscall).bn_set_bf : true ==> W64x2N.valR res = Ri  ] = 1%r.
axiom bn_set_eo_prop : 
  phoare[ M(Syscall).bn_set_eo : true ==> W64xN.valR res = q  ] = 1%r.
axiom bn_set_eb_prop : 
  phoare[ M(Syscall).bn_set_eb : true ==> W64x2N.valR res = Rip  ] = 1%r.



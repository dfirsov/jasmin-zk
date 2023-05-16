require import AllCore Distr DInterval List Int IntDiv.

from Jasmin require import JModel JBigNum.
require import Array32 Array64 Array128.

require import Ring_ops_spec.
import Zp.
import W64xN Sub R. 

require import W64_SchnorrExtract.

(* to be defined *)
op p : int     = witness.
op q : int     = witness.          
op g_int : int = witness.

axiom bn_set_gg_prop :
  phoare[ M(Syscall).bn_set_gg : true ==> W64xN.valR res = val (Zp.inzmod g_int)  ] = 1%r.
axiom bn_set_go_prop : 
  phoare[ M(Syscall).bn_set_go : true ==> W64xN.valR res = p  ] = 1%r.
axiom bn_set_bf_prop : 
  phoare[ M(Syscall).bn_set_bf : true ==> W64x2N.valR res = Ri  ] = 1%r.
axiom bn_set_eo_prop : 
  phoare[ M(Syscall).bn_set_eo : true ==> W64xN.valR res = q  ] = 1%r.
axiom bn_set_eb_prop : 
  phoare[ M(Syscall).bn_set_eb : true ==> W64x2N.valR res = Rip  ] = 1%r.



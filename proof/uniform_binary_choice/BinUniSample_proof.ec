require import AllCore IntDiv CoreMap List Distr DList.
from Jasmin require import JModel.

require import Array32.
require BinUniSample_spec.
require import Array1 WArray1.
require import Finite FinLists.

require import BigNum_proofs.
require import Random_bit_proof.
require import W64_SchnorrExtract.


require import BinUniSample_spec.

clone import RandomChoice as W64xNChoice with type t <- W64.t Array32.t
proof*.

section.

local module W = {
  proc step2(a b : W64.t Array32.t) = {
    var r, cond;
    r <@ M(Syscall).random_bit();
    cond <- r = W8.zero;
    a <@ M(Syscall).bn_cmov(cond, b, a);
    return a;
  }
}.


local lemma lemma5 : 
  equiv [W.step2 ~ BinSampleSpec.main : ={arg} ==>   res{1} = res{2} ].
proc. 
wp.
ecall {1} (bn_cmov_correct cond{1} b{1} a{1}).
wp. 
call random_bit_lemma4.
skip. progress.
smt(@W8).
qed.



local lemma lemma6 : 
  equiv [W.step2 ~ BinSampleSpec.spec : ={arg} ==>   res{1} = res{2} ].
symmetry.
transitivity BinSampleSpec.main
  (={arg} ==> ={res})
  (={arg} ==> ={res}).
progress. smt(). auto.
symmetry.
proc*. ecall (sat_spec a{1} b{1}). skip. auto.
symmetry.
conseq lemma5.
auto. auto.
qed.


lemma uniform_binary_choice_eq : 
  equiv [M(Syscall).uniform_binary_choice ~ BinSampleSpec.spec : ={arg} ==> res{1} = res{2} ].
transitivity W.step2
  (={arg} ==> ={res})
  (={arg} ==> ={res}).
smt(). smt().
proc. wp.
call (_:true). sim. wp.
inline*. wp.  rnd. wp.  skip. progress.
conseq lemma6.
qed.

end section.

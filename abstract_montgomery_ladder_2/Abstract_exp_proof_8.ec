require import AllCore IntDiv CoreMap List.

require import JModel.
require import BitEncoding.
import BS2Int.


require Abstract_exp_proof_7.
clone include Abstract_exp_proof_7.


import IterOp.


module M8 = {
  proc iterop_spec (x:R, n:R) : R = {
    return (x ^ (valR n));
  }  
}.

lemma iterop_real_speac2 :
 equiv[ M8.iterop_spec ~ M1.iterop_spec   : arg{1}.`1 = arg{2}.`1 /\  valR arg{1}.`2 = bs2int arg{2}.`2 ==> ={res}] .
proc. skip. progress.
smt().
qed.



section.
declare module M <: BasicOps.

declare axiom iterop_swap :
 equiv[ M.swapr ~ Spec.swapr    : arg{2}.`1 = arg{1}.`1 /\ arg{2}.`2 = arg{1}.`2 /\   arg{1}.`3 = as_w64 arg{2}.`3
    ==> ={res}].

declare axiom iterop_ithbit :
 equiv[ M.ith_bit ~ Spec.ith_bit    : arg{2}.`1 = arg{1}.`1 /\  arg{2}.`2 = W64.to_uint arg{1}.`2 
    /\ 0 <= ctr{2} < Rsize ==> ={res} /\ (res{2} = W64.one \/ res{2} = W64.zero) ].


declare axiom iterop_opr :
  equiv [ M.opr ~ Spec.mul: arg{1}.`2 = arg{2}.`1 /\ arg{1}.`3 = arg{2}.`2 /\ ImplR p{1} P /\ valR a{1} < P /\ valR b{1} < P ==> ={res} /\ valR res{1} < P  ].


declare axiom stateless_M (x y : glob M) : x = y.


lemma iterop_real_speac :
 equiv[ M1.iterop_spec ~ M7(M).iterop  : valR arg{2}.`1 = P 
   /\  arg{1}.`1 = arg{2}.`2
   /\ bs2int arg{1}.`2 = valR arg{2}.`3
   /\ size arg{1}.`2 = Rsize
   /\ valR x{1} < P
     ==> ={res}].
transitivity M2.iterop
   (={arg} /\  0 < size arg{1}.`2  /\   valR x{1} < P  ==> ={res}) 
  (valR arg{2}.`1 = P 
   /\  arg{1}.`1 = arg{2}.`2
   /\ bs2int arg{1}.`2 = valR arg{2}.`3
   /\ size arg{1}.`2 = Rsize
   /\ valR x{1} < P
     ==> ={res} ).
progress.  exists arg{1}. progress. smt(Rsize_pos). auto.
symmetry.
conseq iterop_2_spec.
auto. auto.
transitivity M3.iterop
  (={arg} /\  0 < size n{1}  ==> ={res})
  (valR arg{2}.`1 = P 
   /\  arg{1}.`1 = arg{2}.`2
   /\ bs2int arg{1}.`2 = valR arg{2}.`3
   /\ size arg{1}.`2 = Rsize
   /\ valR x{1} < P
     ==> ={res} ).
progress. 
exists arg{1}. progress. smt(Rsize_pos). auto.
conseq iterop_2_3.
transitivity M4.iterop
  (arg{1}.`1 = arg{2}.`1 /\ (bitsR arg.`2{1}) = (arg.`2{2})  /\ size n{1} = Rsize /\  0 < size n{1} ==> ={res})
(valR arg{2}.`1 = P 
   /\  arg{1}.`1 = arg{2}.`2
   /\ arg{1}.`2 = arg{2}.`3
   /\ valR x{1} < P
     ==> ={res} ).
progress. 
exists (x{1} , ( n{2})). progress. 
smt (bitsR_prop).
smt(Rsize_pos). auto.
conseq iterop_3_4_1.
transitivity M5.iterop
  (={arg} ==> ={res})
  (valR arg{2}.`1 = P 
   /\  arg{1}.`1 = arg{2}.`2
   /\ arg{1}.`2 = arg{2}.`3
   /\ valR x{1} < P
     ==> ={res} ).
progress. 
exists (x{1} , ( n{2})). progress.  smt(). auto.
conseq iterop_4_5.  
transitivity M6(M).iterop
 (arg{2}.`2 = arg{1}.`1 /\ arg{2}.`3 = arg{1}.`2 /\  valR m{2} = P /\ valR x{1} < P ==> ={res})
  (={arg} ==> ={res}).
progress. smt(). smt().
conseq (iterop_5_6 M iterop_swap iterop_ithbit iterop_opr stateless_M).   smt().
conseq (iterop_6_7 M).
smt (stateless_M).
qed.


end section.




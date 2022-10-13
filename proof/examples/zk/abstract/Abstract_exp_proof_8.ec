require import AllCore IntDiv CoreMap List.

require import JModel.
require import BitEncoding.
import BS2Int.


require Abstract_exp_proof_7.
clone include Abstract_exp_proof_7.


import IterOp.


module M8 = {
  proc expm_spec (x:R, n:R) : R = {
    return (x ^ (valR n));
  }  
}.



lemma exp_real_speac2 :
 equiv[ M8.expm_spec ~ M1.expm_spec   : arg{1}.`1 = arg{2}.`1 /\  valR arg{1}.`2 = bs2int arg{2}.`2 ==> ={res}] .
proc. skip. progress.
smt().
qed.



section.
declare module M <: BasicOps.


declare axiom exp_swap :
 equiv[ M.swapr ~ Spec.swapr    : arg{2}.`1 = arg{1}.`1 /\ arg{2}.`2 = arg{1}.`2 /\   arg{1}.`3 = as_w64 arg{2}.`3
    ==> ={res}].

declare axiom exp_ithbit :
 equiv[ M.ith_bit ~ Spec.ith_bit    : arg{2}.`1 = arg{1}.`1 /\  arg{2}.`2 = W64.to_uint arg{1}.`2 
    /\ 0 <= ctr{2} < Rsize ==> ={res} /\ (res{2} = W64.one \/ res{2} = W64.zero) ].


declare axiom stateless_M (x y : glob M) : x = y.


lemma exp_real_speac :
 equiv[ M1.expm_spec ~ M7(M).expm  : valR arg{2}.`1 = P 
   /\  arg{1}.`1 = arg{2}.`2
   /\ bs2int arg{1}.`2 = valR arg{2}.`3
   /\ size arg{1}.`2 = Rsize
   /\ valR x{1} < P
     ==> ={res}].
transitivity M2.expm
   (={arg} /\  0 < size arg{1}.`2  /\   valR x{1} < P  ==> ={res}) 
  (valR arg{2}.`1 = P 
   /\  arg{1}.`1 = arg{2}.`2
   /\ bs2int arg{1}.`2 = valR arg{2}.`3
   /\ size arg{1}.`2 = Rsize
   /\ valR x{1} < P
     ==> ={res} ).
progress.  exists arg{1}. progress. smt(Rsize_pos). auto.
symmetry.
conseq expm_correct.
auto. auto.
transitivity M3.expm
  (={arg} /\  0 < size n{1}  ==> ={res})
  (valR arg{2}.`1 = P 
   /\  arg{1}.`1 = arg{2}.`2
   /\ bs2int arg{1}.`2 = valR arg{2}.`3
   /\ size arg{1}.`2 = Rsize
   /\ valR x{1} < P
     ==> ={res} ).
progress. 
exists arg{1}. progress. smt(Rsize_pos). auto.
conseq exp_2_3.
transitivity M4.expm
  (arg{1}.`1 = arg{2}.`1 /\ (bitsR arg.`2{1}) = (arg.`2{2})  /\ size n{1} = Rsize /\  0 < size n{1} ==> ={res})
(valR arg{2}.`1 = P 
   /\  arg{1}.`1 = arg{2}.`2
   /\ arg{1}.`2 = arg{2}.`3
     ==> ={res} ).
progress. 
exists (x{1} , ( n{2})). progress. 
smt (bitsR_prop).
smt(Rsize_pos). auto.
conseq exp_3_4_1.

transitivity M5.expm
  (={arg} ==> ={res})
  (valR arg{2}.`1 = P 
   /\  arg{1}.`1 = arg{2}.`2
   /\ arg{1}.`2 = arg{2}.`3
     ==> ={res} ).
progress. 
exists (x{1} , ( n{2})). progress.  smt(). auto.
conseq exp_4_5.  
transitivity M6(M).expm
 (arg{2}.`2 = arg{1}.`1 /\ arg{2}.`3 = arg{1}.`2 /\  valR m{2} = P ==> ={res})
  (={arg} ==> ={res}).
progress. smt(). smt().
conseq (exp_5_6 M exp_swap exp_ithbit _).  admit.
conseq (exp_6_7 M).
smt (stateless_M).
qed.


end section.




(* declare axiom exp_mulm :  *)
(*   equiv [ M.mulm ~ Spec.mulm: valR arg{1}.`2 = asint arg{2}.`1 /\ valR arg{1}.`3 = asint arg{2}.`2 /\ ImplR p{1} P  ==> valR res{1} = asint res{2} ]. *)

(* lemma exp_mulm2 :  *)
(*   equiv [ M.mulm ~ Spec.mul: arg{1}.`2 = arg{2}.`1 /\ arg{1}.`3 = arg{2}.`2 /\ ImplR p{1} P /\ valR a{1} < P /\ valR b{1} < P  ==> ={res} ]. *)
(* transitivity Spec.mulm *)
(*      (valR arg{1}.`2 = asint arg{2}.`1 /\ valR arg{1}.`3 = asint arg{2}.`2 /\ ImplR p{1} P   ==> valR res{1} = asint res{2}) *)
(*      (valR arg{2}.`1 = asint arg{1}.`1 /\ valR arg{2}.`2 = asint arg{1}.`2   ==> valR res{2} = asint res{1}). *)
(* progress.  *)
(* exists (inzp (valR a{1}), inzp (valR b{1}) ). progress. *)
(* smt. smt. smt. smt. *)
(* progress. smt. *)
(* conseq exp_mulm.  *)
(* proc. wp. skip. progress. *)
(* have  ->: valR (a{2} *** b{2}) = valR a{2} * valR b{2} %% P. smt. *)
(* have ->: asint (a{1} * b{1}) = asint (a{1})  * asint  b{1} %% P. smt.  *)
(* smt(). *)
(* qed. *)


(* import Zp. *)

(* lemma kk :  forall (n : int), 0 <= n => forall (a : zp) (b : R), valR b < P => *)
(*   ImplFp b a => *)
(*   ImplFp (b ^ n) (inzp (asint a ^ n)). *)
(* apply intind. progress.  *)
(* rewrite exp_prop1. *)
(* have -> : (asint a ^ 0) = 1. smt. *)
(* rewrite /asint. *)
(* have -> : (Sub.val (inzp 1))%Sub = 1. smt. *)
(* smt(valR_one). *)
(* progress. *)
(* have ->: (b ^ (i + 1)) = b *** (b ^ i). *)
(* rewrite exp_prop3. auto. auto.  auto. *)
(* rewrite exp_prop2. *)
(* rewrite exp_prop7. auto. *)
(* have ->: inzp (asint a ^ (i + 1)) =  inzp (asint a * (asint a ^ i)). *)
(* smt. *)
(* have ->:  inzp (asint a * (asint a ^ i)) = (inzp (asint a)) * (inzp (asint a ^ i)). *)
(* smt. *)
(* rewrite - H2. *)
(* have ->: asint (inzp (valR b) * inzp (valR b ^ i)) *)
(*   = (asint (inzp (valR b)) * (asint  (inzp (valR b ^ i)))) %% P. *)
(* smt. *)
(* have ih :  ImplFp (b ^ i)  (inzp (valR b ^ i)). *)
(* rewrite H2. apply H0. auto. auto. *)
(* rewrite - ih. *)
(* have ->: asint (inzp (valR b)) = valR b. smt. *)
(* have ->: valR (b *** (b ^ i)) =  (valR b) * (valR (b ^ i)) %%P. *)
(* rewrite  to_uintP /=. done. *)
(* auto. *)
(* qed. *)


(* lemma exp_real_speacc : *)
(*  equiv[ Spec.expm ~ M8.expm_spec  :  *)
(*     ImplFp arg{2}.`1 arg{1}.`1 /\ valR arg{2}.`2 = arg{1}.`2 /\ valR x{2} < P ==> ImplFp res{2} res{1}]. *)
(* proc.  *)
(* wp.  skip.  progress. *)
(* apply kk. *)
(* smt. auto. *)
(* auto. *)
(* qed. *)



(* lemma exp_pre_fin : *)
(*  equiv[ Spec.expm ~ M7(M).expm  :  *)
(*        valR arg{2}.`1  = P  *)
(*    /\  ImplFp  arg{2}.`2 arg{1}.`1 *)
(*    /\  arg{1}.`2 =  valR arg{2}.`3 *)
(*      ==> ImplFp res{2} res{1} ]. *)
(* transitivity M8.expm_spec *)
(*   (ImplFp arg{2}.`1 arg{1}.`1 /\ valR arg{2}.`2 = arg{1}.`2 /\ valR x{2} < P ==> ImplFp res{2} res{1}) *)
(*   (valR arg{2}.`1 = P  *)
(*    /\  arg{1}.`1 = arg{2}.`2 *)
(*    /\  arg{1}.`2 =  arg{2}.`3 *)
(*    /\ valR x{1} < P *)
(*      ==> ={res}). *)
(* progress. exists (x{2},n{2}). progress. smt(). smt.  smt. auto. *)
(* conseq exp_real_speacc.    *)
(* transitivity M1.expm_spec   *)
(*   (arg{1}.`1 = arg{2}.`1 /\ valR arg{1}.`2 = bs2int arg{2}.`2 /\ valR x{2} < P ==> ={res}) *)
(*   (valR arg{2}.`1 = P  *)
(*    /\  arg{1}.`1 = arg{2}.`2 *)
(*    /\ bs2int arg{1}.`2 = valR arg{2}.`3 *)
(*    /\ size arg{1}.`2 = Rsize *)
(*    /\ valR x{1} < P *)
(*      ==> ={res}). *)
(* progress.  *)
(* exists (x{1},  Rbits n{2}). *)
(* progress. *)
(* smt(). *)
(* smt(iii). *)
(* smt(). *)
(* conseq exp_real_speac2.  *)
(* progress. conseq exp_real_speac. *)
(* qed. *)

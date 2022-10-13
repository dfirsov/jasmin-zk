

require import AllCore IntDiv CoreMap List.

require import JModel.
require import BitEncoding.
import BS2Int.

op P : int.
axiom P_small1 : 0 <= P.
axiom P_small2 : P < W64.modulus.
axiom P_prime : prime P.

require import Fp_small.

require Abstract_exp_proof_8.
clone import Abstract_exp_proof_8 as ExpW64 with type R  <- W64.t,
                                                 op Rsize <- 64,
                                                 op Rbits <- W64.w2bits,
                                                 op bitsR <- W64.bits2w,
                                                 op P <- P
proof*.
realize Rsize_max. smt(). qed.
realize Rsize_pos. smt(). qed.
realize valr_pos. smt (@W64). qed.
realize iii.  smt (@W64). qed.
realize valr_ofint.  progress.
progress. rewrite /valR. rewrite /of_int. 
have ->: (w2bits ((bits2w (int2bs 64 x)))%W64) 
 = (int2bs 64 x). smt. 
rewrite int2bsK. auto. 
progress. 
have : P < W64.modulus. apply P_small2.
simplify. smt(). auto.
qed.
realize P_prime. apply P_prime. qed.
realize ofint_valr. progress. smt. qed.
realize rbits_bitsr. smt. qed.
realize bitsr_rbits. smt. qed.

(* not ours *)
realize Zp.Sub.insubN. admitted.
realize Zp.Sub.insubT.  admitted.
realize Zp.Sub.valP. admitted.
realize Zp.Sub.valK. admitted.
realize Zp.Sub.insubW. admitted.

import Zp.
(* require import Fp_small_proof. *)
op as_word (x : bool) : W64.t  = x ? W64.one : W64.zero.
op ith_bitword64 (n : W64.t) (x : int)  : W64.t = as_word (n.[x]).
op (^) (x : zp)(n : W64.t) : zp = inzp (asint x ^ W64.to_uint n).
print t.

module ASpecFp = {

  proc ith_bit (k:W64.t, ctr:int) : W64.t = {
    return ith_bitword64 k ctr;
  }

  proc swapw (x1:W64.t, x2:W64.t, toswap:bool) : W64.t * W64.t = {
    return toswap ? (x2,x1) : (x1,x2);
  }
  
  proc mulm(a b: zp): zp = {
    var r;
    r <- a * b;
    return r;
  }
}.




(* minu_one  twos_compl to_uint_and_mod*)
lemma qqq x : 0 < x < 64 => W64.one.[x] = false.
progress. timeout 20. smt.
qed.

lemma exp_ithbit :
 equiv[ M.ith_bit ~ ASpecFp.ith_bit    : arg{2}.`1 = arg{1}.`1 /\  arg{2}.`2 = W64.to_uint arg{1}.`2 
    /\ 0 <= ctr{2} < 64 ==> ={res} /\ (res{2} = W64.one \/ res{2} = W64.zero) ].
    symmetry.
proc. 
wp. skip. 
progress.
rewrite /ith_bitword64.
rewrite /as_word.
rewrite /truncateu8.
have -> : (to_uint (ctr{2} `&` (of_int 63)%W64))
  = (to_uint ctr{2} %% 2 ^ 6).
rewrite - to_uint_and_mod. auto.
smt. simplify.
have -> : (of_int (to_uint ctr{2} %% 64))%W8 = (of_int (to_uint ctr{2}))%W8.
smt.
rewrite /(`>>`).
rewrite /(`>>>`).
rewrite /W64.(`&`).
rewrite /map2.
case (k{2}.[to_uint ctr{2}]).
progress.
apply W64.ext_eq.
progress.
rewrite initiE. auto.
simplify.
rewrite initiE. auto.
simplify.
case (x = 0).
progress. smt. 
progress.
have -> : W64.one.[x] = false. 
smt (qqq).
auto.
progress.
apply W64.ext_eq.
progress.
rewrite initiE. auto.
simplify.
rewrite initiE. auto.
simplify.
case (x = 0).
progress. smt. 
progress. 
smt (qqq).
smt().
qed.    

abbrev ImplWord2 (x : W64.t) (y : int) = W64.to_uint x = y.
abbrev ImplFp2 (a : W64.t) (b : zp) = ImplWord2 a (asint b).

import W64.

equiv mulm_spec:
 M.mulm ~ ASpecFp.mulm:
  ImplWord2 p{1} P /\ ImplFp2 a{1} a{2} /\ ImplFp2 b{1} b{2} ==> ImplFp2 res{1} res{2}.
proof.
proc; simplify; wp; skip => &1 &2 /> Hp Ha Hb /=.
rewrite /DIV_64 /MUL_64 /wdwordu /flags_w2 /flags_w /rflags_undefined /rflags_of_mul Hp /= of_uintK /mulu /=.
have ->: (to_uint (mulhi a{1} b{1}) * 18446744073709551616 + to_uint (a{1} * b{1})) = to_uint a{1} * to_uint b{1}.
 by rewrite -mulhiP /mulu /#.
rewrite modz_small.
 by move: to_uint_cmp modz_cmp; smt.
by rewrite mulE Ha Hb.
qed.



lemma pre_fin_real : 
 equiv[ Spec.expm ~ M7(M).expm :
            valR m{2} = P /\
            ImplFp x{2} a{1} /\ b{1} = valR n{2}  ==>
            ImplFp res{2} res{1}].
apply (exp_pre_fin M).
symmetry.
transitivity ASpecFp.swapw 
  (={arg} ==> ={res})
  (arg{2}.`1 = arg{1}.`1 /\ arg{2}.`2 = arg{1}.`2 /\   arg{2}.`3 = as_word arg{1}.`3
    ==> ={res}).
progress. smt(). smt().
proc. skip. progress.
symmetry.
proc.  wp. skip.
progress.
rewrite /set0_64. simplify.
case (toswap{2}). progress.
rewrite /as_word. simplify.
smt (@W64).
rewrite /as_word. simplify.
smt (@W64).
progress.
rewrite /as_word. simplify.
smt (@W64).  
rewrite /as_word. simplify.
smt (@W64).  
symmetry.
transitivity ASpecFp.ith_bit 
  (={arg} ==> ={res})
  (arg{1}.`1 = arg{2}.`1 /\  arg{1}.`2 = W64.to_uint arg{2}.`2 
    /\ 0 <= ctr{1} < 64 ==> ={res} /\ (res{2} = W64.one \/ res{2} = W64.zero)).
progress. smt(). smt().
proc. skip. progress. rewrite /ith_bitR. rewrite /ith_bitword64.
rewrite /ith_bit. rewrite /as_w64. 
rewrite /as_word.
have -> : nth false (w2bits k{2}) ctr{2}  = k{2}.[ctr{2}].
smt.
auto.
symmetry.
conseq exp_ithbit.
progress.
symmetry.
transitivity ASpecFp.mulm
  (={arg} ==> ={res})    
  (ImplWord2 p{2}  P /\ ImplFp2 a{2} a{1} /\ ImplFp2 b{2} b{1} ==> ImplFp2 res{2} res{1}).
progress. smt(). smt().
proc. wp. skip. progress.
symmetry. conseq mulm_spec. 
progress.
qed.



lemma fin_real : 
 equiv[ Spec.expm ~ M.expm :
            valR m{2} = P /\
            ImplFp x{2} a{1} /\ b{1} = valR n{2}  ==>
            ImplFp res{2} res{1}].
transitivity M7(M).expm
  (valR m{2} = P /\
            ImplFp x{2} a{1} /\ b{1} = valR n{2}  ==>
            ImplFp res{2} res{1})
 (={arg} ==> ={res}).
progress. smt(). smt().
conseq pre_fin_real.
proc. sim.
seq  7  9 : (={x1,x2,x3,x4,d,ctr,n,m}). sim. wp.
call (_:true). wp.  skip. progress. wp.  sp. call (_:true). wp.  skip. progress. skip.
progress. rewrite /oneR. smt(@W64). smt(@W64). 
while (={x1,x2,x3,x4,d,ctr,n,m}). wp.
call (_:true). wp. skip. progress.
call (_:true). wp. skip. progress. wp.
call (_:true). wp. skip. progress.
call (_:true). wp. skip. progress.
call (_:true). wp. skip. progress.
wp.
call (_:true). wp. skip. progress.
call (_:true). wp. skip. progress.
wp. skip. progress. smt(@W64).
skip. progress.
qed.


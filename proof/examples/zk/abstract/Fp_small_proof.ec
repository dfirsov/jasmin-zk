require import AllCore IntDiv.
require import JModel.

require import Fp_small.

require import ZModP.

import W64.
  
op P: int.
axiom p_prime: prime P.
axiom p_small1 : P < W64.modulus.
axiom p_small2 : 1 < P.



clone import ZModP.ZModField as Zp with
        op p <= P
        rename "zmod" as "zp"
        proof prime_p by exact p_prime.

import Zp.


op ( *** ) (a b : t) : t = W64.of_int ((to_uint a * to_uint b)  %%  P).

op (^) (x : zp)(n : t) : zp = inzp (asint x ^ W64.to_uint n).

op as_word (x : bool) : W64.t  = x ? W64.one : W64.zero.
op ith_bitword64 (n : W64.t) (x : int)  : W64.t = as_word (n.[x]).

module ASpecFp = {

  proc ith_bit (k:W64.t, ctr:int) : W64.t = {
    return ith_bitword64 k ctr;
  }


  proc swapw (x1:W64.t, x2:W64.t, toswap:bool) : W64.t * W64.t = {
    return toswap ? (x2,x1) : (x1,x2);
  }

  
  proc addm(a b: zp): zp = {
    var r;
    r <- a + b;
    return r;
  }
  proc subm(a b: zp): zp = {
    var r;
    r <- a - b;
    return r;
  }
  proc mulm(a b: zp): zp = {
    var r;
    r <- a * b;
    return r;
  }

  proc mulmw64(a b: t): t = {
    var r;
     r <- a *** b;
    return r;
  }

  proc expm(a : zp,  b: t): zp = {
    var r;
    r <- a ^ b;
    return r;
  }

}.


abbrev ImplWord (x : t) (y : int) = W64.to_uint x = y.
abbrev ImplFp (a : t) (b : zp) = ImplWord a (asint b).




abbrev M = W64.modulus.


equiv mulm_specw64:
 M.mulm ~ ASpecFp.mulmw64:
  arg{1}.`2 = arg{2}.`1 /\ arg{1}.`3 = arg{2}.`2 /\   ImplWord p{1} P  ==> ={res}.
proof.
proc; simplify; wp; skip => &1 &2 />    /=.
rewrite /DIV_64 /MUL_64 /wdwordu /flags_w2 /flags_w /rflags_undefined /rflags_of_mul /= /mulu /=.
have ->: (to_uint (mulhi a{2} b{2}) * 18446744073709551616 + to_uint (a{2} * b{2})) = to_uint a{2} * to_uint b{2}.
 by rewrite -mulhiP /mulu /#.
rewrite /(\mmod).
rewrite /ulift2.
rewrite /( *** ).
progress.
rewrite H.
auto.
qed.






equiv addm_spec:
 M.addm ~ ASpecFp.addm:
  ImplWord p{1} P /\ ImplFp a{1} a{2} /\ ImplFp b{1} b{2}
  ==> ImplFp res{1} res{2}.
proof.
proc; simplify; wp; skip => &1 &2 /> Hp Ha Hb /=.
case: (addc_carry a{1} b{1} false).
 rewrite /addc /carry_add b2i0 /= => Hcarry.
 have E: to_uint (a{1} + b{1}) = to_uint a{1} + to_uint b{1} - M.
  rewrite to_uintD. 
  have ->: (to_uint a{1} + to_uint b{1}) %% M
           = (to_uint a{1} + to_uint b{1} - M) %% M by smt.
  by rewrite modz_small; move: to_uint_cmp; smt.
 case: (subc_borrow (a{1}+b{1}) p{1} false);
 rewrite /subc /borrow_sub /= b2i0 /= => Hborrow.
  have ->: a{1} + b{1} - p{1} + p{1} - p{1} = a{1} + b{1} - p{1} by ring.
  rewrite to_uintD E -addrA -modzDmr. 
  have ->: ((-M) + W64.to_uint (-p{1}))%%M = W64.to_uint (-p{1}) by smt.
  rewrite to_uintN modzDmr modz_small. smt.
  rewrite addE Ha Hb Hp; smt.
 by have //: to_uint (a{1} + b{1}) < to_uint p{1}
  by rewrite E Hp; move: to_uint_cmp; smt.
rewrite /addc /carry_add b2i0 /= => Hcarry.
case: (subc_borrow (a{1}+b{1}) p{1} false);
rewrite /subc /borrow_sub /= b2i0 /=.
 rewrite to_uintD modz_small; first move: to_uint_cmp; smt(). 
 rewrite Hp => Hborrow. 
 rewrite addE -Ha -Hb modz_small; first move: to_uint_cmp; smt().
 have ->: a{1} + b{1} - p{1} + p{1} - W64.zero = a{1} + b{1} by ring.
 by rewrite to_uintD_small /#.
have ->: a{1} + b{1} - p{1} - W64.zero = a{1} + b{1} - p{1} by ring.
rewrite Hp => Hborrow. 
rewrite to_uintB 1:/# to_uintD_small 1:/# addE; smt.
qed.

equiv subm_spec:
 M.subm ~ ASpecFp.subm:
  ImplWord p{1} P /\ ImplFp a{1} a{2} /\ ImplFp b{1} b{2} ==> ImplFp res{1} res{2}.
proof.
proc; simplify; wp; skip => &1 &2 /> Hp Ha Hb /=.
have E: (- to_uint b{1}) %% P  = (P - to_uint b{1}) %% P.
 have ->//: (- to_uint b{1}) %% P = (P - to_uint b{1}) %% P.
 by rewrite -modzDml modzz /#.
case: (subc_borrow a{1} b{1} false);
rewrite /subc /borrow_sub /= b2i0 /= => Hborrow.
 rewrite addE -Ha oppE -Hb E -modzDmr modz_mod modzDmr.
 rewrite modz_small. smt.
 rewrite to_uintD to_uintD to_uintN Hp.
pose A:= to_uint a{1}.
pose B:= to_uint b{1}.
pose p:= to_uint p{1}.
rewrite modzDmr modzDml.
have ->: A - B + P = A + (P - B) by ring.
rewrite modz_small.
 move: to_uint_cmp; smt.
 done.
rewrite to_uintB 1:/# Ha Hb.
have HH: asint b{2} <= asint a{2} by  smt().
rewrite addE oppE.
move: E; rewrite Hb => ->; rewrite modzDmr.
have ->: asint a{2} + (P - asint b{2}) = asint a{2} - asint b{2} + P.
 by ring.
rewrite -modzDmr modzz /= modz_small.
smt.
done.
qed.

equiv mulm_spec:
 M.mulm ~ ASpecFp.mulm:
  ImplWord p{1} P /\ ImplFp a{1} a{2} /\ ImplFp b{1} b{2} ==> ImplFp res{1} res{2}.
proof.
proc; simplify; wp; skip => &1 &2 /> Hp Ha Hb /=.
rewrite /DIV_64 /MUL_64 /wdwordu /flags_w2 /flags_w /rflags_undefined /rflags_of_mul Hp /= of_uintK /mulu /=.
have ->: (to_uint (mulhi a{1} b{1}) * 18446744073709551616 + to_uint (a{1} * b{1})) = to_uint a{1} * to_uint b{1}.
 by rewrite -mulhiP /mulu /#.
rewrite modz_small.
 by move: to_uint_cmp modz_cmp; smt.
by rewrite mulE Ha Hb.
qed.






require import BitEncoding.
import BS2Int.

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
 = (int2bs 64 x). 
rewrite bits2wK. 
rewrite size_int2bs. auto. auto.
rewrite int2bsK. auto. 
progress. 
have : P < W64.modulus. apply p_small1. simplify. 
smt(). auto.
qed.
realize P_pos. apply p_small2. qed.
realize ofint_valr. progress. smt. qed.
realize rbits_bitsr. smt. qed.
realize bitsr_rbits. smt. qed.

  
 

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


import W64.



lemma exp_mulm2 :
  equiv [ M.mulm ~ Spec.mul: arg{1}.`2 = arg{2}.`1 /\ arg{1}.`3 = arg{2}.`2 /\ ImplR p{1} P /\ valR a{1} < P /\ valR b{1} < P ==> ={res}  /\ valR res{1} < P ].
symmetry.
transitivity ASpecFp.mulm
     (p{1} = P /\ ImplFp a{1} a{2} /\ ImplFp b{1} b{2} ==> ImplFp res{1} res{2})
     (ImplWord p{2} P /\ ImplFp a{2} a{1} /\ ImplFp b{2} b{1} ==> ImplFp res{2} res{1}).
progress.
exists (inzp (valR a{1}), inzp (valR b{1}) ). progress.
smt. smt.  smt. smt. smt. smt.
proc.  wp. skip.  progress. 
smt.
progress.
symmetry. apply mulm_spec.
qed.

require import List.
lemma pre_fin_real : 
 equiv[ M1.expm_spec ~ M7(M).expm :
            valR m{2} = P /\
            ={x} /\
            bs2int n{1} = valR n{2} /\ (size n{1}) = 64 /\ valR x{1} < P ==>
            ={res}].
apply (exp_real_speac M).
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
conseq exp_mulm2. progress. 
qed.

lemma fin_real_suff : 
 equiv[ M7(M).expm ~ M.expm : ={arg} ==> ={res} ].
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



lemma kk :  forall (n : int), 0 <= n => forall (a : zp) (b : W64.t), valR b < P =>
  ImplFp b a =>
  ImplFp (ExpW64.(^) b n) (inzp (asint a ^ n)).
apply intind. progress.
rewrite exp_prop1.
have -> : (asint a ^ 0) = 1. smt.
rewrite /asint.
have -> : (Sub.val (inzp 1))%Sub = 1. smt.
smt(valR_one).
progress.
have ->: (ExpW64.(^) b (i + 1)) = b *** (ExpW64.(^) b  i).
rewrite exp_prop3. auto. auto.  auto.
rewrite exp_prop2.
rewrite exp_prop7. smt.
have ->: inzp (asint a ^ (i + 1)) =  inzp (asint a * (asint a ^ i)).
smt.
have ->:  inzp (asint a * (asint a ^ i)) = (inzp (asint a)) * (inzp (asint a ^ i)).
smt.
rewrite - H2. smt.
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
qed.



lemma exp_real_speacc :
 equiv[ ASpecFp.expm ~ M1.expm_spec  :
    ImplFp arg{2}.`1 arg{1}.`1 /\ bs2int arg{2}.`2  = to_uint arg{1}.`2 /\ valR x{2} < P ==> ImplFp res{2} res{1}].
proc.
wp.  skip.  progress.
rewrite  (kk (bs2int n{2}) _ a{1}). smt. auto. auto. smt.
qed.



lemma fin_real : 
 equiv[ ASpecFp.expm ~ M.expm :
            valR m{2} = P /\
            ImplFp x{2} a{1} /\ n{2} = b{1}  ==>
    ImplFp res{2} res{1}].
transitivity M1.expm_spec
  (ImplFp arg{2}.`1 arg{1}.`1 /\ bs2int arg{2}.`2  = to_uint arg{1}.`2 /\ valR x{2} < P ==> ImplFp res{2} res{1})
  ( valR m{2} = P /\
            ={x} /\
            bs2int n{1} = valR n{2} /\ (size n{1}) = 64 /\ valR x{1} < P ==>
            ={res}).
progress. exists (x{2},w2bits b{1}).
progress. smt(@W64).
auto.
smt.
smt.
smt.
auto.
conseq exp_real_speacc. 
symmetry.
transitivity M7(M).expm
 (={arg} ==> ={res})
 (  valR m{1} = P /\
  x{2} = x{1} /\ bs2int n{2} = valR n{1} /\ size n{2} = 64 /\ valR x{2} < P ==> ={res}).
progress. smt(). smt().
symmetry.
conseq fin_real_suff.
auto. auto. 
symmetry.
conseq pre_fin_real.
smt().
qed.





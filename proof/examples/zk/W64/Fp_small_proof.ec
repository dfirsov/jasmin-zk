require import AllCore IntDiv.
require import JModel.

require import Fp_small.

require import ZModP.

import W64.
  
op P: int.
axiom p_prime: prime P.
axiom p_small: 0 <= P < W64.modulus.



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


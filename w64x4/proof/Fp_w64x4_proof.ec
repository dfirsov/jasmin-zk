require import AllCore IntDiv CoreMap List.

require import JModel.
require import JBigNum.

require import Fp_w64x4_extract.
require import Fp_w64x4_spec.



import Array8 Array4.



module MM = {
  proc cminusP (x:W64.t Array4.t) : W64.t Array4.t = {
    var aux: bool;
    var aux_0: W64.t;
    
    var t:W64.t Array4.t;
    var twop63:W64.t;
    var cf:bool;
    t <- witness;
    t <-  x;
    twop63 <- (W64.of_int 1);
    twop63 <- (twop63 `<<` (W8.of_int 63));
    (aux, aux_0) <- addc_64 t.[0]%Array4 (W64.of_int 19) false;
    cf <- aux;
    t.[0] <- aux_0%Array4;
    (aux, aux_0) <- addc_64 t.[1] (W64.of_int 0) cf;
    cf <- aux;
    t.[1] <- aux_0;
    (aux, aux_0) <- addc_64 t.[2] (W64.of_int 0) cf;
    cf <- aux;
    t.[2] <- aux_0;
    (aux, aux_0) <- addc_64 t.[3] twop63 cf;
    cf <- aux;
    t.[3] <- aux_0;
    x.[0] <- (cf ? t.[0] : x.[0]);
    x.[1] <- (cf ? t.[1] : x.[1]);
    x.[2] <- (cf ? t.[2] : x.[2]);
    x.[3] <- (cf ? t.[3] : x.[3]);
    return (x);
  }


  proc ith_bit (kk:W64.t Array4.t, ctr:W64.t) : W64.t = {
    
    var bit:W64.t;
    var c1:W64.t;
    var c2:W64.t;
    var r:W64.t;
    
    c1 <- (ctr `>>` (W8.of_int 6));
    c2 <- (ctr - (c1 * (W64.of_int 64)));
    r <- kk.[(W64.to_uint c1)];
    bit <@ M.ith_bit64 (r, c2);
    return (bit);
  }

}.


op hui ['a] : 'a t -> int -> 'a = Array4."_.[_]".

import Zp W64x4 R.

lemma r2x_h _x :
 hoare [ M.r2x : x=_x ==> res = ( hui _x 0, hui _x 1, hui _x 2, hui _x 3) ].
proof. by proc; simplify; wp; skip => />. qed.

lemma x2r_h _x0 _x1 _x2 _x3:
 hoare [ M.x2r : x0=_x0 /\ x1=_x1 /\ x2=_x2 /\ x3=_x3 ==> res = Array4.of_list W64.zero [_x0; _x1; _x2; _x3] ].
proof.
proc; simplify; wp; skip => />.
by rewrite -ext_eq_all /all_eq.
qed.

lemma x2r_ll: islossless M.x2r by proc; islossless.

lemma x2r_ph _x0 _x1 _x2 _x3:
 phoare [ M.x2r : x0=_x0 /\ x1=_x1 /\ x2=_x2 /\ x3=_x3 ==> res = Array4.of_list W64.zero [_x0; _x1; _x2; _x3] ] = 1%r.
proof. by conseq x2r_ll (x2r_h _x0 _x1 _x2 _x3). qed.


lemma r2x_ll: islossless M.r2x by proc; islossless.

lemma r2x_ph _x:
 phoare [ M.r2x : x=_x ==> res = ( hui _x 0, hui _x 1, hui _x 2, hui _x 3) ] = 1%r.
proof. by conseq r2x_ll (r2x_h _x). qed.

(* equiv eq_spec: *)
(*  M.bn_eq ~ ASpecFp.eqn: *)
(*   ImplZZ a{1} a{2} /\ ImplZZ b{1} b{2} *)
(*   ==> to_uint res{1} = b2i res{2}. *)
(* proof. *)
(* transitivity  *)
(*  R.Ops.eqR *)
(*  ( ={a,b} ==> to_uint res{1} = b2i res{2} ) *)
(*  ( ImplZZ a{1} a{2} /\ ImplZZ b{1} b{2} *)
(*    ==> ={res} ). *)
(* + by move=> /> &1 &2 H1 H2; exists (a{1},b{1}). *)
(* + by move=> /> *. *)
(* + proc; simplify. *)
(*   wp; while (={a,b,i,acc} /\ 0 <= i{2} <= nlimbs). *)
(*    by wp; skip => /> /#. *)
(*   wp; skip => />; progress. *)
(*   by case: ((AND_64 acc_R acc_R).`5); smt(). *)
(* + proc; simplify. *)
(*   transitivity {1} *)
(*    { zf <@ R.Ops.eqR(a,b); } *)
(*    ( ={a,b} ==> ={zf} ) *)
(*    ( ImplZZ a{1} a{2} /\ ImplZZ b{1} b{2} ==> zf{1} = r{2} ). *)
(*   + by move=> /> &2 *; exists a{2} b{2} => /#. *)
(*   + by auto. *)
(*   + by inline*; sim. *)
(*   + ecall {1} (R.eqR_ph a{1} b{1}). *)
(*     wp; skip => /> &m . *)
(*     case: (a{m}=b{m}) => E; first smt(). *)
(*     rewrite eq_sym neqF. *)
(*     apply (contra _ (a{m}=b{m})); last done. *)
(*     by apply R.bn_inj. *)
(* qed. *)

(* equiv eq0_spec: *)
(*  M.bn_test0 ~ ASpecFp.eqn0: *)
(*   ImplZZ a{1} a{2} *)
(*   ==> to_uint res{1} = b2i res{2}. *)
(* proof. *)
(* transitivity  *)
(*  R.Ops.test0R *)
(*  ( ={a} ==> to_uint res{1} = b2i res{2} ) *)
(*  ( ImplZZ a{1} a{2} ==> ={res} ). *)
(* + by move=> /> &1 *; exists a{1}. *)
(* + by move=> /> *. *)
(* + proc; simplify. *)
(*   wp; while (={a,i,acc} /\ 0 <= i{2} <= nlimbs). *)
(*    by wp; skip => /> /#. *)
(*   wp; skip => />; progress. *)
(*   by case: ((AND_64 acc_R acc_R).`5); smt(). *)
(* + proc; simplify. *)
(*   transitivity {1} *)
(*    { zf <@ R.Ops.test0R(a); } *)
(*    ( ={a} ==> ={zf} ) *)
(*    ( ImplZZ a{1} a{2} ==> zf{1} = r{2} ). *)
(*   + by move=> /> &2 *; exists a{2} => /#. *)
(*   + by auto. *)
(*   + by inline*; sim. *)
(*   + ecall {1} (R.test0R_ph a{1}). *)
(*     by wp; skip => /> &m . *)
(* qed. *)


equiv addc_spec:
 M.bn_addc ~ ASpecFp.addn:
  ImplZZ a{1} a{2} /\ ImplZZ b{1} b{2}
  ==> res{1}.`1=res{2}.`1 /\ ImplZZ res{1}.`2 res{2}.`2.
proof.
transitivity 
 R.Ops.addcR
 ( ={a,b} /\ !c{2} ==> ={res} )
 ( ImplZZ a{1} a{2} /\ ImplZZ b{1} b{2} /\ !c{1}
   ==> res{1}.`1 = res{2}.`1 /\ ImplZZ res{1}.`2 res{2}.`2 ).
+ by move=> /> &1 &2 H1 H2; exists (a{1},b{1},false).
+ by move=> /> *.
+ proc; simplify.
  unroll {2} 3; rcondt {2} 3; first by auto.
  exlim a{1}, b{1} => aa bb.
  while (={i,b} /\ 1 <= i{2} <= nlimbs /\
         (cf,aa){1}=(c,a){2} /\
         (forall k, 0 <= k < i{2} => hui a{1} k = hui r{2} k) /\
         (forall k, i{2} <= k < nlimbs => hui a{1} k = hui aa k)).
   wp; skip => /> &1 &2 Hi1 Hi2 H1 H2 Hi.
   split => *; first smt().
   split => *; first smt().
   split.
    move=> k Hk1 Hk2.
    pose X := (addc _ _ _)%W64.
    pose Y := (addc _ _ _)%W64.
    have ->: X=Y by smt().
    case: (k = i{2}) => ?.
     rewrite /hui.
     by rewrite !set_eqiE /#.
     rewrite /hui.
    by rewrite !set_neqiE /#.
   move=> k Hk1 Hk2. rewrite /hui.
   by rewrite set_neqiE /#.
  wp; skip => /> &2.
  move=> Hc; split => *.
   split => k *. 
    by rewrite (_:k=0) 1:/# /hui !set_eqiE /#.
   by rewrite /hui set_neqiE /#.
  by apply ext_eq; smt().
+ proc; simplify.
  transitivity {1}
   { (c,r) <@ R.Ops.addcR(a,b,c); }
   ( ={a,b,c} ==> ={c,r} )
   ( ImplZZ a{1} a{2} /\ ImplZZ b{1} b{2} /\ !c{1} ==> ={c} /\ ImplZZ r{1} r{2} ).
  + by move=> /> &2 H; exists a{2} b{2} false.
  + by auto.
  + by inline*; sim.
  + ecall {1} (R.addcR_ph a{1} b{1} c{1}); wp; skip => /> &m Hc [c r] /= -> ?.
    by rewrite bn_carryE 1:/# b2i0 /bn_modulus /=.
qed.

equiv cminusP_spec:
 M.cminusP ~ ASpecFp.cminusP:
 ImplZZ xx{1} a{2} ==> ImplZZ res{1} res{2}.
proof.
 transitivity MM.cminusP
   (={arg} ==> ={res})
   (ImplZZ x{1} a{2} ==> ImplZZ res{1} res{2}).
progress. smt(). auto.
proc. wp.  skip.  progress. 
transitivity CSpecFp.cminusP
 ( ImplZZ x{1} a{2} ==> ImplZZ res{1} res{2} )
 ( ={a} /\ a{2} < modulusR ==> ={res} ).
+ move=> /> &2; exists (valR x{2}) => />. 
  smt.
+ by auto.
+ proc.
  seq 16 1: (#pre /\ cf{1}=c{2} /\ ImplZZ t{1} x{2}).
   transitivity {1}
    { (cf, t) <@ R.Ops.addcR(x, (Array4.of_list W64.zero 
                     [W64.of_int 19; W64.zero; W64.zero; W64.of_int (2^63)]), false); }
    ( ={x} ==> ={x, cf, t} )
    ( ImplZZ x{1} a{2} ==> ImplZZ x{1} a{2} /\ cf{1} = c{2} /\ ImplZZ t{1} x{2} ).
   + by move=> /> &1; exists x{1}.
   + by auto.
   + inline*; unroll for {2} 6; wp; skip => />; progress.
      do 2! congr.
      rewrite to_uint_eq to_uint_shl modz_small 1:/# !of_uintK 1..2:/#.
      by rewrite !modz_small /#.
     rewrite -ext_eq_all /all_eq /=.
     do 2! congr.
     rewrite to_uint_eq to_uint_shl modz_small 1:/# !of_uintK 1..2:/#.
     by rewrite !modz_small /#.
   + ecall {1} (R.addcR_ph x{1} (Array4.of_list W64.zero 
                     [W64.of_int 19; W64.zero; W64.zero; W64.of_int (2^63)]) false).
     inline*; wp; skip => /> &1 [c r] /=.
     pose X:= Array4.of_list _ _.
     rewrite bn_carryE 1:/# -exprM /bigint_modulus b2i0 /=.
     have ->/=: valR X = 2^255+19.
      by rewrite bn2seq /bn_seq /X of_listK.
     by move=> -> ->; rewrite bn_modulusE -exprM /=.
  inline*; wp; skip => &1 &2 [H1 [-> H2]] />.
  case: (c{2}) => H.
   pose X:= valR _.
   have ->//: X = valR t{1}.
   by rewrite /X; congr; rewrite -ext_eq_all /all_eq /=.
  pose X:= valR _.
  have ->//: X = valR x{1}.
  by rewrite /X; congr; rewrite -ext_eq_all /all_eq /=.
+ symmetry; conseq cminusP_eq; smt().
qed.

equiv addm_spec:
 M.addm ~ ASpecFp.addm:
  ImplFp a{1} a{2} /\ ImplFp b{1} b{2}
  ==> ImplFp res{1} res{2}.
proof.
transitivity CSpecFp.addm
 (ImplFp a{1} a{2} /\ ImplFp b{1} b{2} ==> ImplZZ res{1} res{2})
 (={a,b} ==> res{1}= asint res{2}).
+ by move=> /> &1 &2 H1 H2 /=; exists (a{2},b{2}) => /=.
+ by auto.
+ proc; simplify.

  (* ecall {1} (x2r_ph f0{1} f1{1} f2{1} f3{1}); simplify. *)
  (* wp; ecall {1} (r2x_ph f{1}); simplify. *)
  call cminusP_spec.
  call addc_spec.
  (* ecall {1} (x2r_ph g00{1} g10{1} g20{1} g30{1}); simplify. *)
  (* ecall {1} (x2r_ph f00{1} f10{1} f20{1} f30{1}); simplify. *)
  wp. simplify. (* ecall {1} (r2x_ph b{1}); ecall {1} (r2x_ph a{1}); simplify. *)
  skip => /> &1 &2 H1 H2.
  have HH: forall (f: R),
            (Array4.of_list W64.zero [hui f 0; hui f 1; hui f 2; hui f 3])
            = f.
   by move=> f; rewrite -ext_eq_all /all_eq /=.
  (* rewrite (HH a{1}) (HH b{1}); move=> />; progress. *)
  (* rewrite (HH result_L0). smt(). *)
+ symmetry; conseq addm_eq; smt().
qed.


module AImpl = {
  proc maskOnCarry(m: int, r: W64.t, _cf: bool): W64.t = {
    (_cf, r) <- subc r r _cf;
    r <- r `&` W64.of_int m;
    return r;
  }
  proc reduce(a: R2): R = {
    var ah, al: W64.t Array4.t;
    var _of, _cf, tmp;
    (ah, al) <@ MulOps.unpackR2(a);
    (_of, _cf, a) <@ MulOps.mul1acc(0, W64.of_int 38, ah, a, false, false);
    (ah, al) <@ MulOps.unpackR2(a);
    tmp <- a.[nlimbs] * W64.of_int 38;
    (_cf, al) <@ Ops.add1R(al, tmp, false);
    tmp <@ M.maskOnCarry(38, tmp, _cf);
    al <- al.[0 <- al.[0] + tmp]%Array4;
    (* al.[0] <- al.[0] + tmp; *)
    return al;
  }
}.

lemma maskOnCarry_h m cf:
 hoare [ M.maskOnCarry :
         _cf=cf /\ mask=m ==> res = if cf then W64.of_int m else W64.zero ].
proof.
proc; simplify.
wp; skip => /> &hr.
have ->: (subc r{hr} r{hr} cf).`2 = if cf then W64.onew else W64.zero.
 rewrite /subc /=.
 have ->: r{hr} - (r{hr} + W64.of_int (b2i cf)) = -W64.of_int (b2i cf) by ring.
 case: cf => E.
  by rewrite b2i1 minus_one.
 by rewrite b2i0; ring.
case: cf => Ecf.
 by rewrite W64.and1w.
by rewrite W64.and0w.
qed.

lemma maskOnCarry_ll: islossless M.maskOnCarry.
proof. by islossless. qed.

lemma maskOnCarry_ph m cf:
 phoare [ M.maskOnCarry :
         _cf=cf /\ mask=m ==> res = if cf then W64.of_int m else W64.zero ] = 1%r.
proof. by conseq maskOnCarry_ll (maskOnCarry_h m cf). qed.

equiv unpack2_eq:
 M.bn2_unpack ~ MulOps.unpackR2 :
 ={a} ==> ={res}.
proof.
proc.
unroll for {1} 4.
unroll for {2} 6.
unroll for {2} 4.
by wp; skip => /> *.
qed.

equiv mul1first_eq:
 M.mul1 ~ MulOps.mul1:
 a{1}=ak{2} /\ ={b}
 ==>
 (res.`1,res.`2,res.`3,res.`4){1} = (W64.zero,res.`1,res.`2,res.`3){2}.
proof.
proc; simplify.
wp.
while ( #pre /\ ={r,i} /\ (a,of_0,cf,_zero){1}=(ak,_of,_cf,W64.zero){2} /\ 
        1 <= i{2} <= nlimbs /\ !_of{2}).
 wp; skip => />; smt(Array8.get_setE Array8.set_set_if).
wp; skip => />; smt (Array8.set_set_if).
qed.

equiv mul1acc_eq :
 M.mul1acc ~ MulOps.mul1acc:
 ={k,a,b} /\ (_zero,of_0,cf,r){1}=(W64.zero,_of,_cf,x){2} /\
  0 <= k{2} < nlimbs
 ==>
 (res.`1,res.`2,res.`3,res.`4){1} = (W64.zero,res.`1,res.`2,res.`3){2}.
proof.
proc. simplify.
wp. while ( #pre /\ ={i} /\ (aux,_zero){1}=(nlimbs-1,W64.zero){2} /\ 
            0 <= i{2} <= nlimbs-1).
 wp; skip => />; smt(get_setE set_set_if).
wp; skip; smt(get_setE set_set_if).
qed.

equiv add1_eq:
 M.bn_add1 ~ Ops.add1R:
 ={a, b} /\ ! c{2} ==> ={res}.
proof.
proc; simplify.
while ( ={i} /\ 1 <= i{2} <= nlimbs /\
        (cf){1}=(c){2} /\
        bnk i{2} a{1} = bnk i{2} r{2} /\
        forall j, i{2} <= j < nlimbs
                  => a{1}.[j] = a{2}.[j] )%Array4.
 wp; skip => /> &1 &2 Hi1 Hi2 IH H Hcond.
 split; first smt().
 split; first smt().
 split.
  rewrite !bnkS 1..2:/# /= !get_setE 1..2:/# /=.
  rewrite !bnk_setO 1..2:/#; congr; smt().
 move=> j Hj1 Hj2; rewrite get_setE 1:/#.
 by rewrite (_:!j = i{2}) 1:/# /= H /#.
wp; skip => /> &2 Hcf.
split.
 split; first by rewrite !bnk1.
 move=> j Hj1 Hj2; rewrite get_setE 1:/#.
 by rewrite (_:!j=0) 1:/#.
move => rL i rR ????.
rewrite (_:i=nlimbs) 1:/# => E ?.
by apply bn_inj.
qed.

equiv reduce_eq:
 M.redp25519 ~ AImpl.reduce:
 ={a} /\ !_cf{1} /\ !_of{1} ==> ={res}.
proof.
proc; simplify; wp.
call (_: true). sim.
call add1_eq.
wp; call unpack2_eq.
wp; call mul1acc_eq.
call unpack2_eq.
wp; skip => />; progress.
by rewrite H4 /#. 
qed.

lemma reduce_spec:
 equiv [ M.redp25519 ~ ASpecFp.reduce :
         ImplZZ2 a{1} a{2} /\ !_cf{1} /\ !_of{1}
         ==> ImplZZ res{1} res{2} ].
proof.
transitivity AImpl.reduce
 (={a} /\ !_cf{1} /\ !_of{1} ==> ={res})
 (ImplZZ2 a{1} a{2} ==> ImplZZ res{1} res{2}).
 + by move=> /> &1 *; exists a{1} => /#.
 + by auto.
 + by apply reduce_eq.
 +
proc; simplify.
wp; ecall {1} (maskOnCarry_ph 38 _cf{1}).
ecall {1} (add1R_ph al{1} tmp{1} false).
wp; ecall {1} (unpackR2_ph2 a{1}).
wp; ecall {1} (mul1acc_ph 0 (W64.of_int 38) ah{1} a{1}).
wp; ecall {1} (unpackR2_ph2 a{1}).
skip => /> &1 [ah0 al0] /= Ea0h _ [_of0 _cf0 r0] ?? /=. 
rewrite expr0 /= => E1.
have X1: R2.bnk 5 r0 = red256 (R2.bn a{1}).
 rewrite E1.
 by rewrite -R2.bn_mod 1:/# Ea0h /red256 /split256 /= bn_modulusE expr0 /= expr0 /#.
move=> [ah1 al1] /= _ Ea1l [_cf1 r1] /=.
have {Ea1l}Ea1l: ImplZZ al1 (R2.bnk 5 r0 %% Fp_w64x4_spec.M).
 have ->: Fp_w64x4_spec.M = modulusR.
  by rewrite bn_modulusE /= expr0.
 by rewrite -R2.bn_mod 1:/# bn_modulusE modz_dvd_pow 1:/# -bn_modulusE.
have Ea1h: to_uint r0.[nlimbs] = R2.bnk 5 r0 %/  Fp_w64x4_spec.M.
 rewrite (_:5=4+1) 1:/# R2.bnkS 1:/# /= expr0 /=.
 rewrite divzDl ?bn_modulusE /=.
  by rewrite dvdz_mull dvdzz.
 rewrite mulzK 1:/# divz_small /=; last done.
 move: (R2.bnk_cmp nlimbs r0).
 by rewrite /= expr0 /#. 
rewrite !b2i0 /= to_uintM_small.
 move: (red256_once (valR2 a{1}) _).
  by move: (R2.bnk_cmp 8 a{1}); rewrite /= expr0 /#.
 by rewrite -X1 of_uintK modz_small /#.
rewrite of_uintK modz_small 1:/# => H1 H2.
have XX: (b2i _cf1, valR r1) = split256 (red256 (red256 (valR2 a{1}))).
 rewrite -X1 /red256 /split256 /= H2 -Ea1l -Ea1h.
 split.
  case: (_cf1) => Ecf.
   have ->: valR al1 + 38 * to_uint r0.[nlimbs]
           = Fp_w64x4_spec.M + (valR al1 + 38 * to_uint r0.[nlimbs] - Fp_w64x4_spec.M) by ring.
   rewrite divzDl 1:dvdzz divzz /=. 
   rewrite divz_small; last done.
   apply bound_abs; split.
    by move: H1; rewrite Ecf eq_sym eqT bn_modulusE /= expr0 /#.
   move=> *.
    smt.
   rewrite divz_small; last done.
   move: H1; rewrite Ecf bn_modulusE /= expr0 /= eq_sym neqF => H1.
   split; smt.
 by rewrite bn_modulusE /= expr0 /= mulrC.
move: (red256_twiceP (valR2 a{1}) (b2i _cf1) (valR r1) _ XX).
 by move: (R2.bnk_cmp 8 a{1}); rewrite /= expr0 /#.
case: (_cf1) => Ecf.
 rewrite /reduce {1}/red256 -XX /= Ecf !b2i1 /=.
 move=> Hr1.
 have Xr: forall r, valR r < W64.modulus => r = Array4.of_list W64.zero [r.[0]; W64.zero; W64.zero; W64.zero]%Array4.
  move=> r Hr; apply bn_inj.
  by move: Hr; rewrite !bn2seq /bn_seq /to_list /mkseq -iotaredE /=; smt(W64.to_uint_cmp).
 rewrite (Xr _) 1:/# !bn2seq /bn_seq /to_list /mkseq -iotaredE /=.
 rewrite to_uintD_small.
  have <-: valR r1 = to_uint r1.[0]%Array4.
   by rewrite Xr 1:/# !bn2seq /bn_seq /to_list /mkseq -iotaredE.
  smt().
 by rewrite of_uintK.
rewrite !b2i0 /= /reduce.
have ->: r1.[0 <- r1.[0]]%Array4 = r1.
 by apply ext_eq; smt(get_setE).
by rewrite {1}/red256 -XX /= Ecf b2i0.
qed.

equiv muln_spec:
 M.bn_muln ~ ASpecFp.muln:
  ImplZZ a{1} a{2} /\ ImplZZ b{1} b{2}
  ==> ImplZZ2 res{1}.`4 res{2}
      /\ res{1}.`1 = W64.zero /\ !res{1}.`2 /\ !res{1}.`3.
proof.
transitivity 
 MulOps.mulR
 ( ={a,b} ==> res{1}.`2=res{2}.`1 /\ res{1}.`3=res{2}.`2 /\ res{1}.`4=res{2}.`3 /\  res{1}.`1 = W64.zero )
 ( ImplZZ a{1} a{2} /\ ImplZZ b{1} b{2} 
   ==> !res{1}.`1 /\ !res{1}.`2 /\ ImplZZ2 res{1}.`3 res{2}).
+ by move=> /> &1 &2 H1 H2; exists (a{1},b{1}).
+ by move=> /> /#.
+ proc; simplify.
  while ( #pre /\ (i,_zero,of_0,cf,r){1}=(k,W64.zero,_of,_cf,r){2} /\
          1 <= k{2} <= nlimbs ).
   by wp; call mul1acc_eq; wp; skip => /> /#.
  by wp; call mul1first_eq; wp; skip => /> /#.
+ proc.
  transitivity {1}
    { (_of,_cf,r) <@ MulOps.mulR(a,b); }
    ( ={a,b} ==> ={_cf,_of,r} )
    ( ImplZZ a{1} a{2} /\ ImplZZ b{1} b{2} ==> !_cf{1} /\ !_of{1} /\ ImplZZ2 r{1} r{2} ).
  + by move=> /> &1; exists a{1} b{1}; auto.
  + by move=> /> *.
  + by inline MulOps.mulR; sim.
  + by ecall {1} (mulR_ph a{1} b{1}); wp; skip.
qed.

equiv mulm_spec:
 M.mulm ~ ASpecFp.mulm:
  ImplFp a{1} a{2} /\ ImplFp b{1} b{2} ==> ImplFp res{1} res{2}.
proof.
transitivity CSpecFp.mulm
 (ImplFp a{1} a{2} /\ ImplFp b{1} b{2} ==> ImplZZ res{1} res{2})
 (={a,b} ==> res{1}= asint res{2}).
+ by move=> /> &1 &2 H1 H2 /=; exists (a{2},b{2}) => />.
+ by auto.
+ proc. inline M._mulm M.freeze CSpecFp.freeze.
  wp; ecall {1} (x2r_ph g0{1} g1{1} g2{1} g3{1}); simplify.
  wp; ecall {1} (r2x_ph g{1}); simplify.
  wp; call cminusP_spec; call cminusP_spec.
  wp; call reduce_spec.
  call muln_spec.
  ecall {1} (x2r_ph g00{1} g10{1} g20{1} g30{1}); simplify.
  wp; ecall {1} (r2x_ph b{1}); simplify.
  skip => /> &1 &2 H1 H2.
  have HH: forall (f: R.t),
            (Array4.of_list W64.zero [f.[0]; f.[1]; f.[2]; f.[3]])%Array4 = f.
   by move=> f; rewrite -ext_eq_all /all_eq /=.
  rewrite (HH b{1}); split; first smt().
  by move=> _ r Hr1 Hr2 Hr3 rr => /> /#.
+ symmetry; conseq mulm_eq; smt().
qed.



(* EXPONENTIATION  *)
(* op P: int. *)
(* axiom p_prime: prime P. *)
(* axiom p_small1 : P < W64.modulus. *)
(* axiom p_small2 : 1 < P. *)


require import BitEncoding.
import BS2Int.

require Abstract_exp_proof_8.




clone import Abstract_exp_proof_8 as ExpW64 with type R  <- R.t,
                                                 op Rsize <- 256,
                                                 op valR <= W64x4.valR,
                                                 op of_int <= bn_ofint,
                                                 op P <- P
proof*.
realize Rsize_max. smt(). qed.
realize Rsize_pos. smt(). qed.
realize valr_pos. smt (@W64x4). qed.
realize iii.  rewrite /Rbits. 
progress. rewrite  size_int2bs. auto. qed.
realize valr_ofint.  progress.
search bn_ofint.
rewrite bn_ofintK. smt.
qed.
realize P_pos. smt. qed.
realize ofint_valr. smt(@W64x4). qed.
realize rbits_bitsr. 
progress. rewrite /Rbits. rewrite /bitsR. 
  have ->: (valR (bn_ofint (bs2int x)))%W64x4 = bs2int x.
rewrite bn_ofintK. smt. smt. qed.
realize bitsr_rbits. 
rewrite /Rbits. rewrite /bitsR.
progress.
rewrite int2bsK. auto. simplify. progress. smt(bnk_cmp).
have : 0 <= valR  x < W64x4.M ^ nlimbs.
rewrite /valR. 
apply (bnk_cmp nlimbs).
progress. smt.
smt(@W64x4).
qed.






require import WArray32.
require import Array32.


lemma qqq x : 0 < x < 64 => W64.one.[x] = false.
progress. timeout 20. smt.
qed.



lemma exp_ithbit a b :
 phoare[ M.ith_bit64   : arg = (a,b) /\
     0 <= to_uint ctr < 64 ==> res = ith_bitword64 a (to_uint b) ] = 1%r.
proc. wp.  skip. progress.
rewrite /ith_bitword64.
rewrite /as_word.
rewrite /truncateu8.
have -> : (to_uint (ctr{hr} `&` (of_int 63)%W64))
  = (to_uint ctr{hr} %% 2 ^ 6).
rewrite - to_uint_and_mod. auto.
smt. simplify.
have -> : (of_int (to_uint ctr{hr} %% 64))%W8 = (of_int (to_uint ctr{hr}))%W8.
smt.
rewrite /(`>>`).
rewrite /(`>>>`).
rewrite /W64.(`&`).
rewrite /map2.
case (k{hr}.[to_uint ctr{hr}]).
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
qed.



require import StdBigop.
import Bigint.
import BIA.


lemma ith_bit_lemmaEq :
      equiv[ MM.ith_bit ~ M.ith_bit : ={arg} ==> ={res}].
proc.
seq 2 4 : (={c1, c2,kk}). wp.
skip. progress.
have -> : 63 = 2^6 - 1. smt().
rewrite and_mod. auto. simplify.
have x:  to_uint (ctr{2} `>>` (of_int 6)%W8) = to_uint ctr{2} %/ 64. smt.
rewrite to_uint_eq.
auto.
rewrite to_uintB. smt.
rewrite to_uintM_small.  smt.
rewrite  shr_div_le.
auto. simplify. smt.
sim.
qed.


lemma ith_bit_lemma' :
      equiv[ M.ith_bit ~ Spec.ith_bit : arg{1}.`1 = arg{2}.`1 /\  W64.to_uint arg{1}.`2 = arg{2}.`2 /\
 0 <= ctr{2} && ctr{2} < 256 ==>
              ={res} /\ (res{2} = W64.one \/ res{2} = W64.zero)].

transitivity MM.ith_bit
   (={arg} ==> ={res})
   (arg{1}.`1 = arg{2}.`1 /\  W64.to_uint arg{1}.`2 = arg{2}.`2 /\
 0 <= ctr{2} && ctr{2} < 256 ==>
              ={res} /\ (res{2} = W64.one \/ res{2} = W64.zero)).
progress. smt(). smt().
symmetry. conseq ith_bit_lemmaEq. auto. auto.
proc.
seq 3 0 : (to_uint c1{1} = (to_uint ctr{1} %/ 64) /\ to_uint c2{1} = (to_uint ctr{1} %% 64) /\ to_uint ctr{1} = ctr{2}
  /\ r{1} = kk{1}.[(to_uint ctr{1} %/ 64)]%Array4 /\ r{2} = kk{1} /\ 0 <= ctr{2} && ctr{2} < 256 ).
wp.  skip. progress. 
smt. 
rewrite modzE. 
have <-: to_uint (ctr{1} `>>` (of_int 6)%W8) = to_uint ctr{1} %/ 64. smt.
rewrite to_uintB.
smt.
smt.
smt.
exists* r{1}, c2{1}. elim*. progress.
call {1} (exp_ithbit r_L c2_L). skip.
progress. smt. smt. 
rewrite /ith_bitword64.  rewrite H0. 
rewrite /ith_bitR. rewrite /Rbits. rewrite /valR.
rewrite /ith_bit.
rewrite /as_word.
rewrite /as_w64.
have ->: (kk{1}.[to_uint ctr{1} %/ 64])%Array4.[to_uint ctr{1} %% 64] 
  = nth false (int2bs 256 ((valR kk{1}))%W64x4) (to_uint ctr{1}) .
rewrite - get_w2bits.
rewrite - get_to_list.
have -> : (W64.w2bits (nth witness ((to_list kk{1}))%Array4 (to_uint ctr{1} %/ 64))) 
 = ((nth witness (map W64.w2bits (to_list kk{1}))%Array4 (to_uint ctr{1} %/ 64))).
rewrite - (nth_map witness witness W64.w2bits). progress.   smt. smt.
auto.
have -> : (nth witness (map W64.w2bits ((to_list kk{1}))%Array4)
     (to_uint ctr{1} %/ 64))
 = (nth [] (map W64.w2bits ((to_list kk{1}))%Array4)
     (to_uint ctr{1} %/ 64)). 
rewrite (nth_change_dfl [] witness). progress.  smt. smt. auto.
rewrite - (BitChunking.nth_flatten false 64 (map W64.w2bits ((to_list kk{1}))%Array4) (to_uint ctr{1})).
rewrite  List.allP. progress. timeout 5. 
print hasP.
print has.
search mem map.
print mapP.
have : exists z, z \in ((to_list kk{1}))%Array4 /\ x = W64.w2bits z.
apply mapP. auto. elim. progress.
have ->: (flatten (map W64.w2bits ((to_list kk{1}))%Array4))  = (int2bs 256 ((valR kk{1}))%W64x4).
have -> : (valR kk{1})%W64x4 = bs2int (flatten (map W64.w2bits ((to_list kk{1}))%Array4)). 
rewrite /bnk. 
search big.
have ->: range 0 4 = [0;1;2;3].  rewrite range_ltn. auto.
rewrite range_ltn. auto. rewrite range_ltn. auto. 
simplify. rewrite range_ltn. auto. 
simplify. rewrite range_geq. auto. auto.
rewrite big_consT.
rewrite big_consT.
rewrite big_consT.
rewrite big_consT. 
rewrite big_nil.
rewrite /to_list.
search mkseq.
print mkseqSr.
have ->: 4 = 0 + 1 + 1 + 1 + 1 . smt().
rewrite   mkseqS. auto.
rewrite   mkseqS. auto.
rewrite   mkseqS. auto.
rewrite   mkseqS. auto.
search mkseq.
rewrite mkseq0. simplify.
search flatten.
rewrite flatten_cons.
rewrite flatten_cons.
rewrite flatten_cons.
rewrite flatten_cons. 
rewrite flatten_nil. 
search (++).
rewrite cats0.
search bs2int.
rewrite bs2int_cat.
rewrite bs2int_cat.
rewrite bs2int_cat. simplify.
smt.
have ->: 256 = size (flatten (map W64.w2bits ((to_list kk{1}))%Array4)). 
rewrite /to_list.
have ->: 4 = 0 + 1 + 1 + 1 + 1 . smt().
rewrite   mkseqS. auto.
rewrite   mkseqS. auto.
rewrite   mkseqS. auto.
rewrite   mkseqS. auto.
rewrite mkseq0. simplify.
rewrite flatten_cons.
rewrite flatten_cons.
rewrite flatten_cons.
rewrite flatten_cons. 
rewrite flatten_nil. 
rewrite size_cat.
rewrite size_cat.
rewrite size_cat.
rewrite size_cat.
simplify. auto.
rewrite  bs2intK. auto. auto.
auto. smt().
qed.



lemma ones64 : (2^ 64  - 1)  = 18446744073709551615. smt(). qed.

print Array4.
lemma swap_lemma :
      equiv[ M.swapr ~ Spec.swapr :
              a{2} = x{1} /\ b{2} = y{1} /\ swap_0{1} = as_w64 c{2} ==> ={res}].
proc.  simplify.
seq 2 0 : (i{1} = 0 /\ a{2} = x{1} /\ b{2} = y{1} /\ swap_0{1} = as_w64 c{2} /\ 
   ((as_bool swap_0{1} => mask{1} = (of_int 18446744073709551615)%W64 )
              /\ (as_bool swap_0{1} = false => mask{1} = (of_int 0)%W64))).
wp. skip. progress. smt(@W64). smt.
while {1} (0 <= i{1} /\ ((as_bool swap_0{1} => mask{1} = (of_int 18446744073709551615)%W64 )
              /\ (as_bool swap_0{1} = false => mask{1} = (of_int 0)%W64)) 
   /\ (forall j, 0 <= j < i{1} => (x{1}.[j])%Array4 = (if as_bool swap_0{1} then (b{2}.[j]) else (a{2}.[j]))%Array4 )  
   /\ (forall j, 0 <= j < i{1} => (y{1}.[j])%Array4 = (if as_bool swap_0{1} then (a{2}.[j]) else (b{2}.[j]))%Array4 )  
   /\ (forall j, i{1} <= j => (x{1}.[j])%Array4 =  (a{2}.[j]))%Array4
   /\ (forall j, i{1} <= j => (y{1}.[j])%Array4 =  (b{2}.[j]))%Array4



 ) (nlimbs - i{1} + 1).


progress. wp.  skip.  progress.   smt().


case (j <  i{hr}). progress.  timeout 15. smt.
progress.
have : j = i{hr}. smt.
progress.
have ->: (x{hr}.[i{hr} <-
    x{hr}.[i{hr}] `^` (x{hr}.[i{hr}] `^` y{hr}.[i{hr}] `&` mask{hr})].[i{hr}])%Array4
 = (x{hr}.[i{hr}] `^` (x{hr}.[i{hr}] `^` y{hr}.[i{hr}] `&` mask{hr}))%Array4. smt.
case (as_bool swap_0{hr}). progress.
rewrite H4. auto.  rewrite H0. auto. rewrite H5. auto. rewrite - ones64. 
have -> : ((a{m}.[i{hr}])%Array4 `^` (b{m}.[i{hr}])%Array4 `&`
 (of_int W64.max_uint)%W64) = a{m}.[i{hr}]%Array4 `^` ((b{m}.[i{hr}])%Array4 `&`
 (of_int W64.max_uint)%W64). smt. 
have ->: ((b{m}.[i{hr}])%Array4 `&` (of_int W64.max_uint)%W64) = ((b{m}.[i{hr}])%Array4). smt.
smt(@W64).
progress. rewrite H4. auto.  rewrite H1. smt(). auto. 

case (j <  i{hr}). progress.  timeout 15. smt.
progress.
have : j = i{hr}. smt.
progress.
have ->: (y{hr}.[i{hr} <-
   y{hr}.[i{hr}] `^` (x{hr}.[i{hr}] `^` y{hr}.[i{hr}] `&` mask{hr})].[i{hr}])%Array4
 = (y{hr}.[i{hr}] `^` (x{hr}.[i{hr}] `^` y{hr}.[i{hr}] `&` mask{hr}))%Array4. smt.
case (as_bool swap_0{hr}). progress.
rewrite H4. auto.  rewrite H0. auto. rewrite H5. auto. rewrite - ones64. 
have -> : ((a{m}.[i{hr}])%Array4 `^` (b{m}.[i{hr}])%Array4 `&`
 (of_int W64.max_uint)%W64) = a{m}.[i{hr}]%Array4 `^` ((b{m}.[i{hr}])%Array4 `&`
 (of_int W64.max_uint)%W64). smt. 
have ->: ((b{m}.[i{hr}])%Array4 `&` (of_int W64.max_uint)%W64) = ((b{m}.[i{hr}])%Array4). smt.
smt(@W64).
progress. rewrite H4. auto.  rewrite H1. smt(). smt(@W64).

smt. smt. smt.




skip. progress. smt().   smt().   smt(). 
case (c{2} = false). progress.  

apply Array4.ext_eq.  progress. rewrite H5. progress. smt(). rewrite /as_bool. rewrite /as_w64. simplify. smt(@W64).
apply Array4.ext_eq.  progress. rewrite H6. progress. smt(). rewrite /as_bool. rewrite /as_w64. simplify. smt(@W64).
progress. have ->: c{2} = true. smt(). simplify.
progress. 
apply Array4.ext_eq.  progress. rewrite H5. progress. smt(). rewrite /as_bool. rewrite /as_w64. simplify. smt(@W64).
apply Array4.ext_eq.  progress. rewrite H6. progress. smt(). rewrite /as_bool. rewrite /as_w64. simplify. smt(@W64).
qed.




lemma expm_mulm_lemma : 
        equiv[ M.mulm ~ Spec.mul :
              ={a} /\
              ={b} /\
              ImplR p{1} P /\ (valR a{1})%W64x4 < P /\ (valR b{1})%W64x4 < P ==>
              ={res} /\ (valR res{1})%W64x4 < P].
symmetry.
transitivity ASpecFp.mulm
     (ImplFp a{1} a{2} /\ ImplFp b{1} b{2} ==> ImplFp res{1} res{2})
     (ImplFp a{2} a{1} /\ ImplFp b{2} b{1} ==> ImplFp res{2} res{1}).
progress.
exists (inzp (valR a{1}), inzp (valR b{1}) )%W64x4. progress.
rewrite inzpK. smt.
rewrite inzpK. smt.
rewrite inzpK. smt.
rewrite inzpK. smt.
progress. smt. smt.
proc.  wp. skip.  progress.
rewrite to_uintP.
       rewrite H H0.
     rewrite mulE.
auto.
symmetry. apply mulm_spec.
qed.




lemma expm_quasi : 
        equiv[ M1.expm_spec ~ M7(M).expm :
              ImplZZ m{2} P /\
              ={x} /\
              bs2int n{1} = (valR n{2})%W64x4 /\
              size n{1} = 256 /\ (valR x{1})%W64x4 < P ==> ={res}].
apply (exp_real_speac M).
conseq swap_lemma. smt(). smt().
conseq ith_bit_lemma'. progress. rewrite H.  auto. smt().
conseq expm_mulm_lemma. smt(). smt(). auto.
qed.




lemma kk :  forall (n : int), 0 <= n => forall (a : zp) (b : R.t), valR%W64x4 b < P =>
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
rewrite - H2. 
have ->: asint (inzp (valR%W64x4 b) * inzp (valR%W64x4 b ^ i))
  = (asint (inzp (valR%W64x4 b)) * (asint  (inzp (valR%W64x4 b ^ i)))) %% P.
smt.
have ih :  ImplFp (b ^ i)%ExpW64  (inzp (valR%W64x4 b ^ i)).
smt.
 (* apply H0. auto. auto. *)
rewrite - ih.
have ->: asint (inzp (valR%W64x4 b)) = valR%W64x4 b. smt.
rewrite  to_uintP /=. done.
qed.


lemma exp_real_speacc :
 equiv[ ASpecFp.expm ~ M1.expm_spec  :
    ImplFp arg{2}.`1 arg{1}.`1 /\ bs2int arg{2}.`2  = valR%W64x4 arg{1}.`2 /\ valR%W64x4 x{2} < P ==> ImplFp res{2} res{1}].
proc.
wp.  skip.  progress.
rewrite  (kk (bs2int n{2}) _ a{1}). smt. auto. auto. smt.
qed.




lemma fin_real_suff : 
 equiv[ M7(M).expm ~ M.expm : ={arg} ==> ={res} ].
proc. sim.
seq  7  19 : (={x1,x2,x3,x4,d,ctr,n,m}). sim. wp. 
call (_:true). sim. wp.  call (_:true). sim. wp.  skip. progress. rewrite /oneR. 
have x : valR%W64x4 (witness.[0 <- W64.one].[1 <- W64.zero].[2 <- W64.zero].[3 <- W64.zero])%Array4 = 1.
progress. rewrite /bnk.
have ->: range 0 4 = [0;1;2;3].  rewrite range_ltn. auto.
rewrite range_ltn. auto. rewrite range_ltn. auto. 
simplify. rewrite range_ltn. auto. 
simplify. rewrite range_geq. auto. auto.
rewrite big_consT.
rewrite big_consT.
rewrite big_consT.
rewrite big_consT. 
rewrite big_nil.
simplify. smt.
smt.
have x : valR%W64x4 (witness.[0 <- W64.one].[1 <- W64.zero].[2 <- W64.zero].[3 <- W64.zero])%Array4 = 1.
progress. rewrite /bnk.
have ->: range 0 4 = [0;1;2;3].  rewrite range_ltn. auto.
rewrite range_ltn. auto. rewrite range_ltn. auto. 
simplify. rewrite range_ltn. auto. 
simplify. rewrite range_geq. auto. auto.
rewrite big_consT.
rewrite big_consT.
rewrite big_consT.
rewrite big_consT. 
rewrite big_nil.
simplify. smt.
smt.
while (={x1,x2,x3,x4,d,ctr,n,m}). wp.
call (_:true). sim. wp. 
call (_:true). sim. wp. 
call (_:true). sim. 
call (_:true). sim. 
call (_:true). sim. 
wp.
call (_:true). sim. 
call (_:true). sim. 
wp. skip. progress.
smt(@W64).
skip. progress.
qed.

lemma fin_real : 
 equiv[ ASpecFp.expm ~ M.expm :
            valR%W64x4 m{2} = P /\
            ImplFp x{2} a{1} /\ n{2} = b{1}  ==>
    ImplFp res{2} res{1}].
transitivity M1.expm_spec
  (ImplFp arg{2}.`1 arg{1}.`1 /\ bs2int arg{2}.`2  = valR%W64x4 arg{1}.`2 /\ valR%W64x4 x{2} < P ==> ImplFp res{2} res{1})
  ( valR%W64x4 m{2} = P /\
            ={x} /\
            bs2int n{1} = valR%W64x4 n{2} /\ (size n{1}) = 256 /\ valR%W64x4 x{1} < P ==>
            ={res}).
progress. exists (x{2},Rbits b{1}).
progress. smt.
smt.
smt.
rewrite /Rbits. smt.
smt.
auto.
conseq exp_real_speacc. 
symmetry.
transitivity M7(M).expm
 (={arg} ==> ={res})
 (  valR%W64x4 m{1} = P /\
  x{2} = x{1} /\ bs2int n{2} = valR%W64x4 n{1} /\ size n{2} = 256 /\ valR%W64x4 x{2} < P ==> ={res}).
progress. smt(). smt().
symmetry.
conseq fin_real_suff.
auto. auto. 
symmetry.
conseq expm_quasi.
progress. 
qed.

require import AllCore IntDiv CoreMap List.

require import JModel.
require import JBigNum.

require import Fp_w64x4_extract_mulm.
require import Fp_w64x4_spec.




import Array8 Array4.
require import Ith_Bit64.

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
    bit <@ IB.ith_bit64 (r, c2);
    return (bit);
  }

}.


import Zp W64x4 R.


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
         (forall k, 0 <= k < i{2} => a{1}.[k] = r{2}.[k])%Array4 /\
         (forall k, i{2} <= k < nlimbs => a{1}.[k] = aa.[k])%Array4).
   wp; skip => /> &1 &2 Hi1 Hi2 H1 H2 Hi.
   split => *; first smt().
   split => *; first smt().
   split.
    move=> k Hk1 Hk2.
    pose X := (addc _ _ _)%W64.
    pose Y := (addc _ _ _)%W64.
    have ->: X=Y by smt().
    case: (k = i{2}) => ?.
     by rewrite !set_eqiE /#.
    by rewrite !set_neqiE /#.
   move=> k Hk1 Hk2.
   by rewrite set_neqiE /#.
  wp; skip => /> &2.
  move=> Hc; split => *.
   split => k *. 
    by rewrite (_:k=0) 1:/# !set_eqiE /#.
   by rewrite set_neqiE /#.
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
  call cminusP_spec.
  call addc_spec.
  wp. simplify.
  skip => /> &1 &2 H1 H2.
  have HH: forall (f: R),
            (Array4.of_list W64.zero [f.[0]; f.[1]; f.[2]; f.[3]])%Array4
            = f.
   by move=> f; rewrite -ext_eq_all /all_eq /=.
+ symmetry; conseq addm_eq; smt().
qed.



equiv subc_spec:
 M.bn_subc ~ ASpecFp.subn:
  ImplZZ a{1} a{2} /\ ImplZZ b{1} b{2}
  ==> res{1}.`1=res{2}.`1 /\ ImplZZ res{1}.`2 res{2}.`2.
proof.
transitivity 
 R.Ops.subcR
 ( (a,b,false){1}=(a,b,c){2} ==> ={res} )
 ( ImplZZ a{1} a{2} /\ ImplZZ b{1} b{2} /\ !c{1}
   ==> res{1}.`1 = res{2}.`1 /\ ImplZZ res{1}.`2 res{2}.`2 ).
+ by move=> /> &1 &2 H1 H2; exists (a{1},b{1},false).
+ by move=> /> *.
+ proc; simplify.
  unroll {2} 3; rcondt {2} 3; first by auto.
  exlim a{1}, b{1} => aa bb.
  while (={i,b} /\ 1 <= i{2} <= nlimbs /\
         (cf, aa){1}=(c, a){2} /\
         (forall k, 0 <= k < i{2} => a{1}.[k] = r{2}.[k])%Array4 /\
         (forall k, i{2} <= k < nlimbs => a{1}.[k] = aa.[k])%Array4).
   wp; skip => /> &1 &2 Hi1 _ Hh1 Hh2 Hi2.
   split => *; first smt().
   split => *; first smt().
   split.
    move=> k Hk1 Hk2.
    pose X := (subc _ _ _)%W64.
    pose Y := (subc _ _ _)%W64.
    have ->: X=Y by smt().
    case: (k = i{2}) => ?.
     by rewrite !set_eqiE /#.
    by rewrite !set_neqiE /#.
   move=> k Hk1 Hk2.
   by rewrite set_neqiE /#.
  wp; skip => />.
  split => *.
   split => k *.
    by rewrite (_:k=0) 1:/# !set_eqiE /#.
   by rewrite set_neqiE /#.
  by apply ext_eq; smt().
+ proc; simplify.
  transitivity {1}
   { (c,r) <@ R.Ops.subcR(a,b,c); }
   ( ={a,b,c} ==> ={c,r} )
   ( ImplZZ a{1} a{2} /\ ImplZZ b{1} b{2} /\ !c{1} ==> ={c} /\ ImplZZ r{1} r{2} ).
  + by move=> /> &2 H; exists a{2} b{2} false.
  + by auto.
  + by inline*; sim.
  + ecall {1} (R.subcR_ph a{1} b{1} c{1}); wp; skip => /> &m Hc [c r] /= -> ?.
    by rewrite bn_borrowE 1:/# b2i0 /bn_modulus /=.
qed.



equiv cminusP2_eq:
 M.cminusP2 ~ CSpecFp.cminusP2: valR x{1} = a{2} /\ a{2}<modulusR ==> valR res{1} = res{2}.
proof.
proc.  inline ASpecFp.ctseln. wp.  
call subc_spec. wp. skip. progress. 
  apply (eq_trans _ (valR pR)); last exact pRE.
  by congr ;rewrite -ext_eq_all /all_eq.
case (result_L.`1 ). progress. 
have : result_R.`1 = true. rewrite - H1. rewrite H3. auto. progress. rewrite H4. simplify.
  by congr ;rewrite -ext_eq_all /all_eq.
progress.
have : result_R.`1 = false. rewrite - H1. rewrite H3. auto. progress. rewrite H4. simplify.
have -> : (result_L.`2.[0 <- result_L.`2.[0]].[1 <- result_L.`2.[1]].[2 <-
     result_L.`2.[2]].[3 <- result_L.`2.[3]])%Array4 = result_L.`2. smt.
auto.
qed.



equiv caddP_spec:
 M.caddP ~ ASpecFp.caddP:
 cf{1}=c{2} /\ ImplZZ x{1} a{2} ==> ImplZZ res{1} res{2}.
proof.
transitivity CSpecFp.caddP
 ( cf{1}=c{2} /\ ImplZZ x{1} a{2} ==> ImplZZ res{1} res{2} )
 ( ={c,a} ==> ={res} ).
+ by move=> /> &1 &2 ??; exists (c{2},a{2}) => /> /#.
+ by auto.
+ proc; simplify.
  call addc_spec.
  inline*; wp; skip => />; progress.
  case: (c{2}) => E /=. 
   apply (eq_trans _ (valR pR)); last exact pRE.
   by congr; rewrite -ext_eq_all /all_eq.
  apply (eq_trans _ (valR zeroR)); last exact zeroRE.
  by congr; rewrite -ext_eq_all /all_eq.
+ symmetry; conseq caddP_eq; smt().
qed.


equiv subm_spec:
 M.subm ~ ASpecFp.subm:
  ImplFp f{1} a{2} /\ ImplFp g{1} b{2} ==> ImplFp res{1} res{2}.
proof.
transitivity CSpecFp.subm
 (ImplFp f{1} a{2} /\ ImplFp g{1} b{2} ==> ImplZZ res{1} res{2})
 (={a,b} ==> res{1}= asint res{2}).
+ by move=> /> &1 &2 H1 H2 /=; exists (a{2},b{2}) => />.
+ by auto.
+ proc. 
  inline M.subm.
  simplify.
  wp. simplify.
  call caddP_spec.
  call subc_spec.
   simplify.
   simplify.
  simplify.
  skip => /> &1 &2 H1 H2.
  have HH: forall (f: R),
            (Array4.of_list W64.zero [f.[0]; f.[1]; f.[2]; f.[3]])%Array4 = f.
   by move=> f; rewrite -ext_eq_all /all_eq /=.
+ symmetry; conseq subm_eq; smt().
qed.


(* LADDER MULTIPLICATION  *)

require import BitEncoding.
import BS2Int.

require Abstract_exp_proof_8.

require import StdBigop.
import Bigint.
import BIA.


clone import Abstract_exp_proof_8 as ExpW64 with type R  <- R.t,
                                                 op P <- P,
                                                 op Rsize <- 256,
                                                 op valR <- W64x4.valR,
                                                 op of_int <- bn_ofint,
                                                 op idR <- bn_ofint  0,
                                                 op ( ** ) <- Int.(+),
                                                 op ( *** ) <=  fun a b => bn_ofint ((valR a + valR b) %% P)

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
realize exp_prop7. progress. smt. qed.
realize exp_prop6. progress.
have ->: (valR (bn_ofint ((valR a + valR b) %% P)) + valR c) %% P
  = ((valR a + valR ((bn_ofint ((valR b + valR c) %% P)))) %% P). timeout 10. smt.
auto.
qed.
realize exp_prop5. progress. smt. qed.
realize mult_valr. progress. smt. qed.
realize idR_leP. smt. qed.

lemma to_uintP: forall (x y : R), valR (x *** y) = (valR x + valR y) %% P.
progress. rewrite /( *** ). smt.
qed.

module AddM = {
  proc ith_bit = M.ith_bit
  proc swapr = M.swapr
  proc opr =  M.addm3
}.



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
call {1} (ithbit64 r_L c2_L). skip.
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
have : exists z, z \in ((to_list kk{1}))%Array4 /\ x = W64.w2bits z.
apply mapP. auto. elim. progress.
have ->: (flatten (map W64.w2bits ((to_list kk{1}))%Array4))  = (int2bs 256 ((valR kk{1}))%W64x4).
have -> : (valR kk{1})%W64x4 = bs2int (flatten (map W64.w2bits ((to_list kk{1}))%Array4)).
rewrite /bnk.
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
rewrite cats0.
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






lemma klo : 
  equiv[ AddM.opr ~ Spec.mul :
            ={a} /\ ={b} /\  p{1} = P /\ valR a{1} < P /\ valR b{1} < P ==>
            ={res} /\ valR res{1} < P].
symmetry.
transitivity ASpecFp.addm 
  (ImplFp arg{1}.`1  arg{2}.`1 /\ ImplFp arg{1}.`2  arg{2}.`2 ==> ImplFp res{1} res{2} )
  (ImplFp a{2} a{1} /\ ImplFp b{2} b{1} /\  p{1} = P /\ valR a{2} < P /\ valR b{2} < P ==>
            ImplFp res{2} res{1} /\ valR res{2} < P).
    progress.
  exists (inzp (valR a{1}), inzp (valR b{1}) )%W64x4. progress.
rewrite inzpK. smt.
rewrite inzpK. smt.
rewrite inzpK. smt.
rewrite inzpK. smt.
progress. smt. 
proc.  wp. skip.  progress.
rewrite to_uintP.
       rewrite H H0.
     rewrite addE.
auto.
symmetry. transitivity M.addm (arg{1}.`2 = arg{2}.`1 /\ arg{1}.`3 = arg{2}.`2 ==> ={res})   (ImplFp arg{1}.`1  arg{2}.`1 /\ ImplFp arg{1}.`2  arg{2}.`2 ==> ImplFp res{1} res{2} /\ valR res{1} < P ).  progress.  exists (a{1},b{1}). progress. progress. 
proc*.  sim.
inline AddM.opr. wp.  call (_:true). sim. wp.  skip. progress.
conseq addm_spec. progress. smt.
qed.


lemma ones64 : (2^64  - 1)  = 18446744073709551615. smt(). qed.

lemma swap_lemma :
      equiv[ AddM.swapr ~ Spec.swapr :
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



lemma mulm_real_spec : 
      equiv[ M1.iterop_spec ~ M7(AddM).iterop :
            ImplZZ m{2} P /\
            ={x} /\
            bs2int n{1} = valR n{2} /\ size n{1} = 256 /\ valR x{1} < P ==>
            ={res}].
apply (iterop_real_speac AddM _ _ _). conseq swap_lemma. smt(). smt().
conseq ith_bit_lemma'. smt().
conseq klo. smt(). auto. auto.
qed.



lemma right_end : 
 equiv[ M7(AddM).iterop ~ M.mulm_ladder : ={arg} ==> ={res} ].
proc. sim.
seq  7  19 : (={x1,x2,x3,x4,d,ctr,n,m}). sim. wp. 
call (_:true). sim. wp.  call (_:true). sim. wp.  skip. progress. rewrite /oneR. 
have x : valR%W64x4 (witness.[0 <- W64.zero].[1 <- W64.zero].[2 <- W64.zero].[3 <- W64.zero])%Array4 = 0.
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
simplify. auto.
smt.
have x : valR%W64x4 (witness.[0 <- W64.zero].[1 <- W64.zero].[2 <- W64.zero].[3 <- W64.zero])%Array4 = 0.
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
simplify. auto.
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




lemma kk :  forall (n : int), 0 <= n => forall (a : zp) (b : R.t), valR%W64x4 b < P =>
  ImplFp b a =>
  ImplFp (ExpW64.(^) b n) (inzp (asint a * n)).
apply intind. progress.
rewrite exp_prop1.
smt.
(* have -> : (Sub.val (inzp 1))%Sub = 1. smt. *)
(* smt(valR_one). *)
progress.

have ->: (ExpW64.(^) b (i + 1)) = b *** (ExpW64.(^) b  i).
rewrite exp_prop3. auto. auto.  auto.
rewrite exp_prop2.
rewrite exp_prop7. smt.
have ->:  (asint a * (i + 1)) =   (asint a + (asint a * i)).
smt().
have ->:  inzp (asint a + (asint a * i)) = (inzp (asint a)) + (inzp (asint a * i)).
smt.
rewrite - H2. 
print ImplFp.
have ->: asint (inzp (valR b) + inzp (valR b * i))
  = (asint (inzp (valR%W64x4 b)) + (asint  (inzp (valR%W64x4 b * i)))) %% P.
smt.
have ih :  ImplFp (b ^ i)%ExpW64  (inzp (valR%W64x4 b * i)).
smt.
 (* apply H0. auto. auto. *)
rewrite - ih.
have ->: asint (inzp (valR%W64x4 b)) = valR%W64x4 b. smt.
simplify. 
rewrite  to_uintP /=. done.
qed.


lemma left_end :
 equiv[ ASpecFp.mulm ~ M1.iterop_spec  :
    ImplFp arg{2}.`1 arg{1}.`1 /\  bs2int arg{2}.`2  = asint arg{1}.`2 /\ valR%W64x4 x{2} < P ==> ImplFp res{2} res{1}].
proc.
wp.  skip.  progress.
rewrite  (kk (bs2int n{2}) _ a{1}). smt. auto. auto. smt.
qed.






equiv mulm_spec:
 M.mulm_ladder ~ ASpecFp.mulm:
  ImplFp x{1} a{2} /\ ImplFp n{1} b{2} /\ ImplZZ m{1} P ==> ImplFp res{1} res{2}.
proof. symmetry.
transitivity M1.iterop_spec
  (ImplFp arg{2}.`1 arg{1}.`1 /\  bs2int arg{2}.`2  = asint arg{1}.`2 /\ valR%W64x4 x{2} < P ==> ImplFp res{2} res{1})
  ( valR%W64x4 m{2} = P /\
            ={x} /\
            bs2int n{1} = valR%W64x4 n{2} /\ (size n{1}) = 256 /\ valR%W64x4 x{1} < P ==>
            ={res}).
progress. exists (x{2},Rbits n{2}).
progress. rewrite -  H0. 
rewrite /Rbits. smt.
smt.
rewrite /Rbits. smt.
rewrite /Rbits. smt.
smt.
auto.
conseq left_end. 
symmetry.
transitivity M7(AddM).iterop
 (={arg} ==> ={res})
 (  valR%W64x4 m{1} = P /\
  x{2} = x{1} /\ bs2int n{2} = valR%W64x4 n{1} /\ size n{2} = 256 /\ valR%W64x4 x{2} < P ==> ={res}).
progress. smt(). smt().
symmetry.
conseq right_end.
auto. auto. 
symmetry.
conseq mulm_real_spec.
progress. 
qed.


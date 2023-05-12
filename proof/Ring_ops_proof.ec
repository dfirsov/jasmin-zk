require import AllCore IntDiv CoreMap List RealExp.

from Jasmin require import JModel JBigNum.
require import Ith_Bit64.
require import Ring_ops_spec.
require import W64_SchnorrExtract.
import Array128 Array64 Array32.

import Zp W64xN R.
import StdBigop Bigint BIA.
require import BarrettRedInt.


op R : W64.t Array64.t = R2.bn_ofint Ri.
lemma ones64 : (2^64  - 1)  = 18446744073709551615. smt(). qed.
op as_bool (x : W64.t) : bool  = (x = W64.one).
op as_w64 (x : bool) : W64.t  = x ? W64.one : W64.zero.

module M = M(Syscall).

lemma kok (a b c : real) : 0%r <= a => 0%r < b => 1%r < c =>
 a <= b / c => a < b.
smt(@Real).
qed.


axiom bn_set_bf_prop : 
  phoare[ M.bn_set_bf : true ==> W64x2N.valR res = Ri  ] = 1%r.
axiom bn_set_go_prop : 
  phoare[ M.bn_set_go : true ==> valR res = p  ] = 1%r.
axiom bn_set_eo_prop : 
  phoare[ M.bn_set_eo : true ==> valR res = p-1  ] = 1%r.
axiom bn_set_eb_prop : 
  phoare[ M.bn_set_eb : true ==> W64x2N.valR res = Rip  ] = 1%r.
axiom bn_set_gg_prop : 
  phoare[ M.bn_set_gg : true ==> valR res = Sub.val g  ] = 1%r.

op ri_uncompute (p : int) : int.
axiom ri_un p : ri_uncompute (valR p)%W64xN = ri (valR p)%W64xN (dnlimbs * nlimbs).

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
         (forall k, 0 <= k < i{2} => a{1}.[k] = r{2}.[k])%Array32 /\
         (forall k, i{2} <= k < nlimbs => a{1}.[k] = aa.[k])%Array32).
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


lemma addc_ph x y:
  phoare[ M.bn_addc :  arg = (x, y)  ==> (valR res.`2) = (valR x + valR y) %% W64xN.modulusR ] = 1%r.
bypr. progress.
 have <- : Pr[ASpecFp.addn(valR a{m}, valR b{m} ) @ &m : (valR a{m} + valR b{m}) %% W64xN.modulusR = res.`2] = 1%r. 
  byphoare (_: arg = (valR a{m}, valR b{m}) ==> _).
proc. wp. skip. progress. auto. auto.
byequiv. conseq addc_spec.  
progress.  smt(). auto. auto.
qed.

    

lemma bn_cmov_correct x y z :
  phoare[ M.bn_cmov :  arg = (x,y,z)  ==> res = if x then z else y ] = 1%r.
proc.
while (cond = x /\ b = z /\ i <= nlimbs 
  /\ (forall j, 0 <= j < i => a.[j]%Array32 = if cond then z.[j] else y.[j])%Array32
  /\ (forall j, i <= j < nlimbs => a.[j] = y.[j]) )%Array32 (nlimbs - i). progress.
wp.  skip.  progress. smt().   smt(@Array32). smt(@Array32). smt(). wp.  skip. progress. smt(@Array32). smt().
apply Array32.ext_eq. progress. smt(@Array32). 
qed.


lemma bn_eq_correct x1 x2 :
  phoare[ M.bn_eq :  arg = (x1,x2) ==> (res = W64.one) = (valR x1 = valR x2)  /\ (res = W64.zero \/ res = W64.one) ] = 1%r.
proc. sp. inline M.sn_cmov.  wp.
while (i <= nlimbs /\ ((result = W64.zero) <=> (forall j, 0 <= j < i => a.[j] = b.[j])%Array32)) (nlimbs - i). progress.
wp.  skip.  progress. smt(). smt(@W64xN).
smt(@W64xN).
smt().
skip. 
progress.
smt().
smt().
case (result0 = W64.zero). simplify.
move => c1.
rewrite (Array32.ext_eq a{hr} b{hr} ). 
have qq : i0 = nlimbs. smt().
rewrite - qq.
smt(). auto.
elim H1. move => H11 H12.
simplify.
have ->: (W64.zero = W64.one) = false. smt(@W64).
smt(@Array32 @W64xN).
smt().
qed.


lemma bn_copy_correct x :
  phoare[ M.bn_copy :  arg = x  ==> res = x ] = 1%r.
proc.
while (a = x /\ i <= nlimbs 
  /\ (forall j, 0 <= j < i => r.[j] = x.[j])%Array32
  ) (nlimbs - i). progress.
wp.  skip.  progress. smt(). smt(@Array32). smt(). wp.  skip. progress. smt(). smt().
apply Array32.ext_eq. progress. smt(). 
qed.



equiv subc_spec:
 M.bn_subc ~ ASpecFp.subn:
  W64xN.valR a{1} = a{2} /\ W64xN.valR b{1} = b{2} (* /\ W64xN.valR b{1}  <= W64xN.valR a{1} *)
  ==> res{1}.`1=res{2}.`1 /\ W64xN.valR res{1}.`2 = res{2}.`2.
proof.
transitivity 
 W64xN.R.Ops.subcR
 ( (a,b,false){1}=(a,b,c){2} ==> ={res} )
 (W64xN.valR  a{1} = a{2} /\ W64xN.valR b{1} = b{2} /\ !c{1} (* /\ W64xN.valR b{1}  <= W64xN.valR a{1} *)
   ==> res{1}.`1 = res{2}.`1 /\ W64xN.valR res{1}.`2 = res{2}.`2 ).
+ by move=> /> &1 &2 H1 H2 ; exists (a{1},b{1},false).
+ by move=> /> *.
+ proc; simplify.
  unroll {2} 3; rcondt {2} 3; first by auto.
  exlim a{1}, b{1} => aa bb.
  while (={i,b} /\ 1 <= i{2} <= dnlimbs /\ 
         (cf, aa){1}=(c, a){2} /\
         (forall k, 0 <= k < i{2} => a{1}.[k] = r{2}.[k])%Array32 /\
         (forall k, i{2} <= k < dnlimbs => a{1}.[k] = aa.[k])%Array32).
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
  by apply Array32.ext_eq; smt().
+ proc; simplify.
  transitivity {1}
   { (c,r) <@ W64xN.R.Ops.subcR(a,b,c); }
   ( ={a,b,c} ==> ={c,r} )
   ( W64xN.valR a{1} = a{2} /\ W64xN.valR b{1} = b{2} /\ !c{1}  (* /\ W64xN.valR b{1}  <= W64xN.valR a{1} *) ==> ={c} 
   /\ W64xN.valR r{1} = r{2} ).
  + by move=> /> &2 H  ; exists a{2} b{2} false.
  + by auto.
  + by inline*; sim.
  + ecall {1} (W64xN.R.subcR_ph a{1} b{1} c{1}); wp; skip => /> &m Hc [c r] /= -> .
progress. 
    by rewrite W64xN.R.bn_borrowE 1:/# b2i0 /bn_modulus /=.
qed.

equiv cminus_spec:
 M.cminusP ~ ASpecFp.cminus:
 W64xN.valR p{1} = p{2} /\ W64xN.valR x{1} = a{2} /\ 0 <= p{2}  ==> W64xN.valR res{1}  =res{2}.
proof.
transitivity CSpecFp.cminus
 ( W64xN.valR p{1} = p{2} /\ W64xN.valR x{1} = a{2} /\ 0 <= p{2}  ==> W64xN.valR res{1}  = res{2} )
 ( ={a,p} /\ a{2} < W64xN.modulusR /\ 0 <= p{2} ==> ={res} ).
  progress. exists (W64xN.valR x{1}, W64xN.valR  p{1}). progress. smt(@W64xN). smt(@W64xN).
auto.
proc.
(ecall {1} (bn_cmov_correct cf{1} z{1} x{1})).  simplify.
conseq (_:  ( (W64xN.valR (if cf{1} then x{1} else z{1}))%W64xN = r{2} )). progress.
inline ASpecFp.ctseln. wp.   simplify.
seq 2 0 : ((W64xN.valR p{1})%W64x2N = p{2} /\ (W64xN.valR x{1})%W64x2N = a{2} /\ z{1} = x{1} /\ 0 <= p{2}  ).
(ecall {1} (bn_copy_correct x{1})).  wp. skip. progress.
seq 1 1 : (cf{1} = c{2} /\ W64xN.valR z{1} = x{2}
  /\ (W64xN.valR p{1})%W64xN = p{2} /\ (W64xN.valR x{1})%W64xN = a{2}  /\ 0 <= p{2}).
call  subc_spec.  skip. progress.
skip. progress.   smt().
proc. inline*. wp.  skip.  progress.
case (a{2} < p{2} = true). move => q. rewrite q. simplify. auto.
move => q. 
have -> : a{2} < p{2} = false. smt(). simplify.
have : p{2} <= a{2}. smt().
move => qq.
have qqq : a{2} - p{2} < modulusR. smt(@Int).
smt(@Int).
qed.




equiv addm_spec_eq:
 M.addm ~ ASpecFp.addm:
    W64xN.valR a{1} = a{2} /\ ImplZZ b{1} b{2} /\  ImplZZ p{1} p{2}
 /\ 0 <= a{2} < p{2} /\ 0 <= b{2} < p{2} /\ 0 <= 2*p{2} < W64xN.modulusR
  ==> ImplZZ res{1} res{2}.
proof.
transitivity CSpecFp.addm
 (ImplZZ a{1} a{2} /\ ImplZZ b{1} b{2} /\ ImplZZ p{1} p{2} /\ 0 <= a{2} < p{2} /\ 0 <= b{2} < p{2} /\ 0 <= 2*p{2} < W64xN.modulusR ==> ImplZZ res{1} res{2} )
 (={a,b,p} /\ 0 <= a{2} < p{2} /\ 0 <= b{2} < p{2} /\ 0 <= 2*p{2} < W64xN.modulusR ==> res{1}=  res{2}).
  progress. smt(). smt().
+ proc; simplify.
  call cminus_spec.
  exists* a{1}. elim*. move => a_L.
  exists* b{1}. elim*. move => b_L.
  call {1} (addc_ph a_L b_L). inline*. wp. skip. progress. smt(@W64xN).  
+ symmetry; conseq addm_eq.  progress. smt(). smt(). smt(). smt(). 
qed.


lemma bn_addm_correct aa bb pp:
  phoare[ M.addm : a = aa /\ b = bb /\ p = pp /\ 0 <= valR a < valR p /\ 0 <= valR b < valR p /\ 0 <= 2* (valR p) < W64xN.modulusR  ==> (valR aa + valR bb)%% (valR pp) = valR res ] = 1%r.
proof. bypr. progress.
 have <- : Pr[ASpecFp.addm(valR a{m}, valR b{m}, valR p{m}) @ &m : (valR a{m} + valR b{m}) %% valR p{m} =  res] = 1%r. 
  byphoare (_: arg = (valR a{m}, valR b{m}, valR p{m}) ==> _).
proc. wp. skip. smt(). auto. auto.
byequiv. conseq addm_spec_eq.
smt(). smt(). auto. auto.
qed.


lemma bn_set0_correct :
  phoare[ M.bn_set0 : true  ==> W64xN.valR res = 0 ] = 1%r.
proc.
while (i <= nlimbs
  /\ (forall j, 0 <= j < i => a.[j]%Array32 = W64.zero)) (nlimbs - i). progress.
wp.  skip.  progress. smt().  smt(@Array32). smt(). wp.  skip. progress. smt(). smt().
rewrite - zeroRE. congr.
apply Array32.ext_eq. progress.  rewrite H1. smt().
rewrite /zeroR. smt(@Array32 @List). 
qed.


require import WArray256 Array256.


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
 wp; skip => />; smt(Array64.get_setE Array64.set_set_if).
wp; skip => />; smt (Array64.set_set_if).
qed.


equiv mul1acc_eq :
 M.mul1acc ~ MulOps.mul1acc:
 W64.to_uint k{1} = k{2} /\ ={a,b} /\ (_zero,of_0,cf,r){1}=(W64.zero,_of,_cf,x){2} /\
  0 <= k{2} < nlimbs
 ==>
 (res.`1,res.`2,res.`3,res.`4){1} = (W64.zero,res.`1,res.`2,res.`3){2}.
proof.
proc. simplify.
wp. while ( #pre /\ ={i} /\ (aux,_zero){1}=(nlimbs-1,W64.zero){2} /\ 
            0 <= i{2} <= nlimbs-1 /\ kk{1} = k{2}).
 wp; skip => />; smt(Array64.get_setE Array64.set_set_if).
wp; skip; smt(Array64.get_setE Array64.set_set_if).
qed.



equiv dmul1first_eq:
 M.dmul1 ~ W64x2N.MulOps.mul1:
 a{1}=ak{2} /\ ={b}
 ==>
 (res.`1,res.`2,res.`3,res.`4){1} = (W64.zero,res.`1,res.`2,res.`3){2}.
proof.
proc; simplify.
wp.
while ( #pre /\ ={r,i} /\ (a,of_0,cf,_zero){1}=(ak,_of,_cf,W64.zero){2} /\ 
        1 <= i{2} <= 32*2 /\ !_of{2} /\ aux{1} = dnlimbs).
wp. skip. progress. smt(Array128.get_setE Array128.set_set_if). smt(Array128.get_setE Array128.set_set_if).
smt(Array128.get_setE Array128.set_set_if). smt(Array128.get_setE Array128.set_set_if). 
 wp; skip => />; smt(Array128.get_setE Array128.set_set_if).
qed.


equiv dmul1acc_eq :
 M.dmul1acc ~ W64x2N.MulOps.mul1acc:
   W64.to_uint k{1} = k{2} /\ ={a,b} /\ (_zero,of_0,cf,r){1}=(W64.zero,_of,_cf,x){2} /\
  0 <= k{2} < dnlimbs
 ==>
 (res.`1,res.`2,res.`3,res.`4){1} = (W64.zero,res.`1,res.`2,res.`3){2}.
proof.
proc. simplify.
wp. while ( #pre /\ ={i} /\ (aux,_zero){1}=(dnlimbs-1,W64.zero){2} /\ 
            0 <= i{2} <= dnlimbs-1 /\ kk{1} = k{2}).
 wp; skip => />; smt(Array128.get_setE Array128.set_set_if).
wp; skip; smt(Array128.get_setE Array128.set_set_if).
qed.


equiv muln_spec aa bb:
 M.bn_muln ~ ASpecFp.muln:
  ImplZZ a{1} a{2} /\ ImplZZ b{1} b{2} /\ aa = a{1} /\ bb = b{1}
  ==> 
  ImplZZ2 res{1}.`4 res{2}
     /\ res{1}.`1 = W64.zero /\ !res{1}.`2 /\ !res{1}.`3 /\ valR2 res{1}.`4 = valR aa * valR bb.
proof.
transitivity 
 MulOps.mulR
 ( ={a,b} ==> res{1}.`2=res{2}.`1 /\ res{1}.`3=res{2}.`2 /\ res{1}.`4=res{2}.`3 /\  res{1}.`1 = W64.zero  )
 ( ImplZZ a{1} a{2} /\ ImplZZ b{1} b{2} /\ aa = a{1} /\ bb = b{1}
   ==> !res{1}.`1 /\ !res{1}.`2 /\ ImplZZ2 res{1}.`3 res{2} /\ valR2 res{1}.`3 = valR aa * valR bb).
+ by move=> /> &1 &2 H1 H2; exists (a{1},b{1}).
+ by move=> /> /#.
+ proc; simplify.
  while ( #pre /\ (i,_zero,of_0,cf,r){1}=(k,W64.zero,_of,_cf,r){2} /\
          1 <= k{2} <= nlimbs ).
  wp. call mul1acc_eq. wp. skip. progress. 
rewrite of_uintK.
apply modz_small. split. smt(). smt(). smt(). smt(). smt().
  wp; call mul1first_eq; wp; skip => /> . 
+ proc.
  transitivity {1}
    { (_of,_cf,r) <@ MulOps.mulR(a,b); }
    ( ={a,b} ==> ={_cf,_of,r} )
    ( ImplZZ a{1} a{2} /\ ImplZZ b{1} b{2} /\ aa = a{1} /\ bb = b{1} ==> !_cf{1} /\ !_of{1} /\ ImplZZ2 r{1} r{2} /\ valR2 r{1} = valR aa * valR bb ).
  progress. exists a{1} b{1}; auto.
  + by move=> /> *.
  + by inline MulOps.mulR; sim.
  + by ecall {1} (mulR_ph a{1} b{1}); wp; skip.
qed.


equiv dmuln_spec:
 M.dbn_muln ~ ASpecFp.muln:
  W64x2N.valR a{1} = a{2} /\  W64x2N.valR b{1} = b{2}
  ==> 
 W64x2N.valR2 res{1}.`4 = res{2}
     /\ res{1}.`1 = W64.zero /\ !res{1}.`2 /\ !res{1}.`3.
proof.
transitivity 
 W64x2N.MulOps.mulR
 ( ={a,b} ==> res{1}.`2=res{2}.`1 /\ res{1}.`3=res{2}.`2 /\ res{1}.`4=res{2}.`3 /\  res{1}.`1 = W64.zero )
 ( W64x2N.valR a{1} = a{2} /\ W64x2N.valR b{1} = b{2} 
   ==> !res{1}.`1 /\ !res{1}.`2 /\ W64x2N.valR2 res{1}.`3 = res{2}).
+ by move=> /> &1 &2 H1 H2; exists (a{1},b{1}).
+ by move=> /> /#.
+ proc; simplify.
  while ( #pre /\ (i,_zero,of_0,cf,r){1}=(k,W64.zero,_of,_cf,r){2} /\
          1 <= k{2} <= dnlimbs /\ aux{1} = 64 ).
  wp. call dmul1acc_eq. wp. skip. progress.
rewrite of_uintK.
apply modz_small. split. smt(). smt(). smt(). smt(). smt(). 
  by wp; call dmul1first_eq; wp; skip => /> /#.
+ proc.
  transitivity {1}
    { (_of,_cf,r) <@ W64x2N.MulOps.mulR(a,b); }
    ( ={a,b} ==> ={_cf,_of,r} )
    ( W64x2N.valR a{1} = a{2} /\ W64x2N.valR b{1} = b{2} ==> !_cf{1} /\ !_of{1} /\ W64x2N.valR2 r{1} = r{2} ).
  + by move=> /> &1; exists a{1} b{1}; auto.
  + by move=> /> *.
  + by inline W64x2N.MulOps.mulR; sim.
  + by ecall {1} (W64x2N.mulR_ph a{1} b{1}); wp; skip.
qed.


equiv dsubc_spec:
 M.dbn_subc ~ ASpecFp.dsubn:
  W64x2N.valR a{1} = a{2} /\ W64x2N.valR b{1} = b{2} (* /\ W64x2N.valR b{1}  <= W64x2N.valR a{1} *)
  ==> res{1}.`1=res{2}.`1 /\ W64x2N.valR res{1}.`2 = res{2}.`2.
proof.
transitivity 
 W64x2N.R.Ops.subcR
 ( (a,b,false){1}=(a,b,c){2} ==> ={res} )
 (W64x2N.valR  a{1} = a{2} /\ W64x2N.valR b{1} = b{2} /\ !c{1} (* /\ W64x2N.valR b{1}  <= W64x2N.valR a{1} *)
   ==> res{1}.`1 = res{2}.`1 /\ W64x2N.valR res{1}.`2 = res{2}.`2 ).
+ by move=> /> &1 &2 H1 H2 ; exists (a{1},b{1},false).
+ by move=> /> *.
+ proc; simplify.
  unroll {2} 3; rcondt {2} 3; first by auto.
  exlim a{1}, b{1} => aa bb.
  while (={i,b} /\ 1 <= i{2} <= dnlimbs /\ 
         (cf, aa){1}=(c, a){2} /\
         (forall k, 0 <= k < i{2} => a{1}.[k] = r{2}.[k])%Array64 /\
         (forall k, i{2} <= k < dnlimbs => a{1}.[k] = aa.[k])%Array64 /\ aux{1} = 64).
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
  by apply Array64.ext_eq; smt().
+ proc; simplify.
  transitivity {1}
   { (c,r) <@ W64x2N.R.Ops.subcR(a,b,c); }
   ( ={a,b,c} ==> ={c,r} )
   ( W64x2N.valR a{1} = a{2} /\ W64x2N.valR b{1} = b{2} /\ !c{1}  (* /\ W64x2N.valR b{1}  <= W64x2N.valR a{1} *) ==> ={c} 
   /\ W64x2N.valR r{1} = r{2} ).
  + by move=> /> &2 H  ; exists a{2} b{2} false.
  + by auto.
  + by inline*; sim.
  + ecall {1} (W64x2N.R.subcR_ph a{1} b{1} c{1}); wp; skip => /> &m Hc [c r] /= -> .
progress. 
    by rewrite W64x2N.R.bn_borrowE 1:/# b2i0 /bn_modulus /=.
qed.



lemma dbn_cmov_correct x y z :
  phoare[ M.dbn_cmov :  arg = (x,y,z)  ==> res = if x then z else y ] = 1%r.
proc.
while (cond = x /\ b = z /\ i <= dnlimbs 
  /\ (forall j, 0 <= j < i => a.[j] = if cond then z.[j] else y.[j])
  /\ (forall j, i <= j < dnlimbs => a.[j] = y.[j]) /\ aux = 64) (dnlimbs - i). progress.
wp.  skip.  progress. smt().   smt(@Array64). smt(@Array64). smt(). wp.  skip. progress. smt(@Array64). smt().
apply Array64.ext_eq. progress. smt(@Array64). 
qed.



require import List.

op oneR : R = (of_list W64.zero (W64.one :: nseq (nlimbs - 1) W64.zero ))%Array32.

    (* TODO: nlimbs specific *)
lemma oneRE: ImplZZ oneR 1.
rewrite /oneR /valR /bnk.
do? (rewrite range_ltn; first by trivial ).
simplify. rewrite range_geq. auto.
do rewrite big_consT.
rewrite big_nil.
 have -> : dig ((of_list W64.zero (W64.one :: nseq (nlimbs - 1) W64.zero)))%Array32 0 = 1.
 simplify. smt(@Int).
 have q : forall x, 0 < x < nlimbs => dig ((of_list W64.zero (W64.one :: nseq (nlimbs - 1) W64.zero)))%Array32 x = 0.
 move => x xp. rewrite /dig.
   have ->: to_uint ((of_list W64.zero (W64.one :: nseq (nlimbs - 1) W64.zero)).[x])%Array32 = 0. 
    do? (rewrite nseqS'; first by trivial). simplify. 
   rewrite nseq0. 
  have -> : (of_list W64.zero [W64.one; W64.zero; W64.zero; W64.zero; W64.zero]).[x]%Array32 = W64.zero. 
rewrite get_of_list. smt().
smt(@List).  smt(@W64). smt().
do? (rewrite q; first smt()). auto.
qed.


lemma bn_set1_correct :
  phoare[ M.bn_set1 : true  ==> W64xN.valR res = 1 ] = 1%r.
proc.
while (0 < i <= nlimbs 
  /\ (forall j, 1 <= j < i => a.[j]%Array32 = W64.zero) /\ a.[0]%Array32 = W64.one) (nlimbs - i). progress.
wp.  skip.  progress. smt(). smt().  smt(@Array32). smt(@Array32). smt(). wp.  skip. progress. smt(@Array32). smt().
rewrite - oneRE. congr.
apply Array32.ext_eq. progress.  
case (x = 0). progress. progress.
rewrite H2. smt(). 
rewrite /oneR. smt(@Array32 @List).
qed.



lemma dbn_copy_correct x :
  phoare[ M.dbn_copy :  arg = x  ==> res = x ] = 1%r.
proc.
while (a = x /\ i <= dnlimbs 
  /\ (forall j, 0 <= j < i => r.[j] = x.[j])
  /\ aux  = 64 ) (dnlimbs - i). progress.
wp.  skip.  progress. smt(). smt(@Array64). smt(). wp.  skip. progress. smt(). smt().
apply Array64.ext_eq. progress. smt(). 
qed.



equiv dcminusP_spec:
 M.dcminusP ~ ASpecFp.cminus:
 W64x2N.valR p{1} = p{2} /\ W64x2N.valR x{1} = a{2} /\ 0 < p{2} ==> W64x2N.valR res{1}  =res{2}.
proof.
transitivity CSpecFp.dcminus
 ( W64x2N.valR p{1} = p{2} /\ W64x2N.valR x{1} = a{2} /\ 0 < p{2} ==> W64x2N.valR res{1}  = res{2} )
 ( ={a,p} /\ a{2} < W64x2N.modulusR /\ 0 < p{2} ==> ={res} ).
  progress. exists (W64x2N.valR x{1}, W64x2N.valR p{1}). progress. smt(@W64x2N). smt(@W64x2N).
+ by auto. 
proc. 
(ecall {1} (dbn_cmov_correct cf{1} z{1} x{1})).  simplify.
conseq (_:  ( (W64x2N.valR (if cf{1} then x{1} else z{1}))%W64x2N = r{2} )). progress.
inline ASpecFp.ctseln. wp.   simplify.
seq 2 0 : ((W64x2N.valR p{1})%W64x2N = p{2} /\ (W64x2N.valR x{1})%W64x2N = a{2} /\ z{1} = x{1} /\ 0 < p{2}).
(ecall {1} (dbn_copy_correct x{1})).  wp. skip. progress.
seq 1 1 : (cf{1} = c{2} /\ W64x2N.valR z{1} = x{2} 
  /\ (W64x2N.valR p{1})%W64x2N = p{2} /\ (W64x2N.valR x{1})%W64x2N = a{2} /\ 0 < p{2}).
call  dsubc_spec.  skip. progress.
skip. progress.   smt().
proc. inline*. wp.  skip.  progress.
case (a{2} < p{2} = true). move => q. rewrite q. simplify. auto.
move => q. 
have -> : a{2} < p{2} = false. smt(). simplify.
have : p{2} <= a{2}. smt().
move => qq.
have qqq : a{2} - p{2} < W64x2N.modulusR. smt(@Int).
smt(@Int).
qed.


import W64x2N.


lemma bn_div2_correct z :
  phoare[ M.div2 : arg = (z,dnlimbs)  ==> (W64x2N.valR res) = (W64x2N.valR2 z) %/  W64x2N.modulusR ] = 1%r.
proc. sp.
while (aux = dnlimbs /\ i <= dnlimbs /\ forall j, 0 <= j < i => r.[j] = x.[dnlimbs + j]) (dnlimbs - i). 
progress. wp. skip. progress.
smt(). smt(@Array64). smt(). skip. progress.
smt(). smt().
have ->:  W64x2N.modulusR  = W64x2N.M^dnlimbs.  rewrite /R.bn_modulus. auto. 
have ->: (R2.bnk (2*dnlimbs) x{hr})%R2 = valR2 x{hr}. auto.
rewrite R2.bghint_div. auto.
rewrite - R.bnkup0.
rewrite /bnkup.
have ->: 
  bigi predT (fun (i1 : int) => to_uint r0.[i1] * W64x2N.M ^ (i1 - 0)) 0 dnlimbs
  = bigi predT (fun (i1 : int) => to_uint x{hr}.[i1 + dnlimbs] * W64x2N.M ^ (i1 - 0)) 0 dnlimbs.
apply eq_big_int. progress. smt(). 
  have ->: bigi predT (fun (i1 : int) => to_uint x{hr}.[i1] * W64x2N.M ^ (i1 - dnlimbs)) dnlimbs
  (2 * dnlimbs)  = bigi predT (fun (i1 : int) => to_uint x{hr}.[i1] * W64x2N.M ^ (i1 - dnlimbs)) (0 + dnlimbs)
  (2 * dnlimbs). auto.
rewrite big_addn. simplify. auto.
qed.



lemma bn_shrink_correct a  :
  phoare[ M.bn_shrink : arg = a  ==> W64xN.valR res = W64x2N.valR a %% W64xN.modulusR ] = 1%r.
proc.
sp.
while (i <= nlimbs /\ forall j, 0 <= j < i => r.[j]%Array32 = x.[j]%Array64) (nlimbs - i). 
progress. wp. skip. progress.
smt(). smt(@Array32). smt(). skip. progress.
smt(). smt(). 
rewrite /W64xN.modulusR. auto.
rewrite W64x2N.R.bn_mod. auto. 
rewrite /bnk. 
apply eq_big_seq. progress. rewrite H1. split.
smt (mem_range). 
smt (mem_range). 
auto.
qed.


lemma bn_expand_correct : forall a,
      phoare[ M.bn_expand : arg = a  ==> W64x2N.valR res =  W64xN.valR a ] = 1%r.
 have  bn_expand_correct : forall a, 
    hoare[ M.bn_expand : arg = a  ==> W64x2N.valR res = W64xN.valR a ].
   move => a.
   proc.
   sp. 
    seq 1 : (a = x /\ i = nlimbs /\ forall i, i < nlimbs => r.[i] = x.[i]%Array32).
    while (i <= nlimbs /\ forall j, 0 <= j < i => r.[j] = x.[j]%Array32). wp.  skip. progress.
    smt(). smt(@Array32 @Array64). skip. progress.
    smt().  smt(). smt(@Array64 @Array32). sp.
    seq 2 : (a = x /\  (forall j, 0 <= j < nlimbs => r.[j]%Array64 = x.[j]%Array32)
         /\ (forall j, nlimbs <= j < 2*nlimbs => r.[j] = W64.zero)).     
    while (a = x /\ nlimbs <= i <= 2*nlimbs 
         /\ (forall j, 0 <= j < nlimbs => r.[j]%Array64 = x.[j]%Array32)
         /\ (forall j, nlimbs <= j < i => r.[j] = W64.zero) /\ aux = 64 ). wp.  skip. progress.
    smt(). smt().
    have z : i{hr} <> j. smt(). 
    rewrite - H1. auto.  smt(@Array32 @Array64).
    case (j = i{hr}). smt(@Array32 @Array64).
    progress.
    have : j < i{hr}.  smt().
    progress.
    rewrite - (H2 j).  smt().
    smt(@Array32 @Array64). wp. 
    skip.  progress.
    smt(@Array32 @Array64). smt(). smt(). 
    skip.  progress.
    have -> : valR r{hr} = (bn_seq ((to_list r{hr}))%Array64).
    apply W64x2N.R.bn2seq. 
    rewrite /to_list.
    have -> : dnlimbs = nlimbs + nlimbs. smt().
    rewrite mkseq_add. auto. auto.
    have -> : mkseq (fun (i0 : int) => r{hr}.[i0]) nlimbs 
      = mkseq (fun (i0 : int) => x{hr}.[i0]%Array32) nlimbs.
    apply eq_in_mkseq. progress. 
    simplify.
    have ->: mkseq (fun (i0 : int) => r{hr}.[nlimbs + i0]) nlimbs
      = mkseq (fun (i0 : int) => W64.zero) nlimbs.
    apply eq_in_mkseq. progress. rewrite H0. smt(). auto.
    have -> : mkseq (fun (_ : int) => W64.zero) nlimbs = nseq nlimbs W64.zero.   
    print mkseq_nth.
     pose s := (nseq nlimbs W64.zero).
    rewrite (eq_mkseq (fun (x: int) => W64.zero) (nth W64.zero s)). 
   apply fun_ext.    apply fun_ext. progress. move => x. smt.
   have ->: nlimbs = size s. rewrite /s. search nseq. rewrite size_nseq. smt.
apply mkseq_nth. 
    rewrite /bn_seq.
    rewrite foldr_cat.
    have ->: (foldr (fun (w : W64.t) (r0 : int) => to_uint w + W64x2N.M * r0) 0
         (nseq nlimbs W64.zero)) = 0.  
       have gen : forall n, 0 <= n => foldr (fun (w : W64.t) (r0 : int) => to_uint w + W64x2N.M * r0) 0
                     (nseq n  W64.zero) = 0.
       apply intind. progress. rewrite nseq0. simplify. auto.
       progress. rewrite nseqS. auto. simplify. rewrite H2. auto.
       apply gen. auto.
    rewrite W64xN.R.bn2seq. rewrite /bn_seq. rewrite /to_list. 
    pose f := (fun (w : W64.t) (r0 : int) => to_uint w + W64x2N.M * r0).
    simplify. auto.    
move => a.
bypr. progress.
 have ->:  1%r = Pr[M.bn_expand(arg{m}) @ &m : true ] . 
byphoare. proc.  while (true) (2*nlimbs -i). progress. wp. skip. smt().
wp. while true (nlimbs - i). progress. wp. skip. smt().
wp.  skip. smt(). auto. auto.
  have ->: Pr[M.bn_expand(arg{m}) @ &m : true]
  = Pr[M.bn_expand(arg{m}) @ &m : (W64x2N.valR res =  W64xN.valR arg{m}) ]  
    + Pr[M.bn_expand(arg{m}) @ &m : (W64x2N.valR res <>  W64xN.valR arg{m}) ].
rewrite Pr[mu_split (W64x2N.valR res =  W64xN.valR arg{m})]. simplify.   auto.
have ->: Pr[M.bn_expand(arg{m}) @ &m : valR res <> valR arg{m}] = 0%r.
byphoare (_: arg = arg{m} ==> _). 
hoare. simplify. conseq (bn_expand_correct arg{m}). auto. auto. auto.
qed.


lemma bn_expand_ho : forall a,
      hoare[ M.bn_expand : arg = a  ==> W64x2N.valR res =  W64xN.valR a ].
move => a. bypr. progress.
have q : 1%r = Pr[W64_SchnorrExtract.M(Syscall).bn_expand(arg{m}) @ &m : true]. 
byphoare (_: arg = arg{m} ==> _). proc*. call (bn_expand_correct ( arg{m})). auto. auto. auto.
have z :  Pr[W64_SchnorrExtract.M(Syscall).bn_expand(arg{m}) @ &m : true] = Pr[W64_SchnorrExtract.M(Syscall).bn_expand(arg{m}) @ &m :
   valR res <> valR arg{m}] +  Pr[W64_SchnorrExtract.M(Syscall).bn_expand(arg{m}) @ &m :
   valR res = valR arg{m}].
rewrite Pr[mu_split (valR res <> valR arg{m})]. simplify. auto.
have w :  Pr[W64_SchnorrExtract.M(Syscall).bn_expand(arg{m}) @ &m : valR res = valR arg{m}] = 1%r.
byphoare (_: arg = arg{m} ==> _). conseq (bn_expand_correct ( arg{m})).  auto. auto.
rewrite Pr[mu_split valR res = valR arg{m}]. simplify. 
have ->: Pr[W64_SchnorrExtract.M(Syscall).bn_expand(arg{m}) @ &m :
   valR res <> valR arg{m} /\ valR res <> valR arg{m}] =
Pr[W64_SchnorrExtract.M(Syscall).bn_expand(arg{m}) @ &m :
   valR res <> valR arg{m}]. rewrite Pr[mu_eq]. auto. auto.
have easy_fact1 : Pr[W64_SchnorrExtract.M(Syscall).bn_expand(arg{m}) @ &m :
   valR res <> valR arg{m}] = 0%r. smt(@Distr).
have easy_fact2 : Pr[W64_SchnorrExtract.M(Syscall).bn_expand(arg{m}) @ &m :
   valR res <> valR arg{m} /\ valR res = valR arg{m}]
 <= Pr[W64_SchnorrExtract.M(Syscall).bn_expand(arg{m}) @ &m :
   valR res <> valR arg{m}]. smt(@Distr).
have easy_fact3 : Pr[W64_SchnorrExtract.M(Syscall).bn_expand(arg{m}) @ &m :
   valR res <> valR arg{m} /\ valR res = valR arg{m}] = 0%r. smt(@Distr).
smt().
qed.



module MM = {
  proc ith_bit (kk:W64.t Array32.t, ctr:W64.t) : W64.t = {
    var bit:W64.t;
    var c1:W64.t;
    var c2:W64.t;
    var r:W64.t;
    c1 <- (ctr `>>` (W8.of_int 6));
    c2 <- (ctr - (c1 * (W64.of_int 64)));
    r <- kk.[(W64.to_uint c1)]%Array32;
    bit <@ IB.ith_bit64 (r, c2);
    return (bit);
  }
}.

lemma ith_bit_lemmaEq :
      equiv[ MM.ith_bit ~ M.ith_bit : ={arg} ==> ={res}].
proc.
seq 2 4 : (={c1, c2,kk}). wp.
skip. progress.
have -> : 63 = 2^6 - 1. smt().
rewrite and_mod. auto. simplify.
have x:  to_uint (ctr{2} `>>` (of_int 6)%W8) = to_uint ctr{2} %/ 64. 
rewrite shr_div_le. auto. smt(@Ring).
rewrite to_uint_eq.
auto.
rewrite to_uintB.  rewrite /(\ule).
rewrite to_uintM_small. rewrite x.  
rewrite W64.to_uint_small. auto.
have  : to_uint ctr{2} %/ 64 * 64 <= to_uint ctr{2}. smt. (* smt (divz_eqP).  *)
have  :  0 <= to_uint ctr{2} && to_uint ctr{2} < W64x2N.M.
apply (W64.to_uint_cmp ctr{2}). clear x.
pose x := to_uint ctr{2} %/ 64 * 64.
pose y := to_uint ctr{2}.
smt().
rewrite x.  smt(shr_div_le). 
rewrite to_uintM_small. rewrite x.  
have ->: to_uint ((of_int 64))%W64 = 64.
rewrite W64.to_uint_small.  auto. auto.
have  : to_uint ctr{2} %/ 64 * 64 <= to_uint ctr{2}. smt. (* smt (divz_eqP).  *)
have  :  0 <= to_uint ctr{2} && to_uint ctr{2} < W64x2N.M.
apply (W64.to_uint_cmp ctr{2}). clear x.
pose x := to_uint ctr{2} %/ 64 * 64.
pose y := to_uint ctr{2}.
smt().
rewrite  shr_div_le.
auto. simplify. 
smt (@W64 @IntDiv).
sim.
qed.

lemma mkseqS' ['a]:
  forall (f : int -> 'a) (n : int),
    0 < n => mkseq f n = rcons (mkseq f (n - 1)) (f (n - 1)).
smt(mkseqS).
qed.

require import BitEncoding.
import BS2Int.

lemma ith_bit_lemma_cspec :
      equiv[ M.ith_bit ~ CSpecFp.ith_bit : arg{1}.`1 = arg{2}.`1 /\  W64.to_uint arg{1}.`2 = arg{2}.`2 /\
 0 <= ctr{2} && ctr{2} < 64*nlimbs ==>
              ={res} /\ (res{2} = W64.one \/ res{2} = W64.zero)].
transitivity MM.ith_bit
   (={arg} ==> ={res})
   (arg{1}.`1 = arg{2}.`1 /\  W64.to_uint arg{1}.`2 = arg{2}.`2 /\
 0 <= ctr{2} && ctr{2} < 64*nlimbs ==>
              ={res} /\ (res{2} = W64.one \/ res{2} = W64.zero)).
progress. smt(). smt().
symmetry. conseq ith_bit_lemmaEq. auto. auto.
proc.
seq 3 0 : (to_uint c1{1} = (to_uint ctr{1} %/ 64) /\ to_uint c2{1} = (to_uint ctr{1} %% 64) /\ to_uint ctr{1} = ctr{2}
  /\ r{1} = kk{1}.[(to_uint ctr{1} %/ 64)]%Array32 /\ r{2} = kk{1} /\ 0 <= ctr{2} && ctr{2} < 64*nlimbs ).
wp.  skip. progress.
rewrite shr_div_le. auto. smt(@Ring).
rewrite modzE.
have <-: to_uint (ctr{1} `>>` (of_int 6)%W8) = to_uint ctr{1} %/ 64. rewrite shr_div_le. auto. smt(@Ring).
rewrite to_uintB. rewrite /(\ule).
            rewrite to_uintM_small.
have x:  to_uint (ctr{1} `>>` (of_int 6)%W8) = to_uint ctr{1} %/ 64.
rewrite shr_div_le. auto. smt(@Ring).
rewrite W64.to_uint_small. auto.
have  : to_uint ctr{1} %/ 64 * 64 <= to_uint ctr{1}. (* smt (divz_eqP). *) smt.
have  :  0 <= to_uint ctr{1} && to_uint ctr{1} < W64x2N.M.
apply (W64.to_uint_cmp ctr{1}).
pose xx := to_uint ctr{1} %/ 64 * 64.
pose yy := to_uint ctr{1}.
smt().
rewrite W64.to_uint_small. auto.
have ->:  to_uint (ctr{1} `>>` (of_int 6)%W8) = to_uint ctr{1} %/ 64.
rewrite shr_div_le. auto. smt(@Ring).
smt.
(* smt (divz_eqP). *)
rewrite shr_div_le.  auto.
rewrite W64.to_uintM.
rewrite W64.to_uint_small. auto.
rewrite shr_div_le.  auto. smt(@W64).
rewrite shr_div_le. auto. smt(@Ring).
exists* r{1}, c2{1}. elim*. progress.
call {1} (ithbit64 r_L c2_L). skip.
progress. smt(). smt().
rewrite /ith_bitword64.  rewrite H0.
rewrite /ith_bitR. rewrite /Rbits. rewrite /valR.
rewrite /ith_bit.
rewrite /as_word.
rewrite /as_w64.
have ->: (kk{1}.[to_uint ctr{1} %/ 64])%Array32.[to_uint ctr{1} %% 64]
  = nth false (BS2Int.int2bs (64 * nlimbs) ((valR kk{1}))%W64xN) (to_uint ctr{1}) .
rewrite - get_w2bits.
rewrite - get_to_list.
have -> : (W64.w2bits (nth witness ((to_list kk{1}))%Array32 (to_uint ctr{1} %/ 64)))
 = ((nth witness (map W64.w2bits (to_list kk{1}))%Array32 (to_uint ctr{1} %/ 64))).
rewrite - (nth_map witness witness W64.w2bits). progress.   smt(). smt(@W64xN).
auto.
have -> : (nth witness (map W64.w2bits ((to_list kk{1}))%Array32)
     (to_uint ctr{1} %/ 64))
 = (nth [] (map W64.w2bits ((to_list kk{1}))%Array32)
     (to_uint ctr{1} %/ 64)).
rewrite (nth_change_dfl [] witness). progress.  smt(). smt(@W64xN @List). auto.
rewrite - (BitChunking.nth_flatten false 64 (map W64.w2bits ((to_list kk{1}))%Array32) (to_uint ctr{1})).
rewrite  List.allP. progress.
have : exists z, z \in ((to_list kk{1}))%Array32 /\ x = W64.w2bits z.
apply mapP. auto. elim. progress.
have ->: (flatten (map W64.w2bits ((to_list kk{1}))%Array32))  = (int2bs (64*nlimbs) ((valR kk{1}))%W64xN).
have -> : (valR kk{1})%W64xN = bs2int (flatten (map W64.w2bits ((to_list kk{1}))%Array32)).
rewrite /bnk.
do? (rewrite range_ltn; first by trivial).
simplify. rewrite range_geq. auto. auto.
do? rewrite big_consT.
rewrite big_nil.
rewrite /to_list.
do? (rewrite mkseqS'; first by trivial).
rewrite mkseq0. simplify.
do? rewrite flatten_cons.
rewrite flatten_nil.
rewrite cats0.
do? rewrite bs2int_cat.
simplify.
(* have ->:  18446744073709551616 ^ 0 = 1. smt(@Ring). *)
(* simplify. *)
smt(@Ring).
have ->: 64*nlimbs = size (flatten (map W64.w2bits ((to_list kk{1}))%Array32)).
rewrite /to_list.
do? (rewrite mkseqS'; first by trivial).
rewrite mkseq0. simplify.
do? rewrite flatten_cons.
rewrite flatten_nil.
do? rewrite size_cat.
simplify. auto.
rewrite  bs2intK. auto. auto.
smt().
auto. smt().
qed.




lemma swap_lemma_cspec :
      equiv[ M.swapr ~ CSpecFp.swapr :
              a{2} = x{1} /\ b{2} = y{1} /\ swap_0{1} = as_w64 c{2} ==> ={res}].
proc.  simplify.
seq 2 0 : (i{1} = 0 /\ a{2} = x{1} /\ b{2} = y{1} /\ swap_0{1} = as_w64 c{2} /\ 
   ((as_bool swap_0{1} => mask{1} = (of_int 18446744073709551615)%W64 )
              /\ (as_bool swap_0{1} = false => mask{1} = (of_int 0)%W64))).
wp. skip. progress. smt(@W64). smt(@W64).
while {1} (0 <= i{1} /\ ((as_bool swap_0{1} => mask{1} = (of_int 18446744073709551615)%W64 )
              /\ (as_bool swap_0{1} = false => mask{1} = (of_int 0)%W64)) 
   /\ (forall j, 0 <= j < i{1} => (x{1}.[j])%Array32 = (if as_bool swap_0{1} then (b{2}.[j]) else (a{2}.[j]))%Array32 )  
   /\ (forall j, 0 <= j < i{1} => (y{1}.[j])%Array32 = (if as_bool swap_0{1} then (a{2}.[j]) else (b{2}.[j]))%Array32 )  
   /\ (forall j, i{1} <= j => (x{1}.[j])%Array32 =  (a{2}.[j]))%Array32
   /\ (forall j, i{1} <= j => (y{1}.[j])%Array32 =  (b{2}.[j]))%Array32
 ) (nlimbs - i{1} + 1).
progress. wp.  skip.  progress.   smt().
case (j <  i{hr}). progress. smt(@Array32).
progress.
have : j = i{hr}. smt().
progress.
have ->: (x{hr}.[i{hr} <-
    x{hr}.[i{hr}] `^` (x{hr}.[i{hr}] `^` y{hr}.[i{hr}] `&` mask{hr})].[i{hr}])%Array32
 = (x{hr}.[i{hr}] `^` (x{hr}.[i{hr}] `^` y{hr}.[i{hr}] `&` mask{hr}))%Array32. smt(@Array32).
case (as_bool swap_0{hr}). progress.
rewrite H4. auto.  rewrite H0. auto. rewrite H5. auto. rewrite - ones64. 
have -> : ((a{m}.[i{hr}])%Array32 `^` (b{m}.[i{hr}])%Array32 `&`
 (of_int W64.max_uint)%W64) = a{m}.[i{hr}]%Array32 `^` ((b{m}.[i{hr}])%Array32 `&`
 (of_int W64.max_uint)%W64).
pose x := a{m}.[i{hr}]%Array32.
pose y := b{m}.[i{hr}]%Array32.
pose z := (of_int W64.max_uint)%W64.
rewrite andwDl.
have ->: (x `&` z) = x. smt (W64.andw1_s).
auto.
have ->: ((b{m}.[i{hr}])%Array32 `&` (of_int W64.max_uint)%W64) = ((b{m}.[i{hr}])%Array32). 
pose y := b{m}.[i{hr}]%Array32.
pose z := (of_int W64.max_uint)%W64.
smt (W64.andw1_s).
smt(@W64).
progress. rewrite H4. auto.  rewrite H1. smt(). auto. 
case (j <  i{hr}). progress. smt(@Array32).
progress.
have : j = i{hr}. smt().
progress.
have ->: (y{hr}.[i{hr} <-
   y{hr}.[i{hr}] `^` (x{hr}.[i{hr}] `^` y{hr}.[i{hr}] `&` mask{hr})].[i{hr}])%Array32
 = (y{hr}.[i{hr}] `^` (x{hr}.[i{hr}] `^` y{hr}.[i{hr}] `&` mask{hr}))%Array32. smt(@Array32).
case (as_bool swap_0{hr}). progress.
rewrite H4. auto.  rewrite H0. auto. rewrite H5. auto. rewrite - ones64. 
have -> : ((a{m}.[i{hr}])%Array32 `^` (b{m}.[i{hr}])%Array32 `&`
 (of_int W64.max_uint)%W64) = a{m}.[i{hr}]%Array32 `^` ((b{m}.[i{hr}])%Array32 `&`
 (of_int W64.max_uint)%W64). 
pose x := a{m}.[i{hr}]%Array32.
pose y := b{m}.[i{hr}]%Array32.
pose z := (of_int W64.max_uint)%W64.
rewrite andwDl.
have ->: (x `&` z) = x. smt (W64.andw1_s).
auto.
have ->: ((b{m}.[i{hr}])%Array32 `&` (of_int W64.max_uint)%W64) = ((b{m}.[i{hr}])%Array32).
pose y := b{m}.[i{hr}]%Array32.
pose z := (of_int W64.max_uint)%W64.
smt (W64.andw1_s).
smt(@W64).
progress. rewrite H4. auto.  rewrite H1. smt(). smt(@W64).
smt(@Array32). smt(@Array32). smt().
skip. progress. smt().   smt().   smt(). 
case (c{2} = false). progress.  
apply Array32.ext_eq.  progress. rewrite H5. progress. smt(). rewrite /as_bool. rewrite /as_w64. simplify. smt(@W64).
apply Array32.ext_eq.  progress. rewrite H6. progress. smt(). rewrite /as_bool. rewrite /as_w64. simplify. smt(@W64).
progress. have ->: c{2} = true. smt(). simplify.
progress. 
apply Array32.ext_eq.  progress. rewrite H5. progress. smt(). rewrite /as_bool. rewrite /as_w64. simplify. smt(@W64).
apply Array32.ext_eq.  progress. rewrite H6. progress. smt(). rewrite /as_bool. rewrite /as_w64. simplify. smt(@W64).
qed.


lemma swap_lemma_ph xx yy ss :
      phoare [ M.swapr : arg = (xx,yy,as_w64 ss) ==> res = if ss then (yy, xx) else (xx, yy)  ] = 1%r.
bypr.
progress.
have ->: 1%r = Pr[ CSpecFp.swapr(x{m},y{m},as_bool swap_0{m}) @&m : res =  if ss then (yy, xx) else (xx, yy)  ].
byphoare (_: arg = (x{m},y{m},as_bool swap_0{m}) ==> _). proc.
skip.  progress. smt. smt(). auto.
byequiv. conseq swap_lemma_cspec.  smt(). smt(). auto. auto.
qed.

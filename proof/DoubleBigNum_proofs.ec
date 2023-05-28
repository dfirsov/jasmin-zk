require import AllCore IntDiv CoreMap List RealExp.
import StdBigop Bigint BIA.

from Jasmin require import JModel.

require import W64_SchnorrExtract.
require import Array128.


require import BigNum_spec AuxLemmas.
import W64x2N R.


require import BitEncoding.
import BS2Int.

module M = M(Syscall).

equiv daddc_spec:
 M.dbn_addc ~ ASpecFp.daddn:
  W64x2N.valR a{1} = a{2} /\ W64x2N.valR b{1} = b{2}
  ==> res{1}.`1=res{2}.`1 /\  W64x2N.valR res{1}.`2 = res{2}.`2.
proof.
transitivity
 R.Ops.addcR
 ( ={a,b} /\ !c{2} ==> ={res} )
 ( W64x2N.valR a{1} = a{2} /\ W64x2N.valR b{1} = b{2} /\ !c{1}
   ==> res{1}.`1 = res{2}.`1 /\ W64x2N.valR res{1}.`2 = res{2}.`2 ).
+ by move=> /> &1 &2 H1 H2; exists (a{1},b{1},false).
+ by move=> /> *.
+ proc; simplify.
  unroll {2} 3; rcondt {2} 3; first by auto.
  exlim a{1}, b{1} => aa bb.
  while (={i,b} /\ 1 <= i{2} <= dnlimbs /\ aux{1} = dnlimbs /\
         (cf,aa){1} = (c,a){2} /\
         (forall k, 0 <= k < i{2} => a{1}.[k] = r{2}.[k])%A /\
         (forall k, i{2} <= k < dnlimbs => a{1}.[k] = aa.[k])%A).
   wp; skip => /> &1 &2 Hi1 Hi2 H1 H2 Hi.
   split => *; first smt().
   split => *; first smt().
   split.
    move=> k Hk1 Hk2.
    pose X := (addc _ _ _)%W64.
    pose Y := (addc _ _ _)%W64.
    have ->: X=Y by smt().
    case: (k = i{2}) => ?.  smt(@A). smt(@A).
    (*  by rewrite !set_eqiE /#. *)
    (* by rewrite !set_neqiE /#. *)
   move=> k Hk1 Hk2. smt(@A).
   (* by rewrite A.set_neqiE /#. *)
  wp; skip => /> &2.
  move=> Hc; split => *.
   split => k *. 
    (* by rewrite (_:k=0) 1:/# !set_eqiE /#. *)
        smt(@A).
        smt(@A).
   (* by rewrite set_neqiE /#. *)
  apply A.ext_eq; smt().
+ proc; simplify.
  transitivity {1}
   { (c,r) <@ R.Ops.addcR(a,b,c); }
   ( ={a,b,c} ==> ={c,r} )
   ( W64x2N.valR a{1} = a{2} /\ W64x2N.valR b{1} = b{2} /\ !c{1} ==> ={c} /\  W64x2N.valR r{1} = r{2} ).
  + by move=> /> &2 H; exists a{2} b{2} false.
  + by auto.
  + by inline*; sim.
  + ecall {1} (R.addcR_ph a{1} b{1} c{1}); wp; skip => /> &m Hc [c r] /= -> ?.
    by  rewrite bn_carryE 1:/# b2i0 /bn_modulus /=.
qed.


lemma daddc_ph x y:
  phoare[ M.dbn_addc :  arg = (x, y)  ==> (W64x2N.valR res.`2) = (W64x2N.valR x + W64x2N.valR y) %% W64x2N.modulusR ] = 1%r.
bypr. progress.
 have <- : Pr[ASpecFp.daddn(W64x2N.valR a{m}, W64x2N.valR b{m} ) @ &m : (W64x2N.valR a{m} + W64x2N.valR b{m}) %% W64x2N.modulusR = res.`2] = 1%r.
  byphoare (_: arg = (W64x2N.valR a{m}, W64x2N.valR b{m}) ==> _).
proc. wp. skip. progress. auto. auto.
byequiv. conseq daddc_spec.
progress.  smt(). auto. auto.
qed.



lemma dbn_cmov_correct x y z :
  phoare[ M.dbn_cmov :  arg = (x,y,z)  ==> res = if x then z else y ] = 1%r.
proc.
while (cond = x /\ b = z /\ i <= dnlimbs  /\ aux = dnlimbs 
  /\ (forall j, 0 <= j < i => a.[j]%A = if cond then z.[j] else y.[j])%A
  /\ (forall j, i <= j < dnlimbs => a.[j] = y.[j]) )%A (dnlimbs - i). progress.
wp.  skip.  progress. smt().   smt(@A). smt(@A). smt(). wp.  skip. progress. smt(@A). smt().
apply A.ext_eq. progress. smt(@A). 
qed.



lemma dbn_copy_correct x :
  phoare[ M.dbn_copy :  arg = x  ==> res = x ] = 1%r.
proc.
while (a = x /\ i <= dnlimbs  /\ aux = dnlimbs
  /\ (forall j, 0 <= j < i => r.[j] = x.[j])%A
  ) (dnlimbs - i). progress.
wp.  skip.  progress. smt(). smt(@A). smt(). wp.  skip. progress. smt(). smt().
apply A.ext_eq. progress. smt(). 
qed.



equiv dsubc_spec:
 M.dbn_subc ~ ASpecFp.dsubn:
  W64x2N.valR a{1} = a{2} /\ W64x2N.valR b{1} = b{2} (* /\ W64xN.valR b{1}  <= W64xN.valR a{1} *)
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
  while (={i,b} /\ 1 <= i{2} <= dnlimbs /\  aux{1} = dnlimbs /\
         (cf, aa){1}=(c, a){2} /\
         (forall k, 0 <= k < i{2} => a{1}.[k] = r{2}.[k])%A /\
         (forall k, i{2} <= k < dnlimbs => a{1}.[k] = aa.[k])%A).
   wp; skip => /> &1 &2 Hi1 _ Hh1 Hh2 Hi2.
   split => *; first smt().
   split => *; first smt().
   split.
    move=> k Hk1 Hk2.
    pose X := (subc _ _ _)%W64.
    pose Y := (subc _ _ _)%W64.
    have ->: X=Y by smt().
    case: (k = i{2}) => ?.
       rewrite  /A."_.[_]".
     by rewrite !A.set_eqiE /#.
       rewrite  /A."_.[_]".
    by rewrite !A.set_neqiE /#.
   move=> k Hk1 Hk2.
       rewrite  /A."_.[_]".
   by rewrite A.set_neqiE /#.
  wp; skip => />.
  split => *.
   split => k *.
       rewrite  /A."_.[_]".
    by rewrite (_:k=0) 1:/# !A.set_eqiE /#.
       rewrite  /A."_.[_<-_]".
       rewrite  /A."_.[_]".
   by rewrite A.set_neqiE /#.
  by apply A.ext_eq; smt().
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


equiv dcminus_spec:
 M.dcminusP ~ ASpecFp.cminus:
 W64x2N.valR p{1} = p{2} /\ W64x2N.valR x{1} = a{2} /\ 0 <= p{2}  ==> W64x2N.valR res{1}  =res{2}.
proof.
transitivity CSpecFp.dcminus
 ( W64x2N.valR p{1} = p{2} /\ W64x2N.valR x{1} = a{2} /\ 0 <= p{2}  ==> W64x2N.valR res{1}  = res{2} )
 ( ={a,p} /\ a{2} < W64x2N.modulusR /\ 0 <= p{2} ==> ={res} ).
  progress. exists (W64x2N.valR x{1}, W64x2N.valR  p{1}). progress. smt(@W64x2N). smt(@W64x2N).
auto.
proc.
(ecall {1} (dbn_cmov_correct cf{1} z{1} x{1})).  simplify.
conseq (_:  ( (W64x2N.valR (if cf{1} then x{1} else z{1}))%W64x2N = r{2} )). progress.
inline ASpecFp.ctseln. wp.   simplify.
seq 4 0 : ((W64x2N.valR p{1})%W64x2N = p{2} /\ (W64x2N.valR x{1})%W64x2N = a{2} /\ z{1} = x{1} /\ 0 <= p{2}  ).
(ecall {1} (dbn_copy_correct x{1})).  wp. skip. progress.
seq 3 1 : (cf{1} = c{2} /\ W64x2N.valR z{1} = x{2}
  /\ (W64x2N.valR p{1})%W64x2N = p{2} /\ (W64x2N.valR x{1})%W64x2N = a{2}  /\ 0 <= p{2}).
call  dsubc_spec.  wp. skip. progress.
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



equiv daddm_spec_eq:
 M.daddm ~ ASpecFp.addm:
    W64x2N.valR a{1} = a{2} /\  W64x2N.valR b{1} = b{2} /\  W64x2N.valR p{1} = p{2}
 /\ 0 <= a{2} < p{2} /\ 0 <= b{2} < p{2} /\ 0 <= 2*p{2} < W64x2N.modulusR
  ==> W64x2N.valR res{1} = res{2}.
proof.
transitivity CSpecFp.daddm
 (W64x2N.valR a{1} = a{2} /\ W64x2N.valR b{1} = b{2} /\ W64x2N.valR p{1} = p{2} /\ 0 <= a{2} < p{2} /\ 0 <= b{2} < p{2} /\ 0 <= 2*p{2} < W64x2N.modulusR ==> W64x2N.valR res{1} = res{2} )
 (={a,b,p} /\ 0 <= a{2} < p{2} /\ 0 <= b{2} < p{2} /\ 0 <= 2*p{2} < W64x2N.modulusR ==> res{1}=  res{2}).
  progress. simplify. smt(). smt().
+ proc; simplify.
  call dcminus_spec.
  exists* a{1}. elim*. move => a_L.
  exists* b{1}. elim*. move => b_L.
  call {1} (daddc_ph a_L b_L). inline*. wp. skip. progress. smt(@W64x2N).  
+ symmetry; conseq daddm_eq.  progress. smt(). smt(). smt(). smt(). 
qed.



lemma dbn_addm_correct aa bb pp:
  phoare[ M.daddm : a = aa /\ b = bb /\ p = pp /\ 0 <= W64x2N.valR a < W64x2N.valR p /\ 0 <= W64x2N.valR b < W64x2N.valR p /\ 0 <= 2* (W64x2N.valR p) < W64x2N.modulusR  ==> (W64x2N.valR aa + W64x2N.valR bb)%% (W64x2N.valR pp) = W64x2N.valR res ] = 1%r.
proof. bypr. progress.
 have <- : Pr[ASpecFp.addm(W64x2N.valR a{m}, W64x2N.valR b{m}, W64x2N.valR p{m}) @ &m : (W64x2N.valR a{m} + W64x2N.valR b{m}) %% W64x2N.valR p{m} =  res] = 1%r. 
  byphoare (_: arg = (W64x2N.valR a{m}, W64x2N.valR b{m}, W64x2N.valR p{m}) ==> _).
proc. wp. skip. smt(). auto. auto.
byequiv. conseq daddm_spec_eq.
smt(). smt(). auto. auto.
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
        1 <= i{2} <= dnlimbs /\ !_of{2} /\ aux{1} = dnlimbs).
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
wp. while ( #pre /\ ={i} /\ (aux,_zero){1}=(dnlimbs-1,W64.zero) /\ 
            0 <= i{2} <= dnlimbs-1 /\ kk{1} = k{2}).
 wp; skip => />; smt(Array128.get_setE Array128.set_set_if).
wp; skip; smt(Array128.get_setE Array128.set_set_if).
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
+ proc; simplify. wp.
  while ( #pre /\ (i,_zero,of_0,cf){1}=(k,W64.zero,_of,_cf){2} /\ bp{1} = b{2} /\ rp{1} = r{2} /\
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
seq 4 0 : ((W64x2N.valR p{1})%W64x2N = p{2} /\ (W64x2N.valR x{1})%W64x2N = a{2} /\ z{1} = x{1} /\ 0 < p{2}).
(ecall {1} (dbn_copy_correct x{1})).  wp. skip. progress.
seq 3 1 : (cf{1} = c{2} /\ W64x2N.valR z{1} = x{2} 
  /\ (W64x2N.valR p{1})%W64x2N = p{2} /\ (W64x2N.valR x{1})%W64x2N = a{2} /\ 0 < p{2}).
call  dsubc_spec.  wp. skip. progress.
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

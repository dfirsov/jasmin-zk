require import Core Int Ring IntDiv StdOrder List Distr Real RealExp.
import Ring.IntID IntOrder.

require import BigNum_spec BigNum_proofs.

require import BarrettRedInt BarrettReduction_Abstract BarrettReduction_Concrete.

require import W64_SchnorrExtract.
import W64xN.
import W64x2N.


equiv mulm_cspec:
 M(Syscall).bn_mulm ~ CSpecFp.mulm:
  valR a{1} = a{2}
  /\ valR p{1} = p{2}
  /\ valR b{1} = b{2}
  /\ valR a{1} < p{2}
  /\ valR b{1} < p{2}
  /\ ImplZZ p{1} p{2}
  /\ valR r{1} = ri_uncompute p{2}
   ==> valR res{1} =  res{2} .
proc. 
call bnreduce_spec.
ecall (muln_spec a{1} b{1}).
wp. skip.
move => &1 &2 H1. split. smt().
move => q1 r1 r2 r3 . split. simplify. rewrite - r3.
smt(@W64xN @W64x2N).
   split.  simplify. smt().
split. simplify. smt.
split.  smt (@W64xN).
split.  smt (W64xN.R.bnk_cmp). simplify. smt(@W64x2N).
qed.


lemma bn_mulm_correct aa bb pp:
  phoare[ M(Syscall).bn_mulm : a = aa /\ b = bb /\ p = pp /\ 0 <= valR a < valR p /\ valR r = ri_uncompute (valR p) /\ 0 <= valR b < valR p 
    ==> (valR aa * valR bb)%% (valR pp) = valR res ] = 1%r.
proof. bypr. progress.
 have <- : Pr[CSpecFp.mulm(valR a{m}, valR b{m}, valR p{m}) @ &m : (valR a{m} * valR b{m}) %% valR p{m} =  res] = 1%r. 
  byphoare (_: arg = (valR a{m}, valR b{m}, valR p{m}) ==> _).
proc. inline*. wp. skip. smt(). auto. auto.
byequiv. conseq mulm_cspec. smt.
smt.
smt(). smt(). 
qed.

lemma bn_mulm_correct_pr &m a b p r:
  W64xN.valR a < W64xN.valR p
  => W64xN.valR b < valR p
  => W64x2N.valR r = ri_uncompute (valR p)
  => Pr[ M(Syscall).bn_mulm(r,p,a,b) @&m : (valR a * valR b) %% (valR p) = valR res ] = 1%r.
proof. progress.
byphoare (_: arg = (r,p,a,b) ==> _).
conseq (bn_mulm_correct a b p). 
progress.
smt(@W64xN).
smt(@W64xN).
auto.
auto.
qed.

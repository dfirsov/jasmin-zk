require import Core Int Ring IntDiv StdOrder List Distr Real RealExp.
import Ring.IntID IntOrder.

require import BarrettRedInt Ring_ops_spec.


equiv mulm_eq:
 CSpecFp.mulm ~ ASpecFp.mulm: 
  a{1} = Zp.asint a{2} /\ b{1} = Zp.asint b{2} /\ p{1} = Zp.p
    ==> res{1} = Zp.asint res{2}.
proof.  proc. inline*. wp.  skip. progress.
smt(@Zp).
qed.


(* parameter for the Barrett reduction  *)
equiv redm_eq:
 ASpecFp.redm ~ CSpecFp.redm: ={a, p} /\ r{2} = (4 ^ k{2} %/ p{2}) 
  /\ 0 < p{2} < W64xN.modulusR
  /\ 0 <= a{2} < p{2} * p{2}
  /\ 0 < p{2} < 2 ^ k{2} 
  /\ 0 <= k{2} ==> ={res}.
proc. inline*. wp. skip. progress.
rewrite -  (barrett_reduction_correct a{2} p{2} k{2} ). auto. auto.  auto. 
rewrite /barrett_reduction. simplify. rewrite /ti. rewrite /ti'. rewrite /ri.
have ->: 2 ^ (2 * k{2}) = 4 ^ k{2}. smt(@Real).
have <-:  a{2} - a{2} * (4 ^ k{2} %/ p{2}) %/ 4 ^ k{2} * p{2}
 = (a{2} - a{2} * (4 ^ k{2} %/ p{2}) %/ 4 ^ k{2}  %%  2 ^ k{2} * p{2}) %% W64x2N.modulusR.
rewrite modz_small.
 have ->: a{2} * (4 ^ k{2} %/ p{2}) %/ 4 ^ k{2}  = ti' a{2} p{2} k{2}. 
  rewrite /ti. rewrite /ti'. rewrite /ri. auto.
have -> : ti' a{2} p{2} k{2} %% 2 ^ k{2} = ti' a{2} p{2} k{2}. 
rewrite modz_small. rewrite /ti'. split. 
apply divz_ge0. 
smt(exprn_ege1).
rewrite /ri. 
  have : 0 <= (4 ^ k{2} %/ p{2}). apply divz_ge0.  smt(). smt(exprn_ege1). smt().
  have ->: `|2 ^ k{2}| = 2 ^ k{2}. smt().
  have : (ti' a{2} p{2} k{2})%r < (2 ^ k{2})%r.
   rewrite - same_t'. auto. auto.
  have qq :  a{2}%r - 2%r * p{2}%r < (t' a{2}%r p{2}%r k{2}%r) * p{2}%r <= a{2}%r. 
   apply st6. smt(). split. smt().  move => ?. rewrite  exp_lemma1. auto. auto. smt(@Real).
  smt(). smt(). auto.
have -> : a{2} - a{2} * (4 ^ k{2} %/ p{2}) %/ 4 ^ k{2} * p{2}
 = ti a{2} p{2} k{2}. rewrite /ti. rewrite /ti'. rewrite /ri. auto.
split. 
   have : 0%r <= (ti a{2} p{2} k{2})%r < 2%r * p{2}%r.
   rewrite - same_t. auto. auto.
     apply (st8 a{2}%r p{2}%r k{2}%r _ _). split.  smt(). smt(). smt(exp_lemma1).
  progress. smt(). 
move => _.
have ->: `|W64xN.modulusR2| = W64xN.modulusR2. rewrite /W64xN.modulusR2. smt(@Ring).
   have : 0%r <= (ti a{2} p{2} k{2})%r < 2%r * p{2}%r.
   rewrite - same_t. auto. auto. 
     apply (st8 a{2}%r p{2}%r k{2}%r _ _). split. smt(). smt().
split. smt(). move => ?. smt(exp_lemma1).
  progress. 
   have : 2 * p{2} < W64xN.modulusR2. rewrite /W64xN.modulusR2. 
   have : W64x2N.M ^ (nlimbs) <= W64x2N.M ^ (2 * nlimbs).
   apply ler_weexpn2l. smt(). smt().
   have : p{2} <= W64x2N.M ^ nlimbs.
    have ->: W64x2N.M ^ nlimbs = W64xN.modulusR. rewrite /W64xN.modulusR. auto. smt().
smt(). smt().
 have ->: a{2} * (4 ^ k{2} %/ p{2}) %/ 4 ^ k{2}  = ti' a{2} p{2} k{2}. 
  rewrite /ti. rewrite /ti'. rewrite /ri. auto.
have -> : ti' a{2} p{2} k{2} %% 2 ^ k{2} = ti' a{2} p{2} k{2}. 
rewrite modz_small. rewrite /ti'. split. 
  have : 0 <= ri p{2} k{2} %/ 4 ^ k{2}. apply divz_ge0. smt(exprn_ege1). rewrite /ri.
  apply divz_ge0.  smt(). smt(exprn_ege1). smt(). 
  have ->: `|2 ^ k{2}| = 2 ^ k{2}. smt().
  have : (ti' a{2} p{2} k{2})%r < (2 ^ k{2})%r.
   rewrite - same_t'. auto. auto.
  have qq :  a{2}%r - 2%r * p{2}%r < (t' a{2}%r p{2}%r k{2}%r) * p{2}%r <= a{2}%r.
   apply st6. smt().  split. smt(). move => ?. smt(exp_lemma1).
  smt().
  smt(). auto.
smt().
auto.
qed.

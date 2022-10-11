require import AllCore IntDiv CoreMap List.

require import JModel.
require import BitEncoding.
import BS2Int.

require import Fp_small.
require import Fp_small_proof.
require import W64_exp_proof_1.
require import W64_exp_proof_2.
require import W64_exp_proof_3.
require import W64_exp_proof_4.
require import W64_exp_proof_5.
require import W64_exp_proof_6.

import Zp.
import IterOp.

module M7 = {
  proc expm_spec (x:W64.t, n:W64.t) : W64.t = {
    return (x ^ (W64.to_uint n)) % W64_exp_proof_1; 
  }  
}.

import IterOp.

lemma iii : forall i, 0 <= i => forall  b,
  iterop (i + 1) ( *** ) b W64.one = b *** iterop i ( *** ) b W64.one.
apply intind.
progress. smt.
progress. 
rewrite /iterop. 
simplify. rewrite iteriS. auto. simplify. 
have ->: (i + 2) = (i+1) + 1. smt().
rewrite iteriS. smt().
rewrite iteriS. smt().
simplify. smt().
qed.

lemma kk     :  forall (n : int), 0 <= n => forall (a : zp) (b : W64.t),
  ImplFp b a =>
  ImplFp (b ^ n)%W64_exp_proof_1 (inzp (asint a ^ n)).
apply intind. progress. 
smt.
progress.
have ->: (b ^ (i + 1))%W64_exp_proof_1 = b *** (b ^ i)%W64_exp_proof_1.
rewrite /(^). 
  have ->: i + 1 < 0 = false. smt(). simplify.
  have ->: i  < 0 = false. smt(). simplify.
rewrite /iterop. simplify.
rewrite - (iii i). auto. rewrite /iterop. simplify. auto.
have ->: inzp (asint a ^ (i + 1)) =  inzp (asint a * (asint a ^ i)).
smt.
have ->:  inzp (asint a * (asint a ^ i)) = (inzp (asint a)) * (inzp (asint a ^ i)).
smt.
rewrite - H1.
have ->: asint (inzp (to_uint b) * inzp (to_uint b ^ i))
  = (asint (inzp (to_uint b)) * (asint  (inzp (to_uint b ^ i)))) %% P.
smt.
have ih :  ImplFp (b ^ i)%W64_exp_proof_1  (inzp (to_uint b ^ i)).
rewrite H1. apply H0. auto.
rewrite - ih.
have ->: asint (inzp (to_uint b)) = to_uint b. smt.
have ->: to_uint (b *** (b ^ i)%W64_exp_proof_1) =  (to_uint b) * (to_uint (b ^ i)%W64_exp_proof_1) %%P.
rewrite /( *** ).
smt.
auto.
qed.


lemma exp_real_speacc :
 equiv[ ASpecFp.expm ~ M7.expm_spec  : 
    ImplFp arg{2}.`1 arg{1}.`1 /\ arg{2}.`2 = arg{1}.`2 ==> ImplFp res{2} res{1}].
proc. 
wp.  skip.  progress.
apply kk.
smt.
auto.
qed.


lemma exp_real_speac2 :
 equiv[ M7.expm_spec ~ M1.expm_spec   : arg{1}.`1 = arg{2}.`1 /\ W64.to_uint arg{1}.`2 = tonat arg{2}.`2 ==> ={res}] .
proc. skip. progress.
smt().
qed.


lemma exp_real_speac :
 equiv[ ASpecFp.expm ~ M.expm  : ImplWord arg{2}.`1 P 
   /\  ImplFp  arg{2}.`2 arg{1}.`1
   /\ arg{1}.`2 =  arg{2}.`3
     ==> ImplFp res{2} res{1} ].
transitivity M7.expm_spec
  (ImplFp arg{2}.`1 arg{1}.`1 /\ arg{2}.`2 = arg{1}.`2 ==> ImplFp res{2} res{1})
  (ImplWord arg{2}.`1 P 
   /\  arg{1}.`1 = arg{2}.`2
   /\  arg{1}.`2 =  arg{2}.`3
     ==> ={res}).
smt().
smt().
conseq exp_real_speacc. 
transitivity M1.expm_spec  
  (arg{1}.`1 = arg{2}.`1 /\ W64.to_uint arg{1}.`2 = tonat arg{2}.`2 ==> ={res})
  (ImplWord arg{2}.`1 P 
   /\  arg{1}.`1 = arg{2}.`2
   /\ tonat arg{1}.`2 = W64.to_uint arg{2}.`3
   /\ size arg{1}.`2 = 64
     ==> ={res}).
progress. 
exists (x{1}, w2bits n{2}).
progress.
smt().
smt().
smt().
conseq exp_real_speac2. 
conseq exp_real_speac.
qed.


pragma Goals:printall.
require import AllCore DBool Bool List Distr.
require import FS_Basics.

import ZMR.

section.

(* completeness in Hoare Logic (does not ensure termination)  *)
local lemma qr_complete_h ya wa : completeness_relation ya wa
   => hoare [ Completeness(HP,HV).run : arg = (ya,wa) ==> res ].
move => [qra invrtbl].
proc. inline*.  wp.
rnd. wp.  rnd.  wp.
skip.  simplify. progress.  simplify. apply ZModpRing.unitrM. smt (zmod_distr_inv).
have -> : s{hr}  = (w{hr} * w{hr}).
apply qra. 
have ->: ch. clear H0. smt(). 
simplify.
smt(@ZMR).
smt(@ZMR).
qed.

(* one-round completeness *)
lemma qr_completeness: forall (statement:qr_stat) (witness:qr_wit) &m,
  completeness_relation statement witness =>
  Pr[Completeness(HP,HV).run(statement, witness) @ &m : res] = 1%r.
move => s w &m [qr invrtbl]. byphoare (_: arg = (s, w) ==> _);auto.
proc*.
seq 1 : true 1%r 1%r 1%r 0%r r.
call (qr_complete_h s w). auto.
conseq (_: true ==> true). inline*. sp.
wp.  progress. rnd. simplify.
conseq (_: true ==> true). smt(@Distr).
wp.  rnd. skip. simplify.
progress. apply zmod_distr_weight. auto. auto. auto.
qed.

(* iterated completeness *)
lemma qr_completeness_iter: forall (statement:qr_stat) (witness:qr_wit) &m n,
        1 <= n =>
       completeness_relation statement witness =>
      Pr[CompletenessAmp(HP,HV).run(statement, witness,n) @ &m : res] = 1%r.
progress.
apply (PerfectCompleteness.completeness_seq HP HV).
progress.
apply qr_completeness. auto. auto. auto.
qed.

end section.

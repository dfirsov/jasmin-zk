require import AllCore Distr Real List.

require import RejectionSamplingModule.
require import RejectionSamplingCorrectness.
require import RejectionSamplingIndexed.


lemma rsP &m P1 Q1 c1 : 
 Impl Q1 P1 => mu d (predC P1) < 1%r =>
  Pr[ RS.sample(P1, c1) @ &m : Q1 res.`2 ] = 
    (mu d Q1) / (1%r - (mu d (predC P1))).
apply ph_main.
qed.

lemma rs_lossless &m P1 c1 : mu d P1 > 0%r =>
  Pr[ RS.sample(P1,c1) @ &m : P1 res.`2 ] = 1%r.
apply rj_lossless.
qed.

lemma rs_index &m P1 Q1 : 
 Impl Q1 P1 => forall i ,  0 <= i =>
  Pr[ RS.sample(P1,0) @ &m : Q1 res.`2 /\ res.`1 = i + 1 ] 
  = (mu d (predC P1)) ^ i *  (mu d Q1).
apply prob.
qed.

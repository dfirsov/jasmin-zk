pragma Goals:printall.
require import Distr Real List AllCore.

require import RejectionSamplingModule.

lemma rj_eq1 : 
 equiv [RS.sample ~ RS.sample1 
   : ={arg} ==> ={res} ].
proof. 
proc.
unroll {1} 3. inline RS.sample. 
sp.  rcondt {1} 1. auto. 
seq 3 2 : (={x, P, c} /\ b{1} = P{2} x{2}).
wp. rnd. skip. progress.
exists* x{1}. elim*. progress.
case (P{1} x_L).
rcondf {2} 1. progress.  wp. 
rcondf {1} 1. progress. skip. auto.
rcondt {2} 1. progress.
sp. wp. 
unroll {1} 1. unroll {2} 1.
rcondt {1} 1. progress.
rcondt {2} 1. progress.
sim.
qed.


lemma ph_l &m P1 Q1 c1 :
  phoare[ RS.sample : arg.`1 = P1 ==> Q1 res.`2 ] 
   = (Pr[ RS.sample(P1, c1) @ &m : Q1 res.`2 ]).
bypr. move => &m0 q. rewrite q.
byequiv (_: arg{1}.`1 = arg{2}.`1 ==> _). proc. 
unroll {1} 3.
unroll {2} 3.
rcondt {1} 3. progress. wp. auto.
rcondt {2} 3. progress. wp. auto.
while (={x,b,P}). auto. wp. rnd. wp. skip. progress. smt().
auto. 
qed.


lemma ph_l2  &m P1 Q1 c1 : Impl Q1 P1 =>
  Pr[ RS.sample1(P1, c1) @ &m : Q1 res.`2 /\ RS.flag = true ] 
  = (mu d (predC P1)) * Pr[ RS.sample(P1,c1) @ &m : Q1 res.`2 ].
move => H.
byphoare (_: arg = (P1, c1) ==> _). proc. sp.
seq 1 : (!P1 x) (mu d (fun x => ! P1 x)) (Pr[RS.sample(P1,c1) @ &m : Q1 res.`2])
 (mu d P1) 0%r (c1 = c /\ P1 = P /\ RS.flag = false).
rnd. skip. auto.
rnd. skip. progress. 
rcondt 2. auto.
call (ph_l &m P1 Q1 c1). auto.  simplify. auto.
hoare. 
rcondf 2. wp. skip.  simplify.  smt().
wp. skip. smt().
progress. progress.  auto. 
qed.

lemma ph_l3  &m P1 Q1 c1 : Impl Q1 P1 =>
  Pr[ RS.sample1(P1, c1) @ &m : Q1 res.`2 /\ RS.flag = false ] 
  = (mu d Q1). 
move => H.
byphoare (_: arg.`1 = P1 ==> _). proc. sp.
seq 1 : (Q1 x) (mu d Q1) 1%r
 (mu d P1) 0%r (P1 = P /\ RS.flag = false).
rnd. skip. auto.
rnd. skip. progress. 
rcondf 2. wp. auto. smt(). wp. skip.  auto.
exists* x. elim*. move => xx.
case (P1 xx).
rcondf 2. wp. skip. progress. hoare. wp. skip. smt().
rcondt 2. wp. skip.  progress. hoare.  
inline*. wp.  while (RS.flag = true). wp.  rnd. skip.
progress. wp.  skip. auto. auto. auto. auto.
qed.
  
lemma ph_l4 &m P1 Q1 :
  Pr[ RS.sample1(P1) @ &m : Q1 res ] 
 = Pr[ RS.sample(P1) @ &m : Q1 res ].
byequiv (_: ={arg} ==> _). symmetry. conseq rj_eq1. auto.
auto. auto. auto.
qed.

lemma ph_l5  &m P1 Q1 c1 : Impl Q1 P1 =>
  Pr[ RS.sample1(P1,c1) @ &m : Q1 res.`2 ] 
  =  (mu d (predC P1)) * Pr[ RS.sample(P1,c1) @ &m : Q1 res.`2 ]     + (mu d Q1).
progress.
rewrite Pr[mu_split RS.flag = true]. 
rewrite ph_l2. auto.
have ->: Pr[RS.sample1(P1,c1) @ &m : Q1 res.`2 /\ RS.flag <> true] 
  = Pr[RS.sample1(P1,c1) @ &m : Q1 res.`2 /\ RS.flag = false].
rewrite Pr[mu_eq]. smt(). auto.
rewrite ph_l3.
auto. auto.
qed.


lemma ph_l6 &m P1 Q1 c1 : Impl Q1 P1 =>
  Pr[ RS.sample(P1,c1) @ &m : Q1 res.`2 ] 
  = (mu d (predC P1)) * Pr[ RS.sample(P1,c1) @ &m : Q1 res.`2 ]
    + mu d Q1.
move => H.
rewrite - ph_l5. auto. 
rewrite   (ph_l4 &m (P1, c1) (fun (x : int * X) => Q1 x.`2) ). auto.
qed.


lemma ph_main &m P1 Q1 c1 : Impl Q1 P1 => mu d (predC P1) < 1%r =>
  Pr[ RS.sample(P1, c1) @ &m : Q1 res.`2 ] = 
 (mu d Q1) / (1%r - (mu d (predC P1))).
proof. move => iqp.
pose p := Pr[RS.sample(P1,c1) @ &m : Q1 res.`2].
pose q := mu d Q1.
pose x := mu d (predC P1).
move => xnon1.
have E1 : p = x * p + q.
 apply ph_l6. auto.
have E2 : p = x^2 * p + x*q + q.
 smt(@Real). clear E1.
have E3 : p - x^2*p = x * q + q.
 smt(@Real). clear E2.
have E4 : p * (1%r - x^2) = q * (1%r + x).  
 smt(@Real). clear E3.
have E5 : p * (1%r - x) * (1%r + x) = q * (1%r + x) . 
 smt(@Real). clear E4.
have xnz : x <> -1%r. rewrite /x.  smt(@Distr).
have E6 : p * (1%r - x) = q.  
 smt(@Real).  clear E5.
smt(@Real).
qed.


lemma rj_lossless &m P1 c1 : mu d P1 > 0%r =>
  Pr[ RS.sample(P1,c1) @ &m : P1 res.`2 ] = 1%r.
progress.
have s1 :   Pr[ RS.sample(P1,c1) @ &m : P1 res.`2 ] 
  = (mu d (predC P1)) * Pr[ RS.sample(P1,c1) @ &m : P1 res.`2 ]
    + mu d P1.
apply ph_l6. auto.
have s2 : Pr[RS.sample(P1,c1) @ &m : P1 res.`2] -
   mu d (predC P1) * Pr[RS.sample(P1,c1) @ &m : P1 res.`2] = mu d P1.
smt(@Real). clear s1.
have s3 : Pr[RS.sample(P1,c1) @ &m : P1 res.`2] * (1%r - mu d (predC P1))  = mu d P1. smt.
have s4:  Pr[RS.sample(P1,c1) @ &m : P1 res.`2] * mu d P1  = mu d P1.
 have yy : (1%r - mu d (predC P1)) 
   = mu d P1. smt(@Distr dll). smt(@Distr).
smt().
qed.


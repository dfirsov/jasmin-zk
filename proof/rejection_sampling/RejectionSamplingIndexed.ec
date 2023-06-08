pragma Goals:printall.
require import AllCore Distr Real List.

require RejectionSamplingModule.

clone import RejectionSamplingModule as RSM.


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
rcondf {2} 1. progress. 
rcondf {1} 1. progress. skip. auto.
rcondt {2} 1. progress.
sp. wp. 
unroll {1} 1. unroll {2} 1.
rcondt {1} 1. progress.
rcondt {2} 1. progress.
sim.
qed.


lemma ph_l &m P1 Q1 c1 i :
  phoare[ RS.sample : arg = (P1, c1) ==> Q1 res.`2 /\ res.`1 = i ] 
   = (Pr[ RS.sample(P1,c1) @ &m : Q1 res.`2 /\ res.`1 = i ]).
bypr. move => &m0 q. rewrite q.
byequiv (_: ={arg} ==> _). proc. 
unroll {1} 3.
unroll {2} 3.
rcondt {1} 3. progress. wp. auto.
rcondt {2} 3. progress. wp. auto.
while (={c,x,b,P}). auto. wp. rnd. wp. skip. progress.
auto. auto.
qed.


lemma ph_l2  &m P1 Q1 c1 i : Impl Q1 P1 =>
  Pr[ RS.sample1(P1,c1) @ &m : Q1 res.`2 /\ RS.flag = true /\ res.`1 = i ] 
  = (mu d (predC P1)) * Pr[ RS.sample(P1,c1+1) @ &m : Q1 res.`2 /\ res.`1 = i ].
move => H.
byphoare (_: arg = (P1 ,c1) ==> _). proc. sp.
seq 1 : (!P1 x) (mu d (fun x => ! P1 x)) (Pr[RS.sample(P1,c1+1) @ &m : Q1 res.`2 /\ res.`1 = i])
 (mu d P1) 0%r (c1 = c /\ P1 = P /\ RS.flag = false).
rnd. skip. auto.
rnd. skip. progress. 
sp. elim*. progress. rcondt 1. auto.
call (ph_l &m P1 Q1 (c1  + 1) i). auto.  simplify.
progress. 
hoare. 
rcondf 2. wp. skip.  simplify.  smt().
wp. skip. smt().
progress. auto. auto.
qed.

lemma ph_l3  &m P1 Q1 c1 : Impl Q1 P1 =>
  Pr[ RS.sample1(P1, c1) @ &m : Q1 res.`2 /\ RS.flag = false ] 
  = (mu d Q1). 
move => H.
byphoare (_: arg = (P1, c1) ==> _). proc. sp.
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
  
lemma ph_l4 &m P1 Q1 c1 i :
  Pr[ RS.sample1(P1,c1) @ &m : Q1 res.`2 /\ res.`1 = i ] 
 = Pr[ RS.sample(P1,c1) @ &m : Q1 res.`2 /\ res.`1 = i ].
byequiv (_: ={arg} ==> _). symmetry. conseq rj_eq1. auto.
auto. auto. auto.
qed.


lemma ph_l5''  &m P1 Q1  : 
   Pr[RS.sample(P1, 0) @ &m : Q1 res.`2 /\ res.`1 = 0] = 0%r.
have :    Pr[RS.sample(P1, 0) @ &m : res.`1 = 0] = 0%r.
byphoare (_: arg = (P1, 0) ==> res.`1 = 0);auto. hoare.
proc.  simplify.
unroll 3. rcondt 3. wp. skip.  auto.
while (0 < c). wp. rnd. skip. smt().
wp. rnd. wp. skip. auto. smt().
smt(@Distr).
qed.

    
lemma ph_l5'  &m P1 Q1 c1 i : 0 <= c1 => Impl Q1 P1 =>
  Pr[ RS.sample(P1,c1+1) @ &m : Q1 res.`2 /\ res.`1 = (i+1) ] 
   = Pr[ RS.sample(P1,c1) @ &m : Q1 res.`2 /\ res.`1 = i ] .
progress. 
byequiv (_: ={P} /\ c{2} + 1 = c{1}  ==> _).
proc.
sp.  while (={P, x, b} /\ c{2} + 1 = c{1}   ).
wp. rnd. skip. progress. skip. progress. smt().
progress.  auto.
qed.

lemma ph_l5g'  &m P1 Q1 c1 i : 
  Pr[ RS.sample(P1,c1) @ &m : Q1 res.`2 /\ res.`1 = i ] 
   = Pr[ RS.sample(P1,c1 -1) @ &m : Q1 res.`2 /\ res.`1 = i - 1 ] .
progress. 
byequiv (_: ={P} /\ c{2} + 1 = c{1}  ==> _).
proc.
sp.  while (={P, x, b} /\ c{2} + 1 = c{1}   ).
wp. rnd. skip. progress. skip. progress. smt().
progress.  
qed.


lemma ph_l5'''  &m P1  c1 i : c1 < i - 1 =>
  Pr[RS.sample1(P1, c1) @ &m :  res.`1 = i /\ RS.flag = false]
  = 0%r. 
progress.
byphoare (_: arg = (P1, c1) ==> _).
hoare. proc.
seq 3 : (RS.flag = false /\ c < i). wp. rnd. wp. skip. 
progress. smt().
case (P x). 
rcondf 1. auto. skip. progress. smt().
rcondt 1. auto. sp. elim*. progress.
inline*.  sp. wp.
while (RS.flag = true). wp. rnd. skip. auto.
skip. auto. auto. auto. qed.


lemma ph_l5  &m P1 Q1 c1 i :  c1 < i - 1 => Impl Q1 P1 =>
  Pr[ RS.sample(P1,c1) @ &m : Q1 res.`2 /\ res.`1 = i ] 
  =  (mu d (predC P1)) * Pr[ RS.sample(P1,c1) @ &m : Q1 res.`2 /\ res.`1 = (i - 1) ].
have ->: Pr[ RS.sample(P1,c1) @ &m : Q1 res.`2 /\ res.`1 = (i - 1) ]
 = Pr[ RS.sample(P1,c1 + 1) @ &m : Q1 res.`2 /\ res.`1 = i ].
 rewrite (ph_l5g' &m P1 Q1 (c1 + 1)). auto.
rewrite - ph_l4.
progress.
rewrite Pr[mu_split RS.flag = true]. 
have -> : Pr[RS.sample1(P1, c1) @ &m : (Q1 res.`2 /\ res.`1 = i) /\ RS.flag = true]
 = Pr[ RS.sample1(P1,c1) @ &m : Q1 res.`2 /\ RS.flag = true /\ res.`1 = i ] .
rewrite Pr[mu_eq]. auto. auto.
rewrite ph_l2. auto.
have ->: Pr[RS.sample1(P1, c1) @ &m : (Q1 res.`2 /\ res.`1 = i) /\ RS.flag <> true]
 = 0%r. 
   have : Pr[RS.sample1(P1, c1) @ &m : (Q1 res.`2 /\ res.`1 = i) /\ RS.flag <> true] <=   Pr[RS.sample1(P1, c1) @ &m :  res.`1 = i /\ RS.flag = false]. 
  rewrite Pr[mu_sub]. smt(). auto. 
  rewrite ph_l5'''. auto. smt(@Distr). auto.
qed.

lemma ph_l6  &m P1 Q1 c1 i :  c1 = i - 1 => Impl Q1 P1 =>
  Pr[ RS.sample(P1,c1) @ &m : Q1 res.`2 /\ res.`1 = i ] 
  =  (mu d Q1).
rewrite - ph_l4.
progress.
have ->:   Pr[ RS.sample1(P1,i-1) @ &m : Q1 res.`2 /\ res.`1 = i ] 
 =   Pr[ RS.sample1(P1,i-1) @ &m : Q1 res.`2 /\ RS.flag = false ] .
byequiv (_: ={arg} /\ arg{1} = (P1, i-1) ==> _). proc.
seq 3 3 : (={P, RS.flag, x , c} /\ RS.flag{1} = false /\ c{1} = i ).
wp. rnd. wp. auto. 
case (P{1} x{1}).
rcondf {1} 1. progress.
rcondf {2} 1. progress. skip. auto.
rcondt {1} 1. progress.
rcondt {2} 1. progress. 
sp. elim*. progress.
inline*.
wp. sp. 
unroll {1} 1.
unroll {2} 1.
rcondt {1} 1. progress.
rcondt {2} 1. progress. 
while (={x0, c0, b, P0} /\ RS.flag{2} = true /\ i < c0{1}).
wp. rnd. skip. progress. 
smt(). wp. rnd. skip. progress.  smt(). smt(). auto. auto.
apply ph_l3. auto.
qed.


lemma prob  &m P1 Q1 : Impl Q1 P1 => forall i ,  0 <= i =>
  Pr[ RS.sample(P1,0) @ &m : Q1 res.`2 /\ res.`1 = i + 1 ] 
  = (mu d (predC P1)) ^ i *  (mu d Q1).
move => H.
apply intind.
progress. rewrite ph_l6. auto. auto. smt(@Int).
progress. 
rewrite ph_l5. smt(). auto.
simplify. rewrite H1. smt(@RealExp @Real).
qed.

require import Core Int IntDiv Ring IntDiv StdOrder List Distr Real.
require import Ring_ops_spec.

require RejectionSampling.
clone import RejectionSampling as RS with type X <- int,
                                          op d <- D,
                                          op defX <- 0
proof*. 
realize dll. apply D_ll. qed.




op RSP (a:int) x =  x < a.
lemma rsample_pr1  a1  &m r : 
  Pr[CSpecFp.rsample(a1) @ &m : res = r]
  =  Pr[RS.sample(RSP a1, 0) @ &m : res = r].
byequiv (_: arg{1} = a1 /\ c{2} = 0 /\ P{2} = RSP a1  ==> _) .
proc. sp.
while (a{1} = a1 /\ P{2} = RSP a1 /\ i{1} = c{2} /\ b{1} = !b{2} /\ x{1} = x{2} ).
wp. inline*. wp.  rnd. skip. progress. rewrite /RSP.  
skip. progress. auto. auto.
qed.

lemma rsample_pr2  a1  &m PP : 
  Pr[CSpecFp.rsample(a1) @ &m : PP res]
  =  Pr[RS.sample(RSP a1, 0) @ &m : PP res].
byequiv (_: arg{1} = a1 /\ c{2} = 0 /\ P{2} = RSP a1  ==> _) .
proc. sp.
while (a{1} = a1 /\ P{2} = RSP a1 /\ i{1} = c{2} /\ b{1} = !b{2} /\ x{1} = x{2} ).
wp. inline*. wp.  rnd. skip. progress. rewrite /RSP.
skip. progress. auto. auto.
qed.


lemma rsample_pr_out a1 &m xx : ! (RSP a1 xx)
   =>  Pr[CSpecFp.rsample(a1) @ &m : res.`2 = xx ] = 0%r.
progress.  byphoare (_: arg = a1 ==> _). hoare.
simplify. proc. 
while (a = a1 /\ (b /\ i <> 0 => a <= x) /\ (!b => x < a) ).
wp. inline ASpecFp.subn. wp. rnd.
skip. progress. smt(@Distr). wp. skip.  progress.  smt.
auto. auto. qed.

lemma rsample_pr a1 &m i x : 1 <= i => RSP a1 x =>
    Pr[CSpecFp.rsample(a1) @ &m : res = (i,x) ]
     = (mu D (predC (RSP a1)) ^ (i - 1) * mu D (pred1 x)).
progress.
rewrite rsample_pr1.
have ->: Pr[RS.sample(RSP a1, 0) @ &m  : res = (i, x)] 
 = Pr[RS.sample(RSP a1, 0) @ &m : res.`2 = x /\ res.`1 = i]. 
rewrite Pr[mu_eq]. smt(). auto.
rewrite   (Indexed.prob  &m (RSP a1) (fun z => z = x) _ (i - 1) _).
progress.  auto. smt(). congr. simplify. smt(@Distr).
qed.

require import AuxLemmas.

(* need to prove what Top.M equals to (W64x2N.modulusR ?) *)
lemma rsample_uni &m x P : P < M =>  0 <= x =>  RSP P x =>
    Pr[CSpecFp.rsample(P) @ &m : res.`2 = x ]
     = 1%r / P%r.
move => H1 H2 H3.
rewrite  (rsample_pr2 P &m (fun (rres : int * int) => rres.`2 = x)). 
simplify.
rewrite (Correctness.ph_main  &m (RSP P)  (fun rres => rres = x) ). smt().
 have -> : mu D (predC (RSP P)) = 1%r - mu D (RSP P).
rewrite mu_not.  smt. 
 have q : mu D (RSP P) > 0%r. 
 apply witness_support.
  exists 0. smt.
 smt.
have -> : mu D (transpose (=) x) = 1%r / M%r. apply  D_mu. 
have : x < M. smt(). smt (D_sup).
have -> : mu D (predC (RSP P)) = 1%r - mu D ((RSP P)).  
rewrite mu_not. rewrite /weight.
rewrite is_losslessP. apply D_ll. smt().
have -> : mu D (RSP P) = P%r / M%r. rewrite /RSP.
have -> : mu D (transpose Int.(<) P)
 = mu D (LessThan P).
apply mu_eq_support.
smt (D_sup). 
rewrite (d_uni_sum D M _ _ _ P _ _). apply D_uni.
apply D_ll. move => x0. rewrite /LessThan. move => q. 
smt(D_sup).
smt. smt(). congr.
rewrite - (D_mu x _). 
 have : x < M. smt. smt(D_sup). simplify. 
rewrite mu1_uni_ll. apply D_uni. apply D_ll.
have -> : x \in D = true. 
 have : x < M. smt. smt(D_sup). simplify. smt().
smt.
qed.


lemma rsample_lossless a1 &m  : 0%r < mu D (RSP a1) =>
    Pr[CSpecFp.rsample(a1) @ &m : true ]
     = 1%r.
have ->: Pr[CSpecFp.rsample(a1) @ &m : true ]
  =  Pr[RS.sample(RSP a1, 0) @ &m : true ].
byequiv (_: arg{1} = a1 /\ c{2} = 0 /\ P{2} = RSP a1  ==> _) .
proc. sp.
while (a{1} = a1 /\ P{2} = RSP a1  /\ b{1} = !b{2} /\ x{1} = x{2} ).
wp. inline*. wp.  rnd. skip. progress. rewrite /RSP.
    skip. progress. auto. auto.
progress.
have xx : Pr[RS.sample(RSP a1, 0) @ &m : RSP a1 res.`2 ] = 1%r.
apply (Correctness.rj_lossless &m (RSP a1) 0 _) .  auto. 
smt(@Distr).
qed.


lemma rsample_lossless0 a1 &m P :  mu D (RSP a1) <= 0%r =>
    Pr[CSpecFp.rsample(a1) @ &m : P res ]
     = 0%r.
progress. byphoare (_: arg = a1 ==> _). hoare. simplify.
proc.
while(b /\ a = a1 ).  wp.
inline ASpecFp.subn. wp.  rnd. 
skip. progress.
smt(@Distr). auto. auto. 
auto. qed.


lemma rsample_lossless2 a1 &m  : 
    Pr[CSpecFp.rsample(a1) @ &m :  ! (res.`2 \in D) ]
     = 0%r.
byphoare (_: arg = a1 ==> _). hoare.  proc.
sp. while (x \in D). wp.  inline*. wp.  rnd. skip.
progress. skip. progress. smt. auto. auto.
qed.

lemma rsample_lossless3 a1 &m  : 0%r < mu D (RSP a1) =>
    Pr[CSpecFp.rsample(a1) @ &m : (res.`2 \in D)  ]
     = 1%r.
move => ass.
rewrite - (rsample_lossless a1 &m). 
auto.
have -> : Pr[CSpecFp.rsample(a1) @ &m : true]
 = Pr[CSpecFp.rsample(a1) @ &m : res.`2 \in D]
  + Pr[CSpecFp.rsample(a1) @ &m : !(res.`2 \in D)].
rewrite Pr[mu_split (res.`2 \in D)] . auto.
rewrite rsample_lossless2. auto.
qed.


lemma rsample_lossless4 P &m  : 0 < P < M =>
    Pr[CSpecFp.rsample(P) @ &m : LessThan P res.`2  ]
     = 1%r.
move => PP.
rewrite - (Correctness.rj_lossless &m (RSP P) 0 _ ).  
 apply witness_support.
  exists 0. split. rewrite /RSP. smt. smt.
rewrite -   (rsample_pr2 P &m (fun (rres : int * int) => RSP P rres.`2)).
simplify.
have -> : Pr[CSpecFp.rsample(P) @ &m : RSP P res.`2]
 = Pr[CSpecFp.rsample(P) @ &m : res.`2 \in D /\ (RSP P res.`2)].
rewrite Pr[mu_split (res.`2 \in D)] . auto. 
have ->: Pr[CSpecFp.rsample(P) @ &m : RSP P res.`2 /\ (res.`2 \notin D)]
 = 0%r. timeout 15. smt. simplify.
rewrite Pr[mu_eq]. smt. auto.
rewrite Pr[mu_eq]. 
progress.  
rewrite /D.
apply supp_duniform.
have : res{hr}.`2 < M. smt.
smt.
smt(). smt(D_sup).
smt(). auto.
qed.


equiv rsample_eq P:
 CSpecFp.rsample ~ ASpecFp.rsample: 
  ={arg} /\ arg{1} = P /\ 0 < P < M ==> res{1}.`2 = res{2}.
proof.  
bypr res{1}.`2 res{2}. 
progress. move => &1 &2 aa [H ] H0. 
progress. rewrite - H.  rewrite  H0.
case (LessThan P aa). move => c1.
rewrite (rsample_uni &1 aa _ _). 
smt(). smt(). smt().
byphoare (_: arg = P ==> _). proc.
rnd. skip. simplify. move => &hr pa.
rewrite pa.
 rewrite duniform1E.
have -> : aa \in range 0 P = true. smt. simplify.
congr.  smt(@List). auto. auto.
move => c2.
have ->: Pr[CSpecFp.rsample(P) @ &1 : res.`2 = aa] = 0%r.
have ->: 
  Pr[CSpecFp.rsample(P) @ &1 : res.`2 = aa] = 
  Pr[CSpecFp.rsample(P) @ &1 : (res.`2 = aa) /\ ! LessThan  P res.`2].
rewrite Pr[mu_eq]. auto. auto. 
have : Pr[CSpecFp.rsample(P) @ &1 : LessThan P res.`2] = 1%r. apply rsample_lossless4. smt.
move => q. 
 have ops : Pr[CSpecFp.rsample(P) @ &1 : ! LessThan P res.`2] = 0%r.
 have : 1%r = Pr[CSpecFp.rsample(P) @ &1 : LessThan P res.`2]
     + Pr[CSpecFp.rsample(P) @ &1 : ! (LessThan P res.`2)] . 
  rewrite - (rsample_lossless P &1). 
 apply witness_support.
  exists 0. smt.
  rewrite Pr[mu_split (LessThan P res.`2)]. auto.
  smt.
timeout 15. smt.
byphoare (_: arg = P ==> _).
hoare. proc.
rnd. skip. move => &hr Q1 r0 Q2.
have : LessThan P r0. rewrite /LessThan. split.  smt(@Distr @DInterval @List).
progress. smt(@Distr @DInterval @List).
smt(). auto. auto.
qed.

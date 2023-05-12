pragma Goals:printall.
require import AllCore Distr List Binomial.
require import Ring StdRing StdOrder StdBigop Discrete RealSeq RealSeries RealLub.
(*---*) import IterOp Bigint Bigreal Bigreal.BRA.
(*---*) import IntOrder RealOrder RField.
require import Finite.
require (*--*) FinType.
require import RandomFacts.
require FiniteApproximation.

theory Avg.

type at. (* argument type *)
type rt. (* return type   *)
type at1, at2.

module type RunAvg = {
  proc main(r : at, i2 : at2) : rt
}.

module WorkAvg(A : RunAvg) = {
  proc main(d : at distr, i2 : at2) = {
    var r, b,i22,dd;
    i22 <- i2;
    dd <- d;
    r <$ dd;
    b <@ A.main(r,i22);
    return (b, r);
  }
}.



section.

local module WorkAvg'(A : RunAvg) = {
  proc main(d : at distr, i2 : at2) = {
    var r, b;
    r <$ d;
    b <@ A.main(r,i2);
    return r;
  }
}.


declare module A <: RunAvg.

clone import FiniteApproximation.FinApprox with type rt <- at,
                                                type at <-  at distr * at2.


local lemma finApproxCons &m d :  
  exists (D : at distr),  exists (J : int -> at option),
  (forall M, mu D M = Pr[ WorkAvg'(A).main(d) @ &m :  M res ])
  /\ enumerate J (support D)
  /\ (forall (epsilon : real), 0%r < epsilon 
        => exists (N : int), 
        Pr[ WorkAvg'(A).main(d)
           @ &m : ! (res \in (pmap J (range 0 N))) ] < epsilon).
elim (fin_approx_prog_no_glob (WorkAvg'(A)) &m d).
progress. exists D. exists J. progress.
qed.


local lemma be &m P d : Pr[WorkAvg(A).main(d) @ &m : P res.`2 ]
  = Pr[WorkAvg'(A).main(d) @ &m : P res ].
byequiv. proc. 
call (_:true).
rnd. wp. skip. progress. progress. auto.
qed.


local lemma ebse &m P d i2 : Pr[WorkAvg'(A).main(d,i2) @ &m : P res ] <= mu d P.
proof. byphoare (_: arg = (d , i2) ==> _). proc. 
seq 1 : (P r) (mu d P) 1%r 1%r 0%r.
rnd.  skip. auto.
rnd. skip. smt(). 
call (_: true ==> true). bypr.  move => &m0 _. rewrite Pr[mu_le1]. auto. skip. auto.
hoare.  call (_:true). skip. auto. auto. auto. auto.
qed.


local lemma hzc ['a] : forall (d : 'a distr),
     mu d (fun x => x \in d) = mu d predT.
proof. smt(@Distr). qed.


local lemma le7main &m (d : at distr) i2 :  
  exists (J : int -> at option) ,
  enumerate J (support d)
  /\ (forall (epsilon : real), 0%r < epsilon =>
  exists (N : int), Pr[ WorkAvg(A).main(d,i2)
                       @ &m : ! (res.`2 \in (pmap J (range 0 N))) ] < epsilon).
proof.
have : summable (mass d).
  have ->: mass d = mu1 d. 
   apply fun_ext. move => x. smt(massE).
  apply summable_mu1.
move => sd.
have :   exists (J : int -> at option) ,
  enumerate J (support (mass d)).
 apply (sum_to_enum (mass d) sd).
elim. move => j smd. exists j.
have : (support (mass d)) = (support d).
apply fun_ext. move => a. smt(@Distr).
move => ee. split. rewrite - ee. apply smd.
elim (finApproxCons &m (d,i2)). move => D J. progress.
have ejD : enumerate j (support D). 
apply (jokk D d). move => M. rewrite H. apply (ebse &m M d).
smt().
elim (H1 epsilon H2). move => N prep.
elim (prjokk D J j  ejD H0 N). 
move => N0 prop2. exists N0.
rewrite (be &m (fun r =>  !(r \in pmap j (range 0 N0)))).
have opm1 : Pr[WorkAvg'(A).main(d,i2) 
              @ &m : (fun (r : at) => ! (r \in pmap j (range 0 N0))) res] 
        = Pr[WorkAvg'(A).main(d,i2) 
            @ &m : res \in D /\ (fun r => !(r \in pmap j (range 0 N0))) res]. 
rewrite - (H (fun r => (r \in D) /\ (fun r => !(r \in pmap j (range 0 N0))) r)).
rewrite - (H (fun r => ! (r \in pmap j (range 0 N0)))). simplify. 
rewrite mu_and. smt(@Distr hzc).
rewrite opm1. 
have : Pr[WorkAvg'(A).main(d,i2) 
         @ &m : (res \in D) /\ (fun r => ! (r \in pmap j (range 0 N0))) res] 
    <= Pr[WorkAvg'(A).main(d,i2) 
         @ &m : res \in D /\ ! (res \in pmap J (range 0 N))].
rewrite Pr[mu_sub]. smt(). auto.
move => ineq.
have : Pr[WorkAvg'(A).main(d,i2) 
         @ &m : (res \in D) /\ ! (res \in pmap J (range 0 N))] 
     = Pr[WorkAvg'(A).main(d,i2) @ &m :  ! (res \in pmap J (range 0 N))].
rewrite - (H (fun r => (r \in D) /\ (fun r => ! (r \in pmap J (range 0 N))) r)).
rewrite - (H (fun r => ! (r \in pmap J (range 0 N)))). simplify. 
rewrite mu_and. smt(@Distr hzc).
smt().
qed.


local lemma oks' &m P d i2: 
  summable (fun r => (mu1 d r) * Pr[ A.main(r,i2) @ &m : P res ]).
simplify summable. exists 1%r.
move => J u. 
have oks : big predT (fun (i : at) => `|mu1 d i|) J <= 1%r.
have oks' : (fun (i : at) => `|mu1 d i|) = (fun (i : at) => mass d i).
apply fun_ext. move => i. rewrite massE. smt(@Distr).
rewrite oks'.
have ->: (fun (i : at) => mass d i) 
  = (fun (i : at) => mu1 d i). apply fun_ext. move => i. smt(massE).
rewrite -  mu_mem_uniq. auto. smt(@Distr).
have : big predT (fun i => `|mu1 d i * Pr[A.main(i,i2) @ &m : P res]|) J 
       <= big predT (fun i => `|mu1 d i|) J.
apply ler_sum_seq .
move => a aj _. simplify.
have : 0%r <= Pr[A.main(a,i2) @ &m : P res] <= 1%r.
rewrite Pr[mu_le1]. auto. rewrite Pr[mu_ge0]. auto.
elim.  move => q1 q2. 
rewrite abs1.
rewrite (abs2 (Pr[A.main(a,i2) @ &m : P res])). progress.
have : `|mu1 d a| >= 0%r. apply abs3.
move => q. smt().
smt().
qed.


local lemma oks'' &m P J (d : at distr) i2 :
 enumerate J (support d) =>
 enumerate J (support (fun (r : at) => mu1 d r * Pr[A.main(r,i2) @ &m : P res])).
move => ep.  split.
elim ep. progress.
simplify support.
elim ep. move => _ qq.
move => x xpr. apply qq.
smt(@Distr).
qed.


local lemma jk &m P d i2 : forall l,  uniq l =>
  big predT (fun (r : at) => mu1 d r * Pr[A.main(r,i2) @ &m : P res]) l
  = Pr[WorkAvg(A).main(d,i2) @ &m : P res.`1 /\ mem  l res.`2 ].
proof. apply list_ind. simplify.  rewrite Pr[mu_false]. smt().
move => x l. simplify.
move => ih ihp. 
have e : Pr[WorkAvg(A).main(d,i2) 
           @ &m : P res.`1 /\ (res.`2 = x \/ (res.`2 \in l))] = 
    Pr[WorkAvg(A).main(d,i2) 
      @ &m : (P res.`1 /\ res.`2 = x) \/ (P res.`1 /\ res.`2 \in l)].
rewrite Pr[mu_eq]. smt(). auto. rewrite e. clear e.
have e : Pr[WorkAvg(A).main(d,i2) 
           @ &m : P res.`1 /\ res.`2 = x \/ P res.`1 /\ (res.`2 \in l)] 
       = Pr[WorkAvg(A).main(d,i2) 
           @ &m : P res.`1 /\ res.`2 = x ] 
       + Pr[WorkAvg(A).main(d,i2) @ &m : P res.`1 /\ (res.`2 \in l)].
rewrite Pr[mu_disjoint]. smt(). auto. 
rewrite e. clear e.
have e : Pr[WorkAvg(A).main(d,i2) @ &m : P res.`1 /\ res.`2 = x] 
         = mu1 d x * Pr[A.main(x,i2) @ &m : P res].
byphoare (_: exists ga, ga = (glob A) /\ ga = (glob A){m} /\ arg = (d,i2)  ==> _). 
proc. elim*. move => ga. 
pose z := (Pr[A.main(x,i2) @ &m : P res]).
seq 2 : (ga = (glob A) /\ ga = (glob A){m} /\ (d,  i2) = (dd,  i22)) 
        1%r (mu1 d x * z) 0%r 0%r. 
wp. skip. auto.
wp. skip. 
have  zp :  z = Pr[A.main(x, i2) @ &m : P res]. smt().
progress.
seq 1 : (r = x) (mu1 d x) z 1%r 0%r 
        (glob A = ga /\ (glob A){m} = ga /\ i22 = i2 /\ d = d).  
sp. rnd. wp.  skip. progress. 
rnd. skip. progress. 
have pp : phoare [ A.main : arg = (x,i2) /\ glob A = (glob A){m} /\ (glob A) = ga 
                 ==> P res ] =  Pr[A.main(x,i2) @ &m : P res]. 
bypr. move => &m0 c. 
byequiv (_: (glob A){1} = ga /\ (glob A){2} = ga /\ ={r,i2} ==> _) . 
proc*. call (_:true). skip. progress. smt(). progress. 
call pp. skip. progress. smt(). 
hoare. call(_:true). skip. progress. smt(). smt(). hoare.  wp. skip. smt().
smt().
smt(). 
auto.
smt().
qed.     


local lemma oks &m P d i2 : 
  exists (J : int -> at option),
  enumerate J (support (fun r => (mu1 d r) * Pr[ A.main(r,i2) @ &m : P res ])) 
  /\ summable (fun r => (mu1 d r) * Pr[ A.main(r,i2) @ &m : P res ]) 
  /\ RealSeq.convergeto 
      (fun N => big predT (fun r => (mu1 d r) * Pr[ A.main(r,i2) @ &m : P res]) 
                          (pmap J (range 0 N))) 
      (Pr[ WorkAvg(A).main(d,i2) @ &m  : P res.`1 ]).
proof. elim (le7main &m d  i2). move => J. elim. progress. exists J.
split.
apply (oks'' &m P J d i2 H).
split. 
apply oks'.
move => epsilon eps_prop.
elim (H0 epsilon eps_prop).
move => N eq. exists N.
move => n npr.
rewrite jk. smt(@List).
have : Pr[WorkAvg(A).main(d,i2) @ &m : P res.`1 /\ (res.`2 \in pmap J (range 0 n))]
        <= Pr[WorkAvg(A).main(d,i2) @ &m : P res.`1].
rewrite Pr[mu_sub]. progress. auto.
move => obv.
have : `|Pr[WorkAvg(A).main(d,i2) 
           @ &m : P res.`1 /\ (res.`2 \in pmap J (range 0 n))] -
         Pr[WorkAvg(A).main(d,i2) @ &m : P res.`1]| 
        = Pr[WorkAvg(A).main(d,i2) @ &m : P res.`1] 
        - Pr[WorkAvg(A).main(d,i2) 
            @ &m : P res.`1 /\ (res.`2 \in pmap J (range 0 n))].
smt().
move => obve. rewrite obve.
have : Pr[WorkAvg(A).main(d,i2) @ &m : P res.`1] 
     - Pr[WorkAvg(A).main(d,i2) 
         @ &m : P res.`1 /\ (res.`2 \in pmap J (range 0 n))] 
     = Pr[WorkAvg(A).main(d,i2) 
         @ &m : P res.`1 /\ !(res.`2 \in pmap J (range 0 n))].
have ze : Pr[WorkAvg(A).main(d,i2) @ &m : P res.`1 ] 
        = Pr[WorkAvg(A).main(d,i2) 
            @ &m : P res.`1 /\ (res.`2 \in pmap J (range 0 n)) ] 
        + Pr[WorkAvg(A).main(d,i2) 
            @ &m : P res.`1 /\ !(res.`2 \in pmap J (range 0 n)) ]. 
rewrite Pr[mu_split (res.`2 \in pmap J (range 0 n))]. auto.
rewrite ze. smt().
move => ze. rewrite ze.
have : Pr[WorkAvg(A).main(d,i2) @ &m : P res.`1 /\ !(res.`2 \in pmap J (range 0 n))]
    <= Pr[WorkAvg(A).main(d,i2) @ &m : ! (res.`2 \in pmap J (range 0 N))].
rewrite Pr[mu_sub]. progress.  
have : forall m x, N <= m => x \in pmap J (range 0 N) => x \in pmap J (range 0 m). 
smt(@List).
move => zne. clear ze obve obv. clear H0 H.
smt (pmc). auto. smt().
qed.


lemma averaging &m M i d : 
  Pr[ WorkAvg(A).main(d,i) @ &m  : M res.`1 ] 
     = sum (fun x => (mu1 d x) * Pr[ A.main(x,i) @ &m : M res ]).
elim (oks &m M d i). move => J. elim. move => e s. elim s.
move => s c1.
have f2 :  RealSeq.convergeto 
            (fun N => big predT 
                       (fun r => (mu1 d r) * Pr[ A.main(r,i) @ &m : M res ]) 
                       (pmap J (range 0 N))) 
           (sum (fun r => (mu1 d r) * Pr[ A.main(r,i) @ &m : M res ])).
apply (summable_cnvto 
        (fun r => (mu1 d r) * Pr[ A.main(r,i) @ &m : M res ]) J 
        (support (fun r => (mu1 d r) * Pr[ A.main(r,i) @ &m : M res ]))). 
progress. auto. auto.
smt(@RealSeq).
qed.


end section.
end Avg.


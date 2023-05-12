pragma Goals:printall.
require import AllCore List Binomial.
require import Ring StdRing StdOrder StdBigop Discrete RealSeq RealSeries RealLub.
(*---*) import IterOp Bigint Bigreal Bigreal.BRA.
(*---*) import IntOrder RealOrder RField.
require import Finite.
require (*--*) FinType.
require import Distr.
require import RandomFacts.
require Reflection.

theory FinApprox.

section.

local lemma nosmt le3 ['a] : forall (d : 'a distr),  
   mu d predT = sum (fun (x : 'a) =>  mass d x).
proof.  progress. 
rewrite muE. rewrite /predT. simplify. smt(massE).
qed.

local lemma nosmt le4 ['a] :  forall (d : 'a distr),  
   summable (fun (x : 'a) => mass d x).
proof. progress.
exists 1%r. move => J ju. 
have  : isdistr (mass d). 
  have ->: (mass d) = mu1 d. smt(massE).
  apply isdistr_mu1. 
case.
move => id1 id2.
have e :  (fun (i : 'a) => `|mass d i|)
      = (fun (i : 'a) =>  mass d i).
apply fun_ext. move => i. 
smt().
rewrite e. 
apply (id2 J).
apply ju.
qed.


local lemma nosmt le5 ['a] :  forall (d : 'a distr), 
  exists (J : int -> 'a option),
  enumerate J (support (mass d)).
proof. progress.
apply sum_to_enum. apply le4.
qed.


local lemma nosmt le6 ['a] : forall (d : 'a distr), 
  exists (J : int -> 'a option),
  enumerate J (support (mass d)) /\
  mu d predT = lim (fun (n : int) => big predT (mass d) (pmap J (range 0 n))).
proof. progress. elim (le5 d). progress. 
exists J. progress.  rewrite - (sumE (mass d) J). apply H. apply le4. 
  have ->: (mass d) = mu1 d. smt(massE).
rewrite le3.  smt(massE).
qed.

search mu.
local lemma le7_convto ['a] : forall (d : 'a distr), 
  exists (J : int -> 'a option),
  enumerate J (support (mass d)) /\
    mu d predT = lim (fun (n : int) => big predT (mass d) (pmap J (range 0 n)))  /\
    RealSeq.convergeto (fun N => mu d (predC (mem (pmap J (range 0 N))))) 0%r.
proof. progress. elim (le6 d). progress. 
exists J. progress.
pose br := (fun (n : int) => big predT (mass d) (pmap J (range 0 n))).
pose brr := (fun (l : real) => (RealSeq.convergeto br l)).
case (exists (x : real), brr x).
move => eb.
have opp : RealSeq.convergeto br (lim br).
smt(@RealSeq).
move => epsilon H1.
have ik : exists (N : int), forall (n : int), N <= n => `|br n - (lim br)| < epsilon.
apply (opp epsilon H1).
elim ik.
move => N Np.
have ikkk :  lim br = mu d predT.
rewrite H0. auto.
have akk : forall n, br n  = big predT (mass d) (pmap J (range 0 n)).
auto.
have ikk : forall (n : int), N <= n => lim br - br n < epsilon.
rewrite ikkk.
move => n np. rewrite (akk n).
have jkl : forall (d : 'a distr)  l ,  uniq l => big predT (mass d) l = mu d (mem l).
move => d0. apply list_ind. simplify.  simplify big.
have ->: mem [] = (fun (x : 'a) => false). smt().
rewrite mu0. auto.
move => x l. simplify.
move => ih ihp. 
have e : mem (x :: l) = fun z => (z = x) \/ mem l z.
smt().
rewrite e.
rewrite (mu_disjoint d0 (pred1 x) (fun z => mem l z)).
move => p.
elim. move => p1 p2.
smt().
elim ihp. move => p1 p2.
rewrite - (ih p2).
have o : mu d0 (transpose (=) x) = mu1 d0 x. smt().
rewrite o. clear o.
have o : mu1 d0 x = mass d0 x . smt(massE).
rewrite o. clear o.
smt().
have get : big predT (mass d) (pmap J (range 0 n)) <= mu d predT.
rewrite (jkl d). smt(@List). smt(@Distr).
have ee : mu d predT - big predT (mass d) (pmap J (range 0 n))
 = `|mu d predT - big predT (mass d) (pmap J (range 0 n))|.
smt().
rewrite ee. clear ee.
have el : 
 `|mu d predT - big predT (mass d) (pmap J (range 0 n))| 
 =  `|big predT (mass d) (pmap J (range 0 n)) - mu d predT|.
smt(). rewrite el.
rewrite - ikkk.
 clear el. apply (Np n). apply np.
have kka : forall n, big predT (mass d) (pmap J (range 0 n)) 
         = mu d (mem (pmap J (range 0 n))).
move => n. 
have jj : (fun (x : 'a) => mass d x) 
    = (fun (x : 'a) => mass d x).
apply fun_ext. move => x. simplify. 
simplify. auto. 
have ooz : uniq ((pmap J (range 0 n))).
smt(@List).
rewrite (mu_mem_uniq d (pmap J (range 0 n)) ooz).
smt(massE).
have ak : forall (n : int), N <= n => mu d predT - (mu d (mem (pmap J (range 0 n)))) < epsilon.
smt().
have ykk : forall (n : int), N <= n =>  mu d predT - mu d (mem (pmap J (range 0 n)))  < epsilon.
move => n p.  apply (ak n p).
exists N.
have oli : forall n,  mu d (predC (mem (pmap J (range 0 n)))) = mu d predT - mu d (mem (pmap J (range 0 n))).
smt(@Distr).
move => n Nn.
rewrite oli.
simplify. smt().
move => sb.
have sb' : (forall (x : real), ! brr x). smt().
have f1 : mu d predT = 0%r.
rewrite H0.
simplify lim.
rewrite choiceb_dfl.
apply sb'.
auto. move => epsilon ep.
exists 0. 
have okl : pmap J (range 0 0) = []. smt(@List).
move => n n0. simplify. smt(@Distr). 
qed.


local lemma le7 ['a] : forall (d : 'a distr), 
  exists (J : int -> 'a option),
  enumerate J (support (mass d)) /\
  mu d predT = lim (fun (n : int) => big predT (mass d) (pmap J (range 0 n))) /\
   (forall (epsilon : real), 0%r < epsilon =>  
     exists (N : int), mu d (predC (mem (pmap J (range 0 N)))) < epsilon).
proof. progress. elim (le6 d). progress. 
exists J. progress.
pose br := (fun (n : int) => big predT (mass d) (pmap J (range 0 n))).
pose brr := (fun (l : real) => (RealSeq.convergeto br l)).
case (exists (x : real), brr x).
move => eb.
have opp : RealSeq.convergeto br (lim br).
smt(@RealSeq).
have ik : exists (N : int), forall (n : int), N <= n => `|br n - (lim br)| < epsilon.
apply (opp epsilon H1).
elim ik.
move => N Np.
have ikkk :  lim br = mu d predT.
rewrite H0. auto.
have akk : forall n, br n  = big predT (mass d) (pmap J (range 0 n)).
auto.
have ikk : forall (n : int), N <= n => lim br - br n < epsilon.
rewrite ikkk.
move => n np. rewrite (akk n).
have jkl : forall (d : 'a distr)  l ,  uniq l => big predT (mass d) l = mu d (mem l).
move => d0. apply list_ind. simplify.  simplify big. rewrite mu0. auto.
move => x l. simplify.
move => ih ihp. 
have e : mem (x :: l) = fun z => (z = x) \/ mem l z.
smt().
rewrite e.
rewrite (mu_disjoint d0 (pred1 x) (fun z => mem l z)).
move => p.
elim. move => p1 p2.
smt().
elim ihp. move => p1 p2.
rewrite - (ih p2).
have o : mu d0 (transpose (=) x) = mu1 d0 x. smt (massE).
rewrite o. clear o.
have o : mu1 d0 x = mass d0 x. smt(massE).
rewrite o. clear o.
smt().
have get : big predT (mass d) (pmap J (range 0 n)) <= mu d predT.
rewrite (jkl d). smt(@List). smt(@Distr).
have ee : mu d predT - big predT (mass d) (pmap J (range 0 n))
 = `|mu d predT - big predT (mass d) (pmap J (range 0 n))|.
smt().
rewrite ee. clear ee.
have el : 
 `|mu d predT - big predT (mass d) (pmap J (range 0 n))| 
 =  `|big predT (mass d) (pmap J (range 0 n)) - mu d predT|.
smt(). rewrite el.
rewrite - ikkk.
 clear el. apply (Np n). apply np.
have kka : forall n, big predT (mass d) (pmap J (range 0 n)) 
                    = mu d (mem (pmap J (range 0 n))).
move => n. 
have jj : (fun (x : 'a) => mass d x) 
    = (fun (x : 'a) => mass d x).
apply fun_ext. move => x. simplify. 
simplify. auto. 
have ooz : uniq ((pmap J (range 0 n))).
smt(@List).
rewrite (mu_mem_uniq d (pmap J (range 0 n)) ooz).
smt(massE).
have ak : forall (n : int), N <= n => 
  mu d predT - (mu d (mem (pmap J (range 0 n)))) < epsilon.
smt().
have ykk : forall (n : int), N <= n => 
 mu d predT - mu d (mem (pmap J (range 0 n))) < epsilon.
move => n p.  apply (ak n p).
exists N.
have oli : forall n, mu d (predC (mem (pmap J (range 0 n)))) 
                   = mu d predT - mu d (mem (pmap J (range 0 n))). smt(@Distr).
rewrite oli.
apply ykk.
progress.
move => sb.
have sb' : (forall (x : real), ! brr x). smt().
have f1 : mu d predT = 0%r.
rewrite H0.
simplify lim.
rewrite choiceb_dfl.
apply sb'.
auto.
exists 0. 
have okl : pmap J (range 0 0) = []. smt(@List).
rewrite okl.
simplify. rewrite f1.
smt().
qed.


lemma fin_pr_approx_distr_enum_conv ['a] : forall (d : 'a distr),
  exists (J : int -> 'a option),
    enumerate J (support d) /\
    RealSeq.convergeto 
     (fun N => mu d (predC (mem (pmap J (range 0 N))))) 
     0%r.
proof. move => d. elim (le7_convto d). progress. 
exists J. split. 
have : support (mass d) = support d.
apply fun_ext. move => x. simplify support.
simplify RealSeries.support.
have : mass d x >= 0%r. smt(@Distr).
move => prr. smt(@Distr).
move => q. rewrite - q. apply H.
progress.
qed.


lemma fin_pr_approx_distr_conv ['a] : forall (d : 'a distr),
  exists (L : int -> 'a list),
    RealSeq.convergeto 
       (fun n => mu d (predC (mem (L n)))) 
       0%r.
proof. move => d. elim (fin_pr_approx_distr_enum_conv d). 
progress. exists (fun n => (pmap J (range 0 n))). 
apply H0.
qed.


lemma fin_pr_approx_distr ['a] :  forall (d : 'a distr),
  exists (J : int -> 'a option),
      enumerate J (support d)
  /\ (forall (epsilon : real), 0%r < epsilon 
        => exists (N : int), 
           mu d (predC (mem (pmap J (range 0 N)))) < epsilon).
proof. move => d. elim (le7 d). progress. 
exists J. split. 
have : support (mass d) = support d.
apply fun_ext. move => x. simplify support.
simplify RealSeries.support.
have : mass d x >= 0%r. smt(@Distr).
move => prr. smt(@Distr).
move => q. rewrite - q. apply H.
progress.
qed.


end section.



section.

type at, rt.

clone import Reflection.Refl with type rt <- rt,
                                  type at <- at.


declare module A  <: RunnableRefl.


local lemma nosmt ex_distr_with_glob :
   exists (D : (glob A) -> at -> (rt * glob A) distr),
   forall  &m M a, mu (D (glob A){m} a) M = Pr[ A.main(a) @ &m : M (res, glob A) ].
proof.
apply (reflection A).
qed.


local lemma nosmt ex_distr_without_glob :
   exists (D : (glob A) -> at -> rt distr),
   forall &m M a, mu (D (glob A){m} a) M = Pr[ A.main(a) @ &m : M res ].
proof.
apply (reflection_simple_res A).
qed.


lemma fin_approx_prog_enum_conv &m :  forall a,
  exists (D : (rt * glob A) distr),  
  exists (J : int -> (rt * glob A) option),
  (forall M, mu D M = Pr[ A.main(a) @ &m :  M (res, glob A) ])
  /\ enumerate J (support D) /\
  RealSeq.convergeto 
    (fun N => Pr[ A.main(a) @ &m : ! ((res , glob A) \in (pmap J (range 0 N))) ]) 
    0%r.
proof. elim ex_distr_with_glob.
progress. 
pose d := (D (glob A){m} a).
exists d.
elim (fin_pr_approx_distr_enum_conv d).
progress.
exists J. progress. apply H.
move => epsilon ep.
elim (H1 epsilon ep ). progress.
exists N. move => n nN. 
have <-:  mu (D (glob A){m} a) (predC (mem (pmap J (range 0 n)))) 
        = Pr[A.main(a) @ &m : ! ((res, (glob A)) \in pmap J (range 0 n))].
   have ->:  Pr[A.main(a) @ &m : ! ((res, (glob A)) \in pmap J (range 0 n))]
             = Pr[A.main(a) @ &m : (predC (mem (pmap J (range 0 n)))) (res, (glob A)) ].
   rewrite Pr[mu_eq].  move => &hr.
      pose x := (res{hr}, (glob A){hr}).
      smt(). auto.
simplify. apply H.
apply H2.
auto.
qed.


lemma fin_pr_approx_prog_conv &m :  forall a,
  exists (L : int -> (rt * glob A) list),
  RealSeq.convergeto 
           (fun N => Pr[ A.main(a) @ &m : ! ((res , glob A) \in (L N)) ]) 
           0%r.
proof. move => a. elim (fin_approx_prog_enum_conv &m a).
progress. exists (fun n => (pmap J (range 0 n))). apply H1.
qed.



lemma fin_approx_prog &m :  forall a,
  exists (D : (rt * glob A) distr),  
  exists (J : int -> (rt * glob A) option),
  (forall M, mu D M = Pr[ A.main(a) @ &m :  M (res, glob A) ])
  /\ enumerate J (support D)
  /\ (forall (epsilon : real), 0%r < epsilon 
        => exists (N : int), 
           Pr[ A.main(a) @ &m : ! ((res , glob A) \in (pmap J (range 0 N))) ] < epsilon).
proof. elim ex_distr_with_glob.
progress. 
pose d := (D (glob A){m} a).
exists d.
elim (fin_pr_approx_distr d).
progress.
exists J. progress. apply H.
elim (H1 epsilon H2). progress.
exists N. rewrite - (H &m (predC (mem (pmap J (range 0 N))))).
apply H3.
qed.




lemma fin_approx_prog_no_glob_conv &m :  
 forall a,
  exists (D : rt distr),  
  exists (J : int -> rt option),
  (forall M, mu D M = Pr[ A.main(a) @ &m :  M res ])
  /\ enumerate J (support D) /\
  RealSeq.convergeto 
     (fun N => Pr[ A.main(a) @ &m : ! (res \in (pmap J (range 0 N))) ]) 
     0%r.
proof. move => a. 
elim ex_distr_without_glob. progress.
pose d := (D (glob A){m} a).
exists d.
elim (fin_pr_approx_distr_enum_conv d).
progress.
exists J. progress. apply H.
move => epsilon ep.
elim (H1 epsilon ep). progress.
exists N. move => n nN. 
have <-:  mu (D (glob A){m} a) (predC (mem (pmap J (range 0 n)))) 
        = Pr[A.main(a) @ &m : ! ((res) \in pmap J (range 0 n))].
   have ->:  Pr[A.main(a) @ &m : ! ((res) \in pmap J (range 0 n))]
           = Pr[A.main(a) @ &m : (predC (mem (pmap J (range 0 n)))) res ].
   rewrite Pr[mu_eq].  move => &hr.
      pose x := (res{hr}).
      smt(). auto.
simplify.  apply H.
apply H2.
auto.
qed.


lemma fin_approx_prog_no_glob &m :  forall a,
  exists (D : rt distr),   exists (J : int -> rt option),
  (forall M, mu D M = Pr[ A.main(a) @ &m :  M res ])
  /\ enumerate J (support D)
  /\ (forall (epsilon : real), 0%r < epsilon 
        => exists (N : int), 
           Pr[ A.main(a) @ &m : ! (res \in (pmap J (range 0 N))) ] < epsilon).
proof. move => a. 
elim ex_distr_without_glob. progress.
pose d := (D (glob A){m} a).
exists d.
elim (fin_pr_approx_distr d).
progress.
exists J. progress. apply H.
elim (H1 epsilon H2). progress.
exists N. rewrite - (H &m (predC (mem (pmap J (range 0 N))))).
apply H3.
qed.


end section.
end FinApprox.

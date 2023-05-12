pragma Goals:printall.
require import AllCore Distr List Binomial.
require import Ring StdRing StdOrder StdBigop Discrete RealSeq RealSeries RealLub.
(*---*) import IterOp Bigint Bigreal Bigreal.BRA.
(*---*) import IntOrder RealOrder RField.
require import Finite.
require (*--*) FinType.
require import Logic.



(* "sum" interpretation of dlet *)
lemma dlet_mu_main ['a, 'b]:
  forall (d : 'a distr) (f : 'a -> 'b distr) M,
    mu (dlet d f) M = sum (fun (a : 'a) => mu1 d a * mu (f a) M).
have dletE_swap' :
  forall (d : 'a distr) (f : 'a -> 'b distr) (P : 'b -> bool),
    mu (dlet d f) P = 
    sum (fun (a : 'a) => (mass d a) * 
                          sum (fun (b : 'b) => if P b then  mass (f a) b else 0%r)).
move => d f P. rewrite  dlet_muE_swap.
have qq : (fun (a : 'a) =>
     sum (fun (b : 'b) => if P b then mu1 d a * mu1 (f a) b else 0%r)) 
 =  (fun (a : 'a) =>
      sum (fun (b : 'b) => mass d a  * (if P b then mass (f a) b else 0%r))).
apply fun_ext. move => a. 
have aux2 : (fun (b : 'b) => if P b then mu1 d a * mu1 (f a) b else 0%r)  
 = (fun (b : 'b) => mass d a * if P b then mass (f a) b else 0%r). 
apply fun_ext. move => b. smt(massE).
rewrite aux2. auto.
rewrite  qq.
have aux3 : (fun (a : 'a) =>
     sum (fun (b : 'b) => mass d a * if P b then mass (f a) b else 0%r)) = 
      (fun (a : 'a) =>
     mass d a * sum (fun (b : 'b) => if P b then mass (f a) b else 0%r)).
apply fun_ext.   move => a.  
apply (sumZ (fun (b : 'b) =>  if P b then mass (f a) b else 0%r)  (mass d a) ) .
rewrite aux3. auto.
move => d f M.      
have qqq : (fun (a : 'a) => mu1 d a * mu (f a) M) = (fun (a : 'a) => (mass d a) * 
         sum (fun (b : 'b) => if M b then  mass (f a) b else 0%r)).
apply fun_ext. move => a.
have ooo : mu (f a) M = sum (fun (b0 : 'b) => if M b0 then mass (f a) b0 else 0%r).
rewrite muE.
smt(massE).
smt(massE).
rewrite  (dletE_swap' d f M). rewrite qqq. auto.
qed.


lemma all_distr_countable (X : 'a distr) : countable (support X). 
proof. rewrite /support.  
  have ->: (fun (x : 'a) => 0%r < mu1 X x)
         = (fun (x : 'a) => mu1 X x <> 0%r).
    apply fun_ext.  move => x. smt(massE @Distr).
apply (countable_mu1 X).
qed.


lemma dmeq ['a, 'b] (d : 'a distr) (M : 'b * 'a -> bool) (r : 'b) : 
   mu d (fun x => M (r, x)) = mu (dmap d (fun x => (r, x))) M.
proof. rewrite dmapE. simplify. smt(). 
qed.


lemma zkj ['a] f : forall x (l : 'a list),
  big predT f (x :: l) = (f x) + big predT f l.
proof. smt().
qed.


lemma sm_than (a b : real) : (forall e, e > 0%r => a >= b - e) => a >= b.
proof. case (b <= a). auto.
move => asbn.
have : a < b. smt().
move => asb pr. clear asbn.
pose d := b - a.
have : d > 0%r. smt().
move => dpos.
have : d = b - a. smt().
move => deq.
have : exists q, q > 0%r /\ q < d. smt().
elim. move => q [qp1] qp2. 
have : d - q > 0%r. smt().
move => dmq.
have : b - (d - q) <= a. smt().
smt().
qed.


op some_real : (real -> bool) -> real = fun p => choiceb p 0%r.


lemma some_real_prop E : (exists p, E p /\ (forall q, E q =>  p = q)) => E (some_real E).
proof. move => q. apply (choicebP E 0%r). elim q. move => p. elim. move => ep pr.
exists p. auto.
qed. 


lemma some_real_prop' E : (exists p, E p ) => E (some_real E).
proof. move => q. apply (choicebP E 0%r). elim q. move => p.  move => ep.
exists p. auto.
qed. 


lemma jokk ['a] (d1 d2 : 'a distr) : 
  (forall M, mu d1 M <= mu d2 M) 
  => forall J, enumerate J (support d2) => enumerate J (support d1).
move => pr. move => j ejd2. 
split. smt().
move => x xid1.   
elim ejd2. move => q1 q2.
apply (q2 x).
smt().
qed.


lemma prjokk ['a]  (d  : 'a distr) j J : 
  enumerate J (support d) => enumerate j (support d)
  => forall n, exists N, forall x, x \in d => x \in (pmap j (range 0 n)) 
      => x \in (pmap J (range 0 N)).
move => e1 e2.  apply natind. smt(@List).
simplify. move => n nc ih. 
elim ih. move => N Np.
case (j n = None).
move => jn1.
have : forall m, j m = None => pmap j (range 0 (m+1)) = pmap j (range 0 m).
apply natind.  simplify.
move => n0 n0p zz. 
case (n0 < 0).
smt(@List).
move => nlz.
have : n0 = 0. smt(). 
move => ko. rewrite ko. simplify.
   simplify pmap.
have : pmap j (range 0 0) = []. smt(@List).
move => ke. rewrite ke. clear ke.
have : range 0 1 = 0 :: []. smt(@List).
move => ke. rewrite ke. clear ke. simplify. smt().
simplify.
move => n0 n0p. move => ih2 pr.
rewrite (rangeSr 0 (n0+1)) . smt().
rewrite - cats1.
rewrite pmap_cat. 
have : pmap j [n0 + 1] = [].
smt(@List).
move => k. rewrite k. smt(@List).
move => prop. exists N. move => x. rewrite prop. auto. progress. apply Np. auto. auto.
move => jnn.
pose z := (j n).
have : z = (j n). smt(). 
have : z <> None. smt().
elim (j n).
 smt().
move => a ap1 ap2.
have : j n = Some a. smt().
move => q.
elim e1.
move => q1 q2.
case (a \in d).
move => aid.
elim (q2 a aid). move => i ip. 
case (i < N).
move => inp. exists N.
move => x xd. rewrite rangeSr. smt(). rewrite - cats1. rewrite pmap_cat.
case (x \in pmap j (range 0 n)).
move => xn. move => _. apply Np. auto. auto.
move => alt alt2.
have : x = a. smt(@List).
move => xa. rewrite xa. clear alt alt2. clear Np. 
have : i \in (range 0 N). apply mem_range. smt(). smt(@List).
move => npr.
have : N <= i.  smt().
clear npr. move => npr.
exists (i+1).
move => x xd. rewrite rangeSr. smt(). rewrite - cats1. rewrite pmap_cat.
have qq : forall x (n : int) m, n <= m => x \in pmap J (range 0 n) => x \in pmap J (range 0 m).
move => xx nn mm nm xip.
elim (pmapP J (range 0 nn) xx ).
move => ok1 ok2. elim (ok1 xip). move => x0. elim. move => x01 x02. 
have : x0 \in (range 0 mm). smt(@List).
smt(@List).
case (x \in pmap j (range 0 n)).
move => l1 l2.
apply (qq x N (i+1)). smt().
apply Np. auto. auto.
move => alt alt2.
have : x = a. smt(@List).
move => xa. rewrite xa.
have : i  \in (range 0 (i+1)). smt(@List). smt(@List).
move => anid.
exists N.
move => x xd.
rewrite rangeSr. smt(). rewrite - cats1. rewrite pmap_cat.
case (x \in pmap j (range 0 n)).
move => xn. move => _. apply Np. auto. auto.
move => alt alt2.
have : x = a. smt(@List).
smt().
qed.


lemma abs1 : forall (a c : real) , `|a * c| = `|a| * `|c|. by smt(). qed. 


lemma abs2 : forall (a : real) ,  a >= 0%r =>  `|a| = a. by smt(). qed.


lemma abs3 : forall (a : real), `|a| >= 0%r. by smt(). qed.


lemma pmc1 (N : int)  : forall  m (x : int), N <= m => x \in (range 0 N) 
  => x \in (range 0 m). by smt(@List). qed.


lemma pmc2 ['a] J    : forall  l m (x : 'a), (forall (y : int), mem  l y => mem m y) 
  => x \in pmap J l => x \in pmap J m. by smt(@List). qed.


lemma pmc ['a] J (N : int)  : forall  m (x : 'a), N <= m => x \in pmap J (range 0 N) 
  => x \in pmap J (range 0 m). by smt (pmc1 pmc2). qed.


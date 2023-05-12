pragma Goals:printall.
(* -------------------------------------------------------------------- *)
require import AllCore Binomial.
require import Ring StdRing StdOrder StdBigop Discrete.
require import RealFun RealSeq RealSeries.
(*---*) import IterOp Bigint Bigreal Bigreal.BRA.
(*---*) import IntOrder RealOrder RField.
require import Finite.
require (*--*) FinType.
require import Distr List.
require import RandomFacts.
require FiniteApproximation.
clone import FiniteApproximation.FinApprox.


section.

local lemma Jensen_inf0 ['a] : forall (X : 'a distr) (d c : real)
 (epsilon : real), epsilon > 0%r
  => c < d => 
     exists M, is_finite M /\ mu X (predC M) <= (epsilon / (d - c)).
proof. progress.
elim (fin_pr_approx_distr X).
move => J [Je Jp].
have edc : 0%r < (epsilon / (d - c)).
smt().
elim (Jp (epsilon / (d - c))  edc ).
move => N Np. 
exists (mem ((pmap J ((range 0 N))))).
split. 
apply mkfinite. exists (pmap J (range 0 N)).
auto.
smt().
qed.


local lemma is_loss ['a] (X : 'a distr) M : mu X M > 0%r 
 => is_lossless (inv (mu X M)  \cdot drestrict X M).
proof. have dw : weight (drestrict X M) = (mu X M). smt(@Distr).
rewrite - dw.
apply dscalar_ll.
qed.



local lemma has_E' k (X : 'a distr) g :  hasE X g  => 0%r <= k && k <= inv (weight X)
 => hasE (k \cdot X) g.
rewrite /hasE. progress.

have ->: (fun (x : 'a) => g x * mu1 (k \cdot X) x)
 = (fun (x : 'a) => k * (g x * mu1 X x)).
apply fun_ext. move => x. rewrite dscalar1E. auto.
auto. smt().
apply summableZ. auto.
qed.


local lemma has_E (X : 'a distr) M g :  mu X M > 0%r => hasE X g 
 => hasE (inv (mu X M) \cdot drestrict X M) g.
proof. progress.
have f1 : hasE (drestrict X M) g. 
apply hasE_drestrict. auto.
apply has_E'. auto.
split. smt(). progress.
have ->: (weight (drestrict X M)) = mu X M. smt(@Distr).
auto.
qed.


local lemma qqq (X : 'a distr) c f : 0%r <= c && c <= inv (weight X) 
  => c * E X f = E (c \cdot X) f.
proof. rewrite /E. rewrite - sumZ.
move => p. apply eq_sum.
 move => x.
simplify.
rewrite /(dscalar).
    rewrite /mscalar.
have ss : isdistr (fun (x0 : 'a) => c * mass X x0).
apply isdistr_mscalar.
have ->: (fun (x0 : 'a) => mass X x0) = (fun (x0 : 'a) => mu1 X x0). apply fun_ext. smt(massE).
apply isdistr_mu1. 
split.
smt().
progress. 
rewrite weightE.
have ->: (fun (x0 : 'a) => mu1 (mk (mass X)) x0)
 = (fun (x0 : 'a) => mu1 X x0).
apply fun_ext. move => x0. 
rewrite  muK. 
have ->: (mass X) = mu1 X. smt(massE).
apply isdistr_mu1. 
smt(massE).
rewrite - weightE. smt().
rewrite muK. 
apply isdistr_mscalar. apply isdistr_mu1.
split. smt().
progress.
have ->: (weight (mk (fun (x0 : 'a) => mu1 X x0)))
 = weight X.
rewrite weightE. rewrite weightE. simplify.
have ->: (fun (x0 : 'a) => mu1 (mk (fun (x0_0 : 'a) => mu1 X x0_0)) x0)
 = (fun (x0 : 'a) => mu1 X x0). apply fun_ext.  move => x0.
rewrite muK. 
apply isdistr_mu1. simplify. auto. auto. smt(@Distr).
smt().
qed.


local lemma www (X : 'a distr) (g : 'a -> real) M: 
 Ec X g M = (inv (mu X M)) * E (drestrict X M) g.
proof. smt (@Distr @Real qqq). 
qed.

local lemma iii a b : (a > 0%r) => (b > 0%r) => b <= a => inv a <= inv b .
smt().
qed.


local lemma ooo (X : 'a distr) M g : 
 (inv (mu X M)) * E (drestrict X M) g = E (inv (mu X M) \cdot drestrict X M) g.
proof.
 rewrite /E. rewrite - sumZ.
 apply eq_sum.
 move => x.
simplify.
rewrite /drestrict /mrestrict /dscalar  /mscalar .
have s1 : isdistr (fun (x0 : 'a) => if M x0 then mu1 X x0 else 0%r).
apply isdistr_mrestrict.
rewrite muK. apply s1.
have s2 : isdistr (fun (x0 : 'a) =>
        inv (mu X M) * (fun (x1 : 'a) => if M x1 then mu1 X x1 else 0%r) x0).
apply isdistr_mscalar. apply s1.
split.
smt(@Distr @Real).
move => q1.
have ->: mu (mk (fun (x1 : 'a) => if M x1 then mu1 X x1 else 0%r)) predT = mu X M.
rewrite muE. rewrite muE.
apply eq_sum.
move => y. simplify.
simplify predT.
rewrite muK. apply s1.
simplify. auto. auto.
simplify.
rewrite muE. 
have f : (fun (x0 : 'a) =>
     mu1 (mk (fun (x1 : 'a) => if M x1 then mu1 X x1 else 0%r)) x0 / mu X M)
 = (fun (x0 : 'a) => (if M x0 then mu1 X x0 else 0%r) / mu X M).
apply fun_ext. move => x0. rewrite muK. 
smt(). smt().
rewrite muK.  rewrite f. smt().
rewrite f.
simplify.
have ->: sum (fun (x0 : 'a) => if pred1 x x0 then mu1 X x0 else 0%r)
  =  mu1 X x.
rewrite muE. auto. auto.
qed.


local lemma uuu (X : 'a distr) (g : 'a -> real) M :
  (inv (mu X M)) * E (drestrict X M) g = Ec X g M.
proof. smt(www). qed.


local lemma Jensen_inf1 (X : 'a distr) (g : 'a -> real) M:
   hasE X g =>
      E X g = mu X M * Ec X g M + mu X (predC M) * Ec X g (predC M).
proof. move => XghasE.
rewrite (Ec_split M). apply XghasE.
auto.
qed.


local lemma ec_edot (X : 'a distr) M g : Ec X g M = E (inv (mu X M) \cdot drestrict X M) g.
proof. rewrite - ooo. smt(www). qed.


local lemma Jensen_inf_1 (X : 'a distr) (g : 'a -> real) M:
 hasE X g =>
 E X g = mu X M * E (inv (mu X M)  \cdot drestrict X M) g  
       + mu X (predC M) * E (inv (mu X (predC M)) \cdot drestrict X (predC M)) g.
proof.  move => XhasEg.
rewrite (Jensen_inf1 X g M). auto.
rewrite - ooo. rewrite - ooo.
rewrite exp_drestrict.
have opp : (inv (mu X M) * (mu X M * Ec X g M)) = Ec X g M.
rewrite - uuu. smt(@Real).
rewrite opp.
have ppo : mu X (predC M) * (inv (mu X (predC M)) * E (drestrict X (predC M)) g) =  E (drestrict X (predC M)) g.
smt(@Real @Distr).
rewrite ppo.
rewrite exp_drestrict.
auto.
qed.


local lemma Jensen_inf2 (X : 'a distr) (g : 'a -> real) f M:
   is_lossless X =>
   (forall (a b : real), (convex f a b)) =>
    f (mu X M * Ec X g M  + mu X (predC M) * Ec X g (predC M))
    <= mu X M * f (Ec X g M)
    + mu X (predC M) * f (Ec X g (predC M)).
proof.  move => llX fconv.
have co : mu X (predC M) = 1%r - mu X M. smt(@Distr).
rewrite co. 
apply (fconv (Ec X g M) (Ec X g (predC M)) (mu X M)).
smt(@Distr).
qed.


local lemma Jensen_inf4_gen_1 ['a] :  forall D (g : 'a -> real) b, 
    is_lossless D =>
    (forall x, x \in D => g x <= b) =>
    hasE D g =>
    E D g <=  b.
proof.
move => D g b ll ld he.
have zz : E D (fun _ => b) <= b.
rewrite expC.
have ws1 : weight D <= 1%r. smt().
have ws2 : 0%r <= weight D. smt(). smt().
apply (ler_trans (E D (fun (_ : 'a) => b))).
apply in_ler_exp.
apply he.
apply hasEC.
auto. apply zz.
qed.


local lemma Jensen_inf4_gen_2 ['a] : forall D (g : 'a -> real) a,
 is_lossless D =>
 (forall x, x \in D => a <= g x) =>
 hasE D g =>
   a <= E D g.
move => D g a ld q he.
have zz : a = E D (fun _ => a).
rewrite expC.
smt().
rewrite  zz.
apply in_ler_exp.
apply hasEC.
apply he.
progress.
qed.


local lemma wdrestr (X : 'a distr) M : (mu X M) = (weight (drestrict X M)).
proof. smt(@Distr). qed.


local lemma jensen_ie (X : 'a distr) g f (a b c d : real) :
  hasE X g =>
  hasE X (f \o g) =>
  (forall (a b : real), (convex f a b)) =>
  is_lossless X =>
  (forall x, a <= x <= b => c <= f x <= d) =>
  (forall x, x \in X => a <= g x <= b) =>
  forall epsilon, epsilon > 0%r =>
     f (E X g) <= E X (f \o g) + epsilon.
proof. move => XghasE XfghasE fconv ll fvals xvals eps eprop.
case (b < a). move => p.
have : exists x, x \in X.
elim (witness_support  predT X).
move => i1 _. 
  have wo : 0%r < weight X. smt().
  elim (i1 wo).
smt().
elim. move=> x xi.
have : false.
  have : a <= g x.  smt(). 
  have : a <= g x && g x <= b. apply xvals. apply xi.
  move => [f1 f2]  .
  have : g x = b. smt().
  have : g x = a. smt().
  smt().
  smt().
move => nabp.
have abp : a <= b. smt().
case (d < c). move => p.
have : c <= f a && f a <= d.
apply fvals. split. smt(). move => _. apply abp. 
move => [f1 f2].
have : f a = c. smt().
have : f a = d. smt().
smt().
case (d = c). move => dce.
have : forall x, a <= x <= b => c <= f x <= d.
move => x xp.
apply (fvals x xp).
rewrite dce. move => ep.   
have : forall x, a <= x <= b => f x = c.
smt().
move => fpv _.
  have : a <= E X g <= b.
   split.     
  have ->: a = E X (fun x => a).
  rewrite expC. smt().
  apply in_ler_exp. apply hasEC. apply XghasE.
  smt().  
  have ->: b = E X (fun x => b).
  rewrite expC. smt(). move => _.   apply in_ler_exp.  apply XghasE. apply hasEC.
  smt().    
move => ei.
have ->: f (E X g) = c. smt().
rewrite (eq_exp X (f \o g) (fun _ => c)). smt().
have ->: E X (fun (_ : 'a) => c) = c.
rewrite expC. smt().
smt(). 
move => ndcp1 ndcp2.
have  dcp : c < d.
smt().
elim (Jensen_inf0 X d c eps  eprop dcp).
move => M p. elim p.
move => finM muXC.
rewrite (Jensen_inf1 X g M).  auto.      (* step 1 *)
apply (ler_trans (mu X M * f (Ec X g M) + mu X (predC M) * f (Ec X g (predC M)))).
apply (Jensen_inf2 X g f M). auto.  auto. (* step 2 *)
apply (ler_trans (mu X M *  (Ec X (f \o g) M) + mu X (predC M) * f (Ec X g (predC M)))).
rewrite ec_edot.
case ((mu X M) = 0%r).
smt().
move => mupos.
  have ff1 : f (E (inv (mu X M) \cdot drestrict X M) g)
      <= (E (inv (mu X M) \cdot drestrict X M) (f \o g)).
  apply Jensen_fin.
have dfin : is_finite (support (inv (mu X M) \cdot drestrict X M)).
   rewrite /is_finite.
   elim finM.
   move => s spr.  exists (filter (fun x => mu1 X x <> 0%r) s).
   rewrite /is_finite_for.
   split. smt(@List).
   move => x.
   split.
   move => xi.
   elim (spr). move => _ pr.
   elim (pr x).      move => p1 p2.
   have Mx : M x. smt(@List).
   have xX : x \in X. smt(@Distr @List).
   have xXM : x \in (drestrict X M). smt(@Distr).
   apply supp_dscalar. smt(@Distr).
   have ->: (mu X M) = (weight (drestrict X M)). apply wdrestr.  auto.  auto.
   move => pr.
    have  xiX : forall x, x \in (inv (mu X M) \cdot drestrict X M)
       => x \in (drestrict X M).
       move => y pr1.
       have : y \in (inv (mu X M) \cdot drestrict X M) <=> y \in drestrict X M.
       apply supp_dscalar. smt(@Distr).
       have : weight (drestrict X M) = mu X M. rewrite -  wdrestr.  auto.
       smt(). move => eq. smt(@Distr). 
       have o1 : x \in s. smt(@Distr).
       have o2 : mu1 X x <> 0%r. smt(@Distr).
       smt(@List).
 auto. 
apply is_loss. smt(@Distr). apply fconv.
  rewrite (ec_edot X M (f \o g)).
  have ff2 : mu X M >= 0%r.
  smt(@Distr).
  smt().        (* step 3 *)
apply (ler_trans
  (mu X M *  (Ec X (f \o g) M) + mu X (predC M) * d)).
case ((mu X (predC M)) = 0%r).
smt().
move => nz.
   have ff1 : f (Ec X g (predC M)) <= d.
     have ff2 : a <= Ec X g (predC M) <= b.
      split. rewrite ec_edot. apply Jensen_inf4_gen_2. apply is_loss.
      smt(@Distr).
have  xiX : forall x, x \in (inv (mu X (predC M)) \cdot drestrict X (predC M))
   => x \in X.
   move => x pr.
   have : x \in (inv (mu X (predC M)) \cdot drestrict X (predC M)) <=> x \in drestrict X (predC M).
   apply supp_dscalar. smt(@Real @Distr).
   have : weight (drestrict X (predC M)) = mu X (predC M).
   smt(@Distr). move => eq. smt().
   smt(@Distr). smt().
   apply has_E. smt(@Distr). smt(). progress. rewrite ec_edot. apply Jensen_inf4_gen_1. 
   apply is_loss. smt(@Distr).
have  xiX : forall x, x \in (inv (mu X (predC M)) \cdot drestrict X (predC M))
   => x \in X.
   move => x pr.
   have : x \in (inv (mu X (predC M)) \cdot drestrict X (predC M)) <=> x \in drestrict X (predC M).
   apply supp_dscalar. smt(@Distr).
   have : weight (drestrict X (predC M)) = mu X (predC M).
   smt(@Distr). move => eq. smt(@Distr).
   smt(@Distr). smt().
apply has_E. smt(@Distr).
smt().
have dp : mu X (predC M) * f (Ec X g (predC M)) <= mu X (predC M) * d.
  have qq : forall (a b c : real), a >= 0%r => b <= c => a * b <= a * c. smt().
  have mup : mu X (predC M) >= 0%r. smt(@Distr).
  smt().
smt().
  have mup : mu X (predC M) >= 0%r. smt(@Distr).
  have : mu X (predC M) * f (Ec X g (predC M)) <= mu X (predC M) * d.
   clear finM muXC nz eprop. smt().
  smt().
apply (ler_trans (E X (f \o g) -  mu X (predC M) * Ec X (f \o g) (predC M) + mu X (predC M) * d)).
  have : E X (f \o g) = mu X M * Ec X (f \o g) M
                        + mu X (predC M) * Ec X (f \o g) (predC M).
  apply Ec_split. apply XfghasE.
move => eq.
   have : mu X (predC M) * Ec X (f \o g) (predC M) =  E X (f \o g) - mu X M * Ec X (f \o g) M. smt().
   move => eq2.  rewrite  eq2.
   have ->: E X (f \o g) - (E X (f \o g) - mu X M * Ec X (f \o g) M) = mu X M * Ec X (f \o g) M. smt().
 auto.
apply (ler_trans (E X (f \o g) -  mu X (predC M) * c + mu X (predC M) * d)).
   case (mu X (predC M) = 0%r). smt().
   move => mpMnz.
   have cb : c <= Ec X (f \o g) (predC M).
   rewrite ec_edot.
   apply (Jensen_inf4_gen_2 (inv (mu X (predC M)) \cdot drestrict X (predC M)) (f \o g) ).  apply is_loss. smt(@Distr).
have  xiX : forall x, x \in (inv (mu X (predC M)) \cdot drestrict X (predC M))
   => x \in X.
   move => x pr.
   have : x \in (inv (mu X (predC M)) \cdot drestrict X (predC M)) <=> x \in drestrict X (predC M).
   apply supp_dscalar. smt(@Distr).
   have : weight (drestrict X (predC M)) = mu X (predC M).
   smt(@Distr). move => eq. smt().
   smt(@Distr).
smt().
 apply has_E. smt(@Distr). apply XfghasE.
  have : E X (f \o g) - mu X (predC M) * Ec X (f \o g) (predC M) <=
         E X (f \o g) - mu X (predC M) * c.
     have muc : mu X (predC M) * c <= mu X (predC M) * Ec X (f \o g) (predC M).
      have mup : mu X (predC M) >= 0%r. smt(@Distr).
      clear finM muXC eprop mpMnz.  
           have q : forall (a b c : real) ,  0%r <= a => c <= b => a * c <= a * b. smt(). apply q. smt(). smt().

     smt().
smt().
have ->: E X (f \o g) - mu X (predC M) * c + mu X (predC M) * d
  =    E X (f \o g) + (d - c) * mu X (predC M).
smt().
apply (ler_trans (E X (f \o g) + (d - c) *   (eps / (d-c)) )).  clear XghasE XfghasE fconv ll fvals xvals finM.
   have trivia: forall (a b c : real), a >= 0%r => b <= c => a * b <= a * c. smt().
   have trivia2 : (d - c) * mu X (predC M) <= (d - c) * (eps / (d - c)). apply trivia. auto. auto.
smt(). smt(). smt(). smt().
qed.


lemma Jensen_inf (X : 'a distr) g f (a b c d : real) :
  is_lossless X 
  => hasE X g
  =>  hasE X (f \o g)
  => (forall (a b : real), (convex f a b))
  => (forall x, a <= x <= b => c <= f x <= d)
  => (forall x, x \in X => a <= g x <= b)
  => f (E X g) <= E X (f \o g).
proof. progress. apply sm_than.
progress.
  have sm : f (E X g) <= E X (f \o g) + e.
  apply (jensen_ie X g f a b c d);auto.
smt().
qed.


end section.

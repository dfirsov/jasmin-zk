pragma Goals:printall.
require import AllCore.
require import Distr.
require import AllCore List Binomial.
require import Ring StdRing StdOrder StdBigop Discrete RealSeq RealSeries RealLub.
(*---*) import IterOp Bigint Bigreal Bigreal.BRA.
(*---*) import IntOrder RealOrder RField.
require import Finite.
require (*--*) FinType.

require import RandomFacts.

theory Refl.

type at, rt.

module type RunnableRefl = {
  proc run(a:at) : rt
}.


module SF = {
   proc sampleFrom (d : rt distr)  = {
        var r; 
        r <$ d;
        return r;
    }
}.

module PP(A : RunnableRefl) = {
   proc sampleFrom (d : rt distr)  = {
        var r; 
        r <$ d;
        return r;
    }
   proc run2(a : at) = {
      var r;
      r <@ A.run(a);
      return r;
    }
}.


section.

declare module A <: RunnableRefl. 

local module P = {
   proc sampleFrom (d : (rt * (glob A)) distr)  = {
        var r; 
        r <$ d;
        return r;
    }
   proc run2(a : at) = {
      var r;
      r <@ A.run(a);
      return r;
    }
}.


local lemma filter_le1 : forall (l : bool list), filter (fun _ => true) l = l.  
proof. apply list_ind. smt(). smt().
qed.


local lemma bigLemma ['a] (f : 'a -> real) : forall l x,  big predT f (x :: l)
     = f x + big predT f l.
proof. apply list_ind. smt(). move => x l ih. simplify. smt().
qed.


op pickme ['a] (c : real) (a : 'a) (x0 : 'a) : real = if a = x0 then c else 0%r. 


local lemma iot2 ['a] (c : real) (a : 'a) : 0%r <= c => summable (pickme c a).
proof. move => pr. simplify summable.
exists c.
apply list_ind.
smt().
simplify.
move => x l ih.
elim.
move => xnil ul.
rewrite (bigLemma (fun (i : 'a) => `|pickme c a i|) l x).
simplify.
case (a = x).
move => axe.
rewrite axe.
simplify pos pickme. 
  have :  forall (l : 'a list) x, !(x \in l) =>
   big predT (fun (i : 'a) => `|if x = i then c else 0%r|) l  = 0%r.
apply list_ind. smt(). simplify.
move => x0 l0 ihh. move => x1 prr.
have : (x1 <> x0 /\ !(x1 \in l0)) . smt().
elim. move => p1 p2. 
rewrite (bigLemma (fun (i : 'a) => `|if x1 = i then c else 0%r|) l0 x0).
simplify. rewrite (ihh x1 p2). simplify. rewrite p1. simplify. auto.
move => prop1.
rewrite (prop1 l x xnil). progress. smt().
move => ane. simplify pickme. rewrite ane. simplify.
have : `|0%r| + big predT (fun (i : 'a) => `|if a = i then c else 0%r|) l  
         =  big predT (fun (i : 'a) => `|if a = i then c else 0%r|) l. smt().
move => qoq. rewrite qoq.
apply ih. apply ul.
qed.


local lemma iot ['a] (a : 'a) (c : real) : summable (pickme c a) => 0%r <= c 
  => sum (pickme c a) = c.
proof. move => ps cp. simplify sum. rewrite ps. simplify.
simplify psum.
simplify psum_pred.
pose E_pos := (fun (M : real) => exists (J : 'a list), 
  uniq J /\ M = big predT (fun (x : 'a) => `|pos (pickme c a) x|) J).
pose E_neg := (fun (M : real) => exists (J : 'a list), 
  uniq J /\ M = big predT (fun (x : 'a) => `|neg (pickme c a) x|) J).
have : ub E_neg 0%r.
have :  forall J,  big predT (fun (x : 'a) => `|neg (pickme c a) x|) J = 0%r.
apply list_ind. smt(). move => x l ih. simplify.     
rewrite (bigLemma (fun (x0 : 'a) => `|neg (pickme c a) x0|) l x).
simplify. rewrite ih. simplify neg pickme. smt().
move => bignegval.
simplify ub. 
move => y q. 
elim q. apply list_ind.
smt(). move => x l ih. simplify.
elim. elim. move => xnl ul.
move => qq. rewrite qq.
rewrite (bignegval (x::l)). auto.
move => ubc.
have : E_neg 0%r.
exists []. simplify. smt().
move => eng.
have : has_lub E_neg.
simplify has_lub.
progress. simplify nonempty. exists 0%r. apply eng.
simplify has_ub.
simplify nonempty.
exists 0%r. apply ubc.
move => haslubneg.
have : lub E_neg <= 0%r.
apply lub_le_ub. apply haslubneg. apply ubc.
move => lneg0.
have : lub E_neg >= 0%r.
apply lub_upper_bound. apply haslubneg. 
apply eng.
move => lneg0'.
have : lub E_neg = 0%r.
smt().
move => lubnege0.
rewrite lubnege0.
simplify.
have : ub E_pos c.
simplify ub. 
move => y q. 
elim q.  apply list_ind.
smt().
simplify.
move => x l ih. elim. elim.
move => xnl ul.
rewrite (bigLemma (fun (x0 : 'a) => `|pos (pickme c a) x0|) l x). simplify.
have : forall (l : 'a list) x, !(x \in l) => big predT
  (fun (x0 : 'a) =>
     `|if (if x = x0 then c else 0%r) < 0%r then 0%r
       else `|if x = x0 then c else 0%r| |) l  = 0%r.
apply list_ind. move => l0 x1. smt().
simplify.
move => x0 l0  ni x1 pr . 
have : ! (x1 = x0) /\ !(x1 \in l0). smt().
elim. move => p1 p2.
rewrite (bigLemma (fun (x0_0 : 'a) =>
     `|if (if x1 = x0_0 then c else 0%r) < 0%r then 0%r
       else `|if x1 = x0_0 then c else 0%r| |) l0 x0).
simplify. rewrite ni. assumption. smt().
move => qoq.
case (a = x).
move => axe.
rewrite axe.
simplify pos pickme. 
have : `|if c < 0%r then 0%r else `|c| | = c. smt().
move => qq. rewrite qq.
rewrite (qoq l x xnl). simplify.
move=> yce. rewrite yce. auto.
(* CONTINUTE *)
move => anex. move => qzx.
have : y = big predT (fun (x0 : 'a) => `|pos (pickme c a) x0|) l.
rewrite qzx. simplify pos pickme.  rewrite anex. simplify. smt().
move => ye.
have :  uniq l /\ y = big predT (fun (x0 : 'a) => `|pos (pickme c a) x0|) l. 
split. apply ul. apply ye.
apply ih. move => ubcc.
have : has_lub (fun (M : real) =>
     exists (J : 'a list),
       uniq J /\
       M = big predT (fun (x : 'a) =>
            `|pos (fun (x0 : 'a) => if a = x0 then c else 0%r) x|) J).
split. exists c.
exists (a :: []).
split. smt(). simplify. simplify big. simplify predT. smt().
exists c. apply ubcc.
move => haslub.
have : lub (fun (M : real) =>
     exists (J : 'a list),
       uniq J /\
       M =
       big predT
         (fun (x : 'a) =>
            `|pos (fun (x0 : 'a) => if a = x0 then c else 0%r) x|) J) <= c.
apply lub_le_ub. apply haslub. apply ubcc.
move => lublec.
have : lub (fun (M : real) =>
     exists (J : 'a list),
       uniq J /\
       M =
       big predT
         (fun (x : 'a) =>
            `|pos (fun (x0 : 'a) => if a = x0 then c else 0%r) x|) J) >= c.
apply lub_upper_bound. apply haslub. simplify. 
exists [a]. split. smt().
simplify big predT pos. simplify. smt().
move => lubgec.       
have : c = lub
  (fun (M : real) =>
     exists (J : 'a list),
       uniq J /\
       M =
       big predT
         (fun (x : 'a) =>
            `|pos (fun (x0 : 'a) => if a = x0 then c else 0%r) x|) J).
smt().
move => ceq.  rewrite - ceq.
simplify pos. simplify. auto.
qed.


local lemma gen_fact &m : forall  a (l : (rt * (glob A)) list), uniq l 
 => Pr[ A.run(a) @ &m : (res , (glob A)) \in l ] 
  = big predT (fun (x : (rt * (glob A))) => 
                    Pr[A.run(a) @ &m: res=x.`1 /\ (glob A) = x.`2]) 
              l.
proof. move => a. apply list_ind.
simplify. rewrite Pr[mu_false].
smt(). simplify.
move => x l p1 p2. simplify.
rewrite Pr[mu_disjoint].
smt().
elim p2.
move => p21 p22.
have : big predT (fun (x0 : (rt * (glob A))) => 
                       Pr[A.run(a) @ &m : res = x0.`1 /\ (glob A) = x0.`2]) 
                 (x :: l)
    = Pr[A.run(a) @ &m : res = x.`1 /\ (glob A) = x.`2] 
    + big predT (fun (x0 : (rt * (glob A))) => 
                      Pr[A.run(a) @ &m : res = x0.`1 /\ (glob A) = x0.`2]) 
                l.
simplify predT big. auto.
move => q. rewrite q.
rewrite (p1 p22).
have ee : Pr[A.run(a) @ &m : (res, (glob A)) = x] 
        = Pr[A.run(a) @ &m : res = x.`1  /\ (glob A) = x.`2 ]. 
rewrite Pr[mu_eq]. smt(). auto.
rewrite ee. auto.
qed.


lemma reflection :
    exists (D : (glob A) -> at -> (rt * glob A) distr),
    forall &m M i, mu (D (glob A){m} i) M = Pr[ A.run(i) @ &m : M (res, glob A)].
proof. 
(* introduce P as in the paper *)
pose PR := fun (g : glob A) (a : at) (x : rt * glob A) => 
                some_real (fun p => forall &m, (glob A){m} = g => 
                            Pr[A.run(a) @ &m : res=x.`1 /\ (glob A) = x.`2 ] = p).
pose D := (fun (g : glob A) (a : at) => mk (PR g a)).
exists D.
move => &m M.
have : forall a (x : rt * glob A) &m' &m'' , 
          (glob A){m'} = (glob A){m} => 
          (glob A){m''} = (glob A){m} => 
          Pr[A.run(a) @ &m': res = x.`1 /\ (glob A) = x.`2] 
          = Pr[A.run(a) @ &m'': res = x.`1 /\ (glob A) = x.`2].
move => a x &m' &m'' a1 a2.  
byequiv. proc*.  call(_:true). skip. smt(). progress. progress.
move => H1'. 
have : forall a (x : rt * glob A), 
   Pr[A.run(a) @ &m: res=x.`1 /\ (glob A) = x.`2] = PR (glob A){m} a x.
move => a x. simplify.
have : forall &n,
  (glob A){n} = (glob A){m} =>
  Pr[A.run(a) @ &n : res = x.`1 /\ (glob A) = x.`2]
  = some_real (fun (p : real) => forall &n0,
         (glob A){n0} = (glob A){m} => 
         Pr[A.run(a) @ &n0 : res = x.`1 /\ (glob A) = x.`2] = p).
  simplify. move => &n c1.
  have : exists (p : real),
    (forall &n0, (glob A){n0} = (glob A){m} => 
      Pr[A.run(a) @ &n0 : res = x.`1 /\ (glob A) = x.`2] = p) /\
    forall (q : real), (forall &n0, (glob A){n0} = (glob A){m} => 
      Pr[A.run(a) @ &n0 : res = x.`1 /\ (glob A) = x.`2] = q) 
    => p = q.   
  exists (Pr[A.run(a) @ &m :  res = x.`1 /\ (glob A) = x.`2 ]).
  progress.
  apply (H1' a x &n0 &m). assumption.
  auto.
   rewrite (H &m).  auto. auto.
  move => prem.
  have : forall &n0,
  (glob A){n0} = (glob A){m} =>
  Pr[A.run(a) @ &n0 : res = x.`1 /\ (glob A) = x.`2 ] =
  some_real (fun (p : real) => forall &n0_0, (glob A){n0_0} = (glob A){m}
        => Pr[A.run(a) @ &n0_0 : res = x.`1 /\ (glob A) = x.`2 ] = p).       
  apply (some_real_prop (fun (p : real) => forall &n0, (glob A){n0} = (glob A){m} 
        => Pr[A.run(a) @ &n0 : res = x.`1 /\ (glob A) = x.`2 ] = p)).
  simplify.
   apply prem.
   move => qqq.
   apply (qqq &n).   assumption.
   move => pop.
 rewrite  (pop &m). reflexivity. reflexivity.   
move => H2.
have : (PR (glob A){m}) = (fun (a : at) (x : (rt * (glob A))) 
                            => Pr[A.run(a) @ &m: res = x.`1 /\ (glob A) = x.`2 ]). (* TODO: add name Q_well_def  *)
apply fun_ext. move => a. apply fun_ext. move => q. rewrite - (H2 a q). reflexivity.
move => H21 a.
have nice: isdistr (PR (glob A){m} a).     
  have : (forall (s : ((rt * (glob A)) list)), uniq s => 
      big predT (PR (glob A){m} a) s <= 1%r).  rewrite  H21.
  apply list_ind. smt().
  move => x l. simplify. 
  move => q1 q2.
  rewrite - (gen_fact &m a (x :: l)).  apply q2.
  rewrite Pr [mu_le1]. auto.
  move => fact1.
  have : (forall (x : rt * (glob A)), 0%r <= PR (glob A){m} a x). 
  move => x. rewrite - (H2 a x). rewrite Pr[mu_ge0]. auto.
  move => fact2.
  split. apply fact2. apply fact1.
have H7: forall M, Pr[ P.sampleFrom((D (glob A){m} a)) @ &m  : M res ] 
                   = mu (D (glob A){m} a) M.
  move => M0.
  byphoare (_ : d = (D (glob A){m} a) ==> _).
  proc.
  rnd. skip. move => &hr prr .  progress. smt().
  smt(). auto.
have H3: forall M, equiv [P.sampleFrom ~ A.run : ={glob A} /\ arg{1} = (D (glob A){m} a) 
                         /\ (glob A){2} = (glob A){m} /\ arg{2} = a 
                         ==> M res{1} <=> M (res , glob A){2}].
  move => M0.
  conseq (_: _ ==> res{1}.`1 = res{2} /\ res{1}.`2 = (glob A){2} ).
    smt().
  bypr (res{1}) (res, glob A){2}.
    smt().
  move => &1 &2 aa p1. 
  (* move up to toplevel. *)
  have good_q: Pr[A.run(a) @ &m : (res , glob A) = aa] 
               = Pr[A.run(a) @ &2 : (res , glob A) = aa] .
    have eq1 : Pr[A.run(a) @ &m : (res, (glob A)) = aa] 
               = Pr[A.run(a) @ &m : res = aa.`1 /\ (glob A) = aa.`2].
      rewrite Pr[mu_eq]. progress. smt(). auto.
    have eq2 : Pr[A.run(a) @ &2 : (res, (glob A)) = aa] 
               = Pr[A.run(a) @ &2 : res = aa.`1 /\ (glob A) = aa.`2].
      rewrite Pr[mu_eq]. progress. smt(). auto.
    rewrite eq1 eq2.
    apply (H1' a aa &m &2). auto.  smt(). 
  elim p1. move => p11. elim. move => p12. elim. move => p13 p14. rewrite p14.
  rewrite -  good_q.
  have eq1 : Pr[A.run(a) @ &m : (res, (glob A)) = aa] 
             = Pr[A.run(a) @ &m : res = aa.`1 /\ (glob A) = aa.`2].
    rewrite Pr[mu_eq]. progress. smt(). auto.
  rewrite eq1.
  rewrite (H2 a aa).
  rewrite p12.
  byphoare (_ : d = (D (glob A){m} a) ==> _).
    proc. rnd. skip. move => &hr prr. progress. 
    elim prr.
    move => prr1 prr2.
    rewrite prr1.
    have x: mu (mk (PR (glob A){m} a)) (transpose (=) aa) = mu1 (mk (PR (glob A){m} a)) aa.
      rewrite /pred1. smt().
    rewrite x. clear x.
    rewrite -  massE. smt(@Distr).
    (* rewrite  muK.  
    apply nice. *) 
    auto. auto. auto.
have H4: forall M, Pr[ P.sampleFrom((D (glob A){m} a)) @ &m : M res ] 
                   = Pr[ A.run(a) @ &m : M (res , (glob A)) ].
  move => M0. byequiv (_: (glob A){1} = (glob A){m} /\ ={glob A} /\ d{1} = D (glob A){m} a 
                          /\ arg{2} = a  ==> _). conseq (H3 M0). 
  move => &1 &2 prr.  progress. smt(). smt().
  smt(). smt(). auto. auto.
rewrite - (H7 M).
rewrite - (H4 M).
by reflexivity.
qed.



lemma asdistr : forall (D : (glob A) -> at -> rt distr),
  (forall &m M a, mu (D (glob A){m} a) M = Pr[ A.run(a) @ &m :  M res ])
  => forall &m a, equiv [SF.sampleFrom ~ A.run : ={glob A} /\ arg{1} = (D (glob A){m} a) 
                         /\ (glob A){2} = (glob A){m} /\ arg{2} = a 
                         ==>  res{1} =  res{2}].
move => D pr.
move => &m az.
bypr (res{1}) (res{2}). auto.
move => &1 &2 aa p1. 
have good_q: Pr[A.run(az) @ &m : (res) = aa] 
               = Pr[A.run(az) @ &2 : (res) = aa] .
byequiv. proc*.  call (_:true). skip. progress. smt(). auto. auto.                       
have <-: mu (D (glob A){2} a{2}) (fun r =>  r = aa) = Pr[A.run(a{2}) @ &2 : res = aa]. rewrite pr.
auto. simplify. 
byphoare (_: arg = d{1} ==> _). proc. rnd. skip. progress. smt(). auto. auto.
qed.
                       

lemma reflection_simple : exists (D : (glob A) -> at -> (glob A) distr),
    forall &m M i, mu (D (glob A){m} i) M = Pr[ A.run(i) @ &m :  M (glob A) ].
proof.
elim reflection. progress.
exists (fun ga i => dmap (D ga i) (fun (x : rt * (glob A)) => x.`2)).
progress.
rewrite - (H &m (fun (x : rt * (glob A)) => M x.`2) i) .
rewrite dmapE. auto.
qed.


lemma reflection_simple_res : exists (D : (glob A) -> at -> rt distr),
    forall &m M a, mu (D (glob A){m} a) M = Pr[ A.run(a) @ &m :  M res ].
proof.
elim reflection. progress.
exists (fun ga i => dmap (D ga i) (fun (x : rt * (glob A)) => x.`1)).
progress.
rewrite - (H &m (fun (x : rt * (glob A)) => M x.`1) a) .
rewrite dmapE. auto.
qed.


end section.
end  Refl.

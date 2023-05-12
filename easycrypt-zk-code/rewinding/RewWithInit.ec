pragma Goals:printall.
require import AllCore.

require import Distr.
require import List.
require import AllCore List Binomial.
require import Ring StdRing StdOrder StdBigop Discrete RealSeq RealSeries.
(*---*) import IterOp Bigint Bigreal Bigreal.BRA.
(*---*) import IntOrder RealOrder RField.
require import Finite.
require (*--*) FinType.
require import RealFun.
require import JensensInf.
require import RandomFacts.
require import SquareConvex.


theory RWI.

type sbits, iat, rrt, irt.

op pair_sbits : sbits * sbits -> sbits.
op unpair: sbits -> sbits * sbits.
axiom ips: injective pair_sbits. 
axiom unpair_pair x : unpair (pair_sbits x) = x.


require RewBasics.
clone import RewBasics as RW with type sbits <- sbits,
                                  type iat   <- iat,
                                  type iat2  <- irt,
                                  type rrt   <- rrt,
                                  type irt   <- irt,
                                  op pair_sbits <- pair_sbits,
                                  op unpair <- unpair.


require Reflection.
clone import Reflection.Refl as Re with
                                  type at  <- iat,
                                  type rt  <- irt * sbits.

  


require FiniteApproximation.
clone import FiniteApproximation.FinApprox as FA with type at <- iat,
                                                      type rt <- irt * sbits.


module QQ(A : RewRun, B : Initializer) = {
    module G = GetRunSetRunConj(A)

    proc main51(i:iat) = {
      var rb,s;
      rb <@ B.init(i);
      s <@ A.getState();
      return (rb, s);
    }

    proc main52(i : irt) = {
      var r;
      r <@ G.main(i);
      return r;
    }
    
    proc main5(i:iat) = {
      var s, r;
      s <@ main51(i);
      r <@ main52(s.`1);
      return (r,s);
    }

    proc main6(i:iat) = {
      var s, r;
      s <@ main51(i);
      r <@ A.run(s.`1);
      return ((s.`1, r),s);
    }

    proc main(i:iat) = {
      var s, r0, r1, r2;
      r0 <@ B.init(i);
      s <@ A.getState();
      r1 <@ A.run(r0);
      A.setState(s);
      r2 <@ A.run(r0);
      return ((r0,r1), (r0, r2));
    }

    proc main_run'(i:iat) = {
      var s, r, r0;
      r0 <@ B.init(i);
      s <@ A.getState();
      r <@ A.run(r0);
      return (r0, r);
    }

    proc main_run(i:iat) = {
      var r, r0;
      r0 <@ B.init(i);
      r <@ A.run(r0);
      return (r0, r);
    }
}.


section.
declare module A <: RewRun.
declare module B <: Initializer.


local module RunMe = {
  module QQ = QQ(A,B)
  proc main(i:iat) : irt * sbits = {
      var s, r;
      s <@ QQ.main51(i);
      r <@ A.run(s.`1);
      return s;    
  }
}.


(* ASSUMPTIONS *)
declare axiom Bsens : equiv[ B.init ~ B.init : ={arg, glob A, glob B} ==> ={glob A} ].    
declare axiom Bsens2 : equiv[ B.init ~ B.init : ={arg, glob A, glob B} ==> ={res, glob A} ].    

declare axiom RewProp :
  exists (f : glob A -> sbits),
  injective f /\
  (forall &m, Pr[ A.getState() @ &m : (glob A) = ((glob A){m})
                                   /\ res = f ((glob A){m} ) ] = 1%r) /\
  (forall &m b (x: glob A), b = f x =>
    Pr[A.setState(b) @ &m : glob A = x] = 1%r) /\
  islossless A.setState.

  
(* declare axiom ll_A_run : islossless A.run. *)
declare axiom ll_B_init : islossless B.init.
(* /ASSUMPTIONS *)



local lemma intlem1 &m M i :
    Pr[ QQ(A,B).main5(i) @ &m : M res.`1.`1 /\ M res.`1.`2 ]
    = Pr[ QQ(A,B).main(i) @ &m : M res.`1 /\ M res.`2 ].
proof. byequiv (_: (={arg, glob A, glob B}) ==> _).
proc. inline*. 
seq 2 1 : (rb{1} = r0{2} /\ ={glob A}). sp. call Bsens2. skip. auto.
wp. call(_:true). wp.
elim (rewindable_A A RewProp).
move => fA [s1 [s2 [s3]]] s4. 
call (_:true). call(_:true).
call (_:true).
wp.
conseq (_: exists ga, (glob A){1} = ga /\ rb{1} = r0{2} /\ ={glob A} ==> _). smt().
elim*. move => ga. call {1} (s2 ga).
skip. progress. auto. auto.
qed.


local lemma intlem2 &m M i : Pr[ QQ(A,B).main6(i) @ &m : M res.`1 ] 
 = Pr[ QQ(A,B).main_run'(i) @ &m : M res ].
proof.  byequiv (_: (={arg, glob A, glob B}) ==> _).
proc. inline*. 
seq 2 1 : (rb{1} = r0{2} /\ ={glob A}). sp. call Bsens2. skip. auto.
wp. call (_:true). wp. call (_:true). skip. progress. auto. auto.
qed.
  

local lemma www : forall &m i, forall (s0 : sbits) r,
   phoare [ QQ(A,B).main51 : arg = i /\ (glob A) = (glob A){m} 
   /\ (glob B) = (glob B){m} ==> res.`2 = s0 /\ res.`1 = r ] 
   = Pr[ QQ(A,B).main51(i) @ &m : res.`2 = s0 /\ res.`1 = r].
proof. move => &m i s0 r. bypr.
move => &m0. move => e. byequiv (_: ={arg, glob A, glob B} ==> _).
proc.
seq 1 1 : (={rb, glob A}).
call Bsens2.
skip. auto. 
call (_:true).
skip. progress. progress. trivial.
qed.


local lemma yyy &m0 &m1 M a : (glob A){m0} = (glob A){m1} => 
  Pr[QQ(A,B).main52(a) @ &m1 : M res.`1 /\ M res.`2] 
  = Pr[QQ(A,B).main52(a) @ &m0 : M res.`1 /\ M res.`2]. 
move => q. byequiv. proc. 
inline*. wp. call(_:true). wp. call (_:true). call(_:true). 
call(_:true).  wp. skip. progress. smt().  auto. auto.
qed.


local lemma zzz &m &n : exists (f : glob A -> sbits),
       injective f 
    /\ (forall (x : glob A),
         phoare[ A.getState : (glob A) = x ==> (glob A) = x  /\ res = f x ] = 1%r) 
    /\ (forall (x : glob A),
         hoare[ A.getState : (glob A) = x ==> (glob A) = x  /\ res = f x ]) 
    /\ (forall (x: glob A),
         phoare[A.setState: b = f x ==> glob A = x] = 1%r)
    /\ (forall (x: glob A),
         hoare[A.setState: b = f x ==> glob A = x])
    /\ islossless A.setState
    (* /\ islossless A.run *)
(*    /\ islossless B.init  *)
    (* assumptions above, payload below *)
    /\ (forall &m M s0 a, f (glob A){m} = s0 => 
         phoare [ QQ(A,B).main52 : f (glob A) = s0 /\ arg = a ==> M res.`1 
                /\ M res.`2  ] 
         = Pr[ QQ(A,B).main52(a) @ &m : M res.`1 /\ M res.`2  ]).
elim (rewindable_A_plus A RewProp) .
progress.
exists f.
progress. (* apply ll_A_run. *) (* apply ll_B_run.*)
bypr.  move => &m1 eq.
have jk  : (glob A){m0} = (glob A){m1}. smt().
elim eq. move => _ z. rewrite z.
apply (yyy &m0 &m1 ). auto.
qed.


local lemma qqq &m &n : exists (f : glob A -> sbits),
       injective f 
    /\ (forall (x : glob A),
         phoare[ A.getState : (glob A) = x ==> (glob A) = x  /\ res = f x ] = 1%r) 
    /\ (forall (x : glob A),
         hoare[ A.getState : (glob A) = x ==> (glob A) = x  /\ res = f x ]) 
    /\ (forall (x: glob A),
         phoare[A.setState: b = f x ==> glob A = x] = 1%r)
    /\ (forall (x: glob A),
         hoare[A.setState: b = f x ==> glob A = x])
    /\ islossless A.setState
    (* /\ islossless A.run *)
(*    /\ islossless B.init *)
    (* assumptions above, payload below *)
    /\ (forall &m M s0 r, f (glob A){m} = s0 => 
         phoare [ QQ(A,B).main52 : f (glob A) = s0 /\ arg = r 
         ==> M res.`1 /\ M res.`2  ] 
       = Pr[ QQ(A,B).main52(r) @ &m : M res.`1 /\ M res.`2  ])
    /\ (forall s0 r, (forall &n, f (glob A){n} <> s0) => 
         (forall &m M i, Pr[ QQ(A,B).main6(i) @ &m : M res.`1 
         /\ res.`2.`2 = s0 /\ res.`2.`1 = r ] = 0%r))
    /\ (forall s0 r, (forall &n , f (glob A){n} <> s0) => 
         (forall &m M i, Pr[ QQ(A,B).main5(i) @ &m : M res.`1.`1 
         /\ M res.`1.`2 /\ res.`2.`2 = s0 /\ res.`2.`1 = r ] = 0%r))
    /\ (forall s0 r, (forall &n , f (glob A){n} <> s0) => 
         (forall &m i, Pr[ QQ(A,B).main51(i) @ &m :  res.`2 = s0 
          /\ res.`1 = r ] = 0%r))
    /\ forall &m M &n s0 i r , f (glob A){n} = s0 => 
        Pr[ QQ(A,B).main5(i) @ &m : M res.`1.`1 /\ M res.`1.`2 
          /\ res.`2.`2 = s0 /\ res.`2.`1 = r ] 
      = Pr[ QQ(A,B).main51(i) @ &m : res.`2 = s0 /\ res.`1 = r ] 
      * Pr[ QQ(A,B).main52(r) @ &n : M res.`1 /\ M res.`2 ].
proof. elim (zzz &m &n).
progress. exists f. progress. byphoare.
proc. seq 1 : (f (glob A) = s0) 0%r 0%r 1%r 0%r (f (glob A) = s.`2). 
inline*. wp.
seq 2 : (true).
call (_:true). wp.  skip. auto.
conseq (_: exists q, q = glob A ==> _). smt().
elim*. move => q.
inline*. wp.
call (H1 q).
skip. smt().
hoare.
inline*.
wp.
seq 2 : (true). 
call (_:true). wp. skip. auto.
conseq (_: exists q, q = glob A ==> _). smt().
elim*. move => q.
call (H1 q).
skip. smt().
simplify.
hoare. call(_:true).
skip. smt(). auto. auto. auto.
byphoare.
proc.
seq 1 : (f (glob A) = s0) 0%r 0%r 1%r 0%r (f (glob A) = s.`2). 
inline*. wp.
seq 2 : (true). 
call (_:true).  wp. skip. auto.
conseq (_: exists q, q = glob A ==> _). smt().
elim*. move => q.
inline*. wp.
call (H1 q).
skip. smt().
hoare.
inline*.
wp.
seq 2 : (true). sp.
call (_:true). skip. auto.
conseq (_: exists q, q = glob A ==> _). smt().
elim*. move => q.
call (H1 q).
skip. smt().
simplify.
hoare. call(_:true).
inline*.  wp.  call(_:true). wp. call(_:true). call(_:true).  call (_: true).  wp. skip. auto.
skip. smt(). auto. auto. auto.
byphoare.
proc.
seq 1 : (true) 1%r 0%r 1%r 0%r . 
call (_:true).  skip. auto.
conseq (_: exists q, q = glob A ==> _). smt().
elim*. move => q.
hoare.
call (H1 q).
skip. smt(). exfalso. auto.
auto. auto. auto.
byphoare (_ :  (arg = i) /\ (glob A) = (glob A){m0} /\ (glob B) = (glob B){m0} ==> _).
proc*.
inline QQ(A,B).main5.
pose x := (Pr[QQ(A,B).main51(i) @ &m0 : res.`2 =  f (glob A){n0} /\ res.`1 = r]). 
pose y := (Pr[QQ(A,B).main52(r) @ &n0 : M res.`1 /\ M res.`2]). simplify.
seq 2 : (s = (r, f (glob A){n0})) (Pr[QQ(A,B).main51(i) @ &m0 : res.`2 = f (glob A){n0} /\ res.`1 = r ]) y (1%r - x) 0%r (f (glob A) = s.`2). sp.
inline*.
seq 2 : (i1 = i0). sp.
call (_: true).  skip. progress.
conseq (_: exists w, exists z, glob A = w /\ glob B = z /\ i1 = i0 ==>  i1 = i0 /\ f (glob A) = s.`2 /\ rb = s.`1).
smt(). smt(). elim*.  move => w z. wp.
conseq (_: _ ==> (glob A) = w  /\ s0 = f w /\ i1 = i0 /\ rb =  rb).
progress.
call (H1 w).
progress. 
call (www &m0  i (f (glob A){n0}) r). wp.
skip. progress.
simplify. smt().
have H8 : phoare[ QQ(A,B).main52 : f (glob A) =  f (glob A){n0} /\ arg = r 
          ==> M res.`1 /\ M res.`2] 
          = Pr[QQ(A,B).main52(r) @ &n0 : M res.`1 /\ M res.`2 ]. 
apply (H5 &n0). auto.
have q1 : Pr[QQ(A,B).main52(r) @ &n0 : M res.`1 /\ M res.`2] = y. auto.
have q3 : phoare[ QQ(A,B).main52 : f (glob A) =  f (glob A){n0} /\ arg = r 
          ==> M res.`1 /\ M res.`2] = y.  rewrite - q1.
apply H8. wp. call q3. skip. progress. 
wp. hoare. call(_:true). inline*.  wp. call(_:true). wp. 
call(_:true). call(_:true).  call (_: true).  wp. skip. auto.
skip. progress.
smt(). smt(). auto. auto.
qed.


local lemma ooo &m &n : exists (f : glob A -> sbits),
       injective f 
    /\ (forall (x : glob A),
         phoare[ A.getState : (glob A) = x ==> (glob A) = x  /\ res = f x ] = 1%r) 
    /\ (forall (x : glob A),
         hoare[ A.getState : (glob A) = x ==> (glob A) = x  /\ res = f x ]) 
    /\ (forall (x: glob A),
         phoare[A.setState: b = f x ==> glob A = x] = 1%r)
    /\ (forall (x: glob A),
         hoare[A.setState: b = f x ==> glob A = x])
    /\ islossless A.setState
    (* /\ islossless A.run *)
(*    /\ islossless B.init  *)
    (* assumptions above, payload below *)
    /\ (forall &m M s0 a, f (glob A){m} = s0 => 
         phoare [ QQ(A,B).main52 : f (glob A) = s0 /\ arg = a 
         ==> M res.`1 /\ M res.`2  ] 
       = Pr[ QQ(A,B).main52(a) @ &m : M res.`1 /\ M res.`2  ])
    /\ (forall s0 r, (forall &n, f (glob A){n} <> s0) => 
         (forall &m M i, Pr[ QQ(A,B).main6(i) @ &m : M res.`1 
                           /\ res.`2.`2 = s0 /\ res.`2.`1 = r ] = 0%r))
    /\ (forall s0 r, (forall &n , f (glob A){n} <> s0) => 
         (forall &m M i, Pr[ QQ(A,B).main5(i) @ &m : M res.`1.`1 /\ M res.`1.`2 
                           /\ res.`2.`2 = s0 /\ res.`2.`1 = r ] = 0%r))
    /\ (forall s0 r, (forall &n , f (glob A){n} <> s0) => 
         (forall &m i, Pr[ QQ(A,B).main51(i) @ &m :  res.`2 = s0 
                         /\ res.`1 = r ] = 0%r))    
   /\ (forall &m &n M s0 i r, f (glob A){n} = s0 => 
        Pr[ QQ(A,B).main5(i) @ &m : M res.`1.`1 /\ M res.`1.`2 
          /\ res.`2.`2 = s0 /\ res.`2.`1 = r ] 
      = Pr[ QQ(A,B).main51(i) @ &m : res.`2 = s0 /\ res.`1 = r ] 
      * Pr[ A.run(r) @ &n : M (r, res) ] * Pr[ A.run(r) @ &n : M (r, res) ]).
proof. elim (qqq &m &n). progress. exists f. progress .
have eq :  Pr[QQ(A,B).main52(r) @ &n0 : M res.`1 /\ M res.`2] 
           = Pr[ GetRunSetRunConj(A).main(r) @ &n0 : M res.`1 /\ M res.`2 ].
byequiv;auto.
proc. inline*.  wp. call (_:true). wp. call(_:true). call(_:true). 
call(_:true). wp. skip. progress.
have eq2 : Pr[QQ(A,B).main5(i) @ &m0 : M res.`1.`1 
             /\ M res.`1.`2 /\ res.`2.`2 = f (glob A){n0} /\ res.`2.`1 = r] 
           = Pr[QQ(A,B).main51(i) @ &m0 : res.`2 = f (glob A){n0} /\ res.`1 = r] 
             * Pr[QQ(A,B).main52(r) @ &n0 : M res.`1 /\ M res.`2].
rewrite (H9 &m0 M &n0).  by reflexivity.
auto. rewrite eq2 eq.
rewrite (dbl_main_no_number A). apply RewProp. smt().
qed.


local lemma ppp &m &n : exists (f : glob A -> sbits),
       injective f 
    /\ (forall (x : glob A),
         phoare[ A.getState : (glob A) = x ==> (glob A) = x  /\ res = f x ] = 1%r) 
    /\ (forall (x : glob A),
         hoare[ A.getState : (glob A) = x ==> (glob A) = x  /\ res = f x ]) 
    /\ (forall (x: glob A),
         phoare[A.setState: b = f x ==> glob A = x] = 1%r)
    /\ (forall (x: glob A),
         hoare[A.setState: b = f x ==> glob A = x])
    /\ islossless A.setState
    (* /\ islossless A.run *)
(*    /\ islossless B.init *)
    (* assumptions above, payload below *)
    /\ (forall &m M s0 a, f (glob A){m} = s0 => 
         phoare [ QQ(A,B).main52 : f (glob A) = s0 /\ arg = a ==> M res.`1 
         /\ M res.`2  ] 
       = Pr[ QQ(A,B).main52(a) @ &m : M res.`1 /\ M res.`2  ])
    /\ (forall s0 r, (forall &n, f (glob A){n} <> s0) => 
         (forall &m M i, Pr[ QQ(A,B).main6(i) @ &m : M res.`1 /\ res.`2.`2 = s0 
                           /\ res.`2.`1 = r ] = 0%r))
    /\ (forall s0 r, (forall &n , f (glob A){n} <> s0) => 
         (forall &m M i, Pr[ QQ(A,B).main5(i) @ &m : M res.`1.`1 /\ M res.`1.`2 
                           /\ res.`2.`2 = s0 /\ res.`2.`1 = r ] = 0%r))
    /\ (forall s0 r, (forall &n , f (glob A){n} <> s0) => 
         (forall &m i, Pr[ QQ(A,B).main51(i) @ &m :  res.`2 = s0 
                         /\ res.`1 = r ] = 0%r))    
   /\ (forall &m &n M s0 i r, f (glob A){n} = s0 => 
        Pr[ QQ(A,B).main5(i) @ &m : M res.`1.`1 /\ M res.`1.`2 
          /\ res.`2.`2 = s0 /\ res.`2.`1 = r ] 
        = Pr[ QQ(A,B).main51(i) @ &m : res.`2 = s0 /\ res.`1 = r ] 
          * Pr[ A.run(r) @ &n : M (r, res) ] * Pr[ A.run(r) @ &n : M (r, res) ])
    /\ (forall &m &n M s0 i r, f (glob A){n} = s0 => 
        Pr[ QQ(A,B).main6(i) @ &m : M res.`1 /\ res.`2.`2 = s0 /\ res.`2.`1 = r ] 
      = Pr[ QQ(A,B).main51(i) @ &m : res.`2 = s0 /\ res.`1 = r ] 
        * Pr[ A.run(r) @ &n : M (r, res) ]).
proof. elim (ooo &m &n). progress. exists f. progress. 
byphoare (_ : (arg = i) /\ (glob A) = (glob A){m0} 
              /\ (glob B) = (glob B){m0} ==> _).
proc*. inline QQ(A,B).main6.
pose x := (Pr[QQ(A,B).main51(i) @ &m0 : res.`2 = f (glob A){n0} /\ res.`1 = r]).
pose y := (Pr[A.run(r) @ &n0 : M (r, res)]). simplify.
seq 2 : (s.`2 = f (glob A){n0} /\ s.`1 = r) 
        (Pr[QQ(A,B).main51(i) @ &m0 : res.`2 = f (glob A){n0} /\ res.`1 = r]) 
        y (1%r - x) 0%r (f (glob A) = s.`2). sp.
inline*. seq 1 : (i1 = i0). wp. skip. auto. seq 1 : (i1 = i0).
call (_:true). skip. auto.
conseq (_: exists w, exists z, glob A = w /\ glob B = z ==> _).
smt(). progress. elim*.  move => w z. wp.
conseq (_: _ ==> (glob A) = w  /\ s0 = f w ).
progress. call (H1 w).  skip.
progress. call (www &m0 i (f (glob A){n0}) r).
simplify. wp. skip. progress. wp. simplify.
have q2 : forall &n0, f (glob A){n0} = f (glob A){n0} => 
  phoare[ A.run : arg = r /\ f (glob A) = f (glob A){n0} 
  ==> M (r, res)] = Pr[A.run(r) @ &n0 : M (r, res)]. 
move => &no eq. bypr. move => &mo eq2. byequiv.
proc*. call (_:true). skip. progress. smt(). smt(). smt(). smt().
have q1 : Pr[A.run(r) @ &n0 : M (r, res)] = y. auto.
have q3 : phoare[ A.run : arg = r /\ f (glob A) = f (glob A){n0} 
          ==> M (r, res)] = y.  rewrite - q1.
apply (q2 &n0). auto. call q3. skip. progress. smt().
wp. hoare. call(_:true). inline*. wp.  
skip. smt(). simplify. smt(). auto. auto.
qed.


local lemma bigLemma ['a] (f : 'a -> real) : forall l x, 
  big predT f (x :: l) = f x + big predT f l.
proof. apply list_ind. smt(). move => x l ih. simplify. smt().
qed.


local lemma lll &m P i : forall (M : sbits list), uniq M =>
  Pr[ QQ(A,B).main5(i) @ &m : P res.`1.`1 /\ P res.`1.`2 /\ (res.`2.`2 \in M) ] 
  = big predT  (fun x => Pr[ QQ(A,B).main5(i) @ &m : P res.`1.`1 
                           /\ P res.`1.`2 /\ (res.`2.`2 = x) ]) M.
proof. apply list_ind.
simplify. rewrite Pr[mu_false]. smt().
simplify.   
move => x l ih. 
rewrite (bigLemma (fun (x0 : sbits) => Pr[QQ(A,B).main5(i) @ &m : P res.`1.`1 
                             /\ P res.`1.`2 /\ res.`2.`2 = x0]) l x). simplify.
elim. move => ne un. rewrite - ih. apply un.
have qq : Pr[QQ(A,B).main5(i) @ &m : P res.`1.`1 /\ P res.`1.`2 
            /\ (res.`2.`2 = x \/ (res.`2.`2 \in l))]
        = Pr[QQ(A,B).main5(i) @ &m : (P res.`1.`1 /\ P res.`1.`2 /\ res.`2.`2 = x) 
            \/ (P res.`1.`1 /\ P res.`1.`2 /\ res.`2.`2 \in l)] .
rewrite Pr[mu_eq ]. smt(). auto. rewrite qq.
rewrite Pr[ mu_disjoint ]. smt().
auto.
qed.


local lemma nnn &m &n : exists (f : glob A -> sbits),
       injective f
    /\ (forall (x : glob A),
         phoare[ A.getState : (glob A) = x ==> (glob A) = x  /\ res = f x ] = 1%r)
    /\ (forall (x : glob A),
         hoare[ A.getState : (glob A) = x ==> (glob A) = x  /\ res = f x ])
    /\ (forall (x: glob A),
         phoare[A.setState: b = f x ==> glob A = x] = 1%r)
    /\ (forall (x: glob A),
         hoare[A.setState: b = f x ==> glob A = x])
    /\ islossless A.setState
    (* /\ islossless A.run *)
(*    /\ islossless B.init *)
    (* assumptions above, payload below *)
    /\ (forall &m M s0 a, f (glob A){m} = s0 =>
         phoare [ QQ(A,B).main52 : f (glob A) = s0 /\ arg = a ==> M res.`1 
                /\ M res.`2  ]
       = Pr[ QQ(A,B).main52(a) @ &m : M res.`1 /\ M res.`2  ])
    /\ (forall s0 r, (forall &n, f (glob A){n} <> s0) =>
         (forall &m M i, Pr[ QQ(A,B).main6(i) @ &m : M res.`1 
                           /\ res.`2.`2 = s0 /\ res.`2.`1 = r ] = 0%r))
    /\ (forall s0 r, (forall &n , f (glob A){n} <> s0) =>
         (forall &m M i, Pr[ QQ(A,B).main5(i) @ &m : M res.`1.`1 /\ M res.`1.`2 /\ res.`2.`2 = s0 /\ res.`2.`1 = r ] = 0%r))
    /\ (forall s0 r, (forall &n , f (glob A){n} <> s0) =>
         (forall &m i, Pr[ QQ(A,B).main51(i) @ &m :  res.`2 = s0 /\ res.`1 = r ] = 0%r))
    /\ (forall &m &n M s0 i r, f (glob A){n} = s0 =>
        Pr[ QQ(A,B).main5(i) @ &m : M res.`1.`1 /\ M res.`1.`2 /\ res.`2.`2 = s0 /\ res.`2.`1 = r ]
        = Pr[ QQ(A,B).main51(i) @ &m : res.`2 = s0 /\ res.`1 = r ] * Pr[ A.run(r) @ &n : M (r, res) ] * Pr[ A.run(r) @ &n : M (r, res) ])
   /\ (forall &m &n M s0 i r, f (glob A){n} = s0 =>
        Pr[ QQ(A,B).main6(i) @ &m : M res.`1 /\ res.`2.`2 = s0 /\ res.`2.`1 = r ]
      = Pr[ QQ(A,B).main51(i) @ &m : res.`2 = s0 /\ res.`1 = r ] * Pr[ A.run(r) @ &n : M (r, res) ])
   /\ (forall &m &n M s0 i r, f (glob A){n} = s0 =>
        Pr[ QQ(A,B).main5(i) @ &m : M res.`1.`1 /\ M res.`1.`2 /\ res.`2.`2 = s0 /\ res.`2.`1 = r ]
        = Pr[ QQ(A,B).main51(i) @ &m : res.`2 = s0 /\ res.`1 = r ] * Pr[ A.run(r) @ &n : M (r, res) ] * Pr[ A.run(r) @ &n : M (r, res) ])
   /\ (forall P i (M : (irt * sbits) list), uniq M =>
      Pr[ QQ(A,B).main5(i) @ &m : P res.`1.`1 /\ P res.`1.`2 /\ (res.`2 \in M)  ]
      = big predT (fun (x : irt * sbits) =>   Pr[ QQ(A,B).main51(i) @ &m : res = x  ] * (some_real (fun y => exists &l, f (glob A){l} = x.`2 /\  Pr[ A.run(x.`1) @ &l : P (x.`1, res) ]  = y )) * (some_real (fun y => exists &l, f (glob A){l} = x.`2 /\  Pr[ A.run(x.`1) @ &l : P (x.`1, res) ]  = y )))                    M).
proof. elim (ppp &m &n). progress. exists f. split. assumption.
split. assumption. split. assumption. split. assumption. split. assumption.
split. assumption. split. assumption. split. assumption. split. assumption.
split. assumption.
split. assumption. split. assumption. split. assumption.  (* split. assumption. *)
move => P i. apply list_ind. simplify. rewrite Pr[mu_false]. smt().
simplify.
move => x l ih.
elim. move=> xl ul.
have qq : Pr[QQ(A,B).main5(i) @ &m : P res.`1.`1 /\ P res.`1.`2 /\ (res.`2 = x \/ (res.`2 \in l))]
        = Pr[QQ(A,B).main5(i) @ &m : (P res.`1.`1 /\ P res.`1.`2 /\ res.`2 = x) \/ (P res.`1.`1 /\ P res.`1.`2 /\ res.`2 \in l)] .
rewrite Pr[ mu_eq ]. smt(). auto.
have ->: Pr[QQ(A, B).main5(i) @ &m :
   P res.`1.`1 /\
   P res.`1.`2 /\ (res.`2 = x \/ (res.`2 \in l)) ]
  = Pr[QQ(A, B).main5(i) @ &m :
       P res.`1.`1 /\
       P res.`1.`2 /\ (res.`2 = x  \/ (res.`2 \in l))].
rewrite Pr[mu_eq]. smt(). auto.
rewrite qq.
rewrite Pr[ mu_disjoint ]. smt().
pose E (x0 : irt * sbits) :=  (fun (y : real) =>
          exists &l, f (glob A){l} = x0.`2 /\ Pr[A.run(x0.`1) @ &l : P (x0.`1, res)] = y).
rewrite (bigLemma (fun (x0 : irt * sbits) =>
     Pr[QQ(A,B).main51(i) @ &m : res = x0] *
     some_real
       (E x0) *
     some_real
       (E x0)) l x).
simplify.
simplify.
rewrite - ih. apply  ul.
have : Pr[QQ(A,B).main51(i) @ &m : res = x ] *
some_real (E x) *
some_real (E x) = Pr[QQ(A,B).main5(i) @ &m : P res.`1.`1 /\ P res.`1.`2 /\ res.`2 = x ].
case (exists &l, f (glob A){l} = x.`2).
elim. move => &lk lp.
have : E x (some_real (E x)).
apply (some_real_prop (E x)).
exists (Pr[ A.run(x.`1) @ &lk : P (x.`1, res) ]).
split. progress. simplify E. exists &lk.
smt().
move => q. elim.
move => &l0.
elim.
move => o1 o2.    rewrite - o2.
byequiv.  proc*. call (_:true). skip. progress. smt(). smt(). smt().
elim.
move => &l. elim.
move => c eq.
rewrite - eq.
have ->: Pr[QQ(A, B).main51(i) @ &m : res = x] = Pr[QQ(A, B).main51(i) @ &m : res.`2 = x.`2 /\ res.`1 = x.`1].  rewrite Pr[mu_eq]. smt(). auto.
have ->: Pr[QQ(A, B).main5(i) @ &m : P res.`1.`1 /\ P res.`1.`2 /\ res.`2 = x]
     = Pr[QQ(A, B).main5(i) @ &m : P res.`1.`1 /\ P res.`1.`2 /\ res.`2.`2 = x.`2 /\ res.`2.`1 = x.`1 ] . rewrite Pr[mu_eq]. smt(). auto.
rewrite (H9  &m &l  P x.`2 i ).
 smt().  auto.
move => dnem.
have : (forall &n0, f (glob A){n0} <> x.`2). smt().
move => prr.
have ->: Pr[QQ(A, B).main51(i) @ &m : res = x] = Pr[QQ(A, B).main51(i) @ &m : res.`2 = x.`2 /\ res.`1 = x.`1].  rewrite Pr[mu_eq]. smt(). auto.
have ->: Pr[QQ(A, B).main5(i) @ &m : P res.`1.`1 /\ P res.`1.`2 /\ res.`2 = x]
     = Pr[QQ(A, B).main5(i) @ &m : P res.`1.`1 /\ P res.`1.`2 /\ res.`2.`2 = x.`2 /\ res.`2.`1 = x.`1 ] . rewrite Pr[mu_eq]. smt(). auto.
rewrite (H8 x.`2). apply prr.
rewrite (H7 x.`2). apply prr.
auto.
move => opp.
rewrite opp.
auto.
qed.


local module W2 = {
  module Q = QQ(A,B)
  proc main(i:iat) = {
    var r;
    r <@ Q.main5(i);
    return r.`2;
  }
}.


local lemma nnn1 &m &n : exists (f : glob A -> sbits),
       injective f
    /\ (forall (x : glob A),
         phoare[ A.getState : (glob A) = x ==> (glob A) = x  /\ res = f x ] = 1%r)
    /\ (forall (x : glob A),
         hoare[ A.getState : (glob A) = x ==> (glob A) = x  /\ res = f x ])
    /\ (forall (x: glob A),
         phoare[A.setState: b = f x ==> glob A = x] = 1%r)
    /\ (forall (x: glob A),
         hoare[A.setState: b = f x ==> glob A = x])
    /\ islossless A.setState
    (* /\ islossless A.run *)
(*    /\ islossless B.init *)
    (* assumptions above, payload below *)
    /\ (forall &m M s0 a, f (glob A){m} = s0 =>
         phoare [ QQ(A,B).main52 : f (glob A) = s0 /\ arg = a ==> M res.`1 /\ M res.`2  ]
       = Pr[ QQ(A,B).main52(a) @ &m : M res.`1 /\ M res.`2  ])
    /\ (forall s0 r, (forall &n, f (glob A){n} <> s0) =>
         (forall &m M i, Pr[ QQ(A,B).main6(i) @ &m : M res.`1 /\ res.`2.`2 = s0 /\ res.`2.`1 = r ] = 0%r))
    /\ (forall s0 r, (forall &n , f (glob A){n} <> s0) =>
         (forall &m M i, Pr[ QQ(A,B).main5(i) @ &m : M res.`1.`1 /\ M res.`1.`2 /\ res.`2.`2 = s0 /\ res.`2.`1 = r ] = 0%r))
    /\ (forall s0 r, (forall &n , f (glob A){n} <> s0) =>
         (forall &m i, Pr[ QQ(A,B).main51(i) @ &m :  res.`2 = s0 /\ res.`1 = r ] = 0%r))
    /\ (forall &m &n M s0 i r, f (glob A){n} = s0 =>
        Pr[ QQ(A,B).main5(i) @ &m : M res.`1.`1 /\ M res.`1.`2 /\ res.`2.`2 = s0 /\ res.`2.`1 = r ]
        = Pr[ QQ(A,B).main51(i) @ &m : res.`2 = s0 /\ res.`1 = r ] * Pr[ A.run(r) @ &n : M (r, res) ] * Pr[ A.run(r) @ &n : M (r, res) ])
   /\ (forall &m &n M s0 i r, f (glob A){n} = s0 =>
        Pr[ QQ(A,B).main6(i) @ &m : M res.`1 /\ res.`2.`2 = s0 /\ res.`2.`1 = r ]
      = Pr[ QQ(A,B).main51(i) @ &m : res.`2 = s0 /\ res.`1 = r ] * Pr[ A.run(r) @ &n : M (r, res) ])
   /\ (forall &m &n M s0 i r, f (glob A){n} = s0 =>
        Pr[ QQ(A,B).main5(i) @ &m : M res.`1.`1 /\ M res.`1.`2 /\ res.`2.`2 = s0 /\ res.`2.`1 = r ]
        = Pr[ QQ(A,B).main51(i) @ &m : res.`2 = s0 /\ res.`1 = r ] * Pr[ A.run(r) @ &n : M (r, res) ] * Pr[ A.run(r) @ &n : M (r, res) ])
   /\ (forall P i,
      Pr[ QQ(A,B).main5(i) @ &m : P res.`1.`1 /\ P res.`1.`2 ]
      = sum (fun (x : irt * sbits) =>  Pr[ QQ(A,B).main51(i) @ &m : res = x  ] * (some_real (fun y => exists &l, f (glob A){l} = x.`2 /\  Pr[ A.run(x.`1) @ &l : P (x.`1, res) ]  = y )) * (some_real (fun y => exists &l, f (glob A){l} = x.`2 /\  Pr[ A.run(x.`1) @ &l : P (x.`1, res) ]  = y )))).
proof. elim (nnn &m &n). progress. exists f. split. assumption.
split. assumption. split. assumption. split. assumption. split. assumption.
split. assumption. split. assumption. split. assumption. split. assumption.
split. assumption.
split. assumption. split. assumption. split. assumption.  (* split. assumption. *)
move => P i.
  clear H0 H1 H2 H3 H4 H5 H6 H7 H8  H9 H10 H11   .
  have refl1 :     exists (D : (irt * sbits) distr),  
  exists (J : int -> (irt * sbits) option),
  (forall M, mu D M = Pr[ QQ(A,B).main5(i) @ &m :  M res.`2 ])
  /\ enumerate J (support D) /\
  RealSeq.convergeto (fun N => Pr[ QQ(A,B).main5(i) @ &m : ! (res.`2 \in (pmap J (range 0 N))) ]) 0%r.
  elim (fin_approx_prog_no_glob_conv W2 &m i). move => D J. elim. move => DP [JP1 JP2]. 
    have D5 : forall (M : irt * sbits -> bool), mu D M = Pr[QQ(A, B).main5(i) @ &m : M res.`2].
     move => M. rewrite DP.
     byequiv (_: (={arg, glob A, glob B}) ==> _). proc.
     inline W2.Q.main5.
     wp.   call(_: (={arg, glob A}) ==> ={res}). sim.
    call (_: (={arg, glob A, glob B}) ==> ={glob A, res}). 
    proc. seq 1 1 : (={rb, glob A}). call Bsens2. skip. auto. call (_:true). skip. smt(). wp. skip. smt().
    auto.  auto. 
    exists D J.
    split.
    apply D5.
    split. apply JP1.
    have ->: (fun (N : int) =>
      Pr[QQ(A, B).main5(i) @ &m : ! (res.`2 \in pmap J (range 0 N))]) = (fun (N : int) =>
           Pr[W2.main(i) @ &m : ! (res \in pmap J (range 0 N))]).
    apply fun_ext. move => N. rewrite -  (D5 (fun (r : irt * sbits) => ! (r \in pmap J (range 0 N))) ).
    rewrite DP. auto.
         apply JP2.
pose g := (fun (x : irt * sbits) =>
     Pr[QQ(A, B).main51(i) @ &m : res = x] *
     some_real
       (fun (y : real) =>
          exists &l,
            f (glob A){l} = x.`2 /\ Pr[A.run(x.`1) @ &l : P (x.`1, res)] = y) *
     some_real
       (fun (y : real) =>
          exists &l,
            f (glob A){l} = x.`2 /\ Pr[A.run(x.`1) @ &l : P (x.`1, res)] = y)).
have zz: forall x, Pr[QQ(A, B).main5(i) @ &m :
          P res.`1.`1 /\ P res.`1.`2 /\ res.`2 = x] =  Pr[QQ(A, B).main51(i) @ &m : res = x] *
some_real
  (fun (y : real) =>
     exists &l,
       f (glob A){l} = x.`2 /\ Pr[A.run(x.`1) @ &l : P (x.`1, res)] = y) *
some_real
  (fun (y : real) =>
     exists &l,
       f (glob A){l} = x.`2 /\ Pr[A.run(x.`1) @ &l : P (x.`1, res)] = y).
move => x.
rewrite (H12 P i (x :: []) ). smt().
simplify big. rewrite /predT /g. simplify. smt().
auto.
elim refl1. move => D J p. elim p. move => p1 [p2 p3].
have conv1 : RealSeq.convergeto (fun (n : int) => big predT g (pmap J (range 0 n))) (sum g).
apply (summable_cnvto g J (support D)).
auto.
move => x.
rewrite /support. 
rewrite p1. rewrite /pred1 /g. 
  have ff: Pr[QQ(A, B).main5(i) @ &m :
          P res.`1.`1 /\ P res.`1.`2 /\ res.`2 = x]
        <= Pr[QQ(A, B).main5(i) @ &m : res.`2 = x].
rewrite Pr[mu_sub]. smt(). auto.
rewrite -  zz.
smt(@Distr).
rewrite /summable.  
exists 1%r.
move => J' J'u. 
have ->: (fun (x : irt * sbits) => `|g x|)
     = (fun (x : irt * sbits) => g x).
apply fun_ext. move => x. rewrite /g.
rewrite - zz. smt(@Distr).
rewrite /g. rewrite -  (H12 P). apply J'u.
rewrite Pr[mu_le1]. auto.
have lim1 : lim ((fun (n : int) => big predT g (pmap J (range 0 n)))) = (sum g). 
apply lim_cnvto. apply conv1.
rewrite - lim1.    
have : lim (fun (n : int) => big predT g (pmap J (range 0 n))) = Pr[QQ(A, B).main5(i) @ &m : P res.`1.`1 /\ P res.`1.`2].
apply lim_cnvto.
move => eps epsp.
elim (p3 eps epsp). simplify.
move => N Np. exists N.
move => n np.
have ->: big predT g (pmap J (range 0 n))
        = Pr[QQ(A, B).main5(i) @ &m : P res.`1.`1 /\ P res.`1.`2 /\ res.`2 \in (pmap J (range 0 n)) ].
rewrite H12. smt(@List).
auto.
have ->: Pr[QQ(A, B).main5(i) @ &m : P res.`1.`1 /\ P res.`1.`2] =
 Pr[QQ(A, B).main5(i) @ &m : P res.`1.`1 /\ P res.`1.`2 /\ (res.`2 \in pmap J (range 0 n)) ]   +  Pr[QQ(A, B).main5(i) @ &m : P res.`1.`1 /\ P res.`1.`2 /\ !(res.`2 \in pmap J (range 0 n)) ].
  have ->: Pr[QQ(A, B).main5(i) @ &m : P res.`1.`1 /\ P res.`1.`2 ] = Pr[QQ(A, B).main5(i) @ &m :  (P res.`1.`1 /\ P res.`1.`2 /\ (res.`2 \in pmap J (range 0 n)) \/ P res.`1.`1 /\ P res.`1.`2 /\ !(res.`2 \in pmap J (range 0 n)) ) ].
    rewrite Pr[mu_eq]. smt(). auto.
rewrite Pr[mu_disjoint].
smt().
auto. 
have ->: Pr[QQ(A, B).main5(i) @ &m :
     P res.`1.`1 /\ P res.`1.`2 /\ (res.`2 \in pmap J (range 0 n))] -
  (Pr[QQ(A, B).main5(i) @ &m :
      P res.`1.`1 /\ P res.`1.`2 /\ (res.`2 \in pmap J (range 0 n))] +
   Pr[QQ(A, B).main5(i) @ &m :
      P res.`1.`1 /\ P res.`1.`2 /\ ! (res.`2 \in pmap J (range 0 n))]) = 
   - Pr[QQ(A, B).main5(i) @ &m :
      P res.`1.`1 /\ P res.`1.`2 /\ ! (res.`2 \in pmap J (range 0 n))]. smt().
have ->: `|- Pr[QQ(A, B).main5(i) @ &m :
       P res.`1.`1 /\ P res.`1.`2 /\ ! (res.`2 \in pmap J (range 0 n))]| = Pr[QQ(A, B).main5(i) @ &m :
       P res.`1.`1 /\ P res.`1.`2 /\ ! (res.`2 \in pmap J (range 0 n))]. smt(@Distr).
have o : Pr[QQ(A, B).main5(i) @ &m :
   P res.`1.`1 /\ P res.`1.`2 /\ ! (res.`2 \in pmap J (range 0 n))] <= Pr[QQ(A, B).main5(i) @ &m : ! (res.`2 \in pmap J (range 0 n))]. rewrite Pr[mu_sub]. smt(). auto. 
have : Pr[QQ(A, B).main5(i) @ &m : ! (res.`2 \in pmap J (range 0 n))] < eps.
   have ->: Pr[QQ(A, B).main5(i) @ &m : ! (res.`2 \in pmap J (range 0 n))] = `|Pr[QQ(A, B).main5(i) @ &m : ! (res.`2 \in pmap J (range 0 n))]|. smt(@Distr).
apply Np. apply np.
smt().
smt().
qed.


local lemma jjj &m &n : exists (f : glob A -> sbits),
       injective f
   /\ (forall (x : glob A),
         phoare[ A.getState : (glob A) = x ==> (glob A) = x  /\ res = f x ] = 1%r)
   /\ (forall (x : glob A),
         hoare[ A.getState : (glob A) = x ==> (glob A) = x  /\ res = f x ])
   /\ (forall (x: glob A),
         phoare[A.setState: b = f x ==> glob A = x] = 1%r)
   /\ (forall (x: glob A),
         hoare[A.setState: b = f x ==> glob A = x])
   /\ islossless A.setState
   (* /\ islossless A.run *)
(*    /\ islossless B.init  *)
    (* assumptions above, payload below *)
   /\ (forall &m M s0 a, f (glob A){m} = s0 =>
         phoare [ QQ(A,B).main52 : f (glob A) = s0 /\ arg = a ==> M res.`1 /\ M res.`2  ]
       = Pr[ QQ(A,B).main52(a) @ &m : M res.`1 /\ M res.`2  ])
   /\ (forall s0 r, (forall &n, f (glob A){n} <> s0) =>
         (forall &m M i, Pr[ QQ(A,B).main6(i) @ &m : M res.`1 /\ res.`2.`2 = s0 /\ res.`2.`1 = r ] = 0%r))
   /\ (forall s0 r, (forall &n , f (glob A){n} <> s0) =>
         (forall &m M i, Pr[ QQ(A,B).main5(i) @ &m : M res.`1.`1 /\ M res.`1.`2 /\ res.`2.`2 = s0 /\ res.`2.`1 = r ] = 0%r))
   /\ (forall s0 r, (forall &n , f (glob A){n} <> s0) =>
         (forall &m i, Pr[ QQ(A,B).main51(i) @ &m :  res.`2 = s0  /\ res.`1 = r ] = 0%r))
   /\ (forall &m &n M s0 i r, f (glob A){n} = s0 =>
        Pr[ QQ(A,B).main5(i) @ &m : M res.`1.`1 /\ M res.`1.`2 /\ res.`2.`2 = s0 /\ res.`2.`1 = r ]
        = Pr[ QQ(A,B).main51(i) @ &m : res.`2 = s0 /\ res.`1 = r ] * Pr[ A.run(r) @ &n : M (r, res) ] * Pr[ A.run(r) @ &n : M (r, res) ])
   /\ (forall &m &n M s0 i r, f (glob A){n} = s0 =>
        Pr[ QQ(A,B).main6(i) @ &m : M res.`1 /\ res.`2.`2 = s0 /\ res.`2.`1 = r ]
      = Pr[ QQ(A,B).main51(i) @ &m : res.`2 = s0 /\ res.`1 = r ] * Pr[ A.run(r) @ &n : M (r, res) ])
   /\ (forall &m &n M s0 i r, f (glob A){n} = s0 =>
        Pr[ QQ(A,B).main5(i) @ &m : M res.`1.`1 /\ M res.`1.`2 /\ res.`2.`2 = s0 /\ res.`2.`1 = r ]
        = Pr[ QQ(A,B).main51(i) @ &m : res.`2 = s0 /\ res.`1 = r ] * Pr[ A.run(r) @ &n : M (r, res) ] * Pr[ A.run(r) @ &n : M (r, res) ])
  /\ (forall P i,
      Pr[ QQ(A,B).main5(i) @ &m : P res.`1.`1 /\ P res.`1.`2 ]
      = sum (fun (x : irt * sbits) =>  Pr[ QQ(A,B).main51(i) @ &m : res = x  ] * (some_real (fun y => exists &l, f (glob A){l} = x.`2 /\  Pr[ A.run(x.`1) @ &l : P (x.`1, res) ]  = y )) * (some_real (fun y => exists &l, f (glob A){l} = x.`2 /\  Pr[ A.run(x.`1) @ &l : P (x.`1, res) ]  = y ))))
  /\   (forall P i (M : (irt * sbits) list) , uniq M =>
      Pr[ QQ(A,B).main6(i) @ &m : P res.`1 /\ (res.`2 \in M) ]
      = big predT (fun x =>   Pr[ QQ(A,B).main51(i) @ &m : res = x ] * (some_real (fun y => exists &l, f (glob A){l} = x.`2 /\  Pr[ A.run(x.`1) @ &l : P (x.`1, res) ]  = y )))                    M).
elim (nnn1 &m &n). progress. exists f. split. assumption.
split. assumption. split. assumption. split. assumption. split. assumption.
split. assumption. split. assumption. split. assumption. split. assumption.
split. assumption.
split. assumption. split. assumption. split. assumption.  split. assumption. (* split. assumption. *)
move => P i.
apply list_ind. simplify. rewrite Pr[mu_false]. smt().
simplify.
move => x l ih .
elim. move=> xl ul.
have : Pr[QQ(A,B).main6(i) @ &m : P res.`1 /\ (res.`2 = x \/ (res.`2 \in l))  ]
        = Pr[QQ(A,B).main6(i) @ &m : (P res.`1 /\ res.`2 = x ) \/ (P res.`1 /\ res.`2 \in l ) ].
rewrite Pr[ mu_eq ]. smt(). auto.
move => qq. rewrite qq.
rewrite Pr[ mu_disjoint ]. smt().
pose E (x0 : irt * sbits) :=  (fun (y : real) =>
          exists &l, f (glob A){l} = x0.`2 /\ Pr[A.run(x0.`1) @ &l : P (x0.`1, res)] = y).
rewrite  (bigLemma (fun (x0 : (irt * sbits)) =>
     Pr[QQ(A,B).main51(i) @ &m : res = x0] *
     some_real
       (E x0)) l x).
simplify.
simplify.
rewrite - ih. apply  ul.
have : Pr[QQ(A,B).main51(i) @ &m : res = x] *
some_real (E x) = Pr[QQ(A,B).main6(i) @ &m : P res.`1 /\ res.`2 = x ].
case (exists &l, f (glob A){l} = x.`2).
elim. move => &lk lp.
have : E x (some_real (E x)).
apply (some_real_prop (E x)).
exists (Pr[ A.run(x.`1) @ &lk : P (x.`1, res) ]).
split. progress. simplify E. exists &lk.
smt().
move => q. elim.
move => &l0.
elim.
move => o1 o2.    rewrite - o2.
byequiv. proc*. call(_:true). skip. progress. smt(). smt(). smt().
elim.
move => &l. elim.
move => c eq.
rewrite - eq.
have ->: Pr[QQ(A, B).main51(i) @ &m : res = x] = Pr[QQ(A, B).main51(i) @ &m : res.`2 = x.`2 /\ res.`1 = x.`1].  rewrite Pr[mu_eq]. smt(). auto.
have ->: Pr[QQ(A, B).main6(i) @ &m : P res.`1 /\ res.`2 = x] = Pr[QQ(A, B).main6(i) @ &m : P res.`1 /\ res.`2.`2 = x.`2 /\ res.`2.`1 = x.`1].  rewrite Pr[mu_eq]. smt(). auto.
rewrite (H10 &m &l P  x.`2 i ).
smt().  smt().
move => dnem.
have : (forall &n0, f (glob A){n0} <> x.`2). smt().
move => prr.
have ->: Pr[QQ(A, B).main51(i) @ &m : res = x] = Pr[QQ(A, B).main51(i) @ &m : res.`2 = x.`2 /\ res.`1 = x.`1].  rewrite Pr[mu_eq]. smt(). auto.
have ->: Pr[QQ(A, B).main6(i) @ &m : P res.`1 /\ res.`2 = x] = Pr[QQ(A, B).main6(i) @ &m : P res.`1 /\ res.`2.`2 = x.`2 /\ res.`2.`1 = x.`1].  rewrite Pr[mu_eq]. smt(). auto.
rewrite (H8 x.`2). apply prr.
rewrite (H6 x.`2). apply prr.
smt().
move => opp.
rewrite opp.
auto.
qed.


local module W3 = {
  module Q = QQ(A,B)
  proc main(i:iat) = {
    var r;
    r <@ Q.main6(i);
    return r.`2;
  }
}.


local lemma jjj1 &m &n : exists (f : glob A -> sbits),
       injective f
    /\ (forall (x : glob A),
         phoare[ A.getState : (glob A) = x ==> (glob A) = x  /\ res = f x ] = 1%r)
    /\ (forall (x : glob A),
         hoare[ A.getState : (glob A) = x ==> (glob A) = x  /\ res = f x ])
    /\ (forall (x: glob A),
         phoare[A.setState: b = f x ==> glob A = x] = 1%r)
    /\ (forall (x: glob A),
         hoare[A.setState: b = f x ==> glob A = x])
    /\ islossless A.setState
    (* /\ islossless A.run *)
(*    /\ islossless B.init  *)
    (* assumptions above, payload below *)
    /\ (forall &m M s0 a, f (glob A){m} = s0 =>
         phoare [ QQ(A,B).main52 : f (glob A) = s0 /\ arg = a ==> M res.`1 /\ M res.`2  ]
       = Pr[ QQ(A,B).main52(a) @ &m : M res.`1 /\ M res.`2  ])
    /\ (forall s0 r, (forall &n, f (glob A){n} <> s0) =>
         (forall &m M i, Pr[ QQ(A,B).main6(i) @ &m : M res.`1 /\ res.`2.`2 = s0 /\ res.`2.`1 = r ] = 0%r))
    /\ (forall s0 r, (forall &n , f (glob A){n} <> s0) =>
         (forall &m M i, Pr[ QQ(A,B).main5(i) @ &m : M res.`1.`1 /\ M res.`1.`2 /\ res.`2.`2 = s0 /\ res.`2.`1 = r ] = 0%r))
    /\ (forall s0 r, (forall &n , f (glob A){n} <> s0) =>
         (forall &m i, Pr[ QQ(A,B).main51(i) @ &m :  res.`2 = s0  /\ res.`1 = r ] = 0%r))
   /\ (forall &m &n M s0 i r, f (glob A){n} = s0 =>
        Pr[ QQ(A,B).main5(i) @ &m : M res.`1.`1 /\ M res.`1.`2 /\ res.`2.`2 = s0 /\ res.`2.`1 = r ]
        = Pr[ QQ(A,B).main51(i) @ &m : res.`2 = s0 /\ res.`1 = r ] * Pr[ A.run(r) @ &n : M (r, res) ] * Pr[ A.run(r) @ &n : M (r, res) ])
    /\ (forall &m &n M s0 i r, f (glob A){n} = s0 =>
        Pr[ QQ(A,B).main6(i) @ &m : M res.`1 /\ res.`2.`2 = s0 /\ res.`2.`1 = r ]
      = Pr[ QQ(A,B).main51(i) @ &m : res.`2 = s0 /\ res.`1 = r ] * Pr[ A.run(r) @ &n : M (r, res) ])
   /\ (forall &m &n M s0 i r, f (glob A){n} = s0 =>
        Pr[ QQ(A,B).main5(i) @ &m : M res.`1.`1 /\ M res.`1.`2 /\ res.`2.`2 = s0 /\ res.`2.`1 = r ]
        = Pr[ QQ(A,B).main51(i) @ &m : res.`2 = s0 /\ res.`1 = r ] * Pr[ A.run(r) @ &n : M (r, res) ] * Pr[ A.run(r) @ &n : M (r, res) ])
  /\ (forall P i,
      Pr[ QQ(A,B).main5(i) @ &m : P res.`1.`1 /\ P res.`1.`2 ]
      = sum (fun (x : irt * sbits) =>  Pr[ QQ(A,B).main51(i) @ &m : res = x  ] * (some_real (fun y => exists &l, f (glob A){l} = x.`2 /\  Pr[ A.run(x.`1) @ &l : P (x.`1, res) ]  = y )) * (some_real (fun y => exists &l, f (glob A){l} = x.`2 /\  Pr[ A.run(x.`1) @ &l : P (x.`1, res) ]  = y ))))
  /\   (forall P i,
      Pr[ QQ(A,B).main6(i) @ &m : P res.`1 ]
      = sum (fun (x : irt * sbits) =>   Pr[ QQ(A,B).main51(i) @ &m : res = x ] * (some_real (fun y => exists &l, f (glob A){l} = x.`2 /\  Pr[ A.run(x.`1) @ &l : P (x.`1, res) ]  = y )))).
proof. elim (jjj &m &n). progress. exists f. split. assumption.
split. assumption. split. assumption. split. assumption. split. assumption.
split. assumption. split. assumption. split. assumption. split. assumption.
split. assumption.
split. assumption. split. assumption. split. assumption.  split. assumption. 
(* split. assumption. *)
move => P i.
  clear H0 H1 H2 H3 H4 H5 H6 H7 H8  H9 H10 H11 H12 .
  have refl1 :     exists (D : (irt * sbits) distr),  
  exists (J : int -> (irt * sbits) option),
  (forall M, mu D M = Pr[ QQ(A,B).main6(i) @ &m :  M res.`2 ])
  /\ enumerate J (support D) /\
  RealSeq.convergeto (fun N => Pr[ QQ(A,B).main6(i) @ &m : ! (res.`2 \in (pmap J (range 0 N))) ]) 0%r.
  elim (fin_approx_prog_no_glob_conv W3 &m i). move => D J. elim. move => DP [JP1 JP2]. 
    have D5 : forall (M : irt * sbits -> bool), mu D M = Pr[QQ(A, B).main6(i) @ &m : M res.`2].
     move => M. rewrite DP.
     byequiv (_: (={arg, glob A, glob B}) ==> _). proc.
     inline W3.Q.main6.
     wp.   call(_: (={arg, glob A}) ==> ={res}). sim.
    call (_: (={arg, glob A, glob B}) ==> ={glob A, res}). 
    proc. seq 1 1 : (={rb, glob A}). call Bsens2. skip. auto. call (_:true). skip. smt(). wp. skip. smt().
    auto.  auto. 
    exists D J.
    split.
    apply D5.
    split. apply JP1.
    have ->: (fun (N : int) =>
      Pr[QQ(A, B).main6(i) @ &m : ! (res.`2 \in pmap J (range 0 N))]) = (fun (N : int) =>
           Pr[W3.main(i) @ &m : ! (res \in pmap J (range 0 N))]).
    apply fun_ext. move => N. rewrite -  (D5 (fun (r : irt * sbits) => ! (r \in pmap J (range 0 N))) ).
    rewrite DP. auto.
         apply JP2.
pose g := (fun (x : irt * sbits) =>
     Pr[QQ(A, B).main51(i) @ &m : res = x] *
     some_real
       (fun (y : real) =>
          exists &l,
            f (glob A){l} = x.`2 /\ Pr[A.run(x.`1) @ &l : P (x.`1, res)] = y) ).
have zz: forall x, Pr[QQ(A, B).main6(i) @ &m :
          P res.`1 /\ res.`2 = x] =  Pr[QQ(A, B).main51(i) @ &m : res = x] *
some_real
  (fun (y : real) =>
     exists &l,
       f (glob A){l} = x.`2 /\ Pr[A.run(x.`1) @ &l : P (x.`1, res)] = y) .
move => x.
rewrite (H13 P i (x :: []) ). smt().
simplify big. rewrite /predT /g. simplify. smt().
auto.
elim refl1. move => D J p. elim p. move => p1 [p2 p3].
have conv1 : RealSeq.convergeto (fun (n : int) => big predT g (pmap J (range 0 n))) (sum g).
apply (summable_cnvto g J (support D)).
auto.
move => x.
rewrite /support. 
rewrite p1. rewrite /pred1 /g. 
  have ff: Pr[QQ(A, B).main6(i) @ &m :
          P res.`1 /\ res.`2 = x]
        <= Pr[QQ(A, B).main6(i) @ &m : res.`2 = x].
rewrite Pr[mu_sub]. smt(). auto.
rewrite -  zz.
smt(@Distr).
rewrite /summable.  
exists 1%r.
move => J' J'u. 
have ->: (fun (x : irt * sbits) => `|g x|)
     = (fun (x : irt * sbits) => g x).
apply fun_ext. move => x. rewrite /g.
rewrite - zz. smt(@Distr).
rewrite /g. rewrite -  (H13 P). apply J'u.
rewrite Pr[mu_le1]. auto.
have lim1 : lim ((fun (n : int) => big predT g (pmap J (range 0 n)))) = (sum g). 
apply lim_cnvto. apply conv1.
rewrite - lim1.    
have : lim (fun (n : int) => big predT g (pmap J (range 0 n))) = Pr[QQ(A, B).main6(i) @ &m : P res.`1 ].
apply lim_cnvto.
move => eps epsp.
elim (p3 eps epsp). simplify.
move => N Np. exists N.
move => n np.
have ->: big predT g (pmap J (range 0 n))
        = Pr[QQ(A, B).main6(i) @ &m : P res.`1 /\ res.`2 \in (pmap J (range 0 n)) ].
rewrite H13. smt(@List).
auto.
have ->: Pr[QQ(A, B).main6(i) @ &m : P res.`1] =
 Pr[QQ(A, B).main6(i) @ &m : P res.`1 /\ (res.`2 \in pmap J (range 0 n)) ]   +  Pr[QQ(A, B).main6(i) @ &m : P res.`1 /\ !(res.`2 \in pmap J (range 0 n)) ].
  have ->: Pr[QQ(A, B).main6(i) @ &m : P res.`1 ] = Pr[QQ(A, B).main6(i) @ &m :  (P res.`1 /\ (res.`2 \in pmap J (range 0 n)) \/ P res.`1 /\ !(res.`2 \in pmap J (range 0 n)) ) ].
    rewrite Pr[mu_eq]. smt(). auto.
rewrite Pr[mu_disjoint].
smt().
auto. 
have ->: Pr[QQ(A, B).main6(i) @ &m :
     P res.`1 /\ (res.`2 \in pmap J (range 0 n))] -
  (Pr[QQ(A, B).main6(i) @ &m :
      P res.`1 /\ (res.`2 \in pmap J (range 0 n))] +
   Pr[QQ(A, B).main6(i) @ &m :
      P res.`1 /\ ! (res.`2 \in pmap J (range 0 n))]) = 
   - Pr[QQ(A, B).main6(i) @ &m :
      P res.`1 /\ ! (res.`2 \in pmap J (range 0 n))]. smt().
have ->: `|- Pr[QQ(A, B).main6(i) @ &m :
       P res.`1 /\ ! (res.`2 \in pmap J (range 0 n))]| = Pr[QQ(A, B).main6(i) @ &m :
       P res.`1 /\ ! (res.`2 \in pmap J (range 0 n))]. smt(@Distr).
have o : Pr[QQ(A, B).main6(i) @ &m :
   P res.`1 /\ ! (res.`2 \in pmap J (range 0 n))] <= Pr[QQ(A, B).main6(i) @ &m : ! (res.`2 \in pmap J (range 0 n))]. rewrite Pr[mu_sub]. smt(). auto. 
have : Pr[QQ(A, B).main6(i) @ &m : ! (res.`2 \in pmap J (range 0 n))] < eps.
   have ->: Pr[QQ(A, B).main6(i) @ &m : ! (res.`2 \in pmap J (range 0 n))] = `|Pr[QQ(A, B).main6(i) @ &m : ! (res.`2 \in pmap J (range 0 n))]|. smt(@Distr).
apply Np. apply np.
smt().
smt().
qed.


type a = irt * sbits.


local module W1 : RunnableRefl = {
   module Q = QQ(A,B)
   proc main(i : iat) = {
      var r;
      r <@ Q.main51(i);
      return r;
   }
}.


local lemma derv_final &m :
  forall P i,
      Pr[ QQ(A,B).main5(i) @ &m : P res.`1.`1 /\ P res.`1.`2  ] >= (Pr[ QQ(A,B).main6(i) @ &m : P res.`1 ])^2 .
proof. elim (jjj1 &m &m). progress.
clear H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 .
rewrite H12.
rewrite H13.
clear H12 H13.
pose q (x : irt * sbits) := some_real
       (fun (y : real) =>
          exists &l,
            f (glob A){l} = x.`2 /\ Pr[A.run(x.`1) @ &l : P (x.`1, res)] = y).
have refl1 :  exists (D : (glob QQ(A,B)) -> iat -> (irt * sbits) distr),
    forall M &m a, mu (D (glob QQ(A,B)){m} a) M = Pr[ QQ(A,B).main51(a) @ &m :  M res].
      elim (reflection_simple_res W1). move => D DP. exists D.
      move => M &m0 a. rewrite (DP &m0 M a).
      byequiv (_: ={arg, glob A, glob B} ==> _). proc. inline W1.Q.main51. wp.  
      seq 2 1 : (={rb, glob A}). sp. call Bsens2. skip. smt().
      call (_:true).  skip. smt(). smt(). smt().
elim refl1. move => D DP.
have ->: (fun (x : irt * sbits) =>
     Pr[QQ(A, B).main51(i) @ &m : res = x] *
     some_real
       (fun (y : real) =>
          exists &l,
            f (glob A){l} = x.`2 /\ Pr[A.run(x.`1) @ &l : P (x.`1, res)] = y))
  = (fun (x : irt * sbits) =>
     q x * mass (D (glob QQ(A,B)){m} i) x).
apply fun_ext. move => x. rewrite /q /mass.
rewrite massE. rewrite /mu1. 
rewrite DP. rewrite /pred1. smt().
have -> : (fun (x : irt * sbits) =>
     Pr[QQ(A, B).main51(i) @ &m : res = x] *
     some_real
       (fun (y : real) =>
          exists &l,
            f (glob A){l} = x.`2 /\ Pr[A.run(x.`1) @ &l : P (x.`1, res)] = y) *
     some_real
       (fun (y : real) =>
          exists &l,
            f (glob A){l} = x.`2 /\ Pr[A.run(x.`1) @ &l : P (x.`1, res)] = y)) = (fun (x : irt * sbits) =>
     (q x)^2 * mass (D (glob QQ(A,B)){m} i) x).
apply fun_ext. move => x. rewrite /q /mass.
rewrite massE. rewrite /mu1. 
rewrite DP. rewrite /pred1. smt(@Real).
have : forall x, 0%r <= q x <= 1%r.
 move => x.
  case (exists x0, exists &l, f (glob A){l} = x.`2 /\
                     Pr[A.run(x.`1) @ &l : P (x.`1, res)] = x0).
   move => c1.
  have : exists &l, f (glob A){l} = x.`2 /\
                     Pr[A.run(x.`1) @ &l : P (x.`1, res)] = some_real
                (fun (y : real) =>
                   exists &l,
                     f (glob A){l} = x.`2 /\
                     Pr[A.run(x.`1) @ &l : P (x.`1, res)] = y).
      apply  (some_real_prop' ((fun (y : real) =>
                   exists &l,
                     f (glob A){l} = x.`2 /\
                     Pr[A.run(x.`1) @ &l : P (x.`1, res)] = y))). 
simplify. 
elim c1. move => x0 &l pp. exists x0.  exists &l. apply pp.
elim. move => &l [l1 l2].
rewrite /q. rewrite - l2. rewrite Pr[mu_le1]. rewrite Pr[mu_ge0]. auto.
   move => c2. rewrite /q /some_real.   
rewrite choiceb_dfl. smt().
smt().
move => qpos.   
have str  : forall q J,  (forall i, 0%r <= q i <= 1%r) =>  big predT (fun (i0 : a) => `|q i0 * mass (D (glob QQ(A, B)){m} i) i0|) J
 <= big predT (fun (i0 : a) =>  mass (D (glob QQ(A, B)){m} i) i0) J.
move => g.
apply list_ind. simplify. smt().
simplify. move => x l ih gpos.
rewrite bigLemma. rewrite bigLemma.
simplify.               
  have : `|g x * mass (D ((glob B){m}, (glob A){m}) i) x| <= mass (D ((glob B){m}, (glob A){m}) i) x.
    have ->: `|g x * mass (D ((glob B){m}, (glob A){m}) i) x| = g x * mass (D ((glob B){m}, (glob A){m}) i) x .
    smt(@Distr).
    have qx : 0%r <= g x <= 1%r. apply gpos.
    have mp : 0%r <= mass (D ((glob B){m}, (glob A){m}) i) x. smt(@Distr).
  smt().
smt().
have bmu : forall J, uniq J => big predT (fun (i0 : a) => mass (D (glob QQ(A, B)){m} i) i0) J = mu (D (glob QQ(A, B)){m} i) (mem J).
move => J Jp.
rewrite  mu_mem.
rewrite undup_id. apply Jp.
  have ->: (fun (i0 : a) => mass (D (glob QQ(A, B)){m} i) i0) = (fun (x : irt * sbits) => mu1 (D (glob QQ(A, B)){m} i) x).
  apply fun_ext. move => io. rewrite massE. auto. auto.
have ->: (fun (x : irt * sbits) => q x * mass (D (glob QQ(A, B)){m} i) x)
 = (fun (x : irt * sbits) => q x * mu1 (D (glob QQ(A, B)){m} i) x).
apply fun_ext. move => x. smt(@Distr).
have ->: (fun (x : irt * sbits) => q x ^ 2 * mass (D (glob QQ(A, B)){m} i) x)
 = (fun (x : irt * sbits) => q x ^ 2 * mu1 (D (glob QQ(A, B)){m} i) x).
apply fun_ext. move => x. smt(@Distr @Real).
apply (Jensen_inf (D (glob QQ(A, B)){m} i) q (fun (x : real) => x^2) 0%r 1%r 0%r 1%r _ _ _ _ _ _). 

have ll: is_lossless (D (glob QQ(A, B)){m} i).  rewrite /is_lossless.
   have <-: Pr[QQ(A, B).main51(i) @ &m : predT res] = 1%r.
   byphoare (_: _ ==> _). proc. simplify.  seq 1 : (true). 
   call (_:true). skip. auto. call ll_B_init.   skip. auto.
  elim (rewindable_A_plus A RewProp) . move => z [_ [_ [_ [lg _]]]].
  call lg. skip. progress. hoare.  simplify. call (_:true). skip. auto. auto.
  auto. auto. apply DP. 
apply ll.
rewrite /hasE /summable.
exists 1%r.
move => J Jp.
have : big predT (fun (i0 : a) => mass (D (glob QQ(A, B)){m} i) i0) J  <= 1%r.
rewrite bmu. apply Jp. smt(@Distr).
have : big predT (fun (i0 : a) => `|q i0 * mass (D (glob QQ(A, B)){m} i) i0|) J <= 
  big predT (fun (i0 : a) => mass (D (glob QQ(A, B)){m} i) i0) J .
apply str. apply qpos.
have ->: (fun (i0 : irt * sbits) => `|q i0 * mu1 (D (glob QQ(A, B)){m} i) i0|)
 = (fun (i0 : irt * sbits) => `|q i0 * mass (D (glob QQ(A, B)){m} i) i0|).
  apply fun_ext. move => x. smt(massE).
smt().
rewrite /hasE /summable.
exists 1%r.
move => J Jpos.
have : big predT
    (fun (i0 : a) =>
       `|(\o) (transpose Real.(^) 2) q i0 * mass (D (glob QQ(A, B)){m} i) i0|)
    J <= 
     big predT (fun (i0 : a) => mass (D (glob QQ(A, B)){m} i) i0) J.
apply str.
move => io. split.
simplify.
rewrite /(\o). smt(@Real).
simplify.
rewrite /(\o).
smt(@Real).
have : big predT (fun (i0 : a) => mass (D (glob QQ(A, B)){m} i) i0) J  <= 1%r.
rewrite bmu. apply Jpos. smt(@Distr).
have ->: (fun (i0 : irt * sbits) =>
     `|(\o) (fun (x : real) => x ^ 2) q i0 * mu1 (D (glob QQ(A, B)){m} i) i0|)
 = (fun (i0 : irt * sbits) =>
     `|(\o) (fun (x : real) => x ^ 2) q i0 * mass (D (glob QQ(A, B)){m} i) i0|).
  apply fun_ext. move => x. smt(@Distr).
smt().
apply square_convex.
smt(@Real).
smt().
qed.


lemma rew_with_init &m M i :
   Pr[ QQ(A,B).main(i) @ &m : M res.`1 /\ M res.`2 ] 
     >= Pr[ QQ(A,B).main_run(i) @ &m : M res ]^2.
have q : Pr[ QQ(A,B).main(i) @ &m : M res.`1 /\ M res.`2 ] >= Pr[ QQ(A,B).main_run'(i) @ &m : M res ]^2.
rewrite - intlem1 - intlem2. apply derv_final.
have p : Pr[ QQ(A,B).main_run'(i) @ &m : M res ] = Pr[ QQ(A,B).main_run(i) @ &m : M res ].
elim (rewindable_A_plus A RewProp) . progress.
byequiv (_: (={i,glob A, glob B}) ==> _). proc.
seq 1 1 : (={r0, glob A}). call Bsens2. skip. auto.
call (_:true).
conseq (_: exists ga, ga = (glob A){1} /\ ={r0, glob A} ==> _). smt().
elim*. move => ga.
call {1} (H0 ga). skip. progress. auto.  auto.
rewrite - p.
apply q.
qed.


end section.
end RWI.

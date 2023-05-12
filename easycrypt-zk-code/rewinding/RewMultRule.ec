pragma Goals:printall.
require import AllCore.
require import RewBasics.

type ex1at, ex2at, ex1rt, ex2rt.

module type RewEx1Ex2 = {
  proc getState() : sbits
  proc setState(b : sbits) : unit 
  proc ex1(x1 : ex1at) : ex1rt
  proc ex2(x2 : ex2at) : ex2rt
}.


module GetExec1Set(A : RewEx1Ex2) = {
  proc main(x1 : ex1at) = {
    var s , r;
    s <@ A.getState();
    r <@ A.ex1(x1);
    A.setState(s);
    return r;
  }
}.


module GetExec1SetExec2Conj(A : RewEx1Ex2) = {
  module GRS = GetExec1Set(A)
  proc main(x1 : ex1at, x2 : ex2at) = {
    var  r1, r2, x11, x22;
    x11 <- x1; (* PAPER: cannot prove x{hr} = x{hr} *)
    x22 <- x2;
    r1 <@ GRS.main(x11);
    r2 <@ A.ex2(x22);
    return (r1, r2); 
  }
}.


module MultTriv(A : RewRun, B : RewRun) = {
  proc main(x : iat2, y : iat2) = {
     var r1, r2;
     r1 <@ A.run(x);
     r2 <@ B.run(y);
     return (r1, r2);
  }
}.


lemma rew_mult_simple : forall (P <: RewRun) (Q <: RewRun{-P}) &m M1 M2  i1 i2,
    islossless P.run => islossless Q.run =>
    Pr[ MultTriv(P,Q).main(i1,i2) @ &m : M1 res.`1 /\ M2 res.`2 ]
    = Pr[ P.run(i1) @ &m : M1 res ] * Pr[ Q.run(i2) @ &m : M2 res ].
proof. progress. byphoare (_: (glob P) = (glob P){m} /\ (glob Q) = (glob Q){m} /\ x = i1 /\ y = i2 ==> _).
proc. simplify.
pose p := (Pr[P.run(i1) @ &m : M1 res]).
pose q := (Pr[Q.run(i2) @ &m : M2 res]).
seq 1 : (M1 r1) p q p (0%r) ((glob Q) = (glob Q){m} /\ x = i1 /\ y = i2 ).
call (_:true). skip. auto.
   have ph1 : forall &n x, phoare[ P.run : z = x /\ (glob P) = (glob P){n} ==> M1 res ] = (Pr[ P.run(x) @ &n : M1 res ]).
   progress. bypr. progress. byequiv. proc*. call (_:true). skip. auto. auto. auto.
   call (ph1 &m  i1). skip.  progress.
conseq (_: ((glob Q) = (glob Q){m} /\ x = i1 /\ y = i2) ==> M2 r2). smt(). smt().
   have ph2 : forall &n x, phoare[ Q.run : z = x /\ (glob Q) = (glob Q){n} ==> M2 res ] = (Pr[ Q.run(x) @ &n : M2 res ]).
   progress. bypr. progress. byequiv. proc*. call (_:true). skip.  progress. auto. auto.
   rewrite /q. call (ph2 &m i2). skip.  progress.
hoare. call (_:true). skip. smt().
smt().
smt().
auto.
qed.


section.
declare module A <: RewEx1Ex2.


(* getState lossless follows from rewindable_A, 
  but setState lossless does not, so we ask it *)
(* PAPER: we cannot put these things globally into the section because "op f : glob A -> sbits" is not allowed *)
declare axiom RewProp :
  exists (f : glob A -> sbits),
  injective f /\
  (forall &m, Pr[ A.getState() @ &m : (glob A) = ((glob A){m})
                                   /\ res = f ((glob A){m} ) ] = 1%r) /\
  (forall &m b (x: glob A), b = f x =>
    Pr[A.setState(b) @ &m : glob A = x] = 1%r) /\
  islossless A.setState.



(*  Double run and the respective probabilities: 
 forall &m, if   Pr[ A.exec1 @ &m : r ] = p and
                 Pr[ A.exec1 @ &m : r ] = q
 then Pr[  s <- A.getState; r1 <- A.exec1 ; 
          A.setState(s); r2 <- A.exec2 @ &m 
                       : r1 /\ r2 ] = p * q  
*)
local lemma ex1ex2_1 M1 x1 : forall (ga : glob A),  forall (p : real),
       phoare[ A.ex1 : arg = x1 /\ (glob A) = ga ==> M1 res ] = p
    => phoare[ GetExec1Set(A).main :  arg = x1 /\ (glob A) = ga ==> M1 res /\ (glob A) = ga ] = p.
proof.  move => ga p ph. 
proc. 
elim (rewindable_A_plus A RewProp).
move => fA [s1 [s2 [s2h [s2ll [s3 [s3h ]]]] ]] s3ll.
seq 2 : (M1 r) p (1%r) p  (0%r) (s = fA ga). 
call (_:true).
call (s2h ga). skip. by progress.
call ph.
call (s2 ga). skip. auto.
call (s3 ga). skip. auto.
hoare.
call (_:true). skip. progress. smt().
auto. 
qed.


local lemma ex1ex2_2 M1 x1 : forall (ga : glob A), forall (p : real),
       phoare[ A.ex1 : arg = x1 /\ (glob A) = ga ==> M1 res ] = p
    => phoare[ GetExec1Set(A).main : arg = x1 /\ (glob A) = ga ==> M1 res ] = p.
proof. move => ga p ph.
proc. 
elim (rewindable_A_plus A RewProp).
move => fA [s1 [s2 [s2h [s2ll [s3 [s3h ]]]] ]] s3ll.
seq 2 : (M1 r) p (1%r) p (0%r) (s = fA ga). 
call (_:true).
call (s2h ga). skip. by progress.
call ph.
call (s2 ga). skip. auto.
call (s3 ga). skip. auto.
hoare.
call (_:true). skip. progress.  smt().
qed.


lemma rew_clean : forall &m  M1 i1 , 
     Pr[ GetExec1Set(A).main(i1) @ &m : M1 res /\ (glob A) = (glob A){m} ] = Pr[ A.ex1(i1) @ &m : M1 res ].
proof. move => &m M1 x1.
  have ph1 : forall &n x1, phoare[ A.ex1 : arg = x1 /\ (glob A) = (glob A){n} ==> M1 res ] = Pr[ A.ex1(x1) @ &n : M1 res ].
  progress. bypr. progress. byequiv. proc*. call (_:true). skip. progress. auto. auto.
  have ph2 : forall &n i1, phoare[ GetExec1Set(A).main : arg = i1 /\ (glob A) = (glob A){n} ==> M1 res /\ (glob A) = (glob A){n} ] 
                           = Pr[ A.ex1(i1) @ &n : M1 res ].
  progress. proc*. call (ex1ex2_1 M1 i1  (glob A){n} (Pr[ A.ex1(i1) @ &n : M1 res ])).
  apply ph1. skip. progress.
byphoare (_: arg = x1 /\ (glob A) = (glob A){m} ==> _). proc*. call (ph2 &m x1). skip. auto. auto. auto.
qed.

    
local lemma ex1ex2_3 &m M1 M2 a1 a2 : forall (ga : glob A), 
 forall (p q : real),  (glob A){m} = ga
    => phoare[ A.ex1 : arg = a1 /\ (glob A) = ga ==> M1 res ] = p
    => phoare[ A.ex2 : arg = a2 /\ (glob A) = ga ==> M2 res ] = q
    => Pr[ GetExec1SetExec2Conj(A).main(a1,a2) @ &m : M1 res.`1 /\ M2 res.`2 ] = p * q.
proof. move => ga p q se ph hp. 
byphoare (_ : arg.`1 = a1 /\ arg.`2 = a2 /\ (glob A) = ga ==> _).
elim (rewindable_A_plus A RewProp).
move => fA [s1 [s2 [s2h [s2ll [s3 [s3h ]]]] ]] s3ll.
proc.
seq 3 : (M1 r1) p q p (0%r) ((glob A) = ga /\ x11 = a1 /\ x22 = a2). 
inline*.
wp.
call (s3h ga).
call (_:true).
call (s2h ga).
wp. skip.
progress. 
sp.
call (ex1ex2_2 M1 a1 ga p). 
 skip. auto.
call hp.
skip. progress.   auto. 
hoare.
call (_:true).
auto. smt().
auto.
auto.
auto.
qed.


local lemma ex1ex2_main  &m M1 M2 x1 x2 (ga: glob A) (p q : real) :  (glob A){m} = ga
   => (forall &n, (glob A){n} = ga => Pr[ A.ex1(x1) @ &n : M1 res ] = p)
   => (forall &n, (glob A){n} = ga => Pr[ A.ex2(x2) @ &n : M2 res ] = q)
   => Pr[ GetExec1SetExec2Conj(A).main(x1,x2) @ &m : M1 res.`1 /\ M2 res.`2 ] = p * q.
proof. move => gae pr1 pr2. 
have z1 : phoare[ A.ex1 : arg = x1 /\ (glob A) = ga ==> M1 res ] = p.
bypr. progress. apply (pr1 &m0 ).
auto. 
have z2 : phoare[ A.ex2 : arg = x2 /\ (glob A) = ga ==> M2 res ] = q.
bypr. progress. apply (pr2 &m0 ).
auto. 
apply (ex1ex2_3 &m M1 M2 x1 x2 ga). assumption.
conseq z1. apply z2. 
qed.


local lemma ex1ex2_main_special &m M1 M2 i1 i2 (p q : real):
      Pr[ A.ex1(i1) @ &m : M1 res ] = p =>
      Pr[ A.ex2(i2) @ &m : M2 res ] = q =>
      Pr[ GetExec1SetExec2Conj(A).main(i1,i2) @ &m : M1 res.`1 /\ M2 res.`2 ] = p * q.
proof.
move => Hrun1 Hrun2.
apply(ex1ex2_main &m M1 M2 i1 i2 (glob A){m} p q).
by reflexivity. 
have se1 : Pr[A.ex1(i1) @ &m : M1 res] = Pr[A.ex1(i1) @ &m : M1 res].
byequiv (_:(={glob A, x1}) ==> _). proc*. call(_:true). skip. progress. auto. auto.
rewrite - Hrun1.
progress.
byequiv (_:(={glob A, x1}) ==> _). proc*. call(_:true). skip. progress. auto. auto.
have se1 : Pr[A.ex2(i2) @ &m : M2 res] = Pr[A.ex2(i2) @ &m : M2 res].
byequiv (_:(={glob A, x2}) ==> _). proc*. call(_:true). skip. progress. auto. auto.
rewrite - Hrun2.
progress.
byequiv (_:(={glob A, x2}) ==> _). proc*. call(_:true). skip. progress. auto. auto.
qed.


lemma rew_mult_law &m M1 M2 i1 i2:
      Pr[ GetExec1SetExec2Conj(A).main(i1, i2) @ &m : M1 res.`1 /\ M2 res.`2 ]
    = Pr[ A.ex1(i1) @ &m : M1 res ] * Pr[ A.ex2(i2) @ &m : M2 res ].
proof. apply (ex1ex2_main_special &m M1 M2). auto. auto.
qed.


end section.

pragma Goals:printall.
require import AllCore.

type sbits, iat, irt, rrt, iat2.

op pair_sbits : sbits * sbits -> sbits.
op unpair: sbits -> sbits * sbits.
axiom ips: injective pair_sbits. 
axiom unpair_pair x : unpair (pair_sbits x) = x.



module type Rew = {
  proc getState() : sbits
  proc setState(b : sbits) : unit
}.


module type Initializer = {
  proc init (i:iat) : irt
}.


module type RewRun = {
  proc getState() : sbits
  proc setState(b : sbits) : unit 
  proc run(z : iat2) : rrt
}.


module Skip = {
  proc main() = {}
}.


module Run(A : RewRun) = {
  proc main(z : iat2) = {
    var r;
    Skip.main();
    r <@ A.run(z);
    return r;
  }
}.


module GetRunSet(A : RewRun) = {
  proc getState() = {
    var s;
    s <@ A.getState();
    return s;
  }
  proc setState(s : sbits) = {
    A.setState(s);
  }
  proc main(z : iat2) = {
    var s , r;
    s <@ A.getState();
    r <@ A.run(z);
    A.setState(s);
    return r;
  }
}.


module GetRunSetRun(A : RewRun) = {
  proc main(z : iat2) = {
    var  r;
    GetRunSet(A).main(z);
    r <@ A.run(z);
    return r;
  }
}.

module GetRunSetRunConj(A : RewRun) = {
  module GRS = GetRunSet(A)
  proc main(z : iat2) = {
    var  r1, r2;
    r1 <@ GRS.main(z);
    r2 <@ A.run(z);
    return ((z,r1), (z,r2));
  }
}.
  
section.

declare module A <: Rew.

declare axiom RewProp :
  exists (f : glob A -> sbits),
  injective f /\
  (forall &m, Pr[ A.getState() @ &m : (glob A) = ((glob A){m})
                                   /\ res = f ((glob A){m} ) ] = 1%r) /\
  (forall &m b (x: glob A), b = f x =>
    Pr[A.setState(b) @ &m : glob A = x] = 1%r) /\
  islossless A.setState.

  
(* convenience implications from RewProp *)
lemma rewindable_A :
  exists (f : glob A -> sbits),
  injective f /\
  (forall (x : glob A),
    phoare[ A.getState : (glob A) = x ==> (glob A) = x  /\ res = f x ] = 1%r) /\
  (forall (x: glob A),
    phoare[A.setState: b = f x ==> glob A = x] = 1%r) /\
  islossless A.setState.
proof. elim RewProp.
progress. exists f.
progress.
bypr. progress. 
apply (H0 &m). auto.
bypr.  progress. apply (H1 &m b{m}). auto.
qed.


lemma rewindable_A_plus : 
  exists (f : glob A -> sbits),
  injective f /\
  (forall (x : glob A),
    phoare[ A.getState : (glob A) = x ==> (glob A) = x  /\ res = f x ] = 1%r) /\
  (forall (x : glob A),
    hoare[ A.getState : (glob A) = x ==> (glob A) = x  /\ res = f x ]) /\
  islossless A.getState /\
  (forall (x: glob A),
    phoare[A.setState: b = f x ==> glob A = x] = 1%r) /\
  (forall (x: glob A),
    hoare[A.setState: b = f x ==> glob A = x]) /\
  islossless A.setState.
proof. elim rewindable_A.
move => fA [s1 [s2 [s3]]] s4.
have ll1 :  forall &m,  Pr[A.getState() @ &m : true] = 1%r.
move => &m. byphoare (_: (glob A) = (glob A){m} ==> _). proc*.  call  (s2 (glob A){m} ). auto. auto. auto.
have ll2 : forall &m,  forall (x : glob A), forall (b : sbits),
   b = fA x =>
  Pr[A.setState(b) @ &m : true] = 1%r.
move => &m x bz e.
byphoare (_: (glob A) = (glob A){m} /\ bz = b ==> _). proc*.  call (s3 x). skip.
auto. auto. auto.
exists fA. progress.
bypr.
rewrite Pr[mu_not].
rewrite ll1.
have ll3 : forall &m, ((glob A){m} = x)  => Pr[A.getState() @ &m : (glob A) = x /\ res = fA x] = 1%r.
move => &m eq. byphoare (_: (glob A) = (glob A){m} ==> _) .
proc*. call (s2 x). auto. auto. auto.
smt().  
bypr. progress. apply ll1.
bypr. rewrite Pr[mu_not]. 
move => &m e. rewrite (ll2 &m x). auto.
have qq :  forall &m,  forall (x : glob A), forall (b : sbits),
   b = fA x => Pr[A.setState(b) @ &m : (glob A) = x] = 1%r.  
move => &w z bz eq. byphoare (_: (glob A) = (glob A){w} /\ bz = b ==> _). proc*.
call (s3 z). skip. auto. auto. auto.
rewrite qq. auto. auto.
qed.
end section.


section.

declare module A <: RewRun.


(* getState lossless follows from rewindable_A, but setState lossless does not, so we ask it *)
declare axiom RewProp :
  exists (f : glob A -> sbits),
  injective f /\
  (forall &m, Pr[ A.getState() @ &m : (glob A) = ((glob A){m})
                                   /\ res = f ((glob A){m} ) ] = 1%r) /\
  (forall &m b (x: glob A), b = f x =>
    Pr[A.setState(b) @ &m : glob A = x] = 1%r) /\
  islossless A.setState.


(* Main lemmas of rewindability:

 1/ equiv [ <skip> ~ s <- A.getState; A.run(); A.setState(s) : ={glob A} ==> ={glob A} ]

 2/ equiv [ r <- A.run(); return r ~ s <- A.getState; A.run(); A.setState(s); r <- A.run(); return r  
             : ={glob A} ==> ={res} /\ ={glob A} ].

*)  
local lemma GetRunSetRew' : forall (x : (glob A)), 
   islossless A.run => 
   equiv [ Skip.main ~ GetRunSet(A).main : x = (glob A){1} 
         /\ (glob A){1} = (glob A){2} ==> ={glob A} ].
move => x rll.
proc.
elim (rewindable_A A RewProp). 
move => fA [s1 [s2 [s3]]] s4.
seq 0 1 : (={glob A} /\ fA x = s{2} /\ fA (glob A){2} = s{2} /\ x{2} = (glob A){2}).
call{2} (s2 x).
skip. progress.
seq 0 1 : (fA x = s{2} /\ fA (glob A){1} = s{2} /\ x{2} = (glob A){1}).  
call{2} (_: true ==> true).
skip. progress.
call{2} (s3 x).
skip. progress.
qed.


lemma GetRunSetRew : 
    islossless A.run => 
   equiv [ Skip.main ~ GetRunSet(A).main : ={glob A} ==> ={glob A} ].
proof. move => ill. 
conseq (_: exists (x : glob A) , x = (glob A){1} /\ ={glob A} ==> _).
progress.
exists (glob A){2}. auto.
elim*.
move => x. apply (GetRunSetRew' x ill).
qed.

 
local lemma GetRunSetRunRew :
   islossless A.run =>
  equiv [ Run(A).main ~ GetRunSetRun(A).main : ={arg, glob A}
        ==> ={res} /\ ={glob A} ].
proof.  move => ill.
proc.
seq 1 1 : (={z, glob A}).
call GetRunSetRew.
skip. by trivial.
call (_:true).
skip. by auto.
qed.


lemma GetRunSetRewRes :
   islossless A.run =>
  equiv [ A.run ~ GetRunSet(A).main : ={arg, glob A}
        ==> ={res} ].
proof.  move => ill.
  proc*. inline*.
elim (rewindable_A_plus A RewProp).
move => fA [s1 [s2 [s2h [s2ll [s3 [s3h ]]]] ]] s3ll.
sp. wp.
exists* (glob A){2}. elim*.
auto.
seq 0 1 : (A_R = (glob A){2} /\ z0{2} = z{2} /\ ={z, glob A} /\ s{2} = fA A_R).

call {2} (s2 A_R). skip. progress.
conseq (_: z{1} = z0{2} /\ ={glob A} /\ s{2} = fA A_R  ==> _).  auto.
seq 1 1 : (r{1} = r0{2} /\ ={glob A} /\ s{2} = fA A_R).
call (_:true). skip. progress. 
call {2} (s3 A_R). skip. progress.
qed.


(*  Double run and the respective probabilities: 

 forall &m, if   Pr[ A.run @ &m : r ] = p then

            then Pr[ s <- A.getState; r1 <- A.run ; 
                    A.setState(s);   r2 <- A.run @ &m 
                    : r1 /\ r2 ] = p * p  

*)

lemma dbl1 M : forall (ga : glob A),  forall (p : real),
       phoare[ A.run : (glob A) = ga ==> M res ] = p
    => phoare[ GetRunSet(A).main : (glob A) = ga ==> M res /\ (glob A) = ga ] = p.
proof.  move => ga p ph. 
proc.
elim (rewindable_A_plus A RewProp).
move => fA [s1 [s2 [s2h [s2ll [s3 [s3h ]]]] ]] s3ll.
seq 2 : (M r) p (1%r) p  (0%r) (s = fA ga). 
call (_:true).
call (s2h ga). skip. by progress.
call ph.
call (s2 ga). skip.  auto.
call (s3 ga). skip. auto.
hoare.
call (_:true). skip. progress. smt().
auto. 
qed.


local lemma dbl2 M z: forall (ga : glob A), forall (p : real),
       phoare[ A.run : (glob A) = ga /\ arg = z ==> M (z, res) ] = p
    => phoare[ GetRunSet(A).main : (glob A) = ga /\ arg = z  ==>  M (z, res) ] = p.
proof.  move => ga p ph. 
proc. 
elim (rewindable_A_plus A RewProp).
move => fA [s1 [s2 [s2h [s2ll [s3 [s3h ]]]] ]] s3ll.
seq 2 : (M (z, r)) p (1%r) p (0%r) (s = fA ga). 
call (_:true).
call (s2h ga). skip. by progress.
call ph.
call (s2 ga). skip. auto.
call (s3 ga). skip. auto.
hoare.
call (_:true). skip. progress. smt().
qed.

    
local lemma dbl3 &m M y : forall (ga : glob A), forall (p : real), (glob A){m} = ga
    => phoare[ A.run : (glob A) = ga /\ arg = y ==> M (y, res) ] = p
    => Pr[ GetRunSetRunConj(A).main(y) @ &m : M res.`1 /\ M res.`2 ] = p * p.
proof. move => ga p se ph. 
byphoare (_ : (glob A) = ga /\ arg = y ==> _).
elim (rewindable_A_plus A RewProp).
move => fA [s1 [s2 [s2h [s2ll [s3 [s3h ]]]] ]] s3ll.
proc.
seq 1 : (M (y, r1)) p p p (0%r) ((glob A) = ga /\ z = y). 
inline*.
wp.
call (s3h ga).
call (_:true).
call (s2h ga).
auto. 
 call (dbl2 M y ga p).  skip. auto.
 call ph.
skip.   auto.
hoare.
call (_:true).
auto. smt().
auto.
auto.
auto.
qed.


local lemma dbl_main &m M y (ga : glob A) (p : real) : (glob A){m} = ga =>
      (forall &n, (glob A){n} = ga => Pr[ A.run(y) @ &n : M (y, res) ] = p)
   => Pr[ GetRunSetRunConj(A).main(y) @ &m : M res.`1 /\ M res.`2 ] = p * p.
proof. move => gae pr. 
have z : phoare[ A.run : (glob A) = ga /\ arg = y ==> M (y, res) ] = p.
bypr. progress. apply (pr &m0 ).
auto. apply (dbl3 &m M y ga). assumption.
apply z. qed.


local lemma dbl_main_special &m M y p:
      Pr[ A.run(y) @ &m : M (y, res) ] = p =>
      Pr[ GetRunSetRunConj(A).main(y) @ &m : M res.`1 /\ M res.`2 ] = p * p.
proof.
move => Hrun.
apply(dbl_main &m M y (glob A){m}).
by reflexivity. 
have q : Pr[A.run(y) @ &m : M (y, res)] = Pr[A.run(y) @ &m : M (y, res)].         
byequiv;progress.
proc*.  call (_:true). skip. progress.
rewrite - Hrun.
progress.
byequiv;progress.
proc*.  call (_:true). skip. progress.
qed.


lemma dbl_main_no_number &m M y:
      Pr[ GetRunSetRunConj(A).main(y) @ &m : M res.`1 /\ M res.`2 ]
    = Pr[ A.run(y) @ &m : M (y, res) ] * Pr[ A.run(y) @ &m : M (y, res) ].
proof. apply (dbl_main_special &m M). auto.
qed.        


local lemma exmem' :   exists (f : glob A -> sbits),
  injective f /\
  (forall (x : glob A),
    phoare[ A.getState : (glob A) = x ==> (glob A) = x  /\ res = f x ] = 1%r) /\
  (forall (x : glob A),
    hoare[ A.getState : (glob A) = x ==> (glob A) = x  /\ res = f x ]) /\
  islossless A.getState /\
  (forall (x: glob A),
    phoare[A.setState: b = f x ==> glob A = x] = 1%r) /\
  (forall (x: glob A),
    hoare[A.setState: b = f x ==> glob A = x]) /\
  islossless A.setState /\ 
  (forall (ga : glob A), (forall &m, exists &n, (glob A){n} = ga)).
proof.  elim (rewindable_A_plus A RewProp).
move => f. elim.
move => h1. elim. move => h2. elim.  move=> h3.  elim. 
move => h4. elim. move =>  h5. elim. move => h6 h7.  
exists f. split. auto. split. auto. split. auto.  split. auto.  split. auto.  
split. auto.  split. auto.  move => ga &m. 
have : Pr[ A.setState(f ga) @ &m : exists &n, (glob A){n} = ga ] = 1%r.
byphoare (_: arg = f ga /\ (glob A) = (glob A){m} ==> _). proc*.  
seq 1 : (glob A = ga). call (_:true). skip. auto.
call (h5 ga). skip. auto. skip.
move => &hr p.    exists &hr. apply p.
hoare.  call (h6 ga). skip. auto.
auto. auto. auto.
move => qq.
case (exists &n, (glob A){n} = ga).
auto.
move => pp.
have : Pr[A.setState(f ga) @ &m : exists &n, (glob A){n} = ga] 
     = Pr[A.setState(f ga) @ &m : false ]. rewrite pp. auto.
rewrite qq. 
have : Pr[A.setState(f ga) @ &m : false] = 0%r.
rewrite Pr[mu_false]. auto.
move => k. rewrite k.
auto.
qed.


end section.


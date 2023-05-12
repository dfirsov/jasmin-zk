pragma Goals:printall.
require import AllCore Distr.


theory IterUntilSuccDistr.
type sbits, iat, rrt, irt.

module M = {
  var c : int
  proc whp(MyP : rrt -> bool,myd : rrt distr, s : int, e : int, r : rrt) = {
    c <- s;
    while(c <= e /\ !MyP r){
     r <$ myd;
     c <- c + 1;
    }
    return r;
  }

  proc whp_if_end(MyP : rrt -> bool,myd : rrt distr, s : int, e : int, r : rrt) = {
    var ri : rrt;
    ri <@ whp(MyP,myd, s,e,r);
    if(c <= e + 1 /\ !MyP ri){
      ri <$ myd;
      c <- c + 1;
    }
    return ri;
  }
}.

section.
local lemma whp_split_if_end :  
  equiv[ M.whp ~ M.whp_if_end : ={MyP,myd, s,r} /\ e{1} - 1 = e{2}
        ==> ={res,M.c} ].
proof. proc.
inline*. sp. 
splitwhile{1} 1 : M.c  <= (e - 1) .
seq  1 1 : (={M.c} /\ r{1} = r0{2} /\ myd{1} = myd0{2} /\ e0{2} = e{2} /\ myd0{2} = myd{2}
   /\ MyP0{2} = MyP{1} /\ MyP0{2} = MyP{2} 
   /\ e{1} - 1 = e0{2} /\ (!MyP{1} r{1} => (e{1} - 1) < M.c{1} )).
while (={M.c,myd,MyP} /\ r{1} = r0{2} /\ myd{1} = myd0{2} /\ e0{2} = e{2} 
   /\ MyP{1} = MyP0{2} /\ MyP{2} = MyP0{2}
   /\ e{1} - 1 = e0{2} ).
wp. rnd. skip.  progress. smt().  skip. progress. smt(). smt().
sp. simplify.
case (MyP{1} r{1}).
rcondf {1} 1. progress. skip. smt().
rcondf {2} 1. progress. skip. progress. smt().
skip. progress.
unroll {1} 1.
if. progress.  
rcondf {1} 3. progress.
wp. rnd. skip. progress. smt().
wp. rnd. skip. progress. 
rcondf {1} 1. progress. skip. progress.
qed.


local lemma whp_split_if_end' MyP s e r p P d :  
  (phoare [ M.whp_if_end : arg = (MyP,d,s,e,r) ==> P res ] = p)
   => phoare [ M.whp : arg = (MyP,d,s,e+1,r) ==> P res ] = p.
proof. progress. bypr.
progress.
have <-: Pr[M.whp_if_end(MyP,d, s, e, r) @ &m : P res] = p.
byphoare (_: arg = (MyP,d, s, e, r) ==> _).
conseq H. auto. auto. byequiv.
conseq whp_split_if_end. smt(). auto. auto. auto.
qed.


local lemma lll (b a c : real) : a <= b => b <= c => a <= c.
smt(). qed.

    
local lemma whp_split_if_end_le MyP s e r p myd P :  
  (phoare [ M.whp_if_end : arg = (MyP,myd,s,e,r) ==> P res ] <= p)
   => phoare [ M.whp : arg = (MyP,myd,s,e+1,r) ==> P res ] <= p.
proof. progress. bypr.
progress.
have zz : Pr[M.whp_if_end(MyP, myd,s, e, r) @ &m : P res] <= p.
byphoare (_: arg = (MyP,myd,s, e, r) ==> _).
conseq H. auto. auto. 
apply (lll Pr[M.whp_if_end(MyP,myd,s, e, r) @ &m : P res] ).
byequiv.
 conseq whp_split_if_end. smt(). auto. auto. auto. apply zz.
qed.


local lemma whp_split_if_end_ge MyP s e r p myd P :  
  (phoare [ M.whp_if_end : arg = (MyP,myd,s,e,r) ==> P res ] >= p)
   => phoare [ M.whp : arg = (MyP,myd,s,e+1,r) ==> P res ] >= p.
proof. progress. bypr.
progress.
have zz : Pr[M.whp_if_end(MyP, myd,s, e, r) @ &m : P res] >= p.
byphoare (_: arg = (MyP,myd,s, e, r) ==> _).
conseq H. auto. auto.  
apply (lll Pr[M.whp_if_end(MyP,myd,s, e, r) @ &m : P res] ). auto.
byequiv. 
symmetry. conseq whp_split_if_end. smt(). auto. auto. auto. 
qed.



local lemma iter (p : real) r myda MyPa: 
  (mu myda (fun (x : rrt) => ! MyPa x) = p) =>
  MyPa r = false => forall e, 0 <= e => 
  phoare[ M.whp_if_end : arg = (MyPa,myda, 1,e,r) ==> !MyPa res ] = (p ^ (e+1)).
proof. move => iipr ipr. apply ge0ind. smt().
progress. simplify.
  progress. proc.
inline*. sp.
rcondf 1. skip. smt().
sp. 
rcondt 1. skip. progress. smt().
swap 1 1.  rnd.  simplify.
wp.  skip.  progress. smt(@Real).
progress. proc.
  have phf: phoare[ M.whp : arg = (MyPa,myda, 1, n+1, r) ==> !MyPa res] = (p ^(n+1)).
 apply (whp_split_if_end'  MyPa 1 n r  (p^(n+1)) (fun x => !MyPa x) myda (H0 H) ).
seq 1 : (!MyPa ri) (p ^(n+1)) p 1%r 0%r (myd = myda /\ MyP = MyPa /\ (!MyPa ri => M.c <= e + 1)).
inline*. sp.
seq 1 :  (MyP = MyPa /\ myd = myda  /\ (!MyPa r0 => M.c <= e + 1)).
 while (MyP = MyP0 /\ MyP = MyPa /\ myd = myda /\ e = e0 /\ (!MyPa r0 => M.c <= e0 + 1)).
wp. 
rnd.  skip. progress. smt(). skip. progress. smt(). sp.  skip. progress. 
 call phf. skip.  auto.
rcondt 1. skip. progress. smt().  
wp. simplify.  rnd.  simplify.
skip. progress. 
hoare. 
rcondf 1. skip. progress. smt().
simplify. skip. auto. progress. smt(@Real).
qed.


local lemma iter_le (p : real) MyPa r d:
  (mu d (fun (x : rrt) => ! MyPa x) <= p) =>
    MyPa r = false => forall e, 0 <= e => 
  phoare[ M.whp_if_end : arg = (MyPa, d,1,e,r) ==> !MyPa res ]
     <= (p ^ (e+1)).
proof. move => dpr ipr. apply ge0ind. smt().
progress. simplify.
  progress. proc.
inline*. sp.
rcondf 1. skip. smt().
sp. 
rcondt 1. skip. progress. smt().
swap 1 1.  rnd.  simplify.
wp.  skip.  progress. smt(@Real). 
progress. proc.
  have phf: phoare[ M.whp : arg = (MyPa,d,1, n+1, r) ==> !MyPa res] <= (p ^(n+1)).
 apply (whp_split_if_end_le MyPa 1 n r (p^(n+1)) d (fun x => !MyPa x) (H0 H) ).
seq 1 : (!MyP ri) (p ^(n+1)) p 1%r 0%r (d = myd /\ MyP = MyPa /\ (!MyP ri => M.c <= e + 1)).
inline*. sp.
seq 1 :  (d = myd /\ MyP = MyPa /\ myd = myd0 /\ (!MyP r0 => M.c <= e + 1)).
 while (d = myd /\ myd = myd0 /\ MyP = MyP0 /\ e = e0 /\ (!MyP r0 => M.c <= e0 + 1)).
wp. 
rnd.  skip. progress. smt(). skip. progress. smt(). sp.  skip. progress. 
 call phf. skip.  auto.
rcondt 1. skip. progress. smt(). 
wp. simplify.  rnd.  simplify.
skip. progress.
hoare. 
rcondf 1. skip.  progress. smt().
simplify. skip. auto. smt(@Real).
qed.


local lemma iter_ge (p : real) MyPa r d:
  (mu d (fun (x : rrt) => ! MyPa x) >= p) =>
    MyPa r = false => forall e, 0 <= e => 
  phoare[ M.whp_if_end : arg = (MyPa, d,1,e,r) ==> !MyPa res ]
     >= (p ^ (e+1)).
proof. move => dpr ipr. apply ge0ind. smt().
progress. simplify.
  progress. proc.
inline*. sp.
rcondf 1. skip. smt().
sp. 
rcondt 1. skip. progress. smt().
swap 1 1.  rnd.  simplify.
wp.  skip.  progress. smt(@Real). 
progress. proc.
  have phf: phoare[ M.whp : arg = (MyPa,d,1, n+1, r) ==> !MyPa res] >= (p ^(n+1)).
 apply (whp_split_if_end_ge MyPa 1 n r (p^(n+1)) d (fun x => !MyPa x) (H0 H) ).
seq 1 : (!MyP ri) (p ^(n+1)) p 1%r 0%r (d = myd /\ MyP = MyPa /\ (!MyP ri => M.c <= e + 1)).
inline*. sp.
seq 1 :  (d = myd /\ MyP = MyPa /\ myd = myd0 /\ (!MyP r0 => M.c <= e + 1)).
 while (d = myd /\ myd = myd0 /\ MyP = MyP0 /\ e = e0 /\ (!MyP r0 => M.c <= e0 + 1)).
wp. 
rnd.  skip. progress. smt(). skip. progress. smt(). sp.  skip. progress. 
 call phf. skip.  auto.
rcondt 1. skip. progress. smt(). 
wp. simplify.  rnd.  simplify.
skip. progress.
hoare. 
rcondf 1. skip.  progress. smt().
simplify. skip. auto. smt(@Real).
qed.


lemma iter_sample_eq (p : real) MyP r d:  
   (mu d (fun (x : rrt) => ! MyP x) = p) =>
  MyP r = false => forall e, 0 <= e =>
  phoare[ M.whp : arg = (MyP,d,1,e+1,r) ==> !MyP res ] = (p ^ (e+1)).
move => H1 H e ep.
have fact1  : phoare[ M.whp_if_end : arg = (MyP,d,1,e,r) ==> !MyP res ] = (p ^ (e+1)).
apply (iter  p r d MyP H1 H e ep). auto.
conseq (whp_split_if_end' MyP 1 e r (p^(e+1)) (fun x => !MyP x) d fact1).
qed.



lemma iter_sample_le (p : real) MyP r d:  
   (mu d (fun (x : rrt) => ! MyP x) <= p) =>
   MyP r = false => forall e, 0 <= e =>
    phoare[ M.whp : arg = (MyP,d,1,e+1,r) ==> !MyP res ] <= (p ^ (e+1)).
move => H1 H e ep.
have fact1  : phoare[ M.whp_if_end : arg = (MyP,d,1,e,r) ==> !MyP res ] <= (p ^ (e+1)).
apply (iter_le  p MyP r d H1 H e ep). auto.
conseq (whp_split_if_end_le MyP 1 e r (p^(e+1))  d (fun x => !MyP x) fact1).
qed.



lemma iter_sample_ge (p : real) MyP r d:  
   (mu d (fun (x : rrt) => ! MyP x) >= p) =>
   MyP r = false => forall e, 0 <= e =>
    phoare[ M.whp : arg = (MyP,d,1,e+1,r) ==> !MyP res ] >= (p ^ (e+1)).
move => H1 H e ep.
have fact1  : phoare[ M.whp_if_end : arg = (MyP,d,1,e,r) ==> !MyP res ] >= (p ^ (e+1)).
apply (iter_ge  p MyP r d H1 H e ep). auto.
conseq (whp_split_if_end_ge MyP 1 e r (p^(e+1))  d (fun x => !MyP x) fact1).
qed.

end section.
end IterUntilSuccDistr.



theory IterUntilSuccRew.

type sbits, iat, rrt, irt.

op pair_sbits : sbits * sbits -> sbits.
op unpair: sbits -> sbits * sbits.
axiom ips: injective pair_sbits. 
axiom unpair_pair x : unpair (pair_sbits x) = x.


module type HasRun = {
  proc run(z : irt) : rrt {}
}.


module W(A : HasRun) = {
  var c : int
  proc whp(p : rrt -> bool, i : irt, s : int, e : int, r : rrt) = {
    c <- s;
    while(c <= e /\ !p r){
     r <@ A.run(i);
     c <- c + 1;
    }
    return r;
  }


  proc if_whp(p : rrt -> bool, i : irt, s : int, e : int, r : rrt) = {
    c <- s;
    if(c <= e /\ !p r){
     r <@ A.run(i);
     c <- c + 1;
    }
    r <@ whp(p,i,W.c,e,r);
    return r;
  }

  proc whp_if(p : rrt -> bool, i : irt, s : int, e : int, r : rrt) = {
    var ri;
    c <- s;
    ri <@ whp(p,i,s,e-1,r);
    if(c <= e /\ !p ri){
     ri <@ A.run(i);
     c <- c + 1;
    }
    return ri;
  }

  proc whp_split(p : rrt -> bool, i : irt, s : int, m : int, e : int, r : rrt) = {
    c <- s;
    r <@ whp(p,i,s,m,r);
    r <@ whp(p,i,W.c,e,r);
    return r;
  }
  
}.



require RewBasics.
clone import RewBasics as RW with type sbits <- sbits,
                                  type iat   <- iat,
                                  type iat2  <- irt,
                                  type rrt   <- rrt,
                                  type irt   <- irt,
                                  op pair_sbits <- pair_sbits,
                                  op unpair <- unpair.

                                  


require ReflectionTemp.
clone import ReflectionTemp.Refl as Re with
                                  type at  <- irt,
                                  type rt  <- rrt.


                                  
section.

module DW = {
  var c : int
  proc whp_d(p : rrt -> bool,d : rrt distr, s : int, e : int, r : rrt) = { 
    c <- s;
    while(c <= e /\ !p r){
     r <@ SF.sampleFrom(d);
     c <- c + 1;
    }
    return r;
  }
}.

local clone import IterUntilSuccDistr with type sbits <- sbits,
                                           type iat <- iat,
                                           type rrt <- rrt,
                                           type irt <- irt.
  


op MyPred : rrt -> bool.

declare module A <: HasRun {-W, -DW}.
declare axiom A_ll : islossless A.run.
declare axiom A_rew_ph x : phoare[ A.run : (glob A) = x ==> !MyPred res => (glob A) = x ] = 1%r.



local lemma A_rew_h x : hoare[ A.run : (glob A) = x ==> !MyPred res => (glob A) = x ] .
bypr. progress. 
have <- : Pr[A.run(z{m}) @ &m : false ] = 0%r. rewrite Pr[mu_false]. auto.
have : 1%r = Pr[A.run(z{m}) @ &m : !(!MyPred res => (glob A) = (glob A){m}) ]
  + Pr[A.run(z{m}) @ &m : !MyPred res => (glob A) = (glob A){m} ].
   have <- :  Pr[A.run(z{m}) @ &m : true ] = 1%r. byphoare. apply  A_ll. auto. auto.
rewrite Pr[mu_split (!MyPred res => (glob A) = (glob A){m}) ]. smt().
have ->: Pr[A.run(z{m}) @ &m : (!MyPred res => (glob A) = (glob A){m}) ] = 1%r. byphoare (_: (glob A) = (glob A){m} ==> _). apply (A_rew_ph). auto. auto.
rewrite Pr[mu_false]. smt().
qed.


local lemma asdistr_rew2 : forall (D : (glob A) -> irt -> rrt distr) ,
  (forall &m M a, mu (D (glob A){m} a) M = Pr[ A.run(a) @ &m :  M res ])
  => forall &m a, equiv [SF.sampleFrom ~ A.run : ={glob A} /\ arg{1} = (D (glob A){m} a) 
                         /\ (glob A){2} = (glob A){m} /\ arg{2} = a 
                         ==>  res{1} =  res{2} /\ (!MyPred res{2}  =>(glob A){2} = (glob A){m}) ].
progress.
bypr (res{1}, true) (res{2}, !MyPred res{2} => (glob A){2} = (glob A){m}). progress. smt().
progress. 
have ->: Pr[SF.sampleFrom(d{1}) @ &1 : (res, true) = a0]
 = Pr[SF.sampleFrom(d{1}) @ &1 : res = a0.`1 /\ a0.`2 = true].
rewrite Pr[mu_eq]. smt(). auto.
have ->: Pr[A.run(z{2}) @ &2 : (res, (!MyPred res => (glob A) = (glob A){m})) = a0]
 = Pr[A.run(z{2}) @ &2 : res  = a0.`1 /\ (!MyPred res => (glob A) = (glob A){m})  = a0.`2].
rewrite Pr[mu_eq]. smt(). auto.
case (a0.`2 = true).
progress. rewrite H3. simplify.
have -> : Pr[A.run(z{2}) @ &2 :
   res = a0.`1 /\ (!MyPred res => (glob A) = (glob A){m}) = true]
 = Pr[A.run(z{2}) @ &2 :
   res = a0.`1].
  have kj: Pr[A.run(z{2}) @ &2 : res = a0.`1 /\ (!MyPred res => (glob A) = (glob A){m}) = false] = 0%r.
   have : Pr[A.run(z{2}) @ &2 : !(!MyPred res => (glob A) = (glob A){m})] = 0%r.
   rewrite - H2.
   byphoare (_: (glob A) = (glob A){2} ==> _ ). hoare.  simplify.
    have f : forall ga, phoare[ A.run : (glob A) = ga ==>  (!MyPred res => (glob A) = ga) ] = 1%r.
    move => ga. apply A_rew_ph.  apply A_rew_h. auto. auto.
    progress.
     have : Pr[A.run(arg{2}) @ &2 :
   res = a0.`1 /\ (! MyPred res => (glob A) = (glob A){m}) = false] <= 0%r. rewrite - H4. rewrite Pr[mu_sub]. smt(). auto.
  have : Pr[A.run(arg{2}) @ &2 :
   res = a0.`1 /\ (! MyPred res => (glob A) = (glob A){m}) = false] >= 0%r. rewrite Pr[mu_ge0]. auto. smt().
  have ->: Pr[A.run(arg{2}) @ &2 : res = a0.`1] = Pr[A.run(arg{2}) @ &2 :
   res = a0.`1 /\ (! MyPred res => (glob A) = (glob A){m}) = true] + Pr[A.run(arg{2}) @ &2 :
   res = a0.`1 /\ (! MyPred res => (glob A) = (glob A){m}) = false]. rewrite Pr[mu_split (! MyPred res => (glob A) = (glob A){m})].
smt(). rewrite kj. smt().
byequiv (_: ={glob A} /\ arg{2} = z{2} /\ (glob A){2} = (glob A){m} /\ arg{1} = D (glob A){m} z{2} ==> _).
exists* z{2}. elim*. progress.
proc*.
call  (asdistr A D H &m arg_R ).
auto. progress. auto.
move => hp.
have hpp : a0.`2 = false. smt().
clear hp.
rewrite hpp.
  have ->: Pr[SF.sampleFrom(d{1}) @ &1 : res = a0.`1 /\ false] = 0%r. simplify.
  rewrite Pr[mu_false]. auto.
  have ->: Pr[A.run(z{2}) @ &2 : res = a0.`1 /\ (!MyPred res => (glob A) = (glob A){m}) = false] = 0%r.
   have : Pr[A.run(z{2}) @ &2 : !(!MyPred res => (glob A) = (glob A){m}) ] = 0%r.
   rewrite - H2.
   byphoare (_: (glob A) = (glob A){2} ==> _ ). hoare.  simplify.
    have f : forall ga, phoare[ A.run : (glob A) = ga ==> (!MyPred res => (glob A) = ga) ] = 1%r.
    move => ga. apply A_rew_ph. apply A_rew_h.  auto. auto.
    move => q.
    have : Pr[A.run(arg{2}) @ &2 :
   res = a0.`1 /\ (! MyPred res => (glob A) = (glob A){m}) = false] <= 0%r. rewrite - q. rewrite Pr[mu_sub]. smt(). auto. 
    have : Pr[A.run(arg{2}) @ &2 :
   res = a0.`1 /\ (! MyPred res => (glob A) = (glob A){m}) = false] >= 0%r. rewrite Pr[mu_ge0]. smt(). auto.  smt(). auto.
qed.


  
local lemma prob_refl_app_distr  (da : (glob A) -> irt -> rrt distr) :  
 (forall &m (M : rrt -> bool) (a : irt),
       mu (da (glob A){m} a) M = Pr[A.run(a) @ &m : M res])
 => forall &m P e (s : int) rr ia,  
  Pr[ DW.whp_d(MyPred,da (glob A){m} ia,s,e,rr) @ &m : P res ]
   = Pr[ W(A).whp(MyPred,ia, s,e,rr) @ &m : P res ].
progress. 
byequiv (_: ={p,s,e,r, glob A} /\ d{1} = (da (glob A){m} ia) /\ i{2} = ia /\ p{1} = MyPred
     /\ (glob A){2} = (glob A){m} ==> _). proc.
sp. 
exists* (glob A){2} . elim*. progress.
while (={p,r,e} /\ DW.c{1} = W.c{2} /\ d{1} = da (glob A){m} ia /\ i{2} = ia /\   p{1} = MyPred /\ (!p{1} r{2} => ={glob A} /\ (glob A){2} = (glob A){m}) ).
wp.
call (asdistr_rew2  da H &m ia).
skip. progress;smt(). skip. progress. smt().
progress. 
qed.



lemma iter_run_rew_eq &m (p : real)  i e ra :  MyPred ra = false => 0 <= e =>
   Pr[ A.run(i) @ &m : !MyPred res ]  = p
  => Pr[ W(A).whp(MyPred,i, 1,e,ra) @ &m : !MyPred res ] = p ^ e.
case (e = 0).
progress.
have ->: Pr[A.run(i) @ &m : ! MyPred res] ^ 0 = 1%r. smt(@Real).
byphoare (_: e = 0 /\ s = 1 /\ MyPred ra = false /\ r = ra ==> _).
simplify. proc. 
sp.
rcondf 1. skip. progress. skip. smt(). smt(). auto.  auto. 
move => ez sf ep.
have :  exists e', e' + 1 = e /\ 0 <= e'. smt().
elim. progress.
have exD :  exists (D : (glob A) -> irt -> rrt distr),
      forall &m (M : rrt -> bool) (a : irt),
        mu (D (glob A){m} a) M = Pr[A.run(a) @ &m : M res].
apply (reflection_simple_res A).
elim exD. progress. 
rewrite - (prob_refl_app_distr  D H0 &m (fun x => !MyPred x)).
have ->: Pr[DW.whp_d(MyPred, D (glob A){m} i, 1, e' + 1 , ra) @ &m : !MyPred res]
 = Pr[M.whp(MyPred, D (glob A){m} i, 1, e' + 1 , ra) @ &m : !MyPred res].
byequiv. proc. simplify.  sp. 
conseq (_: ={e,r} /\ p{1} = MyP{2} /\ DW.c{1} = M.c{2} /\ d{1} = myd{2}  ==> _). auto.
while (={e,r} /\ p{1} = MyP{2} /\ DW.c{1} = M.c{2} /\ d{1} = myd{2}). wp. inline*. wp.  rnd. wp. 
skip. progress. 
skip. progress. auto. auto.
byphoare(_: arg = (MyPred,D (glob A){m} i, 1, e' + 1 , ra ) ==> _).
have lf :   mu (D (glob A){m} i) (fun (x : rrt) => ! MyPred x) =
  Pr[A.run(i) @ &m : ! MyPred res].
rewrite H0. auto.
conseq (iter_sample_eq (Pr[A.run(i) @ &m : ! MyPred res]) MyPred  ra (D (glob A){m} i) lf sf e' H ).
auto.
auto.
qed.



lemma iter_run_rew_le &m pr  i e ra :  MyPred ra = false => 0 <= e =>
   Pr[ A.run(i) @ &m : !MyPred res ]  <= pr
  => Pr[ W(A).whp(MyPred,i, 1,e,ra) @ &m : !MyPred res ] <= pr ^ e.
case (e = 0).
progress.
byphoare (_: e = 0 /\ s = 1 /\ p ra = false /\ r = ra ==> _).
simplify. proc.
sp.
rcondf 1. skip. progress. skip. smt(@Real). smt(). auto.  auto.
move => ez sf ep.
have :  exists e', e' + 1 = e /\ 0 <= e'. smt().
elim. progress.
have exD :  exists (D : (glob A) -> irt -> rrt distr),
      forall &m (M : rrt -> bool) (a : irt),
        mu (D (glob A){m} a) M = Pr[A.run(a) @ &m : M res].
apply (reflection_simple_res A).
elim exD. progress.
rewrite - (prob_refl_app_distr  D H1 &m (fun x => !MyPred x)).
have ->: Pr[DW.whp_d(MyPred,D (glob A){m} i, 1, e' + 1 , ra) @ &m : !MyPred res]
 = Pr[M.whp(MyPred,D (glob A){m} i, 1, e' + 1 , ra) @ &m : !MyPred res].
byequiv. proc.  sp.
conseq (_: ={e,r} /\ p{1} = MyP{2} /\ DW.c{1} = M.c{2} /\ d{1} = myd{2}  ==> _). auto.
while (={e,r} /\ p{1} = MyP{2} /\ DW.c{1} = M.c{2} /\ d{1} = myd{2}). wp. inline*. wp.  rnd. wp.
skip. progress.
skip. progress. auto. auto.
byphoare(_: arg = (MyPred,D (glob A){m} i, 1, e' + 1 , ra ) ==> _).
have lf :   mu (D (glob A){m} i) (fun (x : rrt) => ! MyPred x) <= pr. rewrite H1. auto.
conseq (iter_sample_le pr MyPred ra (D (glob A){m} i) lf sf e' H ). auto.
auto.
qed.


lemma iter_run_rew_ge &m pr  i e ra :  MyPred ra = false => 0 <= e =>
   Pr[ A.run(i) @ &m : !MyPred res ]  >= pr
  => Pr[ W(A).whp(MyPred,i, 1,e,ra) @ &m : !MyPred res ] >= pr ^ e.
case (e = 0).
progress.
byphoare (_: e = 0 /\ s = 1 /\ p ra = false /\ r = ra ==> _).
simplify. proc.
sp.
rcondf 1. skip. progress. skip. smt(@Real). smt(). auto.  auto.
move => ez sf ep.
have :  exists e', e' + 1 = e /\ 0 <= e'. smt().
elim. progress.
have exD :  exists (D : (glob A) -> irt -> rrt distr),
      forall &m (M : rrt -> bool) (a : irt),
        mu (D (glob A){m} a) M = Pr[A.run(a) @ &m : M res].
apply (reflection_simple_res A).
elim exD. progress.
rewrite - (prob_refl_app_distr  D H1 &m (fun x => !MyPred x)).
have ->: Pr[DW.whp_d(MyPred,D (glob A){m} i, 1, e' + 1 , ra) @ &m : !MyPred res]
 = Pr[M.whp(MyPred,D (glob A){m} i, 1, e' + 1 , ra) @ &m : !MyPred res].
byequiv. proc.  sp.
conseq (_: ={e,r} /\ p{1} = MyP{2} /\ DW.c{1} = M.c{2} /\ d{1} = myd{2}  ==> _). auto.
while (={e,r} /\ p{1} = MyP{2} /\ DW.c{1} = M.c{2} /\ d{1} = myd{2}). wp. inline*. wp.  rnd. wp.
skip. progress.
skip. progress. auto. auto.
byphoare(_: arg = (MyPred,D (glob A){m} i, 1, e' + 1 , ra ) ==> _).
have lf :   mu (D (glob A){m} i) (fun (x : rrt) => ! MyPred x) >= pr. rewrite H1. auto.
conseq (iter_sample_ge pr MyPred ra (D (glob A){m} i) lf sf e' H ). auto.
auto.
qed.


lemma iter_run_rew_eq_ph &m p i e r :  MyPred r = false => 0 <= e =>
   phoare[ A.run : arg = i /\ (glob A){m} = (glob A) ==> !MyPred res ] = p =>
   phoare [ W(A).whp : arg = (MyPred,i, 1,e,r) /\ (glob A){m} = (glob A) ==> !MyPred res ] = (p ^ e).
move => sf ep ph1.
bypr. progress. rewrite H. simplify.
rewrite -  (iter_run_rew_eq &m0 p  i e r sf ep).
byphoare (_: arg = i /\ (glob A) = (glob A){m0} ==> _). conseq ph1. auto. auto.
auto. auto.
qed.
end section.

end IterUntilSuccRew.


theory IterUntilSucc.
type rt, iat.

module type Run = {
  proc run(i:iat) : rt
}.

module M(A : Run) = {
  var c : int
  proc whp(i : iat, MyP : rt -> bool, s : int, e : int, r : rt) = {
    c <- s;
    while(c <= e /\ !MyP r){
     r <@ A.run(i);
     c <- c + 1;
    }
    return r;
  }

  proc whp_if_end(i : iat, MyP : rt -> bool,s : int, e : int, r : rt) = {
    var ri : rt;
    ri <@ whp(i,MyP, s,e,r);     
    if(c <= e + 1 /\ !MyP ri){
      ri <@ A.run(i);
      c <- c + 1;
    }
    return ri;
  }
}.

section.
declare module A <: Run{-M}.

(* declare axiom A_run_ll : islossless A.run. *)

local lemma whp_split_if_end :  
  equiv[ M(A).whp ~ M(A).whp_if_end : ={glob A, i, MyP, s,r} /\ e{1} - 1 = e{2}
        ==> ={res,M.c} ].
proof. proc.
inline*. sp. 
splitwhile{1} 1 : M.c  <= (e - 1) .
seq  1 1 : (={M.c, glob A} /\ r{1} = r0{2} /\ e0{2} = e{2} /\ i{1} = i0{2} /\ i{2} = i0{2}
   /\ MyP0{2} = MyP{1} /\ MyP0{2} = MyP{2} 
   /\ e{1} - 1 = e0{2} /\ (!MyP{1} r{1} => (e{1} - 1) < M.c{1} )).
while (={M.c,MyP, glob A} /\ r{1} = r0{2} /\ e0{2} = e{2} /\ i{1} = i0{2} /\ i{2} = i0{2}
   /\ MyP{1} = MyP0{2} /\ MyP{2} = MyP0{2}
   /\ e{1} - 1 = e0{2} ).
wp. call (_:true).   skip. progress. smt(). skip. progress. smt(). smt().
sp. simplify.
case (MyP{1} r{1}).
rcondf {1} 1. progress. skip. smt().
rcondf {2} 1. progress. skip. progress. smt().
skip. progress.
unroll {1} 1.
if. progress.  
rcondf {1} 3. progress.
wp. call (_:true). skip. progress. smt().
wp. call (_:true). skip. progress. 
rcondf {1} 1. progress. skip. progress.
qed.



local lemma whp_split_if_end' MyP  i s e r p P :  
  (phoare [ M(A).whp_if_end : arg = (i,MyP,s,e,r) ==> P res ] = p)
   => phoare [ M(A).whp : arg = (i, MyP,s,e+1,r) ==> P res ] = p.
proof. progress. bypr.
progress.
have <-: Pr[M(A).whp_if_end(i, MyP, s, e, r) @ &m : P res] = p.
byphoare (_: arg = (i, MyP, s, e, r) ==> _).
conseq H. auto. auto. byequiv.
conseq whp_split_if_end. smt(). auto. auto. auto.
qed.


local lemma lll (b a c : real) : a <= b => b <= c => a <= c.
smt(). qed.

    
local lemma whp_split_if_end_le MyP i s e r p P :  
  (phoare [ M(A).whp_if_end : arg = (i,MyP,s,e,r) ==> P res ] <= p)
   => phoare [ M(A).whp : arg = (i,MyP,s,e+1,r) ==> P res ] <= p.
proof. progress. bypr.
progress.
have zz : Pr[M(A).whp_if_end(i,MyP, s, e, r) @ &m : P res] <= p.
byphoare (_: arg = (i,MyP,s, e, r) ==> _).
conseq H. auto. auto. 
apply (lll Pr[M(A).whp_if_end(i, MyP,s, e, r) @ &m : P res] ).
byequiv.
conseq whp_split_if_end. smt(). auto. auto. auto. apply zz.
qed.


local lemma whp_split_if_end_ge MyP i s e r p P :  
  (phoare [ M(A).whp_if_end : arg = (i,MyP,s,e,r) ==> P res ] >= p)
   => phoare [ M(A).whp : arg = (i,MyP,s,e+1,r) ==> P res ] >= p.
proof. progress. bypr.
move => &m ae. 
have zz : Pr[M(A).whp_if_end((i,MyP,s,e,r)) @ &m : P res] >= p.
byphoare (_: arg = ((i,MyP,s,e,r)) ==> _).
  conseq H.  progress.  auto.
apply (lll Pr[M(A).whp_if_end(i, MyP, s, e, r) @ &m : P res] ). auto.
byequiv.
symmetry. conseq whp_split_if_end. smt(). auto. auto. auto. 
qed.


local lemma iter_eq (p : real) ia r MyPa: 
   (phoare[ A.run : arg = ia ==> !MyPa res ] = p) =>
  MyPa r = false => forall e, 0 <= e => 
  phoare[ M(A).whp_if_end : arg = (ia, MyPa, 1,e,r) ==> !MyPa res ] = (p ^ (e+1)).
proof. move => iipr ipr. apply ge0ind. smt().
progress. simplify.
  progress. proc.
inline*. sp.
rcondf 1. skip. smt().
sp. 
rcondt 1. skip. progress. smt().
swap 1 1.  
have f : phoare[ A.run : arg = ia ==> ! MyPa res] = (p^1). 
simplify.  conseq iipr. smt(@Real).
 call f. sp. skip. auto.
  simplify.
progress. proc.
  have phf: phoare[ M(A).whp : arg = (ia, MyPa, 1, n+1, r) ==> !MyPa res] = (p ^(n+1)).
 apply (whp_split_if_end'  MyPa ia 1 n r  (p^(n+1)) (fun x => !MyPa x) (H0 H) ).
seq 1 : (!MyPa ri) (p ^(n+1)) p 1%r 0%r (i =  ia /\ MyP = MyPa /\ (!MyPa ri => M.c <= e + 1)).
inline*. sp.
seq 1 :  (i =  ia /\ MyP = MyPa /\ (!MyPa r0 => M.c <= e + 1)).
 while (i = ia /\ i = i0 /\ MyP = MyP0 /\ MyP = MyPa /\ e = e0 /\ (!MyPa r0 => M.c <= e0 + 1)).
wp. 
call (_:true).  skip. progress. smt(). skip. progress. smt(). sp.  skip. progress. 
 call phf. skip.  auto.
rcondt 1. skip. progress. smt().  
wp. simplify.  call iipr.  simplify.
skip. progress. 
hoare. 
rcondf 1. skip.  progress. smt().
simplify. skip. auto. smt(@Real).
qed.

local lemma iter_le (p : real) ia r MyPa:
   (phoare[ A.run : arg = ia ==> !MyPa res ] <= p) =>
  MyPa r = false => forall e, 0 <= e =>
  phoare[ M(A).whp_if_end : arg = (ia, MyPa, 1,e,r) ==> !MyPa res ] <= (p ^ (e+1)).
proof. move => iipr ipr. apply ge0ind. smt().
progress. simplify.
  progress. proc.
inline*. sp.
rcondf 1. skip. smt().
sp.
rcondt 1. skip. progress. smt().
swap 1 1.
have f : phoare[ A.run : arg = ia ==> ! MyPa res] <= (p^1).
conseq iipr. smt(@Real).
call f. sp. skip. auto.
  simplify.
progress. proc.
  have phf: phoare[ M(A).whp : arg = (ia, MyPa, 1, n+1, r) ==> !MyPa res] <= (p ^(n+1)).
 apply (whp_split_if_end_le MyPa  ia 1 n r (p^(n+1))  (fun x => !MyPa x) (H0 H)  ).
seq 1 : (!MyPa ri) (p ^(n+1)) p 1%r 0%r (i = ia /\ MyP = MyPa /\ (!MyPa ri => M.c <= e + 1)).
inline*. sp.
seq 1 :  (i = ia /\ MyP = MyPa /\ (!MyPa r0 => M.c <= e + 1)).
 while (i = ia /\ i = i0 /\ MyP = MyP0 /\ MyP = MyPa /\ e = e0 /\ (!MyPa r0 => M.c <= e0 + 1)).
wp.
call (_:true).  skip. progress. smt(). skip. progress. smt(). sp.  skip. progress.
 call phf. skip.  auto.
rcondt 1. skip. progress. smt().
wp. simplify.  call iipr.  simplify.
skip. progress.
hoare.
rcondf 1. skip.  progress.  smt().
simplify. skip. auto. smt(@Real).
qed.

local lemma iter_ge (p : real) ia r MyPa:
   (phoare[ A.run : arg = ia ==> !MyPa res ] >= p) =>
  MyPa r = false => forall e, 0 <= e =>
  phoare[ M(A).whp_if_end : arg = (ia, MyPa, 1,e,r) ==> !MyPa res ] >= (p ^ (e+1)).
proof. move => iipr ipr. apply ge0ind. smt().
progress. simplify.
  progress. proc.
inline*. sp.
rcondf 1. skip. smt().
sp.
rcondt 1. skip. progress. smt().
swap 1 1.
have f : phoare[ A.run : arg = ia ==> ! MyPa res] >= (p^1).
conseq iipr. smt(@Real).
call f. sp. skip. auto.
  simplify.
progress. proc.
  have phf: phoare[ M(A).whp : arg = (ia, MyPa, 1, n+1, r) ==> !MyPa res] >= (p ^(n+1)).
 apply (whp_split_if_end_ge MyPa  ia 1 n r (p^(n+1))  (fun x => !MyPa x) (H0 H)  ).
seq 1 : (!MyPa ri) (p ^(n+1)) p 1%r 0%r (i = ia /\ MyP = MyPa /\ (!MyPa ri => M.c <= e + 1)).
inline*. sp.
seq 1 :  (i = ia /\ MyP = MyPa /\ (!MyPa r0 => M.c <= e + 1)).
 while (i = ia /\ i = i0 /\ MyP = MyP0 /\ MyP = MyPa /\ e = e0 /\ (!MyPa r0 => M.c <= e0 + 1)).
wp.
call (_:true).  skip. progress. smt(). skip. progress. smt(). sp.  skip. progress.
 call phf. skip.  auto.
rcondt 1. skip. progress. smt().
wp. simplify.  call iipr.  simplify.
skip. progress.
hoare.
rcondf 1. skip.  progress. smt().
simplify. skip. auto. smt(@Real).
qed.



lemma iter_run_eq_ph (p : real) ia MyP r :  
   (phoare[ A.run : arg = ia ==> !MyP res ] = p) =>
  MyP r = false => forall e, 0 <= e =>
  phoare[ M(A).whp : arg = (ia,MyP,1,e+1,r) ==> !MyP res ] = (p ^ (e+1)).
move => H1 H e ep.
have fact1  : phoare[ M(A).whp_if_end : arg = (ia,MyP,1,e,r) ==> !MyP res ] = (p ^ (e+1)).
apply (iter_eq  p ia r  MyP H1 H e ep). auto.
conseq (whp_split_if_end' MyP ia 1 e r (p^(e+1)) (fun x => !MyP x) fact1).
qed.

lemma iter_run_le_ph (p : real) ia MyP r:  
   (phoare[ A.run : arg = ia ==> !MyP res ] <= p) =>
  MyP r = false => forall e, 0 <= e =>
  phoare[ M(A).whp : arg = (ia, MyP,1,e+1,r) ==> !MyP res ] <= (p ^ (e+1)).
move => H1 H e ep.
have fact1  : phoare[ M(A).whp_if_end : arg = (ia,MyP,1,e,r) ==> !MyP res ] <= (p ^ (e+1)).
apply (iter_le   p  ia r MyP H1 H e ep). auto.
conseq (whp_split_if_end_le MyP ia 1 e r (p^(e+1))  (fun x => !MyP x) fact1).
qed.

lemma iter_run_ge_ph (p : real) ia MyP r:  
   (phoare[ A.run : arg = ia ==> !MyP res ] >= p) =>
  MyP r = false => forall e, 0 <= e =>
  phoare[ M(A).whp : arg = (ia, MyP,1,e+1,r) ==> !MyP res ] >= (p ^ (e+1)).
move => H1 H e ep.
have fact1  : phoare[ M(A).whp_if_end : arg = (ia,MyP,1,e,r) ==> !MyP res ] >= (p ^ (e+1)).
apply (iter_ge   p  ia r MyP H1 H e ep). auto.
conseq (whp_split_if_end_ge MyP ia 1 e r (p^(e+1))  (fun x => !MyP x) fact1).
qed.

end section.

end IterUntilSucc.




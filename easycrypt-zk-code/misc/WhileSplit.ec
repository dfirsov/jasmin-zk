pragma Goals:printall.
require import Int Real AllCore Distr FSet StdRing StdOrder StdBigop List.
(*---*) import RField RealOrder Bigreal BRA.

require import AuxResults.

type rrt, irt, sbits, dt, de.

op MyPred : rrt -> bool.
op df : irt -> rrt -> de -> dt.

module type Dist = {
  proc guess(r:dt) : bool
}.

module type Run = {
  proc run(i:irt) : rrt
}.                                  


op pair_sbits : sbits * sbits -> sbits.
op unpair: sbits -> sbits * sbits.


require import WhileNoSuccess.
clone import IterUntilSuccRew as IFB with 
  type rrt <- rrt,
  type irt <- irt,
  type iat <- (rrt -> bool) * irt * int * int * rrt,
  type sbits <- sbits,
  op MyPred <- MyPred,
  op pair_sbits <- pair_sbits,
  op unpair <- unpair.

  
require PrIntervalToSum.
clone import PrIntervalToSum as PIT with type rt <- bool * rrt,
                                         type iat <- ((rrt -> bool) * irt * int * int * rrt)*de .

section.

declare module A <: Run {-W, -DW}.
declare module D <: Dist {-W, -DW}.

declare axiom A_ll : islossless A.run.
declare axiom A_rew_ph x : phoare[ A.run : (glob A) = x ==> !MyPred res => (glob A) = x ] = 1%r.
declare axiom whp_axp : equiv[ D.guess ~ D.guess : ={glob A, arg} ==> ={res}  ].
declare axiom D_ll : islossless D.guess.


local lemma A_rew_hoare x : hoare[ A.run : (glob A) = x ==> !MyPred res => (glob A) = x ] .
proof.  hoare. 
bypr. progress.
have  : 1%r = Pr[A.run(arg{m}) @ &m : true ].
byphoare. conseq A_ll. auto. auto.
rewrite Pr[mu_split (! MyPred res => (glob A) = (glob A){m})].
progress.
have f : Pr[A.run(arg{m}) @ &m : ! MyPred res => (glob A) = (glob A){m}] = 1%r.
byphoare (: (glob A) = (glob A){m} ==> _).
proc*. call (A_rew_ph (glob A){m}).
skip.  auto. auto. auto. smt().
qed.


lemma if_whp_prop : 
  equiv [ W(A).whp ~ W(A).if_whp : ={glob W, glob A, arg} ==>  ={glob W, glob A, res} ].
proc. inline*.
unroll {1} 2.
sp.
if. progress.
seq 2 8 : (={glob A, glob W} /\ e{1} = e0{2} /\ p{1} = p0{2} /\ r{1} = r0{2} /\ i{1} = i0{2} 
  /\ e{2} = e0{2} /\ p{2} = p0{2} /\ r{2} = r0{2} /\ i{2} = i0{2} ).
wp.  call (_:true). skip. progress.
wp.
 while (={glob A, glob W} /\ e{1} = e0{2} /\ p{1} = p0{2} /\ r{1} = r0{2} /\ i{1} = i0{2} ).
wp.
call (_: true). skip. progress.
skip. progress.
sp.
rcondf {1} 1. progress.
rcondf {2} 1. progress. wp. skip. progress. 
qed.


lemma whp_if_prop : 
  equiv [ W(A).whp ~ W(A).whp_if : ={glob W, glob A, arg} ==> ={glob W, glob A, res} ].
proc.
inline*. sp. 
case (s{2} <= e{2}).
splitwhile {1} 1 : (W.c <= e-1).
seq 1 1 : (={W.c, glob A,e,p,i} /\ e{1} = e0{2} + 1  /\ p{1} = p0{2} /\ r{1} = r0{2} /\ i{1} = i0{2} /\ (! p r => W.c = e){1}).
while (={W.c, glob A,e,p,i} /\ e{1} = e0{2} + 1 /\ p{1} = p0{2}  /\ r{1} = r0{2} /\ i{1} = i0{2} /\ (! p r => W.c <= e){1}).
wp. call (_:true). skip. progress.
smt(). smt().
skip. progress. smt().
sp.
unroll {1} 1.
seq 1 1 : (={glob A, W.c,e,p,i} /\ ri{2} = r{1} /\ (! p{1} r{1} => W.c{1} = e{1}+1)). 
if. progress. wp. call (_:true). skip. progress. smt(). skip. progress. smt().
rcondf {1} 1. progress. skip. progress. smt(). skip. progress.
rcondf {1} 1. progress. skip. progress. smt().
rcondf {2} 1. progress. skip. progress. smt().
sp. 
rcondf {2} 1. progress. skip. progress. smt().
skip. progress.
qed.


lemma whp_split_prop : 
  equiv [ W(A).whp ~ W(A).whp_split : m{2} <= e{2}  /\ ={glob W, glob A, p, i, s, e, r}
        ==>  ={glob W, glob A, res} ].
proc.  inline*.
exists* m{2}. elim*. progress.
splitwhile {1} 2 : (W.c <= m_R).      
sp.
seq 1 1 : (={glob A, W.c,p,i,e} /\ m_R = m{2} /\ m{2} <= e{2} /\ e0{2} = m_R /\ r{1} = r0{2} /\ p{1} = p0{2} /\ i{1} = i0{2}).
while (={glob A, W.c,p,i,e} /\ m_R = m{2}  /\ m{2} <= e{2} /\ e0{2} = m_R /\ r{1} = r0{2} /\ p{1} = p0{2} /\ i{1} = i0{2}).
wp. call (_:true). skip. progress. smt(). 
skip. progress. smt().
sp. 
wp.
while (={glob A, W.c,p,i,e} /\ m_R = m{2}  /\ e{2} = e1{2} /\ m{2} <= e{2} /\ e0{2} = m_R /\ r{1} = r1{2} /\ p{1} = p1{2} /\ i{1} = i1{2}).
wp. call (_:true). skip. progress. 
skip. progress.
qed.


module W0(A : Run, D : Dist) = {
  proc run(a : irt,w:de) = {
      var r, b;
      r <@ A.run(a);
      b <@ D.guess(df a r w);
      return (b, r);
  }
}.


module W1(A : Run, D : Dist) = {
  module M = W(A)
  proc run(a : (rrt -> bool) * irt * int * int * rrt, w: de) = {
      var r, b;
      r <@ M.whp(a);
      b <@ D.guess(df a.`2 r w);
      return (b, r);
  }
}.


local module W2 = {
  module M = W(A)
  proc run(a : (rrt -> bool) * irt * int * int * int * rrt, w:de ) = {
      var r, b;
      r <@ M.whp_split(a);
      b <@ D.guess(df a.`2 r w);
      return (b, r);
  }
}.


local module W3 = {
  module M = W(A)
  proc run(a : (rrt -> bool) * irt * int * int * rrt,w:de ) = {
      var r, b;
      r <@ M.whp_if(a);
      b <@ D.guess(df a.`2 r w);
      return (b, r);
  }
}.


local module W3' = {
  module M = W(A)
  proc run(a : (rrt -> bool) * irt * int * int * rrt,w:de ) = {
    var r, b,ri;   
    ri <@ M.whp(a.`1, a.`2, a.`3, a.`4-1, a.`5);
    if (W.c <= a.`4 /\ ! a.`1 ri) {
      W.c <- W.c+1;
      (b,r) <@ W0(A,D).run(a.`2,w);
    }else{
      r <- ri;
      b <@ D.guess(df a.`2 r w);
    }
    return (b, r);
  }
}.


local module W4 = {
  module M = W(A)
  proc run(a : (rrt -> bool) * irt * int * int * rrt,w:de ) = {
      var r;
      M.whp(a);
      r <@ W0(A,D).run(a.`2,w);
      return r;
  }
}.


local module CAW = {
  proc run(a : (rrt -> bool) * irt * int * int * rrt,w:de) = {
    var r;
    r <@ W1(A,D).run(a,w);
    return r;
  }
}.


local lemma w3w3' : equiv[ W3.run ~ W3'.run : ={arg, glob A, glob W} ==> ={res, glob W} ].
proof. proc.
inline W3.M.whp_if. sp.  elim*. progress.
seq 1 1 : ( ={w,a,ri, glob A, glob W} /\ p{1} = a.`1{2} /\ e{1} = a.`4{2} /\ i{1} = a.`2{2} ). 
inline*. sp. 
wp. 
while (={a,  w, glob A, glob W} /\ p{1} = a{2}.`1 /\ i{1} = a.`2{2} /\  i0{1} = i{2} /\ e0{1} = e{2} /\ p0{1} = p{2} /\ r1{1} = r0{2} /\ e{1} = a.`4{2}).
wp.  call (_:true). skip. progress. skip. progress.
if. smt().
inline*. wp.  sp.  call whp_axp. wp.  call (_:true). skip. progress. 
call whp_axp. wp.  skip. progress. 
qed.


local lemma whp_premat_1_eq  pa ia (sa : int) ea ra ja : sa <= ja => ja <= ea + 1 =>
  equiv [ W(A).whp ~  W(A).whp_split : arg{1} = (pa,ia,sa,ja-1,ra) 
  /\ arg{2} = (pa,ia,sa,ja-1,ea,ra) /\  ={glob A} ==>   (((W.c = ja /\ pa res){1} /\ (W.c = ja /\ pa res){2} => ={res, glob A})    /\ (W.c = ja /\ pa res){1}  <=> (W.c = ja /\ pa res){2} )  ].
proof. move => hp ph.
proc*.
inline W(A).whp_split. sp.
seq 1 1 : (={glob A, glob W} /\ p{1} = pa /\ p0{2} = pa /\ r0{1} = r1{2} /\ p{1} = p0{2} /\ e{1} = ja-1 /\ i{1} = i0{2} /\ s{1} = s0{2} /\ (!p r0 => W.c = e + 1){1} /\ e0{2} = ea).
inline*.  sp. wp.
while (={glob A, glob W} /\ (e0,p0,r1,i0){1} = (e1,p1,r2,i1){2} /\ (!p0 r1 => W.c <= e0 + 1){1}). wp. call (_:true). skip. progress.
smt(). skip. progress. smt().
inline*.  sp.
case (pa r0{1}).
rcondf {2} 1. progress.  skip. progress. smt().
wp. skip. progress. wp.
conseq (_:  ={glob A} /\(p1{2} = pa /\ r2{2} = r0{1}) /\ ja  -1 <= e0{2}  /\  (! pa r0{1}) /\ W.c{1} = ja  /\ W.c{2} = W.c{1} /\ e1{2} = e0{2} /\ e1{2} = ea  ==> _ ). progress. smt().  smt().
case ((W.c <= e1 /\ ! p1 r2){2}).
unroll {2} 1. rcondt{2} 1. progress.
seq 0 2 : ( ja < W.c{2} /\ ! pa r0{1}).
wp. call {2} (_: true ==> true). apply A_ll.
skip. progress. smt().
while {2} (ja < W.c{2} /\ ! pa r0{1}) (e1{2} + 1 - W.c{2}).
progress. wp. call (_: true ==> true). apply A_ll. skip. progress. smt(). smt().
skip.    progress;smt().
rcondf {2} 1. progress. skip. smt(). 
qed.


local lemma whp_premat_1 &m pa ia (sa : int) ea ra ja wa : sa <= ja => ja <= ea + 1 =>
  Pr[ W1(A,D).run((pa,ia,sa,ja-1,ra),wa) @ &m : W.c = ja /\ pa res.`2 /\ res.`1 ]
   =   Pr[ W2.run((pa,ia,sa,ja-1,ea,ra),wa) @ &m : W.c = ja /\ pa res.`2 /\  res.`1 ].
proof. move => hp ph.
byequiv. proc*. inline W1(A,D).run. inline W2.run. sp. wp. 
seq 1 1 : ( ={w} /\ a0{1}.`2 = a0{2}.`2 /\ ((W.c = ja/\ pa r0 ){1} <=> (W.c = ja/\ pa r0 ){2})  /\  (((W.c = ja/\ pa r0 ){1} /\ (W.c = ja/\ pa r0 ){2})  => ={r0,w0, glob A})    ).
call (whp_premat_1_eq  pa ia sa ea ra ja hp ph). skip. progress;smt(). 
case (W.c{1} = ja /\ pa r0{1}).
conseq (_: ={glob W, glob A, r0,w0} /\ a0{1}.`2 = a0{2}.`2 ==> _). smt().
call whp_axp.
 skip. progress. smt(). simplify.
call {1} (_: true ==> true ).  apply D_ll.
call {2} (_: true ==> true ).  apply D_ll.
skip. smt(). auto.  auto.
qed.


local lemma whp_cap &m p i (s : int) ea r ja wa :  s <= ja => ja <= ea + 1 =>
   Pr[ W1(A,D).run((p,i,s,ea,r),wa) @ &m : W.c = ja /\ p res.`2 /\ res.`1 ]  
   = Pr[ W1(A,D).run((p,i,s,ja-1,r),wa) @ &m : W.c = ja /\ p res.`2 /\ res.`1 ].
proof.
move => sjp jap.
have ->:  Pr[ W1(A,D).run((p,i,s,ja-1,r),wa) @ &m : W.c = ja /\ p res.`2 /\ res.`1 ]
  =   Pr[ W2.run((p,i,s,ja-1,ea,r),wa) @ &m : W.c = ja /\ p res.`2 /\  res.`1 ].
apply whp_premat_1;auto.
byequiv (_: a{2} = (p, i, s, ja - 1, ea, r) /\
  (glob D){2} = (glob D){m} /\
  (glob A){2} = (glob A){m} /\
  a{1} = (p, i, s, ea, r) /\
  w{1} = w{2} /\  
  (glob D){1} = (glob D){m} /\ (glob A){1} = (glob A){m} /\ (glob W){1} = (glob W){2} ==> _).
proc*. inline W1(A,D).run W2.run. wp. sp.
seq 1 1 : (={glob W, glob A, r0,w0} /\ a0{1}.`2 = a0{2}.`2 ).
call whp_split_prop.
skip. progress. smt(). smt().
call whp_axp. skip. progress. smt(). auto.
auto. 
qed.


local lemma jjj ia wa &m : 
   phoare[ W0(A, D).run : arg = (ia,wa) /\ (glob A) = (glob A){m} ==> MyPred res.`2 /\ res.`1 ] =  Pr[W0(A, D).run(ia, wa) @ &m : MyPred res.`2 /\ res.`1] . 
bypr. progress. rewrite H. simplify. byequiv (_: ={glob A, arg} ==> _).
proc. call whp_axp. call (_:true). skip. progress. auto. auto.
qed.


local lemma whp_cap_fin &m ia (ea : int) r ja wa  :
  2  <= ja     =>
  ja <= ea + 1 =>
  MyPred r = false =>
   Pr[ W1(A,D).run((MyPred,ia,1,ea,r),wa) @ &m : W.c = ja /\ MyPred res.`2 /\ res.`1 ]
     = (Pr[ A.run(ia) @ &m : !MyPred res ] ^ (ja - 2)) 
        * Pr[ W0(A,D).run(ia,wa) @ &m : MyPred res.`2 /\ res.`1 ]. 
proof. progress.
have FG :  phoare[ W0(A,D).run : arg = (ia,wa) /\ (glob A) = (glob A){m}  /\ (glob D) = (glob D){m} 
  ==> MyPred res.`2 /\ res.`1 ] = Pr[ W0(A,D).run(ia,wa) @ &m : MyPred res.`2 /\ res.`1 ].
bypr. move => &m0 [eq1 eq2].  rewrite eq1. rewrite -eq1.
byequiv (_: ={glob A, arg} ==> ={res}).  proc.
call whp_axp. call (_:true). skip. progress. smt(). smt().
have FF : forall ea, 0 <= ea => phoare[ W(A).whp : 
   arg = (MyPred,ia,1,ea,r) /\ (glob A) = (glob A){m}
     ==> !MyPred res ] = (Pr[ A.run(ia) @ &m : !MyPred res ] ^ ea).
move => ea0 ea0p.
conseq (iter_run_rew_eq_ph A _ _ &m Pr[A.run(ia) @ &m : ! MyPred res]  ia ea0 r _ _ _).  auto. apply A_ll. apply A_rew_ph. auto.  auto. 
bypr. move => &m1 [eq1 eq2]. rewrite eq1. 
byequiv (_: ={arg, glob A} ==> ={res}). sim. progress. rewrite eq2. auto. auto.
pose p1 := Pr[ W0(A,D).run(ia,wa) @ &m : MyPred res.`2 /\ res.`1 ].
rewrite  (whp_cap &m MyPred ia 1 ea r ja ). smt(). smt().
have ->: Pr[W1(A,D).run((MyPred, ia, 1, ja - 1, r),wa) @ &m : W.c = ja /\ MyPred res.`2 /\ res.`1]
 = Pr[W3.run((MyPred, ia, 1, ja-1, r),wa) @ &m : W.c = ja /\ MyPred res.`2 /\  res.`1].
byequiv (_: ={glob W(A), arg} ==> _). proc*. inline W1(A,D).run. 
inline W3.run. sp. wp. 
call whp_axp. 
call whp_if_prop. skip. progress. 
auto. auto.
have -> : Pr[W3.run((MyPred, ia, 1, ja - 1, r), wa) @ &m :   W.c = ja /\ MyPred res.`2 /\ res.`1]
 = Pr[W3'.run((MyPred, ia, 1, ja - 1, r), wa) @ &m :   W.c = ja /\ MyPred res.`2 /\ res.`1].
byequiv (_: ={glob A, glob W, arg} ==> _). conseq w3w3'.  progress. auto. auto. auto.
byphoare (_: arg = ((MyPred, ia, 1, ja - 1, r),wa) /\ (glob A) = (glob A){m} ==> _);auto.
proc. inline W3.M.whp_if.  sp.
seq 1 : (! a.`1 ri) (Pr[ A.run(ia) @ &m : !MyPred res ] ^ (ja - 2))  p1 1%r 0%r (w = wa /\ a.`4 = ja - 1 /\ W.c <= a.`4  /\ a.`2 = ia /\ a.`1 = MyPred 
 /\ (!a.`1 ri => W.c = a.`4  /\  (glob A) = (glob A){m}) );auto.
sp. inline W(A).whp. 
wp.
while (W.c <= e + 1 /\ p = MyPred /\ p = MyPred  /\ (!p r0 =>   (glob A) = (glob A){m})). wp. 
call (A_rew_hoare (glob A){m}).
  skip. progress. smt(). smt().  wp. skip. progress.   smt(). smt().  smt().
  call (FF (ja - 2)  ).  smt(). wp. skip. progress.  
rcondt 1. skip. progress. simplify. 
call (jjj ia wa &m). sp. skip. progress.  smt(). smt().
rcondf 1. skip. progress. smt().
hoare.  call (_:true).  wp.  skip. progress. smt().
qed.



local lemma whp_cap_fin_int_sum_D &m ia pa M (ea : int) ra wa :
   Pr[ W1(A,D).run((pa,ia,1,ea,ra),wa) @ &m : 1 < W.c <= ea + 1  /\ M res ] = 
    big predT
      (fun i => Pr[ W1(A,D).run((pa,ia,1,ea,ra),wa) @ &m : W.c = i /\ M res ])
      (range 2 (ea + 2)).
progress.
pose f := fun (x : glob CAW) => x.`1.
have ->: Pr[ W1(A,D).run((pa,ia,1,ea,ra),wa) @ &m : 1 < W.c <= ea + 1 /\ M res ]
  = Pr[ CAW.run((pa,ia,1,ea,ra),wa) @ &m : 2 <= f (glob CAW) <= ea + 1  /\ M res ].
byequiv (_: ={arg, glob A, glob W} ==> ={res, glob W}). proc.
inline*. sp.  wp. 
progress.
seq 2 2 : (r{1} = r0{2} /\ w{1} = w0{2} /\ a{1}.`2 = a0{2}.`2 /\ ={glob A, glob W}). sim.
call whp_axp. skip. progress. smt(). auto. 
smt().
rewrite (pr_interval_to_sum_lemma CAW &m ((pa, ia, 1, ea, ra),wa) f (fun _ x _ => M x)).
simplify.
have <-:  (fun (i : int) => Pr[W1(A,D).run((pa, ia, 1, ea, ra),wa) @ &m : W.c = i /\ M res])
 = (fun (i : int) =>
     Pr[CAW.run((pa, ia, 1, ea, ra),wa) @ &m : f ( (glob CAW)) = i /\ M res]).
apply fun_ext. move => x.
byequiv (_: ={arg, glob A, glob W} ==> ={res, glob W}). proc.
inline*.  wp.  sp.
seq 2 2 : (r{1} = r0{2} /\ w{1} = w0{2} /\ a{1}.`2 = a0{2}.`2 /\ ={glob A, glob W}). sim.
call whp_axp. skip. progress. smt(). auto. 
smt().
auto. 
qed.


lemma whp_cap_fin_int pa ia (ea : int) ra :
  pa ra = false => 1 <= ea =>
   phoare[ W(A).whp : arg = (pa,ia,1,ea,ra) ==> 1 < W.c <= ea + 1 ] = 1%r.
progress. proc. sp.
unroll 1.
rcondt 1. skip. smt().
seq 2 : (W.c = 2 /\ (p, i, s, e) = (pa, ia, 1, ea)).
wp. call (_: true ==> true). auto.
skip. auto.
wp. call (_: true ==> true). apply A_ll.
skip. progress.
while (1 < W.c && W.c <= e + 1) (e + 1 - W.c).
progress. 
wp. call (_: true ==> true). apply A_ll.
skip. progress;smt(). skip. progress;smt().
hoare. simplify.
wp. call (_: true ==> true). auto. skip. auto. auto. 
qed.


local lemma whp_cap_fin_int_D &m pa ia (ea : int) ra wa:
  pa ra = false => 1 <= ea =>
   Pr[ W1(A,D).run((pa,ia,1,ea,ra),wa) @ &m : 1 < W.c <= ea + 1 ] = 1%r.
progress. byphoare (_: arg = ((pa, ia, 1, ea, ra),wa) ==> _).
proc.  call (_:true ==> true). apply D_ll. 
call (whp_cap_fin_int pa ia ea ra). skip. auto. auto. auto.
qed.


local lemma whp_cap_fin_sum' &m  ia (ea : int) r wa :
  MyPred r = false =>
  1 <= ea =>
  Pr[ W1(A,D).run((MyPred,ia,1,ea,r),wa) @ &m : MyPred res.`2 /\ res.`1 ]  
     = big predT
        (fun i => (Pr[ A.run(ia) @ &m : !MyPred res ] ^ (i - 2)) 
          * Pr[ W0(A,D).run(ia,wa) @ &m : MyPred res.`2 /\ res.`1 ]  )
        (range 2 (ea + 2)). 
proof. progress.
have ->: Pr[ W1(A,D).run((MyPred,ia,1,ea,r),wa) @ &m : MyPred res.`2 /\ res.`1 ]  
 = Pr[ W1(A,D).run((MyPred,ia,1,ea,r),wa) @ &m : (1 < W.c <= ea + 1) 
        /\ MyPred res.`2 /\ res.`1 ].
rewrite Pr[mu_split (1 < W.c && W.c <= ea + 1)].
  have ->: Pr[W1(A,D).run((MyPred, ia, 1, ea, r),wa) @ &m :
   (MyPred res.`2 /\ res.`1) /\ ! (1 < W.c && W.c <= ea + 1)] = 0%r.
   have : Pr[W1(A,D).run((MyPred, ia, 1, ea, r),wa) @ &m : ! (1 < W.c && W.c <= ea + 1)] = 0%r.
    have f3 : Pr[W1(A,D).run((MyPred, ia, 1, ea, r),wa) @ &m : (1 < W.c && W.c <= ea + 1)] = 1%r. rewrite (whp_cap_fin_int_D &m). auto.
  auto.
    have f2 : 1%r = Pr[W1(A,D).run((MyPred, ia, 1, ea, r),wa) @ &m : ! (1 < W.c && W.c <= ea + 1)] + Pr[W1(A,D).run((MyPred, ia, 1, ea, r),wa) @ &m : (1 < W.c && W.c <= ea + 1)]. 
    have  <- : Pr[W1(A,D).run((MyPred, ia, 1, ea, r),wa) @ &m : true ] = 1%r.
    have : Pr[W1(A, D).run((MyPred, ia, 1, ea, r), wa) @ &m : true] >= Pr[ W1(A,D).run((MyPred,ia,1,ea,r),wa) @ &m : 1 < W.c <= ea + 1 ].
    rewrite Pr[mu_sub]. auto. auto.
    rewrite whp_cap_fin_int_D. auto. auto. 
    have : Pr[W1(A, D).run((MyPred, ia, 1, ea, r), wa) @ &m : true] <= 1%r. rewrite Pr[mu_le1]. auto. smt().
   rewrite Pr[mu_split (1 < W.c && W.c <= ea + 1)]. simplify.
   smt(). auto. smt(@Distr). smt(@Distr). smt().
rewrite big_int_cond.
rewrite (whp_cap_fin_int_sum_D &m ia MyPred (fun x => MyPred (snd x) /\   fst x) ea r).
simplify.
rewrite big_int_cond.
apply eq_big. auto.
progress.
rewrite (whp_cap_fin &m). auto. smt().
auto.
auto.
qed.


local lemma whp_cap_fin_sum'' &m  ia (ea : int) r wa:
  MyPred r = false =>
  1 <= ea =>
   Pr[ W1(A,D).run((MyPred,ia,1,ea,r),wa) @ &m : MyPred res.`2 /\ res.`1 ]  
      = big predT
         (fun i => (Pr[ A.run(ia) @ &m : !MyPred res ] ^ i) 
           * Pr[ W0(A,D).run(ia,wa) @ &m : MyPred res.`2 /\ res.`1 ])
         (range 0 ea). 
proof. progress.
rewrite (whp_cap_fin_sum' &m);auto.
rewrite (big_reindex (fun (i : int) =>
     Pr[A.run(ia) @ &m : ! MyPred res] ^ i * Pr[W0(A,D).run(ia,wa) @ &m : MyPred res.`2 /\  res.`1]) 2 ea). auto.
qed.



lemma whp_cap_fin_sum &m ia (ea : int) r wa :
  MyPred r = false =>
  Pr[ W1(A,D).run((MyPred,ia,1,ea,r),wa) @ &m : MyPred res.`2 /\ res.`1 ]  
     = big predT
        (fun i => (Pr[ A.run(ia) @ &m : !MyPred res ] ^ i) 
          * Pr[ W0(A,D).run(ia,wa) @ &m : MyPred res.`2 /\ res.`1 ])
        (range 0 ea). 
proof.
case (1 <= ea).
progress. rewrite (whp_cap_fin_sum'' &m);auto.
progress.
have ->: bigi predT
  (fun (i : int) =>
     Pr[A.run(ia) @ &m : ! MyPred res] ^ i * Pr[W0(A,D).run(ia,wa) @ &m : MyPred res.`2 /\ res.`1])
  0 ea = 0%r.
smt(range_geq).
byphoare (_: arg = ((MyPred, ia, 1, ea, r),wa) ==> _).
hoare.
conseq (_: _ ==> ! MyPred res.`2). smt().
proc. sp. simplify. inline W1(A,D).M.whp. sp.
rcondf 1. skip. smt(). call (_: true ==> true). auto. wp. skip. smt(). auto. auto.
qed.



end section.
  

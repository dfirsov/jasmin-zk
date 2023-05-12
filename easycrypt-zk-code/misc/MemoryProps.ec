require import AllCore Distr DBool AuxResults.

require import RandomFacts RealSeries List.
require import Reflection ReflectionComp.

type at2, at1.

clone import ReflComp with type at1 <- at1,
                           type at2 <- at2,
                           type rt1 <- unit,
                           type rt2 <- bool.

                           
section.

declare module A <: RewEx1Ex2.
declare axiom A_run_ll : islossless A.ex1.    



local lemma unit_rule x : x = tt.
elim x. auto. qed.

local lemma prob_refl_app &m p :   
    exists (D1 : at1 -> (glob A) -> (unit * (glob A)) distr)
      (D2 : at2 -> unit * (glob A) -> (glob A) distr),
      (forall &m (M : unit * (glob A) -> bool) i1,
         mu (D1 i1 (glob A){m}) M = Pr[A.ex1(i1) @ &m : M (res, (glob A))]) /\
      (forall &m (M : (glob A) -> bool) (r1 : unit) i2,
         mu (D2 i2 (r1, (glob A){m})) M =
         Pr[A.ex2(i2, r1) @ &m : M (glob A)]) /\
      (forall &m (M : (glob A) -> bool)  i1 i2,
        mu ((dlet (D1 i1 (glob A){m}) (D2 i2))) M =
        Pr[RCR(A).main(i1, i2) @ &m : M (glob A)]) 
   /\ forall (M :  (glob A) -> bool) i1 i2, 
       p < Pr[ RCR(A).main(i1,i2) @ &m : M (glob A) ]  =>
       0%r <= p =>
   exists g, 0%r < mu1 (D1 i1 (glob A){m}) (tt,g)  /\ mu (D2 i2 ((tt,g))) M > p.
proof.  elim (refl_comp_simple A). progress.
exists D1 D2. progress.
pose g0 := (glob A){m}.
case (exists (g : (glob A)),
  0%r < mu1 (D1 i1 g0) (tt, g) /\ p < mu (D2 i2 (tt, g)) M).
auto.
move => G.
have: (forall (g : (glob A)),
     ! (0%r < mu1 (D1 i1 g0) (tt, g) /\ p < mu (D2 i2 (tt, g)) M)).
smt().
clear G.
move => G.
have q : forall (g : glob A),  mu1 (D1 i1 g0) (tt,g) > 0%r => mu (D2 i2 (tt,g)) M <= p .
smt().
have q2 : exists g, 0%r < mu1 (D1 i1 g0) (tt, g).
case (exists (g : (glob A)), 0%r < mu1 (D1 i1 g0) (tt, g)). auto.
move => q21.
have q22  : forall (g : (glob A)), 0%r = mu1 (D1 i1 g0) (tt, g).
smt(@Distr). clear q21.
have : Pr[RCR(A).main(i1, i2) @ &m : true ] = 0%r.
rewrite -  (H1 &m predT). 
rewrite dlet_mu_main. 
apply sum0_eq. progress. 
 have -> : x = (tt, x.`2). 
 rewrite - (unit_rule x.`1). smt().
rewrite - q22. smt(). smt(@Distr).
elim q2. move => g gp.
have : mu (dlet (D1 i1 (glob A){m}) (D2 i2)) M <= p.
rewrite  dlet_mu_main.
rewrite (sum_split _ (pred1 (tt, g))). 
apply (summable_mu1_wght ((D1 i1 (glob A){m})) (fun x => mu (D2 i2 x) M)   _) .
smt(@Distr).
simplify.
have -> : sum
  (fun (x : unit * (glob A)) =>
     if  pred1 (tt, g) x then mu1 (D1 i1 (glob A){m}) x * mu (D2 i2 x) M
     else 0%r) = mu1 (D1 i1 (glob A){m}) (tt,g) * mu (D2 i2 (tt,g)) M.
  have ->: (fun (x : unit * (glob A)) =>
     if  pred1 (tt, g) x then mu1 (D1 i1 (glob A){m}) x * mu (D2 i2 x) M
     else 0%r) = (fun (x : unit * (glob A)) => mu1 (D1 i1 (glob A){m}) (tt,g) * mu (D2 i2 (tt,g)) M *
     if  pred1 (tt, g) x then (mu1 (duniform [(tt,g)]) x)
     else 0%r).
apply fun_ext. move => x.  
case (pred1 (tt, g) x). simplify. progress.
rewrite H4. 
have -> : mu1 (duniform [(tt, g)]) (tt, g) = 1%r. rewrite - H4. 
smt(duniform1E_uniq). 
smt().
smt().
rewrite sumZ. 
rewrite - muE. progress.
have ->: mu1 (duniform [(tt, g)]) (tt, g) = 1%r. smt(@Distr). smt().
have zzz : sum
  (fun (x : unit * (glob A)) =>
     if ! pred1 (tt, g) x then mu1 (D1 i1 (glob A){m}) x * mu (D2 i2 x) M
     else 0%r) <= sum
  (fun (x : unit * (glob A)) =>
     if ! pred1 (tt, g) x then mu1 (D1 i1 (glob A){m}) x * p
     else 0%r).
apply ler_sum. progress. 
case (pred1 (tt, g) x). simplify. auto. simplify. progress.
have ->: x = (tt,x.`2). 
 rewrite - (unit_rule x.`1). smt().
case (mu1 (D1 i1 (glob A){m}) (tt, x.`2) = 0%r). 
smt().
progress.  
have jk : forall (a b c : real), a >= 0%r => b <= c => a * b <= a * c. smt().
apply jk. smt(@Distr). apply q. smt(@Distr).
have ->: (fun (x : unit * (glob A)) =>
     if ! pred1 (tt, g) x then mu1 (D1 i1 (glob A){m}) x * mu (D2 i2 x) M
     else 0%r) = (fun (x : unit * (glob A)) => mu1 (D1 i1 (glob A){m}) x * 
     if ! pred1 (tt, g) x then mu (D2 i2 x) M
     else 0%r).
apply fun_ext. move => x. smt().
apply summable_mu1_wght. progress. smt(@Distr). smt(@Distr).
have -> : (fun (x : unit * (glob A)) =>
     if ! pred1 (tt, g) x then mu1 (D1 i1 (glob A){m}) x * p else 0%r)
 = (fun (x : unit * (glob A)) => p *
     if ! pred1 (tt, g) x then mu1 (D1 i1 (glob A){m}) x else 0%r).
apply fun_ext. move => x. smt().
apply summableZ.
have ->: (fun (x : unit * (glob A)) =>
     if ! pred1 (tt, g) x then mu1 (D1 i1 (glob A){m}) x else 0%r)
 = (fun (x : unit * (glob A)) => mu1 (D1 i1 (glob A){m}) x *
     if ! pred1 (tt, g) x then 1%r else 0%r).
smt().
apply summable_mu1_wght. progress. smt(). smt().
have : mu1 (D1 i1 (glob A){m}) (tt, g) * mu (D2 i2 (tt, g)) M +
sum
  (fun (x : unit * (glob A)) =>
     if ! pred1 (tt, g) x then mu1 (D1 i1 (glob A){m}) x * p
     else 0%r) <= p.
apply (ler_trans1 _ (mu1 (D1 i1 (glob A){m}) (tt, g) * p +
sum
  (fun (x : unit * (glob A)) =>
     if ! pred1 (tt, g) x then mu1 (D1 i1 (glob A){m}) x * p else 0%r) )  p _ _).
clear zzz G H H0 H1. 
have : mu (D2 i2 (tt, g)) M
 <=  p.
smt(). smt().
have ->: mu1 (D1 i1 (glob A){m}) (tt, g) * p +
 sum
  (fun (x : unit * (glob A)) =>
     if ! pred1 (tt, g) x then mu1 (D1 i1 (glob A){m}) x * p else 0%r)
  = sum
  (fun (x : unit * (glob A)) =>
      mu1 (D1 i1 (glob A){m}) x * p).
rewrite (sumD1 (fun (x : unit * (glob A)) => mu1 (D1 i1 (glob A){m}) x * p) (tt,g)). 
have ->: (fun (x : unit * (glob A)) => mu1 (D1 i1 (glob A){m}) x * p) 
 = (fun (x : unit * (glob A)) => p * mu1 (D1 i1 (glob A){m}) x ).
smt().
apply summableZ.
apply summable_mu1.
simplify. auto.
have ->: sum (fun (x : unit * (glob A)) => mu1 (D1 i1 (glob A){m}) x * p)
 = p * sum (fun (x : unit * (glob A)) => mu1 (D1 i1 (glob A){m}) x).
rewrite -  sumZ.   simplify.
 have ->: (fun (x : unit * (glob A)) => mu1 (D1 i1 (glob A){m}) x * p) 
 = (fun (x : unit * (glob A)) => p * mu1 (D1 i1 (glob A){m}) x).
smt().
auto.
have ->: (fun (x : unit * (glob A)) => mu1 (D1 i1 (glob A){m}) x)
 = (fun (x : unit * (glob A)) => if predT x then mu1 (D1 i1 (glob A){m}) x else 0%r).
smt().
rewrite - muE.
have : 0%r <= weight (D1 i1 (glob A){m}) <= 1%r. smt(@Distr).
pose w := weight (D1 i1 (glob A){m}) .
progress. clear zzz gp g q G g0 H1 H0 H. smt().
 smt(). rewrite H1. smt().
qed.


lemma exists_mem_init_run_glob &m M i1 i2 p: 
       p < Pr[ RCR(A).main(i1,i2) @ &m : M (glob A) ] 
   => 0%r <= p
   => exists &n, p < Pr[ A.ex2(i2, tt) @ &n  : M (glob A)] .
elim (prob_refl_app &m p). progress.
elim (H2 M i1 i2 _ _);auto. progress.
have f1 : Pr[A.ex1(i1) @ &m : glob A = g] > 0%r.
have f2 : mu (D1 i1 (glob A){m}) (fun x => snd x = g)  = Pr[A.ex1(i1) @ &m : (glob A) = g].
rewrite (H &m). auto. rewrite - f2. 
have ->: (fun (x : unit * (glob A)) => x.`2 = g) = pred1 (tt,g). apply fun_ext. 
move => x. simplify.
 rewrite - (unit_rule x.`1).
smt(). apply H5.
have f3: exists &n, g = (glob A){n}.
  have  f31: Pr[A.ex1(i1) @ &m : (glob A) = g /\ (exists &n, (glob A) = (glob A){n}) ] = Pr[A.ex1(i1) @ &m : (glob A) = g].
  have <- : Pr[A.ex1(i1) @ &m : (glob A) = g] = Pr[A.ex1(i1) @ &m : (glob A) = g /\ exists &n, (glob A) = (glob A){n}].
  rewrite Pr[mu_split exists &n, (glob A) = (glob A){n}].
  have : Pr[A.ex1(i1) @ &m : (glob A) = g /\ ! (exists &n, (glob A) = (glob A){n})] = 0%r. 
have ->: Pr[A.ex1(i1) @ &m : (glob A) = g /\ ! (exists &n, (glob A) = (glob A){n})]
 = Pr[A.ex1(i1) @ &m : false]. rewrite Pr[mu_eq]. smt(). auto.  rewrite Pr[mu_false]. auto.
smt(). auto.
  have f32 : Pr[A.ex1(i1) @ &m : (glob A) = g /\ exists &n, g = (glob A){n}] =
     Pr[A.ex1(i1) @ &m : (glob A) = g].
  rewrite - f31. rewrite Pr[mu_eq]. progress. auto.
  have f33 : Pr[A.ex1(i1) @ &m : exists &n, g = (glob A){n}] > 0%r.
         have f331 : Pr[A.ex1(i1) @ &m : (glob A) = g /\ exists &n, (glob A) = (glob A){n}] 
                         <= Pr[A.ex1(i1) @ &m : (glob A) = g]. rewrite Pr[mu_sub]. auto. auto.
case (exists &n, g = (glob A){n}). 
rewrite - (H &m  predT i1).  smt(@Distr).
move => ne.  rewrite Pr[mu_false]. simplify.
have c1 : Pr[A.ex1(i1) @ &m : (glob A) = g] = 0%r. rewrite - f32. 
  rewrite  ne. simplify. rewrite Pr[mu_false]. simplify. auto.
smt().
  clear f32 f31 f1    H2 H1 H0 H. 
  case (exists &n, g = (glob A){n}). auto.
  move => q. 
  have : 0%r < Pr[A.ex1(i1) @ &m : false]. rewrite - q. apply f33. rewrite Pr[mu_false]. auto.
elim f3. progress.
exists &n.
rewrite - (H0 &n M tt i2). auto.
qed.
end section.

section.

declare module A <: RewEx1Ex2.
declare axiom A_run_ll : islossless A.ex1.    

local module A' = {
  var r : bool
  proc ex1 = A.ex1
  proc ex2(x:at2*unit) = {
    r <@ A.ex2(x);
    return r;
  }
}.

lemma exists_mem_init_run_res &m M i1 i2 p: 
        0%r <= p =>
       p < Pr[ RCR(A).main(i1,i2) @ &m : M res.`2 ] 
   => exists &n, p < Pr[ A.ex2(i2, tt) @ &n  : M res] .
move => j.
have -> : Pr[ RCR(A).main(i1,i2) @ &m : M res.`2 ]  = Pr[ RCR(A').main(i1,i2) @ &m : M A'.r ] .
byequiv. proc. inline*.
wp.  call (_:true). wp.  call (_:true). skip. auto. auto. auto.
progress.
have f : exists &n, p < Pr[ A'.ex2(i2, tt) @ &n  : M A'.r ] .
apply (exists_mem_init_run_glob A' _ &m (fun (x : glob A') => M x.`1) i1 i2 p). 
proc*. call A_run_ll. skip. auto. simplify.  apply H. auto. 
elim f. progress. exists &n.
have <-: Pr[A'.ex2(i2, tt) @ &n : M A'.r] = 
  Pr[A.ex2(i2, tt) @ &n : M res]. 
byequiv.  proc*. inline*. sp.  wp. call (_:true). skip. auto. auto.
auto. auto.
qed.

end section.
   

module type IR1R2 = {
  proc init(i1:at1) : unit
  proc run1(i2:at2) : bool
  proc run2(i2:at2) : bool
}.

module P(A : IR1R2) = {
  proc main1(i1:at1,i2:at2) = {
    var r : bool;
    A.init(i1);
    r <@ A.run1(i2);
    return r;
  }

  proc main2(i1:at1,i2:at2) = {
    var r : bool;
    A.init(i1);
    r <@ A.run2(i2);
    return r;
  }

  proc init_main12(i1:at1,i2:at2) = {
   var b, r', r : bool;

   A.init(i1);
   b <$ {0,1};
   
   if(b){
     r <@ A.run1(i2);
   }else{
     r' <@ A.run2(i2);
     r  <- !r';
   }
   return r;
  }

  proc main12(i2:at2) = {
   var b, r', r : bool;
   b <$ {0,1};
   
   if(b){
     r <@ A.run1(i2);
   }else{
     r' <@ A.run2(i2);
     r  <- !r';
   }
   return r;
  }


}.


section.

declare module A <: IR1R2.

declare axiom A_init_ll : islossless A.init.
declare axiom A_run2_ll : islossless A.run2.

local op f (x : real) : real = 1%r/2%r * (1%r + x).
local op fop (x : real) : real = 2%r * x - 1%r.

local lemma f_pr1 (a b : real) : a <= b => f a <= f b.
smt().
qed.


local lemma f_pr2 (a b : real) : f a <= f b => a <= b.
smt().
qed.

local lemma f_pr3 (a  : real) : f (fop a) = a.
smt().
qed.

local lemma f_pr4 (a  : real) : fop (f a) = a.
smt().
qed.


local lemma f_pr5 (a b : real) : a <= b => fop a <= fop b.
smt().
qed.

local lemma f_pr6 (a b : real) : fop a <= fop b =>  a <= b.
smt().
qed.

local module A'' = {
  proc ex1(i1:at1) = { 
     A.init(i1);
  }

  proc ex2(x:at2*unit) = {
     var r;
     r <@ P(A).main12(x.`1)     ;
     return r;
  }
}.


local lemma d_b3 &m p M ii1 ii2 : p < Pr[ P(A).init_main12(ii1,ii2) @ &m : M res ] 
   => 0%r <= p
   => exists &n, p < Pr[ P(A).main12(ii2) @ &n : M  res ].
have ->: 
  Pr[ P(A).init_main12(ii1,ii2) @ &m : M res ]
  =  Pr[RCR(A'').main(ii1,ii2) @ &m : M res.`2 ] .
byequiv. proc. inline*. wp. simplify. inline A''.ex1.
sp.  seq 2 4 : (={glob A, b,i1} /\ i2{1} = i20{2}). rnd.  wp. call (_:true). skip.
progress. if. auto. call (_:true). skip.  auto.
wp.  call (_:true). skip.  auto. auto. auto. 
progress.
have : exists &n, p < Pr[ A''.ex2(ii2, tt) @ &n  : M res].
apply (exists_mem_init_run_res A'' _ &m M ii1 ii2 p). 
proc. call A_init_ll. skip. auto.
auto.  auto.
elim. progress.
exists &n. 
have ->: Pr[P(A).main12(ii2) @ &n : M res]
 = Pr[A''.ex2(ii2, tt) @ &n : M res].
byequiv. proc.  inline*. wp. sp. 
seq 1 1 : (={glob A, b,i2}). rnd. skip. auto.
 if. auto. call (_:true). skip.  auto.
wp.  call (_:true). skip.  auto. auto. auto. 
progress.
qed.


local clone import Splitcases as SC with type argt <- at1*at2.

local module T = {
  proc work(i1i2:at1*at2, b:bool) = {
   var r', r : bool;

   A.init(i1i2.`1);   
   if(b){
     r <@ A.run1(i1i2.`2);
   }else{
     r' <@ A.run2(i1i2.`2);
     r  <- !r';
   }
   return r;
  }
}.

local module T2 = {
  proc work(i1i2:at1*at2, b:bool) = {
   var r', r : bool;

   if(b){
     r <@ A.run1(i1i2.`2);
   }else{
     r' <@ A.run2(i1i2.`2);
     r  <- !r';
   }
   return r;
  }
}.

local module W = MeansWithParameter.Rand.


local lemma d_b1 ii1 ii2 &m : Pr[ P(A).init_main12(ii1,ii2) @ &m : res ] 
  = f (Pr[ P(A).main1(ii1,ii2) @ &m : res ] - Pr[ P(A).main2(ii1,ii2) @ &m : res ]) .
have ->: Pr[ P(A).init_main12(ii1,ii2) @ &m : res ] 
 = Pr[ W(T).main(ii1,ii2) @ &m : res.`2 ].
byequiv (_: ={glob A, arg}  ==> _). proc. inline*. swap {1} 2 -1. simplify.
seq 2 4 :( ={b,glob A} /\ (i1,i2){1} = i1i2{2} ).  call (_:true). 
wp.  rnd. skip. progress. (* rewrite /{0,1}. smt(eq_duniformP). smt(eq_duniformP). *)
if. auto. wp. call (_:true). skip. auto.
wp. call (_:true). skip. auto. auto. auto.
rewrite (splitcases T).
have ->: Pr[T.work((ii1,ii2), false) @ &m : res] 
 = Pr[ P(A).main2(ii1,ii2) @ &m : !res ].
byequiv. proc. rcondf {1} 2. progress. call (_:true).
skip. smt().
wp.   sim.  call (_:true). call (_:true).  skip. auto. auto. auto.
have ->: Pr[T.work((ii1,ii2), true) @ &m : res] 
 = Pr[ P(A).main1(ii1,ii2) @ &m : res ].
byequiv. proc. rcondt {1} 2. progress. call (_:true).
skip. smt().
wp.
call (_:true). call (_:true).  skip. auto. auto. auto.
rewrite /f.
have -> : (1%r + (Pr[P(A).main1(ii1,ii2) @ &m : res] - Pr[P(A).main2(ii1,ii2) @ &m : res]))
 = Pr[P(A).main1(ii1,ii2) @ &m : res] + (1%r - Pr[P(A).main2(ii1,ii2) @ &m : res]).
smt().
have ->: (1%r - Pr[P(A).main2(ii1,ii2) @ &m : res]) = Pr[P(A).main2(ii1,ii2) @ &m : !res].
   have -> : 1%r = Pr[P(A).main2(ii1,ii2) @ &m : true].
 byphoare. proc. call A_run2_ll. call A_init_ll. skip.  auto. auto. auto.
rewrite Pr[mu_split res]. simplify. smt().
smt().
qed.


local lemma d_b2  (ii2 : at2)  &m : Pr[ P(A).main12(ii2) @ &m : res ] 
  = f (Pr[ A.run1(ii2) @ &m : res ] - Pr[ A.run2(ii2) @ &m : res ]) .
have ->: Pr[ P(A).main12(ii2) @ &m : res ]
 = Pr[ W(T2).main(witness,ii2) @ &m : res.`2 ].
byequiv (_: ={glob A} /\ arg{1} = arg.`2{2} ==> _). proc. inline*. 
seq 1 3 : (={glob A} /\ b{1} = b{2} /\ i1i2.`2{2} = i2{1}).
wp. 
rnd. skip. progress. (* smt(eq_duniformP). smt(eq_duniformP). wp. *)
if. auto. wp. call (_:true). skip. auto.
wp. call (_:true). skip. auto. auto. auto.
rewrite (splitcases T2).
have ->: Pr[T2.work((witness,ii2), false) @ &m : res]
 = Pr[ A.run2(ii2) @ &m : !res ].
byequiv. proc*. inline*. rcondf {1} 3. progress. wp.
skip.  smt().
wp.   sim.  
call (_:true).  wp.  skip. progress. auto. auto.
have ->: Pr[T2.work((witness,ii2),true) @ &m : res]
 = Pr[ A.run1(ii2) @ &m : res ].
byequiv. proc*. inline*. rcondt {1} 3. progress. wp.
skip.  smt().
wp. call (_:true). wp. skip. auto. auto. auto.
rewrite /f.
have -> : (1%r + (Pr[A.run1(ii2) @ &m : res] - Pr[A.run2(ii2) @ &m : res]))
 = Pr[A.run1(ii2) @ &m : res] + (1%r - Pr[A.run2(ii2) @ &m : res]).
smt().
have ->: (1%r - Pr[A.run2(ii2) @ &m : res]) = Pr[A.run2(ii2) @ &m : !res].
   have -> : 1%r = Pr[A.run2(ii2) @ &m : true].
 byphoare.  conseq A_run2_ll.   auto. auto.
rewrite Pr[mu_split res]. simplify. smt().
smt().
qed.


lemma exists_mem_diff ii1 ii2 &m p: 
       0%r <= p =>
       p < Pr[ P(A).main1(ii1,ii2) @ &m : res ]  - 
               Pr[ P(A).main2(ii1,ii2) @ &m : res ]
   => exists &n, p < Pr[ A.run1(ii2) @ &n : res ] - Pr[ A.run2(ii2) @ &n : res ].
progress.
have f1 : Pr[P(A).main1(ii1,ii2) @ &m : res] - Pr[P(A).main2(ii1,ii2) @ &m : res]
  = fop (Pr[ P(A).init_main12(ii1,ii2) @ &m : res ] ).
rewrite d_b1. smt().
have f2 : p < fop Pr[P(A).init_main12(ii1,ii2) @ &m : res].
smt().
have f3 : f p < Pr[P(A).init_main12(ii1,ii2) @ &m : res]. smt().
have f4 : exists &n,  f p < Pr[ P(A).main12(ii2) @ &n : res ].
apply (d_b3  &m  (f p) (fun x => x) ii1 ii2). auto.
smt(). elim f4. progress.
exists &n.
smt(d_b2).
qed.
   
end section.

section.

declare module A <: IR1R2.

declare axiom A_init_ll1 : islossless A.init.
declare axiom A_run2_ll1 : islossless A.run2.
declare axiom A_run1_ll1 : islossless A.run1.


local module A' = {
  proc init = A.init
  
  proc run1(i2 : at2) : bool  = {
     var r;
     r <@ A.run2(i2);
     return r;
  }
  
  proc run2(i2 : at2) : bool  = {
     var r;
     r <@ A.run1(i2);
     return r;
  }
}.


lemma exists_mem_abs_diff ii1 ii2 &m p: 
       0%r <= p =>
       p <  `|Pr[ P(A).main1(ii1,ii2) @ &m : res ]  - 
               Pr[ P(A).main2(ii1,ii2) @ &m : res ]|
   => exists &n, p < `|Pr[ A.run1(ii2) @ &n : res ] - Pr[ A.run2(ii2) @ &n : res ]|.
proof. 
case (Pr[ P(A).main1(ii1,ii2) @ &m : res ] >
               Pr[ P(A).main2(ii1,ii2) @ &m : res ]).
progress.
have f : exists &n, p < Pr[ A.run1(ii2) @ &n : res ] - Pr[ A.run2(ii2) @ &n : res ]. apply (exists_mem_diff A _ _ ii1 ii2 &m). 
apply A_init_ll1. apply A_run2_ll1.
auto.
smt(). smt().
have ->: Pr[P(A).main2(ii1, ii2) @ &m : res]
 = Pr[P(A').main1(ii1, ii2) @ &m : res]. byequiv.
proc. inline*. wp.  sim. auto. auto.
have ->: Pr[P(A).main1(ii1, ii2) @ &m : res]
 = Pr[P(A').main2(ii1, ii2) @ &m : res]. byequiv.
proc. inline*. wp.  sim. auto. auto.
progress.
have g : Pr[P(A').main2(ii1, ii2) @ &m : res] <= Pr[P(A').main1(ii1, ii2) @ &m : res]. smt().
have f : exists &n, p < Pr[ A'.run1(ii2) @ &n : res ] - Pr[ A'.run2(ii2) @ &n : res ]. apply (exists_mem_diff A' _ _ ii1 ii2 &m). 
apply A_init_ll1. 
proc.  call A_run1_ll1. skip. auto. 
auto. smt().
elim f. progress. exists &n.
have ->: Pr[A.run1(ii2) @ &n : res]
 = Pr[A'.run2(ii2) @ &n : res]. byequiv.
proc*. inline*. sim. auto. auto.
have ->: Pr[A.run2(ii2) @ &n : res]
 = Pr[A'.run1(ii2) @ &n : res]. byequiv.
proc*. inline*. sim. auto. auto.
smt().
qed.    
         
end section.

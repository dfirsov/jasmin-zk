pragma Goals:printall.
require import AllCore.
require import RewBasics.
require import Distr.
require import AllCore List Binomial.
require import Ring StdRing StdOrder StdBigop Discrete RealSeq RealSeries RealLub.
(*---*) import IterOp Bigint Bigreal Bigreal.BRA.
(*---*) import IntOrder RealOrder RField.
require import Finite.
require (*--*) FinType.

require import RewBasics.
require Averaging.
require Reflection.

theory ReflComp. 

type at1, at2, rt1, rt2.

module type RewEx1Ex2 = {
  proc ex1(x1 : at1) : rt1
  proc ex2(x2 : at2, r1 : rt1) : rt2
}.


module RCR(A : RewEx1Ex2)  = {
  proc main(i1 : at1, i2:at2) = {
     var r, r1;
     r1 <@ A.ex1(i1);    
     r  <@ A.ex2(i2,r1);
     return (r1,r);
  }
}.

section.

declare module A <: RewEx1Ex2.


clone import Averaging.Avg with type at <- rt1 * (glob A),
                                type rt <- rt1 * (rt2 * (glob A)),
                                type at1 <- at1,
                                type at2 <- at2.


clone import Reflection.Refl as R_Exec1 with type at <-at1,
                                             type rt <- rt1.


clone import Reflection.Refl as R_Exec2 with type at <-at2 * rt1,
                                             type rt <- rt2.


local module Q = {
  var qg :  (at2 * rt1) -> (glob A) ->  (rt2 * glob A) distr
  
  proc egsd(d : (rt1 * glob A) distr) = {
     var sb;
     sb <$ d;
     return sb;
  }

  
  proc egs(d : (rt1 * glob A) distr, f : (glob A) -> sbits) = {
     var sb;
     sb <@ egsd(d);
    return sb;
  }


  proc sge(d : (rt2 * glob A) distr) = {
    var r;
    r <$ d;
    return r;
  }

  
 proc main_distr(d : at1 -> (rt1 * glob A) distr, 
                 q : (at2 * rt1) -> (glob A) -> (rt2 * glob A) distr, 
                 i1 : at1, i2 : at2, fa : (glob A) -> sbits) = {
    var ga, r;
    ga <@ egs(d i1, fa);
    r <@ sge(q (i2, ga.`1) ga.`2);
    return (ga.`1, r);
 } 

 
 proc main_distr_face(d : at1 -> (rt1 * glob A) distr,  
                      q : (at2 * rt1) -> (glob A) -> (rt2 * glob A) distr, 
                      i1 : at1, i2 : at2) = {
    var ga, r;
    ga <$ d i1;
    r <$ q (i2, ga.`1) ga.`2 ;
    return (ga.`1, r);
 } 

 proc main(ga : rt1 * glob A, i2 : at2) = {
    var r;
    r <$ qg (i2, ga.`1) ga.`2 ;
    return (ga.`1, r);
 }
}.


local module Run_Exec1 = {
  proc main(a : at1) : rt1 = {
      var r;
      r <@ A.ex1(a);
      return r;
  }
}.


local module Run_Exec2 = {
  proc main(a : at2 * rt1) : rt2 = {
      var r;
      r <@ A.ex2(a);
      return r;
  }
}.


local lemma rewindable_A_pp : 
  exists (D : at1 -> (glob A) -> (rt1 * glob A) distr), 
  exists (Q : (at2 * rt1) -> (glob A) ->  (rt2 * glob A) distr),
  (forall M i1 &m, mu (D i1 (glob A){m} ) M = Pr[ A.ex1(i1) @ &m :  M (res, (glob A))]) /\
  (forall M r1 i2 &m, mu (Q (i2, r1) ((glob A){m}) ) (M r1) 
                    = Pr[ A.ex2(i2,r1) @ &m :  M r1 (res, glob A) ]).
proof.  
elim (R_Exec1.reflection Run_Exec1). progress. exists (fun x y => D y x). 
elim (R_Exec2.reflection Run_Exec2). move => Q. progress. exists (fun x y => Q y x). 
progress. rewrite H. 
byequiv. proc*. inline*. sp. wp.
call (_:true). skip. progress. auto. auto.
rewrite H0. byequiv. proc*. inline*. sp. wp. call(_:true). skip. progress. auto. auto.
qed.
 

local lemma locavg :  
 forall &m (P : rt1 * (rt2 * (glob A)) -> bool) d (i1 : at1) i2,
       Pr[WorkAvg(Q).main(d i1,i2) @ &m : P res.`1 ] =
       sum (fun (r : rt1 * (glob A)) => mu1 (d i1) r * Pr[Q.main(r,i2) @ &m : P res]).
proof.  progress.
apply (averaging Q).
qed.


local lemma dlet1lem' &m : forall d i1 i2 q M, 
  q = Q.qg{m} =>
  Pr[ Q.main_distr_face(d, q,i1,i2) @ &m : M res ] 
= Pr[WorkAvg(Q).main(d i1,i2) @ &m : M res.`1 ].
proof. move => d i1 i2 q M e. byequiv.
proc.  inline*. wp. rnd. wp. rnd. wp. skip. progress. smt(). smt(). smt(). smt().
qed.


local lemma dlet1lem &m : forall d q M i1 i2,  q = Q.qg{m} => 
 Pr[ Q.main_distr_face(d, q, i1, i2) @ &m : M res ] 
 = sum (fun (r : (rt1 * glob A)) => mu1 (d i1) r * Pr[Q.main(r,i2) @ &m : M res]).
progress. rewrite( dlet1lem' &m). auto. 
apply (locavg &m M d i1).
qed.  


local lemma rewindable_A_nr1 : 
   exists (D : at1 -> (glob A) ->  (rt1 * glob A) distr), 
   exists (Q : (at2 * rt1) -> (glob A) ->  (rt2 * glob A) distr),
  (forall M i1 &m, mu (D i1 (glob A){m}) M = Pr[ A.ex1(i1) @ &m :  M (res, (glob A))]) /\
  (forall M r1 i2 &m, mu (Q (i2,r1) (glob A){m}) (M r1) 
                    = Pr[ A.ex2(i2,r1) @ &m :  M r1 ((res, glob A))]) /\
  equiv [ A.ex1 ~ Q.egsd :  arg{2} = (D arg{1} (glob A){1}) 
        ==> (glob A){1} = res{2}.`2 /\ res{1} = res{2}.`1 ].
elim rewindable_A_pp.
progress. exists D Q. progress. 
bypr (res,glob A){1} (res){2}. smt(). 
move => &1 &2. move => a p1. 
rewrite - (H (fun (x : rt1 * (glob A) ) => x = a)). 
byphoare (_: arg = D x1{1} (glob A){1} ==> _).
proc. rnd.  skip. progress. smt(). auto. 
qed.


local lemma rewindable_A_nr2 : 
   exists (D : at1 -> (glob A) ->  (rt1 * glob A) distr), 
   exists (Q : (at2 * rt1) -> (glob A) ->  (rt2 * glob A) distr),
  (forall M i1 &m, mu (D i1 (glob A){m}) M = Pr[ A.ex1(i1) @ &m :  M (res, (glob A))]) /\
  (forall M r1 i2 &m, mu (Q (i2,r1) (glob A){m}) (M r1) 
                    = Pr[ A.ex2(i2,r1) @ &m : M r1 ((res, glob A))]) /\
  equiv [ A.ex1 ~ Q.egsd :  arg{2} = (D arg{1} (glob A){1} ) 
        ==> (glob A){1} = res{2}.`2 /\ res{1} = res{2}.`1 ] /\
  equiv [ A.ex1 ~ Q.egs :  arg.`1{2} = (D arg{1} (glob A){1}) 
        ==> (res, glob A){1} = (res){2} ].
elim rewindable_A_nr1.
progress. exists D Q. progress.
proc*. inline Q.egs. wp. sp.
seq 1 1 : ((r,glob A){1} = sb{2} ).
call H1. skip. auto.   smt().
conseq (_: exists ga, (ga) = sb{2} /\ (r,glob A){1} = sb{2}  ==> _). smt().
elim*. move => ga. skip. 
progress.
qed. 


local lemma rewindable_A_nr4 : 
   exists (D : at1 -> (glob A) ->  (rt1 * glob A) distr), 
   exists (Q : (at2 * rt1) -> (glob A) ->  (rt2 * glob A) distr),
  (forall M i1 &m, mu (D i1 (glob A){m}) M = Pr[ A.ex1(i1) @ &m :  M (res, (glob A))]) /\
  (forall M r1 i2 &m, mu (Q (i2,r1) (glob A){m}) (M r1) 
                    = Pr[ A.ex2(i2,r1) @ &m :  M r1 ((res, glob A))]) /\
  equiv [ A.ex1 ~ Q.egsd :  arg{2} = (D arg{1} (glob A){1} ) 
        ==> (glob A){1} = res{2}.`2 /\ res{1} = res{2}.`1 ] /\
  equiv [ A.ex1 ~ Q.egs :  arg.`1{2} = (D arg{1} (glob A){1}) 
        ==> (res, glob A){1} = (res){2} ] /\
  equiv [ A.ex2 ~ Q.sge :  arg{2} = (Q arg{1} (glob A){1} ) 
        ==> res{1} = res{2}.`1 /\ (res,glob A){1} = res{2} ].
elim rewindable_A_nr2.
progress. exists D Q. progress.
bypr (res{1}, (glob A){1}) (res{2}). smt().
move => &1 &2 a pr.
rewrite - (H0 (fun r x => x = a)). 
byphoare (_: arg = d{2} ==> _) . proc.
rnd. skip. smt(). auto. auto.
qed.


local lemma rewindable_A_nr5 : 
   exists (D : at1 -> (glob A) ->  (rt1 * glob A) distr), 
   exists (Q : (at2 * rt1) -> (glob A) ->  (rt2 * glob A) distr),
  (forall M i1 &m, mu (D i1 (glob A){m}) M = Pr[ A.ex1(i1) @ &m :  M (res, (glob A))]) /\
  (forall M r1 i2 &m, mu (Q (i2,r1) (glob A){m}) (M r1) 
                    = Pr[ A.ex2(i2,r1) @ &m :  M r1 ((res, glob A))]) /\
  equiv [ A.ex1 ~ Q.egsd :  arg{2} = (D arg{1} (glob A){1} ) 
        ==> (glob A){1} = res{2}.`2 /\ res{1} = res{2}.`1 ] /\
  equiv [ A.ex1 ~ Q.egs :  arg.`1{2} = (D arg{1} (glob A){1}) 
        ==> (res, glob A){1} = (res){2} ] /\
  equiv [ A.ex2 ~ Q.sge :  arg{2} = (Q arg{1} (glob A){1} ) 
        ==> res{1} = res{2}.`1 /\ (res,glob A){1} = res{2} ] /\
  equiv [ RCR(A).main ~ Q.main_distr : arg.`2{1} = arg.`4{2} /\ arg.`1{1} = arg.`3{2} 
        /\ ={glob A} /\ arg.`1{2} arg.`1{1} = (D arg.`1{1} (glob A){1} ) 
        /\ arg.`2{2} = Q ==> (res.`1,(res.`2,glob A)){1} = res{2} ].
elim rewindable_A_nr4.
progress. exists D Q. progress.
proc. call H3. call H2. skip. progress.   
qed.


local lemma rewindable_A_nr6 : 
   exists (D : at1 -> (glob A) ->  (rt1 * glob A) distr), 
   exists (Q : (at2 * rt1) -> (glob A) ->  (rt2 * glob A) distr),
  (forall M i1 &m, mu (D i1 (glob A){m}) M = Pr[ A.ex1(i1) @ &m :  M (res, (glob A))]) /\
  (forall M r1 i2 &m, mu (Q (i2,r1) (glob A){m}) (M r1) 
                    = Pr[ A.ex2(i2,r1) @ &m :  M r1 ((res, glob A))]) /\
  equiv [ A.ex1 ~ Q.egsd :  arg{2} = (D arg{1} (glob A){1} ) 
        ==> (glob A){1} = res{2}.`2 /\ res{1} = res{2}.`1 ] /\
  equiv [ A.ex1 ~ Q.egs :  arg.`1{2} = (D arg{1} (glob A){1}) 
        ==> (res, glob A){1} = (res){2} ] /\
  equiv [ A.ex2 ~ Q.sge :  arg{2} = (Q arg{1} (glob A){1} ) 
        ==> res{1} = res{2}.`1 /\ (res,glob A){1} = res{2} ] /\
  equiv [ RCR(A).main ~ Q.main_distr : arg.`2{1} = arg.`4{2} /\ arg.`1{1} = arg.`3{2} 
        /\ ={glob A} /\ arg.`1{2} arg.`1{1} = (D arg.`1{1} (glob A){1} ) 
        /\ arg.`2{2} = Q  ==>  (res.`1,(res.`2,glob A)){1} = res{2} ] /\
  equiv [ Q.main_distr ~ Q.main_distr_face : i1{1} = i1{2} /\ i2{1} = i2{2} 
        /\ d{1} = d{2} /\ q{1} = q{2}   ==> ={res} ].
elim rewindable_A_nr5.
progress. exists D Q. progress.
proc. inline*. sp. wp. rnd. wp.   rnd.  skip. progress. 
qed.


local lemma rewindable_A_nr7 : 
   exists (D : at1 -> (glob A) ->  (rt1 * glob A) distr), 
   exists (Q : (at2 * rt1) -> (glob A) ->  (rt2 * glob A) distr),
  (forall M i1 &m, mu (D i1 (glob A){m}) M = Pr[ A.ex1(i1) @ &m :  M (res, (glob A))]) /\
  (forall M r1 i2 &m, mu (Q (i2,r1) (glob A){m}) (M r1) 
                    = Pr[ A.ex2(i2,r1) @ &m :  M r1 ((res, glob A))]) /\
  equiv [ A.ex1 ~ Q.egsd :  arg{2} = (D arg{1} (glob A){1} ) 
        ==> (glob A){1} = res{2}.`2 /\ res{1} = res{2}.`1 ] /\
  equiv [ A.ex1 ~ Q.egs :  arg.`1{2} = (D arg{1} (glob A){1}) 
        ==> (res, glob A){1} = (res){2} ] /\
  equiv [ A.ex2 ~ Q.sge :  arg{2} = (Q arg{1} (glob A){1} ) 
        ==> res{1} = res{2}.`1 /\ (res,glob A){1} = res{2} ] /\
  equiv [ RCR(A).main ~ Q.main_distr : arg.`2{1} = arg.`4{2} /\ arg.`1{1} = arg.`3{2} 
        /\ ={glob A} /\ arg.`1{2} arg.`1{1} = (D arg.`1{1} (glob A){1} ) 
        /\ arg.`2{2} = Q  ==>  (res.`1,(res.`2,glob A)){1} = res{2} ] /\
  equiv [ Q.main_distr ~ Q.main_distr_face :      i1{1} = i1{2} /\ i2{1} = i2{2} 
        /\ d{1} = d{2} /\ q{1} = q{2}   ==> ={res} ] /\
  equiv [ RCR(A).main ~ Q.main_distr_face : ={glob A,i1,i2} 
        /\ arg.`1{2} = (fun x => D  x (glob A){1}) 
        /\ (D arg{1}.`1 (glob A){2}) = d{2} arg{1}.`1 /\ Q = q{2} 
        ==> res{1} = (res{2}.`1, res{2}.`2.`1) /\ (glob A){1} = res{2}.`2.`2 ].
proof. elim rewindable_A_nr6.
progress. exists D Q. progress.
transitivity Q.main_distr 
 (arg.`2{1} = arg.`4{2} /\ arg.`1{1} = arg.`3{2} /\ ={glob A, i1} /\ arg.`1{2} = (fun x => D  x (glob A){1})   /\ arg.`2{2} = Q  ==> 
    res{1} = (res{2}.`1, res{2}.`2.`1) /\ (glob A){1} = res{2}.`2.`2) 
  (={d, q,i1,i2} ==> ={res}).  
move => &1 &2 p.  exists (glob A){1}. exists ((fun x => D x (glob A){2}), Q, arg{1}.`1, arg{1}.`2, witness). progress. 
smt(). smt(). smt(). smt(). smt(). auto. conseq H4.
progress. smt(). smt(). conseq H5. auto. 
qed.

local lemma rewindable_A_nr8 : 
   exists (D : at1 -> (glob A) ->  (rt1 * glob A) distr), 
   exists (Q : (at2 * rt1) -> (glob A) ->  (rt2 * glob A) distr),
  (forall M i1 &m, mu (D i1 (glob A){m}) M = Pr[ A.ex1(i1) @ &m :  M (res, (glob A))]) /\
  (forall M r1 i2 &m, mu (Q (i2,r1) (glob A){m}) (M r1) 
                    = Pr[ A.ex2(i2,r1) @ &m :  M r1 ((res, glob A))]) /\
  equiv [ A.ex1 ~ Q.egsd :  arg{2} = (D arg{1} (glob A){1} ) 
        ==> (glob A){1} = res{2}.`2 /\ res{1} = res{2}.`1 ] /\
  equiv [ A.ex1 ~ Q.egs :  arg.`1{2} = (D arg{1} (glob A){1}) 
        ==> (res, glob A){1} = (res){2} ] /\
  equiv [ A.ex2 ~ Q.sge :  arg{2} = (Q arg{1} (glob A){1} ) 
        ==> res{1} = res{2}.`1 /\ (res,glob A){1} = res{2} ] /\
  equiv [ RCR(A).main ~ Q.main_distr : arg.`2{1} = arg.`4{2} /\ arg.`1{1} = arg.`3{2} 
        /\ ={glob A} /\ arg.`1{2} arg.`1{1} = (D arg.`1{1} (glob A){1} ) 
        /\ arg.`2{2} = Q  ==>  (res.`1,(res.`2,glob A)){1} = res{2} ] /\
  equiv [ Q.main_distr ~ Q.main_distr_face :      i1{1} = i1{2} /\ i2{1} = i2{2} 
        /\ d{1} = d{2} /\ q{1} = q{2}   ==> ={res} ] /\
  equiv [ RCR(A).main ~ Q.main_distr_face : ={glob A,i1,i2} 
        /\ arg.`1{2} = (fun x => D  x (glob A){1}) 
        /\ (D arg{1}.`1 (glob A){2}) = d{2} arg{1}.`1 /\ Q = q{2} 
        ==> res{1} = (res{2}.`1, res{2}.`2.`1) /\ (glob A){1} = res{2}.`2.`2 ] /\
 (forall &m M i1 i2, Pr[ RCR(A).main(i1,i2) @ &m : M (res.`1,(res.`2 , glob A)) ]  
                   = Pr[ Q.main_distr_face(fun x => D x (glob A){m}, Q, i1,i2) 
                       @ &m : M res ]).
proof. elim rewindable_A_nr7.
progress. exists D Q. progress.
byequiv (_: ={glob A,i1,i2}  /\ (fun x => D x (glob A){2}) = d{2} /\ Q = q{2} ==> _). 
conseq H6. progress. progress. auto. smt(). smt(). progress. progress. auto. smt(). smt(). smt(). smt().
qed.




local lemma rewindable_A_nr9 : 
   exists (D : at1 -> (glob A) ->  (rt1 * glob A) distr), 
   exists (Q : (at2 * rt1) -> (glob A) ->  (rt2 * glob A) distr),
  (forall M i1 &m, mu (D i1 (glob A){m}) M = Pr[ A.ex1(i1) @ &m :  M (res, (glob A))]) /\
  (forall M r1 i2 &m, mu (Q (i2,r1) (glob A){m}) (M r1) 
                    = Pr[ A.ex2(i2,r1) @ &m : M r1 ((res, glob A))]) /\
  equiv [ A.ex1 ~ Q.egsd :  arg{2} = (D arg{1} (glob A){1} ) 
        ==> (glob A){1} = res{2}.`2 /\ res{1} = res{2}.`1 ] /\
  equiv [ A.ex1 ~ Q.egs :  arg.`1{2} = (D arg{1} (glob A){1}) 
        ==> (res, glob A){1} = (res){2} ] /\
  equiv [ A.ex2 ~ Q.sge :  arg{2} = (Q arg{1} (glob A){1} ) 
        ==> res{1} = res{2}.`1 /\ (res,glob A){1} = res{2} ] /\
  equiv [ RCR(A).main ~ Q.main_distr : arg.`2{1} = arg.`4{2} /\ arg.`1{1} = arg.`3{2}
        /\ ={glob A} /\ arg.`1{2} arg.`1{1} = (D arg.`1{1} (glob A){1} ) 
        /\ arg.`2{2} = Q  ==>  (res.`1,(res.`2,glob A)){1} = res{2} ] /\
  equiv [ Q.main_distr ~ Q.main_distr_face :      i1{1} = i1{2} /\ i2{1} = i2{2} 
        /\ d{1} = d{2} /\ q{1} = q{2}   ==> ={res} ] /\
  equiv [ RCR(A).main ~ Q.main_distr_face : ={glob A,i1,i2} 
        /\ arg.`1{2} = (fun x => D  x (glob A){1})  
        /\ (D arg{1}.`1 (glob A){2}) = d{2} arg{1}.`1 /\ Q = q{2}   
        ==> res{1} = (res{2}.`1, res{2}.`2.`1) /\ (glob A){1} = res{2}.`2.`2 ] /\
  (forall &m M i1 i2, Pr[ RCR(A).main(i1,i2) @ &m : M (res.`1,(res.`2 , glob A)) ]  
                    = Pr[ Q.main_distr_face(fun x => D x (glob A){m}, Q, i1,i2) 
                        @ &m : M res ]) /\
  (forall &m M i1 i2, Q.qg{m} = Q => 
          Pr[ Q.main_distr_face(fun x => D x (glob A){m}, Q,i1,i2) @ &m : M res ] 
       = sum (fun (r : (rt1 * glob A)) => 
                 mu1 (D i1 (glob A){m}) r * Pr[Q.main(r,i2) @ &m : M res])).
elim rewindable_A_nr8.
progress. exists D Q. progress.
apply (dlet1lem &m). auto.
qed.


require import RandomFacts.

local lemma rewindable_A_nr10 : 
   exists (D : at1 -> (glob A) ->  (rt1 * glob A) distr), 
   exists (Q : (at2 * rt1) -> (glob A) ->  (rt2 * glob A) distr),
  (forall M i1 &m, mu (D i1 (glob A){m}) M = Pr[ A.ex1(i1) @ &m :  M (res, (glob A))]) /\
  (forall M r1 i2 &m, mu (Q (i2,r1) (glob A){m}) (M r1) 
                    = Pr[ A.ex2(i2,r1) @ &m : M r1 ((res, glob A))]) /\
  equiv [ A.ex1 ~ Q.egsd :  arg{2} = (D arg{1} (glob A){1} ) 
        ==> (glob A){1} = res{2}.`2 /\ res{1} = res{2}.`1 ] /\
  equiv [ A.ex1 ~ Q.egs :  arg.`1{2} = (D arg{1} (glob A){1}) 
        ==> (res, glob A){1} = (res){2} ] /\
  equiv [ A.ex2 ~ Q.sge :  arg{2} = (Q arg{1} (glob A){1} ) 
        ==> res{1} = res{2}.`1 /\ (res,glob A){1} = res{2} ] /\
  equiv [ RCR(A).main ~ Q.main_distr : arg.`2{1} = arg.`4{2} /\ arg.`1{1} = arg.`3{2}
        /\ ={glob A} /\ arg.`1{2} arg.`1{1} = (D arg.`1{1} (glob A){1} ) 
        /\ arg.`2{2} = Q  ==>  (res.`1,(res.`2,glob A)){1} = res{2} ] /\
  equiv [ Q.main_distr ~ Q.main_distr_face :      i1{1} = i1{2} /\ i2{1} = i2{2} 
        /\ d{1} = d{2} /\ q{1} = q{2}   ==> ={res} ] /\
  equiv [ RCR(A).main ~ Q.main_distr_face : ={glob A,i1,i2} 
        /\ arg.`1{2} = (fun x => D  x (glob A){1})  
        /\ (D arg{1}.`1 (glob A){2}) = d{2} arg{1}.`1 /\ Q = q{2}   
        ==> res{1} = (res{2}.`1, res{2}.`2.`1) /\ (glob A){1} = res{2}.`2.`2 ] /\
  (forall &m M i1 i2, Pr[ RCR(A).main(i1,i2) @ &m : M (res.`1,(res.`2 , glob A)) ]  
                    = Pr[ Q.main_distr_face(fun x => D x (glob A){m}, Q, i1,i2) 
                        @ &m : M res ]) /\
  (forall &m M i1 i2, Q.qg{m} = Q => 
          Pr[ Q.main_distr_face(fun x => D x (glob A){m}, Q,i1,i2) @ &m : M res ] 
       = sum (fun (r : (rt1 * glob A)) => 
                 mu1 (D i1 (glob A){m}) r * Pr[Q.main(r,i2) @ &m : M res])) /\
  (forall &m M i1 i2, Q.qg{m} = Q => 
          Pr[ Q.main_distr_face(fun x => D x (glob A){m}, Q,i1,i2) @ &m : M res ] 
          = sum (fun (r : (rt1 * glob A)) => 
                   mu1 (D i1  (glob A){m}) r 
                 * mu (dmap (Q (i2, r.`1)  r.`2) 
                      (fun (x : (rt2 * (glob A))) => (r.`1,x))) M)).
proof. elim rewindable_A_nr9.
progress. exists D Q. progress.
rewrite (H8 &m). auto. 
have : forall &m r i2, Pr[ Q.main(r,i2) @ &m : M res ] 
        = mu (Q.qg{m} (i2,r.`1) r.`2) (fun (x : (rt2 * (glob A))) => M (r.`1, x)).
move => &m0 r i2'. byphoare (_: arg.`1 = r /\ arg.`2 = i2' /\ Q.qg = Q.qg{m0} ==> _). 
proc. rnd. skip. progress. auto. auto. 
move => fact. 
have : (fun (r : (rt1 * glob A)) => 
           mu1 (D i1 (glob A){m}) r * Pr[Q.main(r,i2) @ &m : M res]) = 
          (fun (r : (rt1 * glob A)) => 
        mu1 (D i1 (glob A){m}) r 
      * mu (dmap (Q.qg{m} (i2, r.`1)  r.`2) (fun (x : (rt2 * (glob A))) => (r.`1,x))) M).
apply fun_ext. move => r. rewrite fact. rewrite dmeq. auto.
move => ff. rewrite ff. clear ff. 
auto.
qed.


local lemma rewindable_A_nr11 : 
   exists (D : at1 -> (glob A) -> (rt1 * glob A) distr), 
   exists (Q : at2 -> (rt1 * glob A) ->  (rt2 * glob A) distr),
  (forall M i1 &m, mu (D i1 (glob A){m}) M = Pr[ A.ex1(i1) @ &m :  M (res, (glob A))]) /\
  (forall M r1 i2 &m, mu (Q i2 (r1 ,(glob A){m})) (M r1) 
                    = Pr[ A.ex2(i2,r1) @ &m :  M r1 ((res, glob A))]) /\
  forall &m M i1 i2, Q.qg{m} = (fun (ex2a1r : at2 * rt1) g 
       => Q ex2a1r.`1 (ex2a1r.`2, g)) => 
    Pr[ RCR(A).main(i1,i2) @ &m : M (res.`1,(res.`2 , glob A)) ] 
    = mu (dlet (D i1 (glob A){m}) (fun a => dmap (Q i2 a) (fun x => (a.`1, x)))) M.  
proof. elim rewindable_A_nr10.
progress. exists D  (fun x2 (r1g : rt1 * glob A) => Q (x2 , r1g.`1) r1g.`2). split. auto. split.   progress. simplify. 
move => &m M i1 i2 qg.  rewrite (H7 &m). rewrite (H9 &m). smt().
rewrite  (dlet_mu_main (D i1 (glob A){m}) 
            ((fun (a1 : at2) (a2 : (rt1 * glob A)) => 
                   dmap ((fun x2 (r1g : rt1 * glob A) => Q (x2 , r1g.`1) r1g.`2) a1 a2) 
                         (fun x => (a2.`1, x))) i2) M). auto. 
qed.


local module W = {
  proc main(Q : at2 * rt1 -> (glob A) -> (rt2 * (glob A)) distr) = {
     Q.qg <- Q;
  }
}.


local lemma ohj : forall Q &m, Pr[ W.main(Q) @ &m : exists &n, 
  (glob A){n} = (glob A){m} /\ Q.qg{n} = Q ] = 1%r. 
proof. move => Q &m. byphoare (_: arg = Q /\ (glob A) = (glob A){m} ==> _).
proc.  
seq 1 : (Q.qg = Q /\ Q = Q /\ (glob A) = (glob A){m}).  wp. skip. auto.
wp. skip. auto. 
skip. move => &hr e1. elim e1. move => e1 e2. 
exists &hr. split.
auto. rewrite - e1. 
auto. 
hoare. wp. skip. progress. auto.  auto. auto.
qed.


lemma reflectionComp_dmap : 
   exists (D : at1 -> (glob A) ->  (rt1 * glob A) distr), 
   exists (Q : at2 -> (rt1 * glob A) ->  (rt2 * glob A) distr),
  (forall M i1 &m, mu (D i1 (glob A){m}) M = Pr[ A.ex1(i1) @ &m : M (res, (glob A))]) /\
  (forall M r1 i2 &m, mu (Q i2 (r1 ,(glob A){m})) (M r1) 
                    = Pr[ A.ex2(i2,r1) @ &m :  M r1 ((res, glob A))]) /\
  forall &m M i1 i2, Pr[ RCR(A).main(i1,i2) @ &m : M (res.`1, (res.`2 , glob A)) ] 
   = mu (dlet (D i1 (glob A){m}) (fun a => dmap (Q i2 a) (fun x => (a.`1, x)))) M.  
proof. elim rewindable_A_nr11.
progress. exists D Q. split.  auto. split. auto. 
have jj : forall M i1 i2 &1 &2, (glob A){1} = (glob A){2} => 
   Pr[ RCR(A).main(i1,i2) @ &1 : M (res.`1, (res.`2 , glob A)) ] 
 = Pr[ RCR(A).main(i1,i2) @ &2 : M (res.`1, (res.`2, glob A)) ]. progress. byequiv. proc.
call (_:true).
call (_:true). auto. progress. auto. 
move => &m.
progress.
have : exists &n, (glob A){n} = (glob A){m} 
   /\ Q.qg{n} = fun (ex2a1r : at2 * rt1) (g : (glob A)) => Q ex2a1r.`1 (ex2a1r.`2, g).
have iii : Pr[ W.main(fun (ex2a1r : at2 * rt1) (g : (glob A)) 
  => Q ex2a1r.`1 (ex2a1r.`2, g)) @ &m : exists &n, (glob A){n} = (glob A){m} /\ Q.qg{n} 
     = fun (ex2a1r : at2 * rt1) (g : (glob A)) => Q ex2a1r.`1 (ex2a1r.`2, g) ] = 1%r. 
apply (ohj (fun (ex2a1r : at2 * rt1) (g : (glob A)) => Q ex2a1r.`1 (ex2a1r.`2, g)) &m).
smt(@Distr). elim.
move => &n. elim. move => a b.
rewrite - (jj M i1 i2 &n &m). smt().
rewrite (H1 &n M). auto. rewrite a. auto.
qed.


lemma reflectionComp : 
   exists (D : at1 -> (glob A) ->  (rt1 * glob A) distr), 
   exists (Q : at2 -> (rt1 * glob A) ->  (rt2 * glob A) distr),
  (forall M i1 &m, mu (D i1 (glob A){m}) M = Pr[ A.ex1(i1) @ &m :  M (res, (glob A))]) /\
  (forall M r1 i2 &m, mu (Q i2 (r1 ,(glob A){m})) M 
                    = Pr[ A.ex2(i2,r1) @ &m : M ((res, glob A))]) /\
  forall &m M i1 i2, Pr[ RCR(A).main(i1,i2) @ &m : M ((res.`2 , glob A)) ] 
   = mu (dlet (D i1 (glob A){m}) (Q i2)) M.  
elim reflectionComp_dmap.
progress. exists D Q.
progress. rewrite  (H0 (fun x y => M y)). simplify. auto.
rewrite (H1 &m (fun (x : rt1 * (rt2 * (glob A))) => M x.`2) ). 
simplify.   rewrite - dmapE.
rewrite dmap_dlet. 
have ->: (fun (a : rt1 * (glob A)) =>
        dsnd
          ((fun (a0 : rt1 * (glob A)) =>
              dmap (Q i2 a0) (fun (x : rt2 * (glob A)) => (a0.`1, x))) a)) = (Q i2).
apply fun_ext. move => a. simplify. simplify dmap. rewrite dlet_dlet.
have ->: (fun (x1 : rt2 * (glob A)) =>
     dlet ((\o) dunit (fun (x : rt2 * (glob A)) => (a.`1, x)) x1)
       (dunit \o fun (p : rt1 * (rt2 * (glob A))) => p.`2)) = dunit.
apply fun_ext. move => x. rewrite dlet_dunit. rewrite dmap_dunit.
have ->: ((fun (p : rt1 * (rt2 * (glob A))) => p.`2) (a.`1, x)) = x. simplify. auto.
auto.
rewrite dlet_dunit.
rewrite dmap_id. auto. auto.
qed.



lemma refl_comp : 
   exists (D1 : at1 -> glob A -> (rt1 * glob A) distr)
          (D2 : at2 -> (rt1 * glob A) -> (rt2 * glob A) distr),    
  (forall &m M i1, mu (D1 i1 (glob A){m}) M = Pr[ A.ex1(i1) @ &m :  M (res, glob A)]) /\
  (forall &m M r1 i2, mu (D2 i2 (r1 ,(glob A){m})) (M r1) 
       = Pr[ A.ex2(i2,r1) @ &m :  M r1 (res, glob A)]) /\
  forall &m M i1 i2, 
   mu (dlet (D1 i1 (glob A){m}) (fun r => dmap (D2 i2 r) (fun x => (r.`1, x)))) M 
    = Pr[ RCR(A).main(i1,i2) @ &m : M (res.`1, (res.`2 , glob A)) ].  
elim reflectionComp_dmap. progress.
exists D Q. progress.  apply H. apply H0. rewrite H1. auto.
qed.     


lemma refl_comp_simple : 
   exists (D1 : at1 -> (glob A) -> (rt1 * glob A) distr) 
          (D2 : at2 -> (rt1 * glob A) -> (glob A) distr),
  (forall &m M i1, mu (D1 i1 (glob A){m}) M 
                 = Pr[ A.ex1(i1) @ &m : M (res, (glob A))]) /\
  (forall &m M r1 i2, mu (D2 i2 (r1 ,(glob A){m})) M 
                    = Pr[ A.ex2(i2,r1) @ &m : M (glob A)]) /\
  forall &m M i1 i2, mu (dlet (D1 i1 (glob A){m}) (D2 i2)) M
                   = Pr[ RCR(A).main(i1,i2) @ &m : M (glob A) ].
proof. elim reflectionComp.
progress.
exists D. exists  (fun (x : at2) (z : rt1 * glob A) => 
    dmap (Q x z) (fun (y : rt2 * (glob A)) => y.`2)).
progress. apply H. 
rewrite - (H0 (fun (x : rt2 * glob A) => M x.`2) ). rewrite dmapE.
auto.
rewrite (H1 &m (fun (x : rt2 * glob A) => M x.`2)).
rewrite - dmapE.
rewrite dmap_dlet. auto.
qed.


end section.
end ReflComp.

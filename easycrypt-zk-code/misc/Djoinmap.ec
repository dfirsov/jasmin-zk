pragma Goals:printall.
require import AllCore DBool Bool List Distr Int IntDiv AuxResults FSet.

require import AllCore Distr FSet StdRing StdOrder StdBigop List.
(*---*) import RField RealOrder Bigreal BRA.
import BRM.

type a, b.

op d : a -> b distr.

op merge ['a] = (fun (xs : 'a list * 'a list) => xs.`1 ++ xs.`2).
op splitf ['a] (n : int) = (fun (l : 'a list) => (take n l, drop n l)).


module DJM = {

  proc main1(l1 : a list, l2 : a list) = {
    var x1, x2;
    x1 <$ djoinmap d l1;
    x2 <$ djoinmap d l2;
    return (x1, x2);
  }


  proc main2(l1 : a list, l2 : a list) = {
    var x;
    x <$ djoinmap d l1 `*` djoinmap d l2;
    return x;
  }


  proc main3(l1 : a list, l2 : a list) = {
    var x;
    x <$ dmap (djoinmap d l1 `*` djoinmap d l2) merge;
    return x;
  }

  proc main4(l1 : a list, l2 : a list) = {
    var x;
    x <$ djoinmap d (l1 ++ l2) ;
    return x;
  }

  proc main5(l : a list) = {
    var x;
    x <$ djoinmap d l ;
    return x;
  }

  proc main6(l : a list, l' : a list, w : int list) = {
    var x,y;
    (x,y) <@ main1(l,l');
    return (x, y);
  }  
}.

require import DProd.
clone import ProdSampling with type t1 <- b list,
                               type t2 <- b list.

lemma main12 : equiv [ DJM.main1 ~ DJM.main2 : ={arg} ==> ={res} ].
transitivity S.sample2 (arg{2} = (djoinmap d arg{1}.`1, djoinmap d arg{1}.`2) ==> ={res}) (arg{1} = (djoinmap d arg{2}.`1, djoinmap d arg{2}.`2) ==> ={res}).
progress. smt(). auto.
proc. rnd. rnd. skip. progress.
symmetry.
transitivity S.sample (arg{2} = (djoinmap d arg{1}.`1, djoinmap d arg{1}.`2) ==> ={res}) (={arg} ==> ={res}).
progress. smt(). auto.
proc. rnd. skip. progress.
conseq sample_sample2. auto.
qed.



lemma main23 : equiv [ DJM.main3 ~ DJM.main2 : ={arg} ==> res{1} = merge res{2} ].
proc.
exists* l1{1}, l2{1}. 
elim*. progress.
rnd (fun l => (take (size l1_L) l, drop (size l1_L) l)) merge.
skip. 
progress. 
have f1 : xR.`1 \in djoinmap d l1{2}. smt(supp_dprod).
have f2 : xR.`2 \in djoinmap d l2{2}. smt(supp_dprod).
have f3 : size xR.`1 = size l1{2}. smt(@Distr).
have f4 : size xR.`2 = size l2{2}. smt(@Distr).
rewrite /merge.
rewrite - f3. smt(@List).
have ->: mu1 (dmap (djoinmap d l1{2} `*` djoinmap d l2{2}) merge) (merge xR)
 = mu1 ( (djoinmap d l1{2} `*` djoinmap d l2{2})) (splitf (size l1{2}) (merge xR)).
rewrite - (dmap1E_can _ merge (splitf (size l1{2}))).
rewrite /cancel.
rewrite /merge /splitf. smt(@List).
rewrite /merge /splitf. 
progress.
have f1 : a.`1 \in djoinmap d l1{2}. smt(@Distr).
have f2 : a.`2 \in djoinmap d l2{2}. smt(@Distr).
have f3 : size a.`1 = size l1{2}. smt(@Distr).
have f4 : size a.`2 = size l2{2}. smt(@Distr).
rewrite - f3. smt(@Distr). auto.
have f1 : xR.`1 \in djoinmap d l1{2}. smt(@Distr).
have f2 : xR.`2 \in djoinmap d l2{2}. smt(@Distr).
have f3 : size xR.`1 = size l1{2}. smt(@Distr).
have f4 : size xR.`2 = size l2{2}. smt(@Distr).
rewrite /merge.
rewrite - f3. smt().
have f : exists (a : b list * b list), (a \in djoinmap d l1{2} `*` djoinmap d l2{2}) /\ xL = merge a.
apply supp_dmap. auto.
elim f. progress.
smt(@Distr).
smt(@Distr).
qed.


lemma main34 : equiv [ DJM.main4 ~ DJM.main3 : ={arg} ==> ={res} ].
proc.
rnd.  skip. progress.
rewrite - djoin_cat.
simplify.
smt(@List).
rewrite - djoin_cat.
smt(@List).
qed.



lemma djm_main14 : equiv [ DJM.main1 ~ DJM.main4 : ={arg} ==> 
  merge res{1} = res{2} ].
transitivity DJM.main2 (={arg} ==> ={res}) (={arg} ==> merge res{1} = res{2}). 
smt(). auto. conseq main12. 
transitivity DJM.main3 (={arg} ==> merge res{1} = res{2} ) (={arg} ==> ={res}). 
smt(). auto. symmetry. conseq main23.  auto. auto.
symmetry. conseq main34. auto. auto.
qed.






    

 

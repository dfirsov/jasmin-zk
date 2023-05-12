(*

THIS FILE CONTAINS AN UPDATED FORMALIZATION OF FINITE AVERAGING TECHNIQUE FROM STADLIB OF EASYCRYPT.

The main change is that we added "forall quantified" argument to an adversary.
*)

require import AllCore List Distr.
require import Finite.
require (*--*) StdBigop.
(*---*) import StdBigop.Bigbool.BBOr StdBigop.Bigreal.BRA.

type input, output, argt.

op d : input distr.

module type Worker = {
  proc work(ma:argt,x:input) : output
}.

module Rand (W : Worker) = {
  proc main(ma:argt) : input * output = {
    var x, r;

    x <$ d;
    r <@ W.work(ma,x);
    return (x,r);
  }
}.

lemma prCond (A <: Worker) &m (v:input)
             (ev:input -> glob A -> output -> bool) maz:
    Pr[Rand(A).main(maz) @ &m: ev v (glob A) (snd res) /\ v = fst res]
  = (mu1 d v) * Pr[A.work(maz,v) @ &m : ev v (glob A) res].
proof. 
byphoare (_: (glob A) = (glob A){m} /\ maz = arg
            ==> ev (fst res) (glob A) (snd res) /\ fst res = v) => //.
pose pr:= Pr[A.work(maz,v) @ &m: ev v (glob A) res].
proc.
seq 1: (v = x) (mu1 d v) pr 1%r 0%r ((glob A) = (glob A){m} /\ maz = ma)=> //.
+ by rnd.
+ by rnd; auto=> />; rewrite pred1E.
+ call (: (glob A) = (glob A){m} /\ x = v /\ ma = maz
          ==> ev v (glob A) res  )=> //.
  rewrite /pr; bypr. progress.
   byequiv (_: ={glob A, arg} ==> ={res, glob A})=> //. sim. progress.

by hoare; rewrite /fst /snd /=; call (: true); auto=> /#.
qed.

lemma introOrs (A <: Worker) &m (ev:input -> glob A -> output -> bool) maz:
     is_finite (support d)
  => let sup = to_seq (support d) in
       Pr[Rand(A).main(maz) @ &m: ev (fst res) (glob A) (snd res)]
     = Pr[Rand(A).main(maz) @ &m:
            big predT (fun v=> ev v (glob A) (snd res) /\ v = fst res) sup].
proof.
move=> Fsup sup.
byequiv (: ={glob A,arg} ==> ={glob A, res} /\ (fst res{1}) \in d)=> //.
+ by proc; call (_: true); rnd.
move=> |> &2 res2_in_d.
rewrite bigP hasP //=; split.
+ move=> H; exists res{2}.`1=> //=.
  by rewrite mem_filter /predT /sup mem_to_seq.
by move=> [] x />.
qed.

lemma Mean (A <: Worker) &m (ev:input -> glob A -> output -> bool) maz:
     is_finite (support d)
  => let sup = to_seq (support d) in
       Pr[Rand(A).main(maz)@ &m: ev (fst res) (glob A) (snd res)]
     = big predT (fun v, mu1 d v * Pr[A.work(maz,v)@ &m:ev v (glob A) res]) sup.
proof.
move=> Fsup /=.
have:= introOrs A &m ev maz _ => //= ->.
elim: (to_seq (support d)) (uniq_to_seq _ Fsup)=> //= => [|v vs ih [] v_notin_vs uniq_vs].
+ by rewrite big_nil; byphoare (: true ==> false).
rewrite big_cons {2}/predT /=.
have ->:   Pr[Rand(A).main(maz) @ &m:
                big predT (fun v=> ev v (glob A) res.`2 /\ v = res.`1) (v::vs)]
         = Pr[Rand(A).main(maz) @ &m:
                (ev v (glob A) (snd res) /\ v = fst res) \/
                big predT (fun v=> ev v (glob A) res.`2 /\ v = res.`1) vs].
+ by rewrite Pr[mu_eq].
rewrite Pr[mu_disjoint].
+ move=> /> &0; rewrite negb_and negb_and //=.
  case: (v = res{0}.`1)=> //= ->>. 
  case: (ev res{0}.`1 (glob A){0} res{0}.`2)=> //= hev.
  rewrite bigP hasP negb_exists=> //= v'.
  rewrite negb_and negb_and filter_predT.
  by case: (v' = res{0}.`1)=> [->>|//]; rewrite v_notin_vs.
by rewrite ih // (prCond A &m v ev).
qed.

lemma Mean_uni (A <: Worker) &m (ev : input -> glob A -> output -> bool) r maz:
      (forall x, x \in d => mu1 d x = r)
   => is_finite (support d)
   => let sup = to_seq (support d) in
        Pr[Rand(A).main(maz)@ &m: ev (fst res) (glob A) (snd res)]
      = r * big predT (fun v=> Pr[A.work(maz,v) @ &m:ev v (glob A) res]) sup.
proof.
move=> Hd Hfin /=.
have := Mean A &m ev => /= -> //.
rewrite mulr_sumr; apply: eq_big_seq=> /= v.
by rewrite mem_to_seq=> // /Hd ->.
qed.



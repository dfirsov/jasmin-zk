require import AllCore Distr List DBool.


type commitment, opening, message.

op Com  : message -> (commitment * opening) distr.
op Ver : message * (commitment * opening) -> bool.

axiom Com_sound : forall (x : message * (commitment * opening)), x.`2 \in Com x.`1 => Ver x.
axiom Com_lossless : forall b, is_lossless (Com b).

(* two negligible values which we use as upper bounds for statistical hiding  *)
op eps, eps2 : real.  
axiom eps_ge0 : 0%r <= eps.
axiom eps2_ge0 : 0%r <= eps2 < 1%r/4%r.


module type Binder = {
   proc bind() : commitment * message * opening * message * opening
}.

module BindingExperiment (B:Binder) = {
    proc main() : bool = {
      var c, m, m', d, d', v, v';
      (c, m, d, m', d') <@ B.bind();
      v                 <- Ver (m, (c, d));
      v'                <- Ver (m', (c, d'));
      return v /\ v' /\ m <> m';
    }
}.

module type Unhider  = {
  proc choose() : message list * message list
  proc guess(c : commitment list) : bool 
}.


(* Below we give two different formulations of statistical hiding for commitement scheme  *)
module HidingExperiment(U : Unhider) = {
  proc main() : bool = {
    var b : bool;
    var b' : bool;
    var m0 : message list;
    var m1 : message list;
    var co : (commitment * opening) list;
    (m0, m1) <@ U.choose();
    b <$ {0,1};
    co <$ djoinmap Com (if b then m0 else m1);
    b' <@ U.guess(map fst co);
    return b = b';
  }
}.


axiom comm_scheme_hiding_eps2 &m: forall (U <: Unhider),
  `|Pr[HidingExperiment(U).main() @ &m : res] -  1%r/2%r| <= eps2.



module HidingGame(U : Unhider) = {
  proc main(b:bool) : bool = {
    var b' : bool;
    var m0 : message list;
    var m1 : message list;
    var co : (commitment * opening) list;
    (m0, m1) <@ U.choose();
    co <$ djoinmap Com (if b then m0 else m1);
    b' <@ U.guess(map fst co);
    return b';
  }
}.

axiom comm_scheme_hiding_eps &m: forall (U <: Unhider),
  `|Pr[HidingGame(U).main(true) @ &m : res] -  Pr[HidingGame(U).main(false) @ &m : res]| <= eps.

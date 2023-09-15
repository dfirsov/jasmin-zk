require import AllCore Distr StdRing Real.

import RField.


(** pRHL characterisation  of leakage-freeness.

 Here we seek a characterisation of the leakage-free
 property in a pure probabilist Relational Hoare Logic
 formulation. The goal is to avoid handling explicitly
 the leakage, resorting instead to the EC's pRHL
 reasoning.                                      *)


(** The setting:

 We consider a collection of Jasmin procedures that are
 extracted into EC in two modes ([XtrI] and [XtrR]).
 Each one of these is a module that includes the
 EC's model of Jasmin-implemented functions:

  - XtrI.f - an EC procedure modeling the input/output
      behaviour of Jasmin function [f] (hence, calling
      it an abstract or "Ideal" setting). This is
      a stateless module (Jasmin do not allow global
      variables).
  - XtrR.f - an EC procedure that, in addition to the
      input/output behaviour, models also what is leaked
      during execution (accumulated in variable
      [XtrR.leakages]). This is what we call the
      concrete or "Real" setting.

 As a meta-property of the extraction mechanism, we
 have that the behaviour of [XtrI.f] is indeed given
 by the marginal probability of [XtrR.f] (when the
 leakage is ignored). In any case, this fact is
 typically proved automatically with the [sim]
 tactic.

 In what follows, we define an abstract theory [CT_Meta]
 with wrappers that abstracts the Jasmin function under
 consideration -- in there, [JI] and [JR] are
 respectivelly wrappers of the abstract (ideal)
 and concrete (real) extractions of the Jasmin
 function.                                        *)


(** This theory establishes the core definitions
 and properties of the PRHL characterisation of
 Leakage-freeness (what we call the CT-property,
 as it extends the standard non-interference
 based characterisation of the constant-time
 property - here called ct-property).
 In this theory, we focus on a single Jasmin
 function [f]. Bellow, we shall establish
 a compositionality result that ultimately justifies
 this "local" focus.                           *)
abstract theory CT_Meta.

(** types for public and secret inputs, and output *)
type pin_t, sin_t, out_t.

(** This abstracts a single Jasmin function --
 it will represent both the abstract (ideal) or
 concrete (real) extracted variants.          *)
module type JasminProcWrapper = {
 proc main(pin: pin_t, sin: sin_t): out_t
}.


(** The CT-property can be understood as an
 instance of the Real/Ideal paradigm. For a
 given Jasmin function (abstracted by modules
 [JI] and [JR], it establishes the equivalence
 of the concrete (leaky) implementation with
 abstract (pure) implementation combined with
 simulated leakage. Both sides of the equivalence
 are captured by the following modules [SimR]
 and [RSim].                                *)
 


(** [SimR] denotes the Simulated side of the
 captured property (where leakage is simulated
 resorting to the real implementation on
 arbitrary secret inputs).                     *)
module SimR(JI: JasminProcWrapper, JR: JasminProcWrapper) = {
 proc main(pin: pin_t, sin sin': sin_t): out_t = {
  var _r, r;
  _r <@  JR.main(pin, sin');
  r <@  JI.main(pin, sin);
  return r;
 }
}.

(** On the other side, the real (leaky)
 implementation is conditioned by (a possibly
 faulty) dummy simulator. This is a rather
 artificial (technical) artifact to turn
 the CT-property robust on possibly diverging
 programs.                                     *)
module RSim(JI: JasminProcWrapper)(JR: JasminProcWrapper) = {
 proc main(pin: pin_t, sin: sin_t): out_t = {
  var _r, r;
  _r <@  JI.main(pin, sin); (* behaves as a dummy
                             leakage simulator *)
  r <@  JR.main(pin, sin);
  return r;
 }
}.

(** An apparently stronger variant of CT-property
 is based on a more general variant [RSim]. As
 we will see later, it turns out to be provably
 equivalent to the former characterization.    *)
module RSim'(JI: JasminProcWrapper)(JR: JasminProcWrapper) = {
 proc main(pin: pin_t, sin sin': sin_t): out_t = {
  var _r, r;
  _r <@  JI.main(pin, sin');
  r <@  JR.main(pin, sin);
  return r;
 }
}.

(** Another useful definition simplifies the
 right-hand side (simulated) when it is known
 that leakage does not depend on secret inputs
 (standard non-interference). In that case,
 running the simulator on arbitrary secret
 inputs is indeed equivalent to run it with
 the given secret inputs. We call this 
 Coupled-Composition (CC). *)
module CC(JI: JasminProcWrapper, JR: JasminProcWrapper) = {
 proc main(pin: pin_t, sin: sin_t): out_t = {
  var _r, r;
  _r <@  JR.main(pin, sin);
  r <@  JI.main(pin, sin);
  return r;
 }
}.


section.

declare module JR <: JasminProcWrapper.
declare module JI <: JasminProcWrapper {-JR}.

declare axiom stateless_JI &m x: (glob JI){m} = x.

declare axiom proj_JR_JI:
 equiv [ JR.main ~ JI.main
       : ={pin, sin} ==> ={res} ].


lemma JI_JR_prE P &m _pin _sin:
 Pr[ JI.main(_pin,_sin) @ &m : P res ]
 = Pr[ JR.main(_pin,_sin) @ &m : P res ].
proof. by rewrite eq_sym; byequiv proj_JR_JI. qed.

(** STATELESS FACTS *)
lemma JI_pr_m_m' P &m &m' _pin _sin:
 Pr[ JI.main(_pin,_sin) @ &m : P res ]
 = Pr[ JI.main(_pin,_sin) @ &m' : P res ].
proof.
byequiv (: _ ==> ={res}); simplify => //.
by sim => /> *; apply stateless_JI.
qed.

lemma JR_pr_m_m' P &m &m' _pin _sin:
 (glob JR){m} = (glob JR){m'} =>
 Pr[ JR.main(_pin,_sin) @ &m : P (res,glob JR)]
 = Pr[ JR.main(_pin,_sin) @ &m' : P (res,glob JR)].
proof.
move=> E_m_m'.
byequiv (: ={pin,sin,glob JR} /\ pin{2}=_pin /\ sin{2}=_sin /\ (glob JR){1}=(glob JR){m} /\ (glob JR){2}=(glob JR){m'} ==> ={res, glob JR}); simplify => //.
by sim => /> *.
qed.

lemma RSim_pr &m _pin _sin _rl:
 Pr[RSim(JI,JR).main(_pin, _sin) @ &m : (res,glob JR)=_rl]
 = Pr[JI.main(_pin, _sin) @ &m : true]
   * Pr[JR.main(_pin, _sin) @ &m : (res,glob JR)=_rl].
proof.
byphoare (: pin=_pin /\ sin=_sin /\ (glob JR)=(glob JR){m} ==> (res,glob JR)=_rl) => //.
proc; simplify.
seq 1: (true)
       Pr[JI.main(_pin, _sin) @ &m : true]
       Pr[JR.main(_pin, _sin) @ &m : (res,glob JR)=_rl]
       _ 0%r
       (pin=_pin /\ sin=_sin /\ (glob JR) = (glob JR){m}) => //.
+ by call (:true) => //.
+ call (: pin = _pin /\ sin = _sin /\ (glob JR)=(glob JR){m} ==> true).
   bypr; move=> /> &m' Hglob.
   by apply (JI_pr_m_m' predT).
+ by auto.
+ call (: pin=_pin /\ sin=_sin /\ (glob JR)=(glob JR){m} ==> (res,glob JR)=_rl); last first.
   by auto => /> /#.
  bypr; move=> &m' [->] [->] Hglob.
  byequiv => //.
  proc* => //; simplify.
  by call (:true); auto => /> * /#.
qed.

lemma RSim'_pr &m _pin _sin _sin' _rl:
 Pr[RSim'(JI,JR).main(_pin, _sin, _sin') @ &m : (res,glob JR)=_rl]
 = Pr[JI.main(_pin, _sin') @ &m : true]
   * Pr[JR.main(_pin, _sin) @ &m : (res,glob JR)=_rl].
proof.
byphoare (: pin=_pin /\ sin=_sin /\ sin'=_sin' /\ (glob JR)=(glob JR){m} ==> (res,glob JR)=_rl) => //.
proc; simplify.
seq 1: (true)
       Pr[JI.main(_pin, _sin') @ &m : true]
       Pr[JR.main(_pin, _sin) @ &m : (res,glob JR)=_rl]
       _ 0%r
       (pin=_pin /\ sin=_sin /\ (glob JR) = (glob JR){m}) => //.
+ by call (:true) => //.
+ call (: pin = _pin /\ sin = _sin' /\ (glob JR)=(glob JR){m} ==> true).
   bypr; move=> /> &m' Hglob.
   by apply (JI_pr_m_m' predT).
+ by auto.
+ call (: pin=_pin /\ sin=_sin /\ (glob JR)=(glob JR){m} ==> (res,glob JR)=_rl); last first.
   by auto => /> /#.
  bypr; move=> &m' [->] [->] Hglob.
  byequiv => //.
  proc* => //; simplify.
  by call (:true); auto => /> * /#.
qed.

lemma SimR_pr _pin _sin _sin' &m _rl:
 Pr[SimR(JI, JR).main(_pin, _sin, _sin') @ &m : (res,glob JR)=_rl]
 = Pr[JR.main(_pin, _sin') @ &m : (glob JR)=_rl.`2]
   * Pr[JI.main(_pin, _sin) @ &m : res = _rl.`1].
proof.
byphoare (: pin=_pin /\ sin=_sin /\ sin'=_sin' /\ (glob JR)=(glob JR){m} ==> (res,glob JR)=_rl) => //.
proc; simplify.
seq 1: ((glob JR)=_rl.`2)
       Pr[JR.main(_pin, _sin') @ &m : (glob JR)=_rl.`2]
       Pr[JI.main(_pin, _sin) @ &m : res=_rl.`1]
       _ 0%r
       (pin=_pin /\ sin=_sin /\ sin'=_sin') => //.
+ by call (:true) => //.
+ call (: pin = _pin /\ sin = _sin' /\ (glob JR) = (glob JR){m} ==> (glob JR)=_rl.`2).
   bypr; move=> &m' [->] [->] Hglob.
   byequiv => //.
   proc* => //.
   by call (:true); auto => />.
+ by auto.
+ call (: pin=_pin /\ sin=_sin ==> res=_rl.`1); last by auto => /> /#.
  bypr; move=> &m' [->] ->.
  by apply (JI_pr_m_m' (pred1 _rl.`1)).
hoare.
by call (:true); auto => /#.
qed.

lemma CT_pr:
 (* CT *)
 equiv [ RSim(JI,JR).main ~ SimR(JI,JR).main
       : ={pin, sin, glob JR} ==> ={res,glob JR} ]
 <=>
 (* CTpr *)
 forall _pin _sin _sin' &m _rl,
 Pr[ JI.main(_pin,_sin) @ &m : true ]
 * Pr[ JR.main(_pin,_sin) @ &m : (res,glob JR)=_rl]
 = Pr[ JI.main(_pin,_sin) @ &m : res=_rl.`1 ]
   * Pr[ JR.main(_pin,_sin') @ &m : (glob JR)=_rl.`2 ].
proof.
split.
 move => CT_J _pin _sin _sin' &m _rl.
 by rewrite -RSim_pr mulrC -SimR_pr; byequiv CT_J => //=.
move=> CTpr.
bypr (res,glob JR){1} (res,glob JR){2} => //.
move => &1 &2 _rl [->] [->] Eglob.
rewrite /= RSim_pr SimR_pr (CTpr pin{2} sin{2} sin'{2} &1 _rl).
rewrite (JI_pr_m_m' (pred1 _rl.`1) &1 &2) mulrC; congr => //.
by rewrite (JR_pr_m_m' (fun x:_*_=>x.`2=_rl.`2) &1 &2).
qed.

lemma CTplus_pr:
 (* CTplus *)
 equiv [ RSim'(JI,JR).main ~ SimR(JI,JR).main
       : ={pin, sin, glob JR} ==> ={res,glob JR} ]
 <=>
 (* CTpr *)
 forall _pin _sin _sin1' _sin2' &m _rl,
 Pr[ JI.main(_pin,_sin1') @ &m : true ]
 * Pr[ JR.main(_pin,_sin) @ &m : (res,glob JR)=_rl]
 = Pr[ JI.main(_pin,_sin) @ &m : res=_rl.`1 ]
   * Pr[ JR.main(_pin,_sin2') @ &m : (glob JR)=_rl.`2 ].
proof.
split.
 move => CT_J _pin _sin _sin1' _sin2' &m _rl.
 by rewrite -RSim'_pr mulrC -SimR_pr; byequiv CT_J => //=.
move=> CTpr.
bypr (res,glob JR){1} (res,glob JR){2} => //.
move => &1 &2 _rl [->] [->] Eglob.
rewrite /= RSim'_pr SimR_pr (CTpr pin{2} sin{2} sin'{1} sin'{2} &1 _rl).
rewrite (JI_pr_m_m' (pred1 _rl.`1) &1 &2) mulrC; congr => //.
by rewrite (JR_pr_m_m' (fun x:_*_=>x.`2=_rl.`2) &1 &2).
qed.


(* Nice lemmas! but actually we do not rely on them...*)
lemma JI_opsem1E &m:
 exists d, forall _pin _sin &m' r,
  Pr[JI.main(_pin, _sin) @ &m' : res=r]
  = mu1 (d _pin _sin) r.
proof.
pose ff := fun (pin : pin_t) (sin : sin_t) (r : out_t)
 => Pr[JI.main(pin, sin) @ &m : res = r].
pose df := fun (pin : pin_t) (sin : sin_t) =>
 mk (fun (x : out_t) => ff pin sin x).
exists df => pin sin &m' r.
rewrite -(JI_pr_m_m' (pred1 r) &m) /df muK /ff //=.
apply Distr => /=; first smt(mu_bounded).
move => l lU.
have ->: (StdBigop.Bigreal.BRA.big predT (fun (x : out_t) => Pr[JI.main(pin, sin) @ &m : res = x]) l)
 = Pr[JI.main(pin, sin) @ &m : List.(\in) res l].
 rewrite Pr [muE] (RealSeries.sumE_fin _ l) //=.
  move=> x; apply contraR => Hx.
  apply (eq_trans _ Pr[JI.main(pin, sin) @ &m : false]).
   by rewrite Pr [mu_eq] /#. 
  by rewrite Pr [mu_false].
 apply StdBigop.Bigreal.BRA.eq_big_seq => x Hx /=.
 by rewrite Pr [mu_eq] /#.
smt(mu_bounded).
qed.

lemma JI_opsemE &m:
 exists d, forall P _pin _sin &m',
  Pr[JI.main(_pin, _sin) @ &m' : P res]
  = mu (d _pin _sin) P.
proof.
have [dI EdI] := JI_opsem1E &m.
exists dI => P pin sin &m'.
rewrite Pr [muE] muE; apply RealSeries.eq_sum => x /=.
case: (P x) => C.
 by rewrite -(EdI _ _ &m') // Pr [mu_eq] /#.
apply (eq_trans _ Pr[JI.main(pin, sin) @ &m' : false]).
 by rewrite Pr [mu_eq] /#.
by rewrite Pr [mu_false].
qed.


(** This is a workaroud for a current limitation of
 EC's "rewrite Pr" mechanism. It can be
 proved for concrete [JR] modules (see usage below). *)
declare axiom prMuE P pin sin &m:
 Pr[ JR.main(pin,sin) @ &m : P (res,glob JR)]
 = RealSeries.sum (fun (x:_*_) => Pr [JR.main(pin,sin) @ &m : P (res,glob JR) /\ res=x.`1 /\ (glob JR)=x.`2]).

lemma JR_opsem1E &m:
 exists d, forall _pin _sin &m' (_rl:_*_),
  (glob JR){m} = (glob JR){m'} =>
  Pr[JR.main(_pin, _sin) @ &m' : (res,glob JR)=_rl]
  = mu1 (d _pin _sin) _rl.
proof.
pose ff :=
 fun pin sin (rl:_*_) => Pr[JR.main(pin, sin) @ &m : (res,glob JR)=rl].
pose df := fun pin sin => mk (fun x => ff pin sin x).
exists df => pin sin &m' rl Hmm'.
rewrite (JR_pr_m_m' (pred1 rl) &m' &m) 1:/# /df muK /ff //=.
apply Distr => /=; first smt(mu_bounded).
move => xl xlU. 
have ->: (StdBigop.Bigreal.BRA.big predT (fun x => Pr[JR.main(pin, sin) @ &m : (res,glob JR) = x]) xl)
 = Pr[JR.main(pin, sin) @ &m : List.(\in) (res,glob JR) xl].
 rewrite (prMuE (fun rl=>List.(\in) rl xl)%List _ _ &m).
 rewrite (RealSeries.sumE_fin _ xl) //=.
  move=> x; apply contraR => Hx.
  apply (eq_trans _ Pr[JR.main(pin, sin) @ &m : false]).
   by rewrite Pr [mu_eq] /#.
  by rewrite Pr [mu_false].
 apply StdBigop.Bigreal.BRA.eq_big_seq => x Hx /=.
 by rewrite Pr [mu_eq] /#.
smt(mu_bounded).
qed.

lemma JR_opsemE &m:
 exists d, forall P _pin _sin &m',
  (glob JR){m} = (glob JR){m'} =>
  Pr[JR.main(_pin, _sin) @ &m' : P (res,glob JR)]
  = mu (d _pin _sin) P.
proof.
have [dR EdR] := JR_opsem1E &m.
exists dR => P pin sin &m' Hmm'.
rewrite (prMuE P) muE.
apply RealSeries.eq_sum => x /=.
case: (P x) => C.
 by rewrite -(EdR _ _ &m') // Pr [mu_eq] /#.
apply (eq_trans _ Pr[JR.main(pin, sin) @ &m' : false]).
 by rewrite Pr [mu_eq] /#.
by rewrite Pr [mu_false].
qed.

lemma nosmt diverg_lemma pin sin &m:
 (forall x, Pr[JR.main(pin, sin) @ &m : (res,glob JR)=x] = 0%r)
 => Pr[JR.main(pin, sin) @ &m : true] = 0%r.
proof.
move=> eq0_pr; rewrite (prMuE predT) /predT /= RealSeries.sum0_eq //.
by move=> x />; rewrite -(eq0_pr x) Pr [mu_eq] /#.
qed.

lemma CT_diverg:
 (* CT *)
 equiv [ RSim(JI,JR).main ~ SimR(JI,JR).main
       : ={pin, sin, glob JR} ==> ={res, glob JR} ]
 =>
 (* divergence pattern cannot depend on secret inps *)
 forall _pin _sin _sin' &m,
 Pr[ JI.main(_pin,_sin) @ &m : true ] = 0%r
 <=> Pr[ JI.main(_pin,_sin') @ &m : true ] = 0%r.
proof.
move => /CT_pr H _pin _sin _sin' &m.
have HH: forall _pin _sin _sin' &m,
   Pr[JI.main(_pin, _sin') @ &m : true] = 0%r
   => Pr[JI.main(_pin, _sin) @ &m : true] = 0%r;
last by smt().
clear _pin _sin _sin' &m => _pin _sin _sin' &m.
rewrite !(JI_JR_prE predT) /predT /= => Hsin'.
have {H}H: forall _rl,
 Pr[JR.main(_pin, _sin) @ &m : (res,glob JR) = _rl] = 0%r.
 move=> _rl; move: (H _pin _sin _sin' &m _rl); move=> {H}.
 have ->/=: Pr[JR.main(_pin, _sin') @ &m : (glob JR) = _rl.`2] = 0%r by smt(mu_sub mu_bounded).
 rewrite (JI_JR_prE predT) /predT /=.
 have: Pr[JR.main(_pin, _sin) @ &m : (res,glob JR) = _rl] <= Pr[JR.main(_pin, _sin) @ &m : true] by smt(mu_sub).
 smt(mu_bounded).
by rewrite (prMuE predT) RealSeries.sum0_eq //= /#.
qed.

lemma ct_pr:
 (* ct *)
 equiv [ JR.main ~ JR.main
       : ={pin, glob JR} ==> ={glob JR} ]
 <=>
 (* ctpr *)
 forall _pin _sin _sin' &m _l,
  Pr[ JR.main(_pin,_sin) @ &m : (glob JR)=_l]
  = Pr[ JR.main(_pin,_sin') @ &m : (glob JR)=_l ].
proof.
split.
 move => ct_J _pin _sin _sin' &m _l.
 by byequiv ct_J => // /#.
move=> ctpr.
bypr (glob JR){1} (glob JR){2} => //.
move => &1 &2 _l [-> E].
rewrite (JR_pr_m_m' (fun x:_*_=>x.`2=_l) &1 &2) //=.
by apply ctpr.
qed.

(** CT implies the standard non-interference property
  that ensures that secret inputs are not leaked *)
lemma CT_ct:
 (* CT *)
 equiv [ RSim(JI,JR).main ~ SimR(JI,JR).main
       : ={pin, sin, glob JR} ==> ={res, glob JR} ]
 =>
 (* ct *)
 equiv [ JR.main ~ JR.main
       : ={pin, glob JR} ==> ={glob JR} ].
proof.
rewrite CT_pr ct_pr => CT pin sin sin' &m _l.
case: (exists x, 0%r < Pr[JI.main(pin, sin) @ &m : res = x]).
 move => [r Hr].
 have XX: forall _sin',
   Pr[JR.main(pin, _sin') @ &m : (glob JR) = _l]
   = Pr[JR.main(pin, sin) @ &m : (res,glob JR)=(r,_l)]
     * Pr[JI.main(pin, sin) @ &m : true]
     / Pr[JI.main(pin, sin) @ &m : res = r].
  move => _sin'.
  move: (CT pin sin _sin' &m (r,_l)) => E; field E; smt().
 by rewrite (XX sin) (XX sin') /#.
case: (exists x, 0%r < Pr[JI.main(pin, sin') @ &m : res = x]).
 move => [r Hr].
 have XX: forall _sin,
   Pr[JR.main(pin, _sin) @ &m : (glob JR) = _l]
   = Pr[JR.main(pin, sin') @ &m : (res,glob JR)=(r,_l)]
     * Pr[JI.main(pin, sin') @ &m : true]
     / Pr[JI.main(pin, sin') @ &m : res = r].
  move => _sin.
  move: (CT pin sin' _sin &m (r,_l)) => E; field E; smt().
 by rewrite (XX sin'); rewrite (XX sin); smt().
rewrite !negb_exists /= => T1 T2.
have {T1}I1: forall a, Pr[JI.main(pin, sin') @ &m : res = a]=0%r.
 by move=> a; move: (T1 a); smt(mu_bounded).
have {T2}I2: forall a, Pr[JI.main(pin, sin) @ &m : res = a]=0%r.
 by move=> a; move: (T2 a); smt(mu_bounded).
have R1: Pr[JR.main(pin, sin') @ &m : true] = 0%r.
 apply (diverg_lemma pin sin' &m); move => [r rl].
 pose X:= Pr[JR.main(_,_) @ &m : (res,glob JR)=_].
 have: X <= Pr[JR.main(pin, sin') @ &m : res=r] by smt(mu_sub).
 rewrite -(JI_JR_prE (pred1 r)) /pred1 /X /= (I1 r); smt(mu_bounded).
have R2: Pr[JR.main(pin, sin) @ &m : true] = 0%r.
 apply (diverg_lemma pin sin &m); move => [r rl].
 pose X:= Pr[JR.main(_,_) @ &m : (res,glob JR)=_].
 have: X <= Pr[JR.main(pin, sin) @ &m : res=r] by smt(mu_sub).
 rewrite -(JI_JR_prE (pred1 r)) /pred1 /X /= (I2 r); smt(mu_bounded).
smt(mu_sub mu_bounded).
qed.

(* From the non-interference property, we strengthen
 the previously established independence of divergence
 from secret inputs. Indeed, the probability of
 termination is also insensitive to secret inputs. *)
lemma ct_pr_term:
 (* ct *)
 equiv [ JR.main ~ JR.main
       : ={pin, glob JR} ==> ={glob JR} ]
 =>
 (* pr_term *)
 forall _pin _sin _sin' &m,
 Pr[ JI.main(_pin,_sin) @ &m : true]
 = Pr[ JI.main(_pin,_sin') @ &m : true ].
proof.
move => /ct_pr Hct _pin _sin _sin' &m.
have [dR HdR]:= JR_opsemE &m.
rewrite !(JI_JR_prE predT) /predT /=.
rewrite (HdR predT _ _ &m) //.
rewrite (HdR predT _ _ &m) //.
have: dsnd (dR _pin _sin) = dsnd (dR _pin _sin').
 rewrite eq_distr => l.
 rewrite !dmap1E /pred1 /(\o) /=.
 rewrite -(HdR _ _ _ &m) // -(HdR _ _ _ &m) //=.
 by apply Hct.
smt(weight_dmap).
qed.

(* It allow us to recover (an essentially equivalent
  formulation of the) original Leakage-Free definition *)
lemma CT_LF &m':
 (* CT *)
 equiv [ RSim(JI,JR).main ~ SimR(JI,JR).main
       : ={pin, sin, glob JR} ==> ={res, glob JR} ]
 =>
 (* LF *)
 exists f,
  forall pin sin &m rl,
   (glob JR){m} = (glob JR){m'} =>
   let v = Pr[ JR.main(pin,sin) @ &m : (res,glob JR)=rl ] in
   let w = Pr[ JR.main(pin,sin) @ &m : res=rl.`1 ] in
   0%r < w =>
   v / w = f pin rl.`2.
proof.
move => CT.
have /ct_pr_term E:= CT_ct CT.
pose f := fun pin l =>
           Pr[JR.main(pin,witness) @ &m' : (glob JR)=l]
           / Pr[JI.main(pin,witness) @ &m' : true].
exists f => pin sin &m [r l] Eg @/f /=.
rewrite CT_pr in CT.
have {CT}/=CT:= (CT pin sin witness &m (r,l)).
rewrite -(JR_pr_m_m' (fun x:_*_=>x.`2=l) &m &m') //=.
rewrite -(JI_pr_m_m' predT &m).
rewrite -!(JI_JR_prE (pred1 r)) /pred1 /= => Hw.
rewrite -(E pin sin witness); field CT;
smt(mu_sub mu_bounded).
qed.

require import StdOrder.
import RealOrder.

require import List StdBigop. 

import Bigreal.BRA.



lemma mleakP &m pin sin r f:
 (f pin = fun l => Pr[ JR.main(pin,sin) @ &m : (res, glob JR)=(r,l) ] / Pr[ JR.main(pin,sin) @ &m : res=r ])
 => isdistr (f pin).
proof.
move=> E; apply Distr.
 move=> x; rewrite E.
 smt(divr_ge0 mu_bounded).
move=> ll Hll; rewrite E -divr_suml.
case: (Pr[JR.main(pin, sin) @ &m : res = r] = 0%r) => C.
 by rewrite C /=.
rewrite -(eq_bigr _ (fun l => Pr[JR.main(pin,sin) @ &m : (res, (glob JR)) = (r,l)])). 
 by move=> i _ //=.
rewrite ler_pdivr_mulr /=; first smt(mu_bounded).
pose ll':= map (fun l=>(l,r)) ll.
have Hll': uniq ll'.
 by rewrite /ll' map_inj_in_uniq /#.
have ->: ll=undup (unzip1 ll').
 by rewrite undup_id -map_comp /(\o) /= map_id.
rewrite -(eq_big_seq (fun l=>big predT (fun xy:_*_=>Pr[JR.main(pin, sin) @ &m : res = xy.`2 /\ (glob JR) = xy.`1]) (filter (fun xy:_*_=>xy.`1=l) ll'))).
 move=> l; rewrite undup_id /ll' -map_comp /(\o) map_id //=.
 move => Hl.
 have ->: filter (fun xy:_*_=>xy.`1=l) ll' = [ (l,r) ].
  rewrite /ll' filter_map /preim /=.
  by rewrite filter_pred1 count_uniq_mem // Hl b2i1 nseq1 /=.
 by rewrite big_cons big_nil ifT 1:/#.
rewrite -big_pair // big_pair_pswap.
rewrite /predT /(\o) /=.
pose X:= big _ _ _.
have ->: X=Pr[JR.main(pin, sin) @ &m : res = r /\ (glob JR)\in ll].
 rewrite (prMuE (fun xy:_*_=>xy.`1=r /\ xy.`2\in ll) _ _ &m).
 rewrite /X.
 rewrite (RealSeries.sumE_fin _ (map pswap ll')) //=.
   by rewrite -map_comp map_inj_in_uniq /#.
  move=> [a b] /=.
  rewrite /ll' /pswap -map_comp /(\o)/=.
  apply contraR => Hx.
  have Hx2: a<>r \/ ! b \in ll by smt(mapP).
  apply (eq_trans _ Pr[JR.main(pin, sin) @ &m  : false]).
   by rewrite Pr [mu_eq] /#.
  by rewrite Pr [mu_false].
 apply eq_big_seq => [[a b]].
 rewrite /pswap /ll -map_comp /(\o)/= => /mapP [b' /= Hab].
 by rewrite Pr [mu_eq] /#.
smt(mu_sub).
qed.

lemma LF_CT:
 (* ll *)
 (forall pin sin &m, Pr[JI.main(pin, sin) @ &m : true]=1%r) =>
 (* LF *)
 (forall l, exists f,
  forall pin sin &m rl,
   (glob JR){m} = l =>
   Pr[ JR.main(pin,sin) @ &m : (res,glob JR)=rl ]
   / Pr[ JR.main(pin,sin) @ &m : res=rl.`1 ]
   = f pin rl.`2) =>
 (* CT *)
 equiv [ RSim(JI,JR).main ~ SimR(JI,JR).main
       : ={pin, sin, glob JR} ==> ={res, glob JR} ].
proof.
move => JI_ll Hdef.
rewrite CT_pr => pin sin sin' &m [r l].
rewrite JI_ll /=.
have [dR HdR]:= JR_opsemE &m.
have [dI HdI]:= JI_opsemE &m.
pose linit := (glob JR){m}.
move: (Hdef linit).
rewrite /linit  => {Hdef} [[fl Hfl]].
pose dleak := fun pin (sin:sin_t) => mk (fl pin).
pose DR:= fun pin sin => dI pin sin `*` dleak pin sin.
have EdR:forall pin sin, dR pin sin = DR pin sin.
 move=> _pin _sin.
 apply eq_distr => [[r' l']].
 rewrite dprod1E.
 rewrite -(HdI (pred1 r') _ _ &m).
 rewrite muK.
  apply (mleakP &m _pin _sin r' _).
  apply fun_ext => x.
  by rewrite -(Hfl _pin _sin &m (r',x) _) //.
 rewrite -(HdR _ _ _ &m) //.
 rewrite (JI_JR_prE (pred1 r')).
 case: (Pr[JR.main(_pin, _sin) @ &m : res=r'] = 0%r) => C.
  rewrite C /=.
  have ?: Pr[JR.main(_pin, _sin) @ &m : pred1 (r', l') (res, (glob JR))] <= Pr[JR.main(_pin, _sin) @ &m : res = r'].
   by rewrite Pr [mu_sub] /#.
  smt(mu_bounded).
 by rewrite -(Hfl _pin _sin &m (r',l') _) /pred1 //= /#.
rewrite (HdI (pred1 r) _ _ &m).
rewrite (HdR (pred1 (r,l)) _ _ &m) //.
rewrite (HdR (fun xy:_*_=>xy.`2=l) _ _ &m) //.
rewrite {1}EdR dprod1E.
rewrite EdR (dprodE predT (pred1 l)) /dleak.
have ->: weight (dI pin sin') = 1%r.
 rewrite -(HdI predT _ _ &m).
 by apply JI_ll.
done.
qed.


(** Moreover, we get an equivalence from CT to
  a (apparently) more general definition CTplus where
  the "dummy call" on the left-hand side is
  called with arbitrary secret inputs.       *)
lemma CT_CTplus:
 (* CT *)
 equiv [ RSim(JI,JR).main ~ SimR(JI,JR).main
       : ={pin, sin, glob JR} ==> ={res, glob JR} ]
 <=>
 (* CTplus *)
 equiv [ RSim'(JI,JR).main ~ SimR(JI,JR).main
       : ={pin, sin, glob JR} ==> ={res, glob JR} ].
proof.
split.
 move=> CT; have ct:= CT_ct CT.
 move: CT; rewrite CT_pr CTplus_pr.
 move => CT pin sin sin1' sin2' &m rl.
 rewrite (ct_pr_term ct _ _ sin).
 by apply CT.
rewrite CT_pr CTplus_pr => CTplus pin sin sin' &m rl.
by apply CTplus.
qed.

(** Of course, non-interference (which is often
  trivial to establish) allows us to simplify CT
  by factoring out the "independence on secret
  inputs". *)
lemma ct_CC_CT:
 (* ct *)
 equiv [ JR.main ~ JR.main
       : ={pin, glob JR} ==> ={glob JR} ]
 /\
 (* CC *)
 equiv [ RSim(JI,JR).main ~ CC(JI,JR).main
       : ={pin, sin, glob JR}
         ==> ={res, glob JR} ]
 <=>
 (* CT *)
 equiv [ RSim(JI,JR).main ~ SimR(JI,JR).main
       : ={pin, sin, glob JR}
         ==> ={res, glob JR} ].
proof.
split.
 (* ct /\ CC => CT *)
 move => [ct_JR CC_J].
 transitivity CC(JI,JR).main
  ( ={pin, sin, glob JR} ==> ={res, glob JR} )
  ( ={pin, sin, glob JR} ==> ={res, glob JR} ) => //.
  move=> /> &1 &2 -> ->.
  by exists (glob JR){2} (pin,sin){2} => /#.
 proc.
 call (:true).
 call ct_JR.
 by auto => /> &1 &2; apply stateless_JI.
(* CT => ct /\ CC *)
move=> CT_J; rewrite -andaE; split.
 by apply CT_ct.
(* CT /\ ct => CC *)
move=> ct_J.
transitivity SimR(JI,JR).main
 (={pin, sin, glob JR} ==> ={res, glob JR})
 (={pin, sin, glob JR} ==> ={res, glob JR}) => //.
 by move => /> &1 &2 -> ->; exists (glob JR){2} (pin{2},sin{2},witness) => /#.
proc.
call (:true).
call ct_J; auto => />.
smt(stateless_JI).
qed.


(* DETERMINISTIC FUNCTIONALITIES

  Moreover, if we exclude the non-determinism
  from the functionalities, we recover back the
  standard non-interference characterisation of
  constant-time.

  Notice that here we adopt a notion of determinism
  which is fairly weak:
    1) it does not entail termination (uses partiall HL triples)
    2) it only concerns the functionality (is independent of the leakage)

  This makes it easier to prove (e.g. by resorting to
  established correctness lemmas), or to be handled
  by some externally trusted annotation (e.g. established
  by a simple type system -- notice that sources of
  non-determinism in Jasmin are fairly restricted). Notice that the burden on statically check
  non-determinism is much lower that full termination (safety) check.
 *)
lemma JI_det f _pin _sin:
 (* det *)
 hoare [ JI.main : pin=_pin /\ sin=_sin ==> res = f _pin _sin ]
 =>
 forall &m r,
   Pr[JI.main(_pin, _sin) @ &m : res = r ]
   = Pr[JI.main(_pin, _sin) @ &m : r = f _pin _sin ].
proof.
move => Hdet &m r.
byequiv (: ={pin,sin} /\ pin{2}=_pin /\ sin{2}=_sin ==> _) => //.
conseq (: ={pin, sin} ==> true)
       (: pin=_pin /\ sin=_sin ==> res = f _pin _sin)
       _ => //=.
by sim; smt(stateless_JI).
qed.

lemma JR_det f _pin _sin:
 (* det *)
 hoare [ JI.main : pin=_pin /\ sin=_sin ==> res = f _pin _sin ]
 =>
 forall &m l,
   Pr[JR.main(_pin, _sin) @ &m : (glob JR) = l]
   = Pr[JR.main(_pin, _sin) @ &m : (res,glob JR) = (f _pin _sin, l) ].
proof.
move => Hdet &m rl.
rewrite eq_sym.
byequiv (: ={pin,sin,glob JR} /\ pin{2}=_pin /\ sin{2}=_sin ==> _) => //.
conseq (: ={pin, sin, glob JR} ==> ={glob JR})
       (: pin=_pin /\ sin=_sin  ==> res = f _pin _sin)
       _ => //=.
 by conseq proj_JR_JI Hdet => /> /#.
by sim => /> *; apply stateless_J.
qed.


lemma ct_det_CT:
 (* ct *)
 equiv [ JR.main ~ JR.main
       : ={pin, glob JR} ==> ={glob JR} ]
 (* det *)
 =>
 (exists f, forall _pin _sin,
   hoare [ JI.main : pin=_pin /\ sin=_sin ==> res = f _pin _sin ])
 (* CT *)
 => 
 equiv [ RSim(JI,JR).main ~ SimR(JI,JR).main
       : ={pin, sin, glob JR} ==> ={res, glob JR} ].
proof.
rewrite CT_pr ct_pr => ct_j [f Hf] pin sin sin' &m rl.
move: (Hf pin sin) => {Hf} Hf.
case: (rl.`1 = f pin sin) => E.
 rewrite (JI_det _ _ _ Hf &m) E /=; congr.
 by rewrite -(ct_j pin sin sin' &m) (JR_det _ _ _ Hf &m) -E /#.
rewrite (JI_det _ _ _ Hf &m) E Pr [mu_false] /=.
have ?: Pr[JR.main(pin, sin) @ &m : res = rl.`1] = 0%r.
 rewrite -(JI_JR_prE (pred1 rl.`1) &m) /pred1 /= (JI_det _ _ _ Hf &m).
 by rewrite E Pr [mu_false].
have ->//: Pr[JR.main(pin, sin) @ &m : (res,glob JR)=rl] = 0%r.
apply (eq_trans _ Pr[JR.main(pin, sin) @ &m : res = rl.`1 /\ (glob JR) = rl.`2]). 
 smt(mu_sub).
smt(mu_sub mu_bounded).
qed.

(** In most cases, the pattern of non-termination
  is fully determined by public inputs. In that case,
  we get a simpler (and much more intuitive) definition of CT.
*)

lemma pinll_pr:
 (* pinll *)
 (exists f_ll, forall _pin,
  phoare [JI.main : pin=_pin ==> true ] = (b2r (f_ll _pin)))
 <=>
 exists (pin_ll: pin_t -> bool), forall pin sin &m, Pr[ JI.main(pin, sin) @ &m : true ] = (b2r (pin_ll pin)).
proof.
split; move=> [fpinll Hpinll]; exists fpinll.
 by move => pin sin &m; byphoare (Hpinll pin). 
move=> pin.
by bypr => /#.
qed.

lemma pinll_RSim:
 (* pinll *)
 (exists f_ll, forall _pin,
  phoare [JI.main : pin=_pin ==> true ] = (b2r (f_ll _pin)))
 =>
 equiv [ RSim(JI,JR).main ~ JR.main
       : ={pin, sin, glob JR} ==> ={res, glob JR} ].
proof.
move => /pinll_pr [fll Hll].
bypr (res,glob JR){1} (res,glob JR){2} => //.
move => /> &1 &2 rl -> -> Eg.
rewrite RSim_pr Hll.
case: (fll pin{2}) => //= C.
 by rewrite (JR_pr_m_m' (pred1 rl) &1 &2) //.
move: (Hll pin{2} sin{2} &2); rewrite C b2r0.
rewrite (JI_JR_prE predT).
smt(mu_sub mu_bounded).
qed.

lemma pinll_CT:
 (* pinll *)
 (exists f_ll, forall _pin,
  phoare [JI.main : pin=_pin ==> true ] = (b2r (f_ll _pin))) =>
 (* CT *)
 equiv [ RSim(JI,JR).main ~ SimR(JI,JR).main
       : ={pin, sin, glob JR} ==> ={res, glob JR} ] =>
 (* CT' *)
 equiv [ JR.main ~ SimR(JI,JR).main
       : ={pin, sin, glob JR} ==> ={res, glob JR} ].
proof.
move=> pinll CT.
transitivity RSim(JI, JR).main
 ( ={pin, sin, glob JR} ==> ={res, glob JR} )
 ( ={pin, sin, glob JR} ==> ={res, glob JR} ) => //.
+ by move=> /> &1 &2 -> ->; exists (glob JR){2} (pin,sin){2}.
+ by symmetry; conseq (pinll_RSim pinll) => /#.
qed.

(* a specialization of the previous lemma for
 lossless procedures... *)
lemma ll_CT:
 (* ll *)
 islossless JI.main =>
 (* CT *)
 equiv [ RSim(JI,JR).main ~ SimR(JI,JR).main
       : ={pin, sin, glob JR} ==> ={res, glob JR} ] =>
 (* CT' *)
 equiv [ JR.main ~ SimR(JI,JR).main
       : ={pin, sin, glob JR} ==> ={res, glob JR} ].
proof.
move=> ll CT.
apply pinll_CT => //.
exists (fun _ => true) => //= ?.
by conseq ll.
qed.


(* Combining previously established results we
 get what is perhaps simpler path to establish
 CT for non-deterministic programs (in most common
 cases).

   1 - establish termination;
   2 - prove standard non-interference
   3 - establish Coupled-Composition
        ( r <@ fR  ~  _ <@ fR; r <@ fI )
 *)
lemma pinll_ct_CC_CT:
 (* pinll *)
 (exists f_ll, forall _pin,
  phoare [JI.main : pin=_pin ==> true ] = (b2r (f_ll _pin)))
 =>
 (* ct *)
 equiv [ JR.main ~ JR.main
       : ={pin, glob JR} ==> ={glob JR} ]
 /\
 (* CC *)
 equiv [ JR.main ~ CC(JI,JR).main
       : ={pin, sin, glob JR}
         ==> ={res, glob JR} ]
 <=> 
 (* CT *)
 equiv [ RSim(JI,JR).main ~ SimR(JI,JR).main
       : ={pin, sin, glob JR} ==> ={res, glob JR} ].
proof.
move => pinll; split.
 move=> [ct CC].
 rewrite -ct_CC_CT; split => //.
 transitivity JR.main
   (={pin, sin, glob JR} ==> ={res, glob JR})
   (={pin, sin, glob JR} ==> ={res, glob JR}) => //.
  by move => /> &1 &2 -> ->; exists (glob JR){2} (pin,sin){2} => /#.
 by apply pinll_RSim.
rewrite -ct_CC_CT; move => [ct SC]; split => //.
transitivity RSim(JI, JR).main
   (={pin, sin, glob JR} ==> ={res, glob JR})
   (={pin, sin, glob JR} ==> ={res, glob JR}) => //.
 by move => /> &1 &2 -> ->; exists (glob JR){2} (pin,sin){2} => /#.
by symmetry; conseq (pinll_RSim pinll) => /#.
qed.

end section.

end CT_Meta.

(** We now address compositionality (the secret output
 of one function is passed to the secret inputs of
 some other function. For this, we critically rely
 on the strong (equivalent) variant of CT (what we
 have called CT').                                 *)
theory CT_Comp.

type pin1_t, pin2_t, sin1_t, sin2_t, out1_t, out2_t.

clone CT_Meta as F1
 with type pin_t <- pin1_t,
      type sin_t <- sin1_t,
      type out_t <- out1_t.

clone CT_Meta as F2
 with type pin_t <- pin2_t,
      type sin_t <- out1_t * sin2_t,
      type out_t <- out2_t.

type pin_t = pin1_t * pin2_t.
type sin_t = sin1_t * sin2_t.
clone CT_Meta as F
 with type pin_t <- pin_t,
      type sin_t <- sin_t,
      type out_t <- out2_t.

(* we need to combine the two procs, otherwise,
 we... *)
module type Jasmin2ProcWrapper = {
 proc f1(pin: pin1_t, sin: sin1_t): out1_t
 proc f2(pin: pin2_t, sin: out1_t*sin2_t): out2_t
}.

module Proc1 (J: Jasmin2ProcWrapper): F1.JasminProcWrapper = {
 proc main = J.f1
}.

module Proc2 (J: Jasmin2ProcWrapper): F2.JasminProcWrapper = {
 proc main = J.f2
}.

module FComp (J1: F1.JasminProcWrapper)(J2: F2.JasminProcWrapper): F.JasminProcWrapper = {
 proc main(pin: pin_t, sin: sin_t): out2_t = {
  var pin1, pin2, sin1, sin2, r1, r2;
  (pin1, pin2) <- pin;
  (sin1, sin2) <- sin;
  r1 <@ J1.main(pin1, sin1);
  r2 <@ J2.main(pin2, (r1,sin2));
  return r2;
 }
}.

section.

declare module JR <: Jasmin2ProcWrapper.
module JR1 = Proc1(JR).
module JR2 = Proc2(JR).
(*
declare module JR1 <: F1.JasminProcWrapper.
declare module JR2 <: F2.JasminProcWrapper {-JR1}.
(*obs: doesn't work!!!
(* A note about (glob JR1) and (glob JR2): These modules
 are expected to accumulate the leakage in a global variable.
 Hence, they share the state. This justifies why we
 shall only look at (glob JR2), and add the
 axiom [globJR_eq] establishing their equality. Again,
 this axiom can be easily discharged during instantiation. *) 
declare axiom globJR_eq &1 &2:
 (glob JR1){1}=(glob JR1){2} <=> (glob JR2){1}=(glob JR2){2}.
*)
*)

declare module JI1 <: F1.JasminProcWrapper {-JR}.
declare module JI2 <: F2.JasminProcWrapper {-JI1, -JR}.

declare axiom stateless_JI1 &m x: (glob JI1){m} = x.
declare axiom stateless_JI2 &m x: (glob JI2){m} = x.
declare axiom proj_JR_JI1:
 equiv [ JR1.main ~ JI1.main
       : ={pin, sin} ==> ={res} ].
declare axiom proj_JR_JI2:
 equiv [ JR2.main ~ JI2.main
       : ={pin, sin} ==> ={res} ].
declare axiom prMuE1 P pin sin &m:
 Pr[ JR1.main(pin,sin) @ &m : P (res,glob JR1)]
 = RealSeries.sum (fun (x:_*_) => Pr [JR1.main(pin,sin) @ &m : P (res,glob JR1) /\ res=x.`1 /\ (glob JR1)=x.`2]).
declare axiom prMuE2 P pin sin &m:
 Pr[ JR2.main(pin,sin) @ &m : P (res,glob JR2)]
 = RealSeries.sum (fun (x:_*_) => Pr [JR2.main(pin,sin) @ &m : P (res,glob JR2) /\ res=x.`1 /\ (glob JR2)=x.`2]).

lemma Compositionality:
 (* CT *)
 equiv [ F1.RSim(JI1,JR1).main ~ F1.SimR(JI1,JR1).main
       : ={pin, sin, glob JR1} ==> ={res,glob JR1} ]
 =>
 (* CT *)
 equiv [ F2.RSim(JI2,JR2).main ~ F2.SimR(JI2,JR2).main
       : ={pin, sin, glob JR2} ==> ={res,glob JR2} ]
 =>
 (* CT *)
 equiv [ F.RSim(FComp(JI1,JI2),FComp(JR1,JR2)).main ~ F.SimR(FComp(JI1,JI2),FComp(JR1,JR2)).main
       : ={pin, sin, glob FComp(JR1,JR2)} ==> ={res,glob FComp(JR1,JR2)} ].
proof.
rewrite (F1.CT_CTplus JR1 JI1 stateless_JI1 proj_JR_JI1 prMuE1) => CT1.
rewrite (F2.CT_CTplus JR2 JI2 stateless_JI2 proj_JR_JI2 prMuE2) => CT2.
proc*; simplify.
inline F.RSim(FComp(JI1, JI2), FComp(JR1, JR2)).main.
inline FComp(JI1, JI2).main FComp(JR1, JR2).main.
transitivity {1}
 { pin10 <- pin.`1;
   pin2 <- pin.`2;
   sin10 <- sin.`1;
   sin2 <- sin.`2;
   r10 <@ JI1.main(pin10, sin10);
   r1 <@ JR1.main(pin10, sin10);
   r <@ F2.RSim'(JI2,JR2).main(pin2,(r1,sin2),(r10,sin2)); }
 ( ={pin, sin, glob JR2, glob JR1} ==> ={r, glob JR2, glob JR1} )
 ( ={pin, sin, glob JR2, glob JR1} ==> ={r, glob JR2, glob JR1} ) => //.
+ by move=> /> &2; exists (glob JR){2} pin{2} sin{2} => //.
+ inline F2.RSim'(JI2, JR2).main.
  swap {2} 2 4.
  swap {2} 3 4.
  swap {2} 8 2.
  swap {2} [5..9] -1.
  swap {1} [10..13] -3.
  wp; call (: true).
  wp; call (: true).
  wp; call (: true).
  wp; call (: true).
  auto => /> *.
  smt(stateless_JI1 stateless_JI2).
inline F.SimR(FComp(JI1, JI2), FComp(JR1, JR2)).main.
inline FComp(JR1, JR2).main FComp(JI1, JI2).main.
swap {1} 2 1.
swap {1} [3..4] 2.
swap {2} [9..10] 5.
seq 4 13: (#pre /\ r1{1}=r10{2} /\ (pin2=pin.`2){2} /\ (pin20=pin.`2){2} /\ (sin2=sin'.`2){2} /\ (sin20=sin.`2){2}).
+ transitivity {1}
   { r1 <@ F1.RSim'(JI1, JR1).main(pin.`1,sin.`1, sin.`1); }
   ( ={pin, sin, glob JR2, glob JR1}
     ==> ={pin, sin, glob JR2, glob JR1, r1} )
   ( ={pin, sin, glob JR2, glob JR1}
     ==> ={pin, sin, glob JR2, glob JR1} /\
        r1{1} = r10{2} /\ pin2{2} = pin{2}.`2 /\ sin2{2} = sin'{2}.`2 /\
        pin20{2} = pin{2}.`2 /\ sin20{2} = sin{2}.`2) => //.
  - by move => /> &2; exists (glob JR){2} pin{2} sin{2}.
  - by inline *; sim; auto => />; smt(stateless_JI1).
  transitivity {2}
   { r10 <@ F1.SimR(JI1,JR1).main(pin.`1,sin.`1,sin'.`1); }
   ( ={pin, sin, glob JR2, glob JR1}
     ==> ={pin, sin, glob JR2, glob JR1} /\ r1{1}=r10{2} )
   ( ={pin, sin, sin', glob JR2, glob JR1}
     ==> ={pin, sin, glob JR2, glob JR1, r10} /\
        pin2{2} = pin{2}.`2 /\ sin2{2} = sin'{2}.`2 /\
        pin20{2} = pin{2}.`2 /\ sin20{2} = sin{2}.`2)
 => //.
  - by move => /> &2; exists (glob JR){2} pin{2} sin{2} sin'{2}.
  - move => />.
  - by call CT1 => //.
  inline*.
  wp; call (: true).
  wp; call (: true).
  auto => /> *; smt(stateless_JI1).
transitivity {2}
 { r <@ F2.SimR(JI2,JR2).main(pin.`2,(r10,sin.`2), (r1,sin'.`2)); }
 ( ={pin, sin, glob JR2, glob JR1} /\ r1{1}=r10{2}
     ==> ={r, glob JR2, glob JR1} )
 ( ={pin, sin, sin', glob JR2, glob JR1, r1, r10} /\
   pin2{2} = pin{2}.`2 /\ sin2{2} = sin'{2}.`2 /\
   pin20{2} = pin{2}.`2 /\ sin20{2} = sin{2}.`2
   ==> ={glob JR2, glob JR1, r} ) => //.
- by move => /> &2; exists (glob JR){2} pin{2} r1{2} r10{2} sin{2} sin'{2}.
- by call CT2; auto => /> //.
inline*.
wp; call (: true).
wp; call (: true).
auto => /> *; smt(stateless_JI2).
qed.

end section.

end CT_Comp.


require import AllCore Distr.

(** pRHL characterisation  of leakage-freeness.

 Here we seek a characterisation of the leakage-free
 property in a pure probabilist Relational Hoare Logic
 formulation. The goal is to avoid handling explicitly
 the leakage, resorting instead to the EC's [sim]
 tactic.                                            *)


(** The setting:

 we consider a collection of Jasmin procedures that are
 extracted into EC in two modes ([XtrI] and [XtrR]).
 Each one of these is a module that includes the
 EC's model Jasmin-implemented functions:

  - XtrI.f - an EC proc. that models the input/output
      behaviour of Jasmin function [f] (hence, an
      abstract or Ideal setting).
  - XtrR.f - an EC proc.  that, in addition to the
      input/output behaviour, models also what is leaked
      during execution (accumulated in variable
      [XtrR.leakages]). This is what we call the
      concrete or Real setting.

 As a meta-property of the extraction mechanism, we
 have that the behaviour of [XtrI.f] is indeed given
 by the marginal probability of [XtrR.f] (when the
 leakage is ignored). In any case, this fact is
 typically provable automatically with the [sim]
 tactic.                                           *)

from Jasmin require import JModel.
require W64_SchnorrExtract.
require W64_SchnorrExtract_ct.

module XtrR = W64_SchnorrExtract_ct.M(W64_SchnorrExtract_ct.Syscall).
module XtrI = W64_SchnorrExtract.M(W64_SchnorrExtract.Syscall).

require import Array256 Array32 WArray256.


(** Leakage-freeness:

 The characterisation of leakage-freeness in the
 pRHL setting is roughly framed in the Simulation
 paradigm. Intuitively, we shall ask the Real-word
 [XtrR.f] to be simulated by the Ideal-word [XtrI.f]
 and a simulator that has only access to the public
 inputs of [f]. Moreover, we take the simulator to be
 constructed by running the "real" implementation
 itself with arbitrary secret inputs.

 Consider the module:

 module SimR = {
  proc f( pin: pin_t (*public inputs*)
        , sin sin': sin_t (*secret inputs*): out_t = {
    var r;
    r <@ XtrR.f(pin, sin');
    r <@ XtrI.f(pin, sin);
    return r;
  }
 }.

 The leakage-freeness property thus becomes:

 f_CT:
  equiv [ XtrR.f ~ SimR.f
        : ={pin, sin, XtrR.leakages} 
          ==> ={res, XtrR.leakages}.

*)

module SimR = {
 proc randombytes_256(a a' (* ?secret? *): W8.t Array256.t): W8.t Array256.t = {
  var r;
  r <@  W64_SchnorrExtract_ct.Syscall.randombytes_256(a');
  r <@  W64_SchnorrExtract.Syscall.randombytes_256(a);
  return r;
 }
 proc bn_subc( a a' (*secret *): W64.t Array32.t
             , b b' (*secret *): W64.t Array32.t) = {
   var r;
   r <@ XtrR.bn_subc(a', b');
   r <@ XtrI.bn_subc(a, b);
   return r;
 }
 proc bn_rsample(byte_z (*public *): W64.t Array32.t) = {
   var r;
   r <@ XtrR.bn_rsample(byte_z);
   r <@ XtrI.bn_rsample(byte_z);
   return r;
 }
}.

require import DList.
lemma randombytes_256_CT:
 equiv [ W64_SchnorrExtract_ct.Syscall.randombytes_256
         ~ SimR.randombytes_256
       : ={a, glob XtrR}
         ==> ={res, glob XtrR}
       ].
proof.
(* this is currently provable, but not sure if it should be assumed
 as an ASSUMPTION (should system-calls leak?) *)
proc; inline*; simplify.
wp; rnd; auto => />.
apply dmap_ll.
apply dmap_ll.
apply dlist_ll.
by apply W8.dword_ll.
qed.

(** The Jasmin's standard "constant-time" property
 establishes the independence of leakage wrt to the
 secret inputs \footnote{actually, the name was
 coined when the Jasmin language had no support for
 non-deterministic constructs -- we keep it for
 convenience.}.

 f_ct:
  equiv [ XtrR.f ~ XtrR.f
        : ={pin, XtrR.leakages} ==> ={XtrR.leakages} ]

 where [pin] are the public inputs of [f].

 Clearly, this property is a simple consequence of
 the [f_CT] property stated above. However, to some
 extent, the other direction is more insteresting, as
 the [f_ct] property is typically established fully
 automatically (resorting to the [sim] tactic). Hence,
 we observe that, in order to establish the [f_CT]
 property from the [f_ct] property, we are left with
 a slightly simpler version of [f_CT] that resembles
 a kind of Self-Composition:

 module SelfCompR = {
  proc f( pin: pin_t (*public inputs*)
        , sin: sin_t (*secret inputs*): out_t = {
    var r;
    r <@ XtrR.f(pin, sin);
    r <@ XtrI.f(pin, sin);
    return r;
  }
 }.

 f_SC:
  equiv [ XtrR.f ~ SelfCompR.f
        : ={pin, sin, XtrR.leakages} 
          ==> ={res, XtrR.leakages}.

 Intuively, [f_SC] does not bother in calling the
 "simulator" with dummy secret inputs. 
*)

module SelfCompR = {
 proc randombytes_256(a: W8.t Array256.t): W8.t Array256.t = {
  var r;
  r <@  W64_SchnorrExtract_ct.Syscall.randombytes_256(a);
  r <@  W64_SchnorrExtract.Syscall.randombytes_256(a);
  return r;
 }
 proc bn_subc( a b: W64.t Array32.t) = {
   var r;
   r <@ XtrR.bn_subc(a, b);
   r <@ XtrI.bn_subc(a, b);
   return r;
 }
 proc bn_rsample(byte_z: W64.t Array32.t) = {
   var r;
   r <@ XtrR.bn_rsample(byte_z);
   r <@ XtrI.bn_rsample(byte_z);
   return r;
 }
}.

(* we illustrate the previously mentioned observations
  by instantiating them in with the [bn_subc] function. *)
lemma bn_subc_ct_from_CT:
 equiv [ XtrR.bn_subc ~ SimR.bn_subc
       : ={a, b, XtrR.leakages} ==> ={res, XtrR.leakages} ] =>
 equiv [ XtrR.bn_subc ~ XtrR.bn_subc
       : ={XtrR.leakages} ==> ={XtrR.leakages} ].
proof.
move=> H_CT.
proc*.
transitivity{1} { r <@ SimR.bn_subc(a,a,b,b); }
 ( ={a, b, XtrR.leakages} ==> ={r,XtrR.leakages} )
 ( ={XtrR.leakages} ==> ={XtrR.leakages} ) => //.
  move => /> &1 &2.
  exists XtrR.leakages{2} a{1} b{1} => />.
 by call H_CT.
inline SimR.bn_subc.
wp; call{1} (: true ==> true).
 (* XtrI_bn_subc_ll *)
 proc; wp; while (0 < i <= 32) (32-i).
  by move=> z; auto => /> * /#.
 by auto => /> * /#.
by inline*; sim.
qed.

lemma bn_subc_CT_from_ct_and_SC:
 equiv [ XtrR.bn_subc ~ XtrR.bn_subc
       : ={XtrR.leakages} ==> ={XtrR.leakages} ] =>
 equiv [ XtrR.bn_subc ~ SelfCompR.bn_subc
       : ={a, b, XtrR.leakages} ==> ={res, XtrR.leakages} ] =>
 equiv [ XtrR.bn_subc ~ SimR.bn_subc
       : ={a, b, XtrR.leakages} ==> ={res, XtrR.leakages} ].
proof.
move=> H_ct H_SC.
transitivity SelfCompR.bn_subc
 ( ={a, b, XtrR.leakages} ==> ={res, XtrR.leakages} )
 ( ={a, b, XtrR.leakages} ==> ={res, XtrR.leakages} ) => //.
 move => /> &1 &2 -> ->.
 by exists XtrR.leakages{2} (a{2},b{2}); auto.
proc; simplify.
call (: true); first by sim.
by call H_ct; auto.
qed.


(* in the case of [bn_rsample], this degenerate in
 trivial observations, as there are no secret
 inputs (just shown in one direction).                 *)
lemma bn_rsample_CT_from_ct_and_SC:
 equiv [ XtrR.bn_rsample ~ XtrR.bn_rsample
       : ={byte_z, XtrR.leakages} ==> ={XtrR.leakages} ] =>
 equiv [ XtrR.bn_rsample ~ SelfCompR.bn_rsample
       : ={byte_z, XtrR.leakages} ==> ={res, XtrR.leakages} ] =>
 equiv [ XtrR.bn_rsample ~ SimR.bn_rsample
       : ={byte_z, XtrR.leakages} ==> ={res, XtrR.leakages} ].
proof.
move=> H_ct H_SC.
transitivity SelfCompR.bn_rsample
 ( ={byte_z, XtrR.leakages} ==> ={res, XtrR.leakages} )
 ( ={byte_z, XtrR.leakages} ==> ={res, XtrR.leakages} ) => //.
 by move => /> &2; exists XtrR.leakages{2} arg{2}; auto.
by sim.
qed.



(** The case of deterministic functionalities.
    ==========================================

 When [XtrI.f] is deterministic, the property of
 leakage-freeness ([f_CT] presented above) follows
 from the much simpler property [f_ct], that is,
 [f_SC] is a consequence of determinism of [f].

 Again, we illustrate the constructions and results
 with [bn_subc] function.                              *)

(* a (trivial to prove) meta-property of the
 extraction mechanism                            *)
lemma bn_subc_Iproj:
 equiv [ XtrI.bn_subc
         ~ XtrR.bn_subc
       : ={a,b} ==> ={res} ].
proof. by proc; sim. qed.

(* this is the (standard) constant-time characterisation *)
lemma bn_subc_ct : 
 equiv [ XtrR.bn_subc
         ~ XtrR.bn_subc
       : ={XtrR.leakages} ==> ={XtrR.leakages} ].
proof. by proc; sim. qed.

(* determinism of a jasmin program *)
lemma bn_subc_det:
 exists (f: W64.t Array32.t *  W64.t Array32.t ->  bool * W64.t Array32.t),
 forall _a _b,
 phoare [ XtrI.bn_subc
        : a=_a /\ b=_b ==> res = f (_a, _b) ] = 1%r.
proof.
(* this follows from correctness of [bn_subc] *)
admitted.

(* some consequences of determinism (obs: probably,
 some of them are redundant -- just added when their
 need was felt...)                                 *)

lemma bn_subc_det_ph:
 forall (f: W64.t Array32.t * W64.t Array32.t ->  bool * W64.t Array32.t),
 (forall _a _b,
  phoare [ XtrI.bn_subc
        : a=_a /\ b=_b ==> res = f (_a, _b) ] = 1%r)
 =>
 forall _a _b,
 phoare [ XtrR.bn_subc
        : a=_a /\ b=_b ==> res = f (_a, _b) ] = 1%r.
proof.
move=> fsubc Hdet _a _b.
bypr => &m [-> ->].
have <-: Pr[XtrI.bn_subc(_a, _b) @ &m : res = fsubc (_a, _b)] 
         = Pr[XtrR.bn_subc(_a, _b) @ &m : res = fsubc (_a, _b)].
 by byequiv bn_subc_Iproj.
byphoare (: a=_a /\ b=_b ==> _) => //.
by apply (Hdet _a _b).
qed.

lemma bn_subc_det_h:
 forall (f: W64.t Array32.t * W64.t Array32.t ->  bool * W64.t Array32.t),
 (forall _a _b,
  phoare [ XtrI.bn_subc
         : a=_a /\ b=_b ==> res = f (_a, _b) ] = 1%r)
 => 
 forall _a _b,
 hoare [ XtrR.bn_subc: a=_a /\ b=_b ==> res = f (_a, _b) ].
proof.
move=> fsubc Hfsubc _a _b.
bypr => &m [-> ->].
rewrite Pr [mu_not].
have ->: Pr[XtrR.bn_subc(_a, _b) @ &m : true] = 1%r.
 (* bn_subc_ll *)
 byphoare (: true ==> true) => //=.
 proc; wp; while (0 < i <= 32) (32-i).
  by move=> z; auto => /> * /#.
 by auto => /> * /#.
have ->: Pr[XtrR.bn_subc(_a, _b) @ &m : res = fsubc (_a, _b)] = 1%r.
 by byphoare (bn_subc_det_ph fsubc Hfsubc _a _b).
done.
qed.

lemma bn_subc_det_pr:
 forall (f: W64.t Array32.t * W64.t Array32.t ->  bool * W64.t Array32.t),
 (forall _a _b,
  phoare [ XtrI.bn_subc
         : a=_a /\ b=_b ==> res = f (_a, _b) ] = 1%r)
 => 
 forall _a _b _l &m,
 Pr[ XtrR.bn_subc(_a,_b) @ &m: res = f (_a, _b) /\ XtrR.leakages = _l]
 = Pr[ XtrR.bn_subc(_a,_b) @ &m: XtrR.leakages = _l].
proof.
move=> fsubc Hfsubc _a _b _l &m.
rewrite eq_sym Pr [mu_split (res = fsubc (_a, _b))] andbC; ring.
byphoare (: a=_a /\ b=_b ==> _) => //.
hoare.
by conseq (bn_subc_det_h fsubc Hfsubc _a _b) => /> *.
qed.

lemma bn_subc_det_eq:
 forall (f: W64.t Array32.t * W64.t Array32.t ->  bool * W64.t Array32.t),
 (forall _a _b,
  phoare [ XtrI.bn_subc
        : a=_a /\ b=_b ==> res = f (_a, _b) ] = 1%r)
 =>
 forall _a _b,
 equiv [ XtrR.bn_subc ~ XtrR.bn_subc
       : a{2}=_a /\ b{2}=_b /\ ={a,b,XtrR.leakages} ==> ={res, XtrR.leakages} /\ res{2} = f (_a, _b)  ].
proof.
move=> fsubc Hfsubc _a _b.
conseq (: ={XtrR.leakages} ==> ={XtrR.leakages}) (: a=_a /\ b=_b ==> res = fsubc (_a, _b)) (: a=_a /\ b=_b ==> res = fsubc (_a, _b)) => //.
  by apply (bn_subc_det_h fsubc Hfsubc _a _b).
 by apply (bn_subc_det_h fsubc Hfsubc _a _b).
by apply bn_subc_ct.
qed.

(** We can now state self-composition property [bn_subc_SC]
 as a consequence of [bn_subc_det], from which the
 [bn_subc_CT] property is derived.                       *)
lemma bn_subc_SC:
 equiv [ XtrR.bn_subc
         ~ SelfCompR.bn_subc
       : ={a, b, glob XtrR}
         ==> ={res, glob XtrR}
       ].
proof.
proc*; simplify; inline SelfCompR.bn_subc.
have [fsubc Hfsubc] := bn_subc_det.
wp; ecall{2} (Hfsubc a0{2} b0{2}).
exlim a{2}, b{2} => _a _b.
have HH:= bn_subc_det_eq fsubc _ _a _b.
 by apply Hfsubc.
by call HH; auto => /> &2.
qed.

lemma bn_subc_CT:
 equiv [ XtrR.bn_subc
         ~ SimR.bn_subc
       : ={a, b, glob XtrR}
         ==> ={res, glob XtrR}
       ].
proof.
apply bn_subc_CT_from_ct_and_SC.
 by apply bn_subc_ct.
by apply bn_subc_SC.
qed.

(* REMARK: we one finds that going through the [f_SC]
 property is an unnecessary detour, we can go directly
 from [f_ct] and [f_det] into [f_CT]...           *)
lemma bn_subc_det_eq':
 forall (f: W64.t Array32.t * W64.t Array32.t ->  bool * W64.t Array32.t),
 (forall _a _b,
  phoare [ XtrI.bn_subc
        : a=_a /\ b=_b ==> res = f (_a, _b) ] = 1%r)
 =>
 forall _a _a' _b _b',
 equiv [ XtrR.bn_subc ~ XtrR.bn_subc
       : a{1}=_a /\ a{2}=_a' /\ b{1}=_b /\ b{2}=_b' /\ ={XtrR.leakages} ==> ={XtrR.leakages} /\ res{1} = f (_a, _b) /\ res{2} = f (_a', _b') ].
proof.
move=> fsubc Hfsubc _a _a' _b _b'.
conseq (: ={XtrR.leakages} ==> ={XtrR.leakages}) (: a=_a /\ b=_b ==> res = fsubc (_a, _b)) (: a=_a' /\ b=_b' ==> res = fsubc (_a', _b')) => //.
  by apply (bn_subc_det_h fsubc Hfsubc _a _b).
 by apply (bn_subc_det_h fsubc Hfsubc _a' _b').
by apply bn_subc_ct.
qed.

lemma bn_subc_CT':
 equiv [ XtrR.bn_subc
         ~ SimR.bn_subc
       : ={a, b, glob XtrR}
         ==> ={res, glob XtrR}
       ].
proof.
proc*; simplify; inline SimR.bn_subc.
have [fsubc Hfsubc] := bn_subc_det.
wp; ecall{2} (Hfsubc a0{2} b0{2}).
exlim a{2}, a'{2}, b{2}, b'{2} => _a _a' _b _b'.
have HH:= bn_subc_det_eq' fsubc _ _a _a' _b _b'.
 by apply Hfsubc.
by call HH; auto => /> &2.
qed.


(*

  Now, we want to move towards the proof of the
 leakage-freeness property of [bn_rsample]. Following
 the previous discussion, we build on the [bn_rsample_ct]
 property which is trivial to prove.                     *)

lemma bn_rsample_ct:
 equiv [ XtrR.bn_rsample
         ~ XtrR.bn_rsample
       : ={byte_z, XtrR.leakages} ==> ={XtrR.leakages}
       ].
proof. by proc; sim. qed.

lemma bn_rsample_CT_from_SC:
 equiv [ XtrR.bn_rsample
         ~ SelfCompR.bn_rsample
       : ={byte_z, XtrR.leakages}
         ==> ={res, XtrR.leakages} ] =>
 equiv [ XtrR.bn_rsample
         ~ SimR.bn_rsample
       : ={byte_z, XtrR.leakages}
         ==> ={res, XtrR.leakages}
       ].
proof.
apply bn_rsample_CT_from_ct_and_SC.
by apply bn_rsample_ct.
qed.

(*

 In order to prove [bn_rsample_SC], we need to decouple
 the computation of results from the generation of the
 leakage. To do so, we start by spliting a sample
 from [0..R-1] through the probability of a given event.
 Specifically, we shall transform the rejection loop
 as follows:

  ...
  x <$ dR;	  (* [0..R-1] *) 
  b <- pred_ev x; (* acceptance criteria *)
  while (!b) {
    ...
    x <$ dR; 
    b <- pred_ev x;
  }
  return x;

  into:

  ...
  b <$ dbiased (mu dR pred_ev);
  x <$ if b then dcond dR pred_ev
            else dcond dR (predC pred_ev);
  while (!b) {
    ...
    b <$ dbiased (mu dR pred_ev);
    x <$ if b then dcond dR pred_ev
              else dcond dR (predC pred_ev);
  }


  REMARK: notice that the above discussion critically
  depends on the determinism of [bn_subc] (as [pred_ev]
  is actually its functional description). In fact,
  in order to apply this transformation, one should
  previously rely on [bn_subc_CT] in order to recast
  the (leaky) evaluation of [bn_subc] into a pure
  function.
*)

require import DBool DProd.
import Biased.

abstract theory SampleEventSwap.

type in_t.
type out_t.

module SampleEvent = {
 proc sample(i: in_t, d: in_t -> out_t distr, P: out_t -> bool): out_t * bool = {
  var b, x;
  x <$ d i;
  b <- P x;
  return (x, b);
 }
 proc sampleEv(i: in_t, d: in_t -> out_t distr, P: out_t -> bool): out_t * bool = {
  var b, x;
  b <$ dbiased (mu (d i) P);
  x <$ if b then dcond (d i) P else dcond (d i) (predC P);
  return (x, b);
 }
}.


clone DLetSampling as LS with
 type t <- bool,
 type u <- out_t.

equiv sample_sampleEv:
 SampleEvent.sample ~ SampleEvent.sampleEv:
 ={i, d, P} /\ is_lossless (d i){2} 
 ==> ={res}.
proof.
proc; simplify; wp.
case: ((mu (d i) P){2}=0%r).
 seq 0 1: (#pre /\ !b{2}).
  rnd{2}; auto => /> &m Hll Hb; split; first by apply dbiased_ll.
  by move=> _ b; rewrite Hb dbiased0 supp_dunit.
 rnd; auto => /> &m Hll Hb0 Hb; split.
  move=> xR; rewrite dcond_supp; move=> [Hx1 Hx2].
  by rewrite dcond1E Hx2 /= mu_not Hll Hb0 /=.
 move => H xL Hx; split.
  by rewrite dcond_supp Hx /predC /=; apply (eq0_mu (d{m} i{m})).
 by rewrite dcond_supp Hx /predC /= /#.
case: ((mu (d i) P){2}=1%r).
 seq 0 1: (#pre /\ b{2}).
  rnd{2}; auto => /> &m Hll _ Hb; split; first by apply dbiased_ll.
  by move=> _ b; rewrite Hb dbiased1 supp_dunit.
 rnd; auto => /> &m Hll _ Hb1 Hb; split.
  move=> xR; rewrite dcond_supp; move=> [Hx1 Hx2].
  by rewrite dcond1E Hx2 Hb1.
 move => _ xL Hx; split.
  rewrite dcond_supp Hx /=; apply (mu_in_weight _ (d{m} i{m})) => //.
  by rewrite Hb1 Hll.
 by rewrite dcond_supp Hx /#.
transitivity{1} { x <@ LS.SampleDLet.sample(dbiased (mu (d i) P), fun b=> if b then dcond (d i) P else dcond (d i) (predC P)); }
 (={i,d,P} /\ is_lossless (d i){2} /\ 0%r < (mu (d i) P){2} < 1%r
  ==> ={x,i,d,P} /\ is_lossless (d i){2} /\ 0%r < (mu (d i) P){2} < 1%r)
 (={i,d,P} /\ is_lossless (d i){2} /\ 0%r < (mu (d i) P){2} < 1%r ==> ={x} /\ P{1} x{1}=b{2}) => //.
  by move=> /> &m Hll Hbias1 Hbias2; exists P{m} d{m} i{m}; smt(mu_bounded).
 inline*; auto => /> &m Hll Hbias1 Hbias2; split.
  move=> xR.
  by rewrite -marginal_sampling_pred //.
 move => H xL HxL.
 rewrite supp_dlet.
 case: (P{m} xL) => bL.
  exists true => /=.
  rewrite supp_dbiased 1:/#.
  by rewrite dcond_supp.
 exists false => /=.
 rewrite supp_dbiased 1:/#.
 by rewrite dcond_supp.
transitivity{1} { x <@ LS.SampleDep.sample(dbiased (mu (d i) P), fun b=> if b then dcond (d i) P else dcond (d i) (predC P)); }
 (={i,d,P} /\ 0%r < (mu (d i) P){2} < 1%r ==> ={x,i,d,P} /\ 0%r < (mu (d i) P){2} < 1%r)
 (={i,d,P} /\ 0%r < (mu (d i) P){2} < 1%r ==> ={x} /\ P{1} x{1}=b{2}) => //.
  by move=> /> &m Hll Hbias1 Hbias2; exists P{m} d{m} i{m}; auto.
 by symmetry; call LS.SampleDepDLet => //=.
inline*; auto => /> &m Hbias1 Hbias2 b Hb xL.
by case: (b) => Cb; rewrite dcond_supp /#.
qed.

end SampleEventSwap.

(*
  Then, we need to reshape the samplings in the
  RejectionLoop. Specifically, we transform:

  ...
  b <$ dbiased (mu dR pred_ev);
  x <$ if b then dcond dR pred_ev
            else dcond dR (predC pred_ev);
  while (!b) {
    ...
    b <$ dbiased (mu dR pred_ev);
    x <$ if b then dcond dR pred_ev
              else dcond dR (predC pred_ev);
  }

  into:

  ...
  b <$ dbiased (mu dR pred_ev);
            else dcond dR (predC pred_ev);
  while (!b) {
    x <$ dcond dR (predC pred_ev);
    ...
    b <$ dbiased (mu dR pred_ev);
  }
  x <$ dcond dR pred_ev;
  return x;

  We resort to EC's PROM library for this eager/lazy
  sampling rasoning.
*)


abstract theory RejectionLoop.

type t.
type in_t.

op dt: in_t -> t distr.
op p : t -> bool.


module type AdvLoop = {
  proc init(xin: in_t): unit
  proc body(x: t): unit
}.

module RejLoop(L:AdvLoop) = {
  proc loop1 (xin: in_t) = {
    var x, b;
    L.init(xin);
    x <$ dt xin;
    b <- p x;
    while (! b) {
      L.body(x);
      x <$ dt xin;
    }
    return x;
  }
  proc loop2 (xin: in_t) = {
    var x, b;
    L.init(xin);
    b <$ dbiased (mu (dt xin) p);
    while (!b) {
      x <$ dcond (dt xin) (predC p);
      L.body(x);
      b <$ dbiased (mu (dt xin) p);
    }
    x <$ dcond (dt xin) p;
    return x;
  }
}.



require import PROM SmtMap.

clone import PROM.FullRO as ROx with
    type in_t    <- in_t*bool,
    type out_t   <- t, 
    type d_in_t  <- in_t,
    type d_out_t <- t,
    op   dout    <- fun (y:_*_) => if y.`2
                                   then dcond (dt y.`1) p
                                   else dcond (dt y.`1) (predC p)
  proof *.

module RejLoop_D (L:AdvLoop) (O: RO) = {
 proc distinguish(xin: in_t): t = {
  var b, x;
  L.init(xin);
  b <$ dbiased (mu (dt xin) p);
  O.sample(xin,b);
  while (!b) {
    x <@ O.get(xin,b);
    O.rem(xin,b);
    L.body(x);
    b <$ dbiased (mu (dt xin) p);
    O.sample(xin,b);
  }
  x <@ O.get(xin,b);
  (* O.rem(xin,b); *)
  return x;
 }
}.

section.

declare module L <: AdvLoop {-RO, -LRO}.

module RejLoopD = RejLoop_D(L).


equiv loop1_loop2:
 RejLoop(L).loop1 ~ RejLoop(L).loop2:
 ={xin, glob L}
 ==> ={res, glob L}.
proof.
proc*.
transitivity{1}
 { RO.init();
   r <@ RejLoopD(RO).distinguish(xin); }
 ( ={xin, glob L} ==> ={xin, r, glob L} )
 ( ={xin, glob L} ==> ={r, glob L} ) => //.
+ by move=> /> &2; exists (glob L){2} xin{2} => />.
+ inline RejLoop(L).loop1 RejLoopD(RO).distinguish.
  inline RO.sample RO.get.
  seq 2 3: (={xin, xin0, glob L}).
   by call (: true); inline*; auto => />.
  seq 2 5: (={xin, xin0, b, glob L} /\ (RO.m.[(xin0,b)]){2}=Some x{1}).
   admit (*SampleEvSwap*).
  seq 1 1: (={xin, xin0, b, glob L} /\ !b{2} /\ (RO.m.[(xin0,b)]){2}=Some x{1}).
   admit (* loop *).
  wp; rnd{2}; auto => /> &1 &2 Hb Hm; split.
   admit (*ll*).
  move=> _ ?? />.
  have->/=: (xin0{2}, false) \in RO.m{2} by smt().
  by rewrite Hm /=.
transitivity{1}
 { LRO.init();
   r <@ RejLoopD(LRO).distinguish(xin); }
 ( ={xin, glob L} ==> ={xin, r, glob L} )
 ( ={xin, glob L} ==> ={r, glob L} ) => //.
+ by move=> /> &2; exists (glob L){2} xin{2} => />.
+ admit (* need to sort out module restrictions...
           (hopefully, without droping the RejLoop abstraction...)
  call (FullEager.RO_LRO_D RejLoopD).
  *).
inline RejLoop(L).loop2 RejLoopD(LRO).distinguish.
inline LRO.sample LRO.get.
admit.
qed.

end section.

print loop1_loop2.

end RejectionLoop.


(*
  Finally, we observe that the result of [bn_rsample]
  is now fully detached from the leakage generation,
  allowing us to establish the SC property:

  (* XtrR.bn_rsample *)
  ...
  b <$ dbiased (mu dR pred_ev);
            else dcond dR (predC pred_ev);
  while (!b) {
    x <$ dcond dR (predC pred_ev);
    ...
    b <$ dbiased (mu dR pred_ev);
  }
  x <$ dcond dR pred_ev;

  (* XtrI.bn_rsample *)
  x <$ dcond dR pred_ev;

  return x;
*)

(*...*)

(* The code of XtrR.bn_rsample:

  proc bn_rsample(byte_z : W64.t Array32.t) : int * W64.t Array32.t = {
    var aux_5 : bool;
    var aux_4 : bool;
    var aux_3 : bool;
    var aux_2 : bool;
    var aux_1 : bool;
    var aux : int;
    var aux_6 : W64.t;
    var aux_7 : W8.t Array256.t;
    var aux_0 : W64.t Array32.t;
    var i : int;
    var byte_p : W64.t Array32.t;
    var cf : bool;
    var _byte_p : W64.t Array32.t;
    var byte_q : W64.t Array32.t;
    var _0 : bool;
    var _1 : bool;
    var _2 : bool;
    var _3 : bool;
    var _4 : W64.t;
    
    _byte_p <- witness;
    byte_p <- witness;
    byte_q <- witness;
    M.leakages <- (LeakAddr [] :: M.leakages)%List;
    aux <- 0;
    i <- aux;
    M.leakages <- (LeakAddr [] :: M.leakages)%List;
    aux_0 <@ M(SC).bn_set0(byte_p);
    byte_p <- aux_0;
    M.leakages <- (LeakAddr [] :: M.leakages)%List;
    (aux_5, aux_4, aux_3, aux_2, aux_1, aux_6) <- set0_64_;
    _0 <- aux_5;
    cf <- aux_4;
    _1 <- aux_3;
    _2 <- aux_2;
    _3 <- aux_1;
    _4 <- aux_6;
    M.leakages <- (LeakCond (!cf) :: LeakAddr [] :: M.leakages)%List;
    while (!cf){
      M.leakages <- (LeakAddr [] :: M.leakages)%List;
      aux_0 <- byte_p;
      _byte_p <- aux_0;
      M.leakages <- (LeakAddr [] :: M.leakages)%List;
      aux_7 <@
        SC.randombytes_256((init (fun (i_0 : int) => get8 (init64 (fun (i_0_0 : int) => _byte_p.[i_0_0])) i_0))%Array256);
      byte_p <- (init (fun (i_0 : int) => get64 (init8 (fun (i_0_0 : int) => aux_7.[i_0_0])) i_0))%Array32;
      M.leakages <- (LeakAddr [] :: M.leakages)%List;
      aux_0 <@ M(SC).bn_copy(byte_p);
      byte_q <- aux_0;
      M.leakages <- (LeakAddr [] :: M.leakages)%List;
      (aux_5, aux_0) <@ M(SC).bn_subc(byte_q, byte_z);
      cf <- aux_5;
      byte_q <- aux_0;
      M.leakages <- (LeakAddr [] :: M.leakages)%List;
      aux <- i + 1;
      i <- aux;
      M.leakages <- (LeakCond (!cf) :: LeakAddr [] :: M.leakages)%List;
    }
    
    return (i, byte_p);
  }
*)


abstract theory Bn_subc_det.

op fsubc: W64.t Array32.t *  W64.t Array32.t ->  bool * W64.t Array32.t.

axiom subc_det _a _b:
 phoare [ XtrI.bn_subc
        : a=_a /\ b=_b ==> res = fsubc (_a, _b) ] = 1%r.


(*...*)

end Bn_subc_det.




(* TODO: link with low-level Defs. *)

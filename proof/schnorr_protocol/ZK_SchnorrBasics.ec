require import Int IntDiv  Real Distr StdOrder.


(* Embedding into ring theory *)
require import Ring_ops_spec.
require import Ring_ops_proof.
(* require ZModP. *)
(* clone import ZModP.ZModField as Zp *)
(*         rename "zmod" as "zp". *)

import Zp DZmodP.
import ZModpRing.

  (* TODO remove axioms or make this theory abstract *)
axiom p_val_prop1 x : W64xN.valR x < (p-1) * (p-1). 
axiom p_val_prop2 : 2*p < W64xN.modulusR. 

axiom exp_pow x n : x ^^ n = x ^^ (n %% (p-1)).
axiom exps (s : zp) c : Sub.val (s ^^ c) = ((Sub.val s) ^ c) %% p. 

op g : zp.   
axiom g_not_zero : g <> Zp.zero.
lemma g_unit : unit g.  smt(g_not_zero unitE). qed.


(* op g : zp. *)
import Ring.IntID IntOrder.



(* synonyms for readability  *)
type dl_stat = zp.           (* statement *)
type dl_wit  = int.          (* witness *)
type dl_com = zp.            (* commitment *)
type dl_resp = int.          (* response *)
type dl_chal = int.          (* challenge *)



(* the language of Schnorr protocol consists of discrete logarithms  *)

op IsDL (p : dl_stat) (w : dl_wit) : bool = g ^^ w = p.

op soundness_relation    = IsDL.
op completeness_relation = IsDL.
op zk_relation           = IsDL.


(* transcript verification for Honest Vrifier  *)
op verify_transcript (p : dl_stat) (x : dl_com * dl_chal * dl_resp) = 
 let (c,b,r) = x in (g ^^ r) = (p ^^ b) * c.
   
require GenericSigmaProtocol.
require import List .


(* instantiating generic definitions for Schnorr protocol  *)
clone include GenericSigmaProtocol with 
  type statement       <= dl_stat,
  type commitment      <= dl_com,  
  type witness         <= dl_wit,
  type response        <= dl_resp,
  type challenge       <= dl_chal,
  op challenge_set     <=  range 0 (p-1),
  op verify_transcript     <- verify_transcript,
  op soundness_relation    <- soundness_relation,
  op completeness_relation <- completeness_relation,
  op zk_relation           <- zk_relation.
  (* TODO proof* or make this theory abstract *)


(* Honest Prover *)
module HP : HonestProver = {
 var pa : dl_stat
 var wa : dl_wit
 var r : int

 proc commitment(s : dl_stat, w : dl_wit) : dl_com = {  
    (pa, wa) <- (s,w);
    r <$  [0..p-2];
    return g ^^ r;
 }

 proc response(b : dl_chal) : dl_resp = {
    return r + b * wa;
 }  
}.


(* Honest Verifier is derived automatically from "challenge_set" and "verify_transcript" *)
print HV.


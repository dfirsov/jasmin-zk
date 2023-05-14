require import Int IntDiv Real Distr StdOrder List.
(* import Ring.IntID IntOrder. *)

require GenericSigmaProtocol.

require import Group ZModP.
   
clone import ComGroup as CG.

op q : int.
axiom q_prime : prime q.

clone import ZModField as EG with op p <- q
proof prime_p.  realize prime_p. apply q_prime. qed.

(* synonyms for readability  *)
type dl_stat = group.            (* statement *)
type dl_wit  = zmod.              (* witness *)
type dl_com  = group.            (* commitment *)
type dl_resp = zmod.              (* response *)
type dl_chal = zmod.              (* challenge *)

op (^^) (g : group)(p : zmod): group = g ^ (asint p).


(* generator  *)
op g : group.

(* axiom g_not_ine : g <> e. *)
axiom g_is_generator : g ^ q = e.

(* the language of Schnorr protocol consists of discrete logarithms  *)
op IsDL (p : dl_stat) (w : dl_wit) : bool = g ^^ w = p.

op soundness_relation    = IsDL.
op completeness_relation = IsDL.
op zk_relation           = IsDL.


(* transcript verification for Honest Vrifier  *)
op verify_transcript (p : dl_stat) (x : dl_com * dl_chal * dl_resp) = 
 (let (c,b,r) = x in ((g ^^ r) = (p ^^ b) * c)) /\ (p ^ q = e).

(* instantiating generic definitions for Schnorr protocol  *)
clone include GenericSigmaProtocol with 
  type statement       <= dl_stat,
  type commitment      <= dl_com,  
  type witness         <= dl_wit,
  type response        <= dl_resp,
  type challenge       <= dl_chal,
  op challenge_set     <=  DZmodP.Support.enum,
  op verify_transcript     <- verify_transcript,
  op soundness_relation    <- soundness_relation,
  op completeness_relation <- completeness_relation,
  op zk_relation           <- zk_relation.
  (* TODO proof* or make this theory abstract *)


(* Honest Prover *)
module HP : HonestProver = {
 var pa : dl_stat
 var wa : dl_wit
 var r : zmod

 proc commitment(s : dl_stat, w : dl_wit) : dl_com = {  
    (pa, wa) <- (s,w);
    r <$ DZmodP.dunifin;
    return g ^^ r;
 }

 proc response(b : dl_chal) : dl_resp = {
    return r + b * wa;
 }  
}.


(* Honest Verifier is derived automatically from "challenge_set" and "verify_transcript" *)



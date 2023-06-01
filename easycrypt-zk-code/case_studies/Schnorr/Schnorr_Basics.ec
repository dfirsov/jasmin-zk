require import AllCore DBool Bool List Distr AuxResults Finite.

require import CyclicGroup.


import FDistr.


require  GenericSigmaProtocol.


(* synonyms for readability  *)
type dl_stat = group.           (* statement *)
type dl_wit  = t.               (* witness *)
type dl_com = group.            (* commitment *)
type dl_resp = t.               (* response *)
type dl_chal = t.               (* challenge *)


(* the language of Schnorr protocol consists of discrete logarithms  *)
op IsDL (p : dl_stat) (w : dl_wit) : bool = g ^ w = p.

op soundness_relation    = IsDL.
op completeness_relation = IsDL.
op zk_relation           = IsDL.


(* transcript verification for Honest Vrifier  *)
op verify_transcript (p : dl_stat) (x : dl_com * dl_chal * dl_resp) = 
 let (c,b,r) = x in g ^ r = (p ^ b) * c.
   

(* instantiating generic definitions for Schnorr protocol  *)
clone include GenericSigmaProtocol with 
  type statement       <- dl_stat,
  type commitment      <- dl_com,  
  type witness         <- dl_wit,
  type response        <- dl_resp,
  type challenge       <- dl_chal,
  op challenge_set     <=  to_seq (support dt),
  op verify_transcript <- verify_transcript,
  op soundness_relation    <- soundness_relation,
  op completeness_relation <- completeness_relation,
  op zk_relation           <- zk_relation.


(* Honest Prover *)
module HP : HonestProver = {
 var pa : dl_stat
 var wa : dl_wit
 var r : t

 proc commitment(p : dl_stat, w : dl_wit) : dl_com = {  
    (pa, wa) <- (p,w);
    r <$  dt;
    return g ^ r;
 }

 proc response(b : dl_chal) : dl_resp = {
    return r + b * wa;
 }  
}.


(* Honest Verifier is derived automatically from "challenge_set" and "verify_transcript" *)
print HV.


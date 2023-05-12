require import AllCore DBool Bool List Distr Int AuxResults DJoin Permutation.
require  GenericSigmaProtocol.


require CommitmentSpecial.
clone include CommitmentSpecial with type message <- bool.

require Djoinmap.
clone import Djoinmap as DJM  with type a <- bool,
                                   type b <- commitment * opening,
                                    op d <- Com.


(* the number of vertices in the graph  *)
op K : int.
axiom K_pos : 0 < K.

(* parameters needed for rewinding library  *)
type sbits.
op HB_pair_sbits : sbits * sbits -> sbits.
op HB_unpair: sbits -> sbits * sbits.
axiom HB_ips: injective HB_pair_sbits. 
axiom HB_unpair_pair x : HB_unpair (HB_pair_sbits x) = x.

(* K * K list representing K x K adjacency matrix. For technical
reasons it is simpler to work with flat representation of an adjacency
matrix *)
type graph = bool list.         
type hc_stat = graph.           (* statement *)


(* We represent a witness as a list of integers of size K. For example,
witness := [1,2,3] represents a cycle "1 -> 2 -> 3 -> 1". *)
type hc_wit  = int list.        (* witness *)


(* Blum's protocol commitment consits of a list of K commitments   *)
type hc_com  = commitment list. (* commitment *)


(* Depending on the challenge the response is EITHER a permutation
with list of openings OR a witness with a list of openings.  *)
type  ('a, 'b) sum = [Left of 'a | Right of 'b]. 

type hc_resp = (permutation * (opening list), 
                 hc_wit * (opening list)) sum.


(* complete graph (all vertices connected to all other vertices)  *)
op compl_graph     : int -> graph.
op compl_graph_cyc : int -> int list = range 0.

(* Intuitively (permute_graph g p)(i,j) = g(p i, p j). Below we
declaratively describe the properties of permute_graph function.  *)
op permute_graph ['a] (p : permutation) (g : 'a list) : 'a list.


(* Intuitively, "prj_path w g" returns entries which corresponds to the cycle represented by the witness "w".
For example, prj (1,2,3) g := [g(1,2),g(2,3),g(3,1)].
Below we declaratively describe the properties of prj_path function.
*)
op prj_path ['a]  : hc_wit -> 'a list -> 'a list.

(* rep_path w l g -- replace values in "g" at positions which correspond to "w" with values from "l" *)
op rep_path ['a] : int list -> 'a list -> 'a list -> 'a list.


(* to permute a witness we just apply permutation point-wise  *)
op permute_witness : permutation -> hc_wit -> hc_wit = map.


(* transcript verification by Blum's Honest Verifier (see the description in the HamBlum/README.md *)
op hc_verify (p : hc_stat) (c : hc_com) (b : bool)  (r : hc_resp) : bool =
 with r = (Left x) => b /\ all Ver (zip (permute_graph x.`1 p) (zip c x.`2))
                        /\ size c = K * K
                        /\ size p = K * K
                        /\ size x.`2 = K * K
                        /\ x.`1 \in perm_d K
 with r = (Right x) => ! b /\ size x.`1 = K
                           /\ size c = K * K
                           /\ size x.`2 = K
                           /\ all Ver 
                                 (zip (nseq K true) 
                                   (zip ((prj_path x.`1 c)) x.`2))
                           /\ perm_eq x.`1 (range 0 K)
                           /\ size p = K * K.

(* defining relations for completeness, soundness, and ZK *)
op completeness_relation (g : hc_stat) (w : hc_wit) : bool  = 
     K = size w /\ 
     K * K = size g /\ 
     perm_eq w (range 0 K) /\ 
     nseq K true = prj_path w g.
op soundness_relation = completeness_relation.
op zk_relation = completeness_relation.


(* cloning the generic definition with specific Blum details  *)
clone include GenericSigmaProtocol with 
  type statement       <- hc_stat,
  type commitment      <- hc_com,  
  type witness         <- hc_wit,
  type response        <- hc_resp,
  type challenge       <- bool,
  op challenge_set     <=  (false :: true :: []),
  op verify_transcript <= fun p (x : transcript) => hc_verify p x.`1 x.`2 x.`3,
  op soundness_relation    <- soundness_relation,
  op completeness_relation <- completeness_relation,
  op zk_relation           <- zk_relation,
    (* rewindability parameters *)
  type sbits           <- sbits, 
  op pair_sbits        <- HB_pair_sbits, 
  op unpair            <- HB_unpair
proof *.
realize challenge_set_size. auto. qed.
realize challenge_set_unique. auto. qed.
realize ips. apply HB_ips. qed.          (* rewindability encoding  *)
realize unpair_pair. apply HB_unpair_pair. qed. (* rewindability decoding *)


(* Honest Prover  *)
module HP : HonestProver  = {
  var g : graph                 
  var prm : permutation         
  var w : hc_wit                
  var fal : bool list           
  var pi_gwco : (commitment * opening) list
  var pi_w : hc_wit
  
  proc commitment(p_a : hc_stat, w_a : hc_wit)  = {
    g <- p_a;
    w     <- w_a;
    prm   <$ perm_d K;
    fal   <- permute_graph prm g;
    pi_gwco <$ djoinmap Com fal; 

    return map fst pi_gwco;
  }
  
  proc response(b : bool) : hc_resp = {
    pi_w <- permute_witness prm w;
    return if b then Left (prm, map snd pi_gwco) 
                else Right (pi_w, map snd (prj_path pi_w pi_gwco));
 } 
}.


(* Declarative specification of main functions: compl_graph, permute_graph, and prj_path.  *)

axiom prj_path_size ['a] : forall w (s : 'a list), size w <= size s => size (prj_path w s) = size w.

axiom prj_path_map ['a 'b] (f : 'a -> 'b)  w (s : 'a list): prj_path w (map f s) = map f (prj_path w s).

axiom prj_path_in x w (s : 'a list) : x \in prj_path w s => x \in s.

axiom prj_path_zip w (x : 'a list) (y : 'b list) : 
  zip (prj_path w x) (prj_path w y) = prj_path w (zip x y).

axiom prj_path_compl_graph w : size w = K => prj_path w (compl_graph K) = nseq K true.

axiom prj_rep ['a] (g : 'a list) w:  g = rep_path w (prj_path w g) g.

axiom rep_prj ['a] (g : 'a list) w l: l = (prj_path w (rep_path w g l)).

axiom permute_compl_graph p n : permute_graph p (compl_graph n) = (compl_graph n).

axiom compl_graph_prop n : 0 <= n => completeness_relation (compl_graph n) (compl_graph_cyc n).

axiom permute_graph_size perm (g : graph) : size (permute_graph perm g) = size g.

axiom witness_under_permutation g perm w : perm  \in perm_d K =>
 completeness_relation g w = completeness_relation (permute_graph perm g) (permute_witness perm w).

axiom permute_graph_inv  (g : graph) (perm : permutation) : perm \in perm_d K => size g = K * K =>
  permute_graph (inv perm) (permute_graph perm g) = g.

axiom perm_eq_permute w prm : prm \in perm_d K => perm_eq w (range 0 K) => perm_eq (permute_witness prm w) w.

axiom rep_path_map ['a 'b] (g : 'a list) w l l' (f : 'a -> 'b):map f (rep_path w l l') = rep_path w (map f l) (map f l').

axiom rep_path_distr w l l' : djoinmap Com (rep_path w l' l) 
  = dapply (fun x => rep_path w (fst x) (snd x)) ((djoinmap Com l) `*` (djoinmap Com l')).

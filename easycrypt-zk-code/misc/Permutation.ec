require import AllCore List Distr.

(* basic axiomatization of permutations (used only in Hamilton-Blum)  *)
type permutation = int -> int.

op compose : permutation -> permutation -> permutation = (\o).

op inv : permutation -> permutation.
op mk_perm : int list -> permutation.
op perm_d : int -> permutation distr.


axiom perm_d_uni n : is_uniform (perm_d n). 
axiom perm_d_lossless n : is_lossless (perm_d n).

axiom perm_d_inv_closed p n : p \in perm_d n => (inv p) \in perm_d n.
axiom perm_d_comp_closed p q n : p \in perm_d n => q \in perm_d n =>  p \o q \in perm_d n.
axiom perm_d_correct n p : p \in perm_d n => perm_eq (map p  (range 0 n)) (range 0 n).

axiom perm_d_mk_perm p n :  perm_eq p (range 0 n) => (mk_perm p) \in perm_d n.

axiom inv_left p n :  p \in perm_d n => p \o (inv p) = (fun x => x).
axiom inv_right p n :  p \in perm_d n => (inv p) \o p = (fun x => x).

(* 
NOTE: One can derive `mk_perm_inv` from mk_perm def.

axiom mk_perm_def (p : int list) : perm_eq p (range 0 (size p)) => map (mk_perm p) (range 0 (size p)) = p. 
*)
axiom mk_perm_inv (p : int list) : perm_eq p (range 0 (size p)) => map (inv (mk_perm p)) p = range 0 (size p).

require Ring.
require import Int.
import Ring.IntID.
require Constants.
require import IntDiv.

op [opaque] square_and_multiply_state (x y z m : int) = ((x ^ y) * z) %% m.

lemma square_and_multiply_step x y z m:
    0 <= y =>
    square_and_multiply_state x y z m = square_and_multiply_state (x*x %% m) (y %/ 2) ((z * x ^ (y%%2)) %% m) m.
proof.
move => Hy.
have red_mul: forall x' y' x'' y'', x' %% m = x'' %% m => y' %% m = y'' %% m => (x' * y') %% m = (x'' * y'') %% m.
  move => x' y' x'' y'' H1 H2.
  rewrite -modzMm.
  rewrite H1 H2.
  rewrite modzMm.
  by trivial.
have red_exp: forall x' y' x'', x' %% m = x'' %% m => x' ^ y' %% m = x'' ^ y' %% m.
  move => x' y' x'' H1.
  (* Should be elementary? *)
  admit.
(* Bring lhs and rhs into matching shape, modulo modulo. *)
rewrite /square_and_multiply_state {1}(divz_eq y 2).
rewrite exprD_nneg; [ smt() | smt() | ].
rewrite (mulzC (y%/2) 2).
rewrite exprM.
rewrite mulzA.
rewrite (mulzC (x^_) z).
(* Show equality modulo *)
apply red_mul.
apply red_exp.
rewrite modz_mod.
by trivial.
rewrite modz_mod.
by trivial.
qed.

lemma square_and_multiply_end x z m:
    square_and_multiply_state x 0 z m = z %% m.
  rewrite /square_and_multiply_state. trivial.
qed.

lemma test: (Constants.g ^ Constants.ex_w) %% Constants.p = Constants.ex_s.
proof.
  have : square_and_multiply_state Constants.g Constants.ex_w 1 Constants.p = Constants.ex_s.
    rewrite /Constants.ex_w /Constants.p /Constants.g.
    do (rewrite square_and_multiply_end || (rewrite square_and_multiply_step /=; first by trivial)).
    by trivial.
    rewrite /square_and_multiply_state.
    smt(). (* trivial would try to do the exponentiation *)
qed.
    

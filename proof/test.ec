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
rewrite /square_and_multiply_state {1}(divz_eq y 2).
admit.
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
    

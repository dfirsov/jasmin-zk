require Ring.
require import Int.
import Ring.IntID.
require Constants.
require import IntDiv.


section.

op [opaque] square_and_multiply_state (x y z m : int) = ((x ^ y) * z) %% m.

local lemma red_exp' (x' x'' m : int) : forall y, 0 <= y =>  x' %% m = x'' %% m 
  => x' ^ y %% m = x'' ^ y %% m.
apply intind. simplify. progress.
progress.
have ->: x' ^ (i + 1)  = x' * (x' ^ i). smt(@Ring.IntID).
have ->: x'' ^ (i + 1)  = x'' * (x'' ^ i). smt(@Ring.IntID).
have ->: x' * x' ^ i %% m = x' %% m * (x' ^ i %% m) %% m. smt(@IntDiv).
rewrite H0. apply H1. rewrite H1.
smt(@IntDiv).
qed.


local lemma red_exp (x' x''  m : int) : forall y, x' %% m = x'' %% m 
  => x' ^ y %% m = x'' ^ y %% m.
move => y H. 
case (0 <= y). move => H'. apply red_exp'. auto. apply H.
move => H'.
have : y < 0. smt().
progress.
have ->: x' ^ y = x' ^ (-y). smt(@Ring.IntID).
have ->: x'' ^ y = x'' ^ (-y). smt(@Ring.IntID).
apply red_exp'. smt(). auto.
qed.



local lemma square_and_multiply_step x y z m:
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
  apply red_exp. auto.
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

local lemma square_and_multiply_end x z m:
    square_and_multiply_state x 0 z m = z %% m.
  rewrite /square_and_multiply_state. trivial.
qed.

lemma statement_witness_pair_is_valid: (Constants.g ^ Constants.ex_w) %% Constants.p = Constants.ex_s.
proof.
  have : square_and_multiply_state Constants.g Constants.ex_w 1 Constants.p = Constants.ex_s.
    rewrite /Constants.ex_w /Constants.p /Constants.g.
    do (rewrite square_and_multiply_end || (rewrite square_and_multiply_step /=; first by trivial)).
    by trivial.
    rewrite /square_and_multiply_state.
    smt(). (* trivial would try to do the exponentiation *)
qed.


lemma generator_is_valid: (Constants.g ^ Constants.q) %% Constants.p = 1.
proof.
  have : square_and_multiply_state Constants.g Constants.q 1 Constants.p = 1.
    rewrite /Constants.q /Constants.p /Constants.g.
    do (rewrite square_and_multiply_end || (rewrite square_and_multiply_step /=; first by trivial)).
    by trivial.
    rewrite /square_and_multiply_state.
    smt(). 
qed.
    
    



lemma pq_euclid : euclidef Constants.barrett_numerator Constants.p (Constants.barrett_numerator_div_p, Constants.barrett_numerator_mod_p).
rewrite /euclidef. simplify. rewrite /barrett_numberator.  simplify. split. auto.
smt().
qed.


lemma bp_correct : Constants.bp = 4 ^ (64 * 32) %/ Constants.p.
 have ->: 4 ^ (64 * 32) = Constants.barrett_numerator. simplify. auto.
 have  -> : Constants.barrett_numerator = (Constants.p * Constants.barrett_numerator_div_p + Constants.barrett_numerator_mod_p). smt(pq_euclid).
smt(@IntDiv). qed.

end section.

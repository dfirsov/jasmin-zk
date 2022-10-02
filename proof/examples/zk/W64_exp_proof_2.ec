require import AllCore IntDiv CoreMap List.

require import JModel.
require import BitEncoding.
import BS2Int.

require import Fp_small_proof.
require import W64_exp_proof_1.

import Zp.
import IterOp.



module M2 = {

    proc expm (x:W64.t, n:bits) : W64.t = {
    
    var x1, x2, x3, x4 : W64.t;
    var ctr:int;
    var bit, d, p, par :bool;    
    d <- ith_bit n (size n - 1);
    (x1,x2,x3, x4) <- (W64.one,W64.one,x,x * x);

    ctr <- size n - 1;
    p <- d;
    (x1,x3) <- d ? (x3,x1) : (x1,x3);
    (x2,x4) <- d ? (x4,x2) : (x2,x4);

    while (0 < ctr) {
      ctr <- (ctr - 1);
      p <- d;
      d <- d || ith_bit n ctr;
      par <- ith_bit n (ctr + 1) ^ ith_bit n ctr;
      (x1,x2) <- if par then (x2,x1) else (x1, x2);
      x1 <- x1 * x2;
      x2 <- x2 * x2;
      (x1,x3) <- d ^ p ? (x3,x1) : (x1,x3);
      (x2,x4) <- d ^ p ? (x4,x2) : (x2,x4);
    }
    (x1,x2) <- if ! ith_bit n 0 then (x2,x1) else (x1, x2);    
    return x1;
  }  


}.


lemma exp_eq_naive :
 equiv[ M.expm_naive ~ M2.expm : ={arg} /\  0 < size n{1} ==> ={res}].
proc.
wp.
while (={ctr, n, d, p, x3, x4} /\ 0 < ctr{2} + 1 <= size n{2}
   /\ (ith_bit n{2} (ctr{2}  ) => x2{2} = x2{1} /\ x1{2} = x1{1})
   /\ ((!ith_bit n{2} (ctr{2} ) ) => (x1{1} = x2{2} /\ x2{1} = x1{2}))
   ).
wp. skip. progress. smt().     smt. smt.
rewrite H5. simplify. smt().
rewrite H5. simplify. smt().
rewrite H5. simplify. smt().
rewrite H5. simplify. smt().
wp.  
skip. progress. smt(). smt(). 
smt().
qed.



lemma expm_correct : 
  equiv[ M2.expm ~ M.expm_spec : ={arg} /\  0 < size arg{1}.`2 ==> ={res}].
transitivity M.expm_naive 
  (={arg}  /\  0 < size arg{1}.`2 ==> ={res})
  (={arg}  /\  0 < size arg{1}.`2 ==> ={res}).
smt().
auto. symmetry.
conseq exp_eq_naive. auto. auto.
exists* n{1}, x{1}. elim*. progress.
conseq (exp_naive_correct f0 f). progress. smt().
qed.


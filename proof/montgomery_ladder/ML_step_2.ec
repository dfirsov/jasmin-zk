require import AllCore IntDiv CoreMap List.

require import JModel.
require import BitEncoding.
import BS2Int.


require ML_step_1.
clone include ML_step_1.

import IterOp.



module M2 = {

    proc iterop (x:R, n:bits) : R = {
    
    var x1, x2, x3, x4 : R;
    var ctr:int;
    var bit, d, p, par :bool;    
    d <- ith_bit n (size n - 1);
    (x1,x2,x3, x4) <- (idR,idR,x,x *** x);

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
      x1 <- x1 *** x2;
      x2 <- x2 *** x2;
      (x1,x3) <- d ^ p ? (x3,x1) : (x1,x3);
      (x2,x4) <- d ^ p ? (x4,x2) : (x2,x4);
    }
    (x1,x2) <- if ! ith_bit n 0 then (x2,x1) else (x1, x2);    
    return x1;
  }  


}.


lemma iterop_naive_2 :
 equiv[ M1.iterop_naive ~ M2.iterop : ={arg} /\  0 < size n{1} ==> ={res}].
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
rewrite H5. simplify.  
have ->: d{2} ^ d{2} = false. smt(). simplify.
have ->: ith_bit n{2} ctr{2} ^ false = ith_bit n{2} ctr{2}. smt().
smt(exp_prop7). 
wp. skip. progress. smt(). smt(). 
smt().
qed.



lemma iterop_2_spec : 
  equiv[ M2.iterop ~ M1.iterop_spec : ={arg} /\  0 < size arg{1}.`2 /\ valR x{1} < P ==> ={res}].
transitivity M1.iterop_naive 
  (={arg}  /\  0 < size arg{1}.`2  ==> ={res})
  (={arg}  /\  0 < size arg{1}.`2 /\ valR x{2} < P ==> ={res}).
smt().
auto. symmetry.
conseq iterop_naive_2. auto. auto.
exists* n{1}, x{1}. elim*. progress.
conseq (iterop_spec_naive f0 f). progress. smt(). 
qed.


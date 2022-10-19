require import AllCore IntDiv CoreMap List.

require import JModel.
require import BitEncoding.
import BS2Int.
import IterOp.

require Abstract_exp_proof_2.
clone include Abstract_exp_proof_2.


module M3 = {

    proc expm (x:R, n:bits) : R = {
    
    var x1, x2, x3, x4, bit : R;
    var par, p, d : W64.t;
    var ctr:int;

    d <- ith_bitlist n (size n - 1);
    (x1,x2,x3, x4) <- (oneR,oneR,x,x *** x);

    ctr <- size n - 1;
    p <- d;
    (x1,x3) <- as_bool d ? (x3,x1) : (x1,x3);
    (x2,x4) <- as_bool d ? (x4,x2) : (x2,x4);

    while (0 < ctr) {
      ctr <- (ctr - 1);
      p <- d;
      d <-  d `|` ith_bitlist n ctr;
      par <- ith_bitlist n (ctr + 1) `^` ith_bitlist n ctr;
      (x1,x2) <- if as_bool par then (x2,x1) else (x1, x2);
      x1 <- x1 *** x2;
      x2 <- x2 *** x2;
      (x1,x3) <- as_bool (d `^` p) ? (x3,x1) : (x1,x3);
      (x2,x4) <- as_bool (d `^` p)  ? (x4,x2) : (x2,x4);
    }
    (x1,x2) <- if ! as_bool (ith_bitlist n 0)  then (x2,x1) else (x1, x2);    
    return x1;
  }  


}.



lemma exp_2_3 :
 equiv[ M2.expm ~ M3.expm : ={arg} /\  0 < size n{1} ==> ={res}].
proc.
wp.
while (={ctr, n,  x1,x2,  x3, x4}  
  /\ d{1} = as_bool d{2} /\ d{2} = as_w64 d{1} 
  /\ p{1} = as_bool p{2} /\ p{2} = as_w64 p{1} 

    )
   .
wp. skip. progress. 
timeout 20. smt.
timeout 20. smt.
timeout 20. smt.
timeout 20. smt.
smt.
smt.


wp.  skip.  progress.
smt.
smt.
smt.
smt.
smt.
smt.
smt.
qed.

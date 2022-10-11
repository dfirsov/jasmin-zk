require import AllCore IntDiv CoreMap List.

require import JModel.
require import BitEncoding.
import BS2Int.

require import Fp_small.
require import Fp_small_proof.
require import W64_exp_proof_1.
require import W64_exp_proof_2.
require import W64_exp_proof_3.

import Zp.
import IterOp.




module M4 = {

    proc expm (x:W64.t, n:W64.t) : W64.t = {
    
    var x1, x2, x3, x4, bit, d, p, par : W64.t;
    var ctr:int;

    d <- ith_bitword64 n (W64.size - 1);
    (x1,x2,x3, x4) <- (W64.one,W64.one,x,x *** x);

    ctr <- W64.size - 1;
    p <- d;
    (x1,x3) <- as_bool d ? (x3,x1) : (x1,x3);
    (x2,x4) <- as_bool d ? (x4,x2) : (x2,x4);

    while (0 < ctr) {
      ctr <- (ctr - 1);
      p <- d;
      d <-  d `|` ith_bitword64 n ctr;
      par <- ith_bitword64 n (ctr + 1) `^` ith_bitword64 n ctr;
      (x1,x2) <- if as_bool par then (x2,x1) else (x1, x2);
      x1 <- x1 *** x2;
      x2 <- x2 *** x2;
      (x1,x3) <- as_bool (d `^` p) ? (x3,x1) : (x1,x3);
      (x2,x4) <- as_bool (d `^` p)  ? (x4,x2) : (x2,x4);
    }
    (x1,x2) <- if ! as_bool (ith_bitword64 n 0)  then (x2,x1) else (x1, x2);    
    return x1;
  }  


}.

axiom qqq n x :
  ith_bitlist (W64.w2bits n) x = ith_bitword64 n x.


axiom www n x : size n = 64 =>
  ith_bitlist n x = ith_bitword64 (W64.bits2w n) x.


lemma exp_3_4_1 :
 equiv[ M3.expm ~ M4.expm : arg{1}.`1 = arg{2}.`1 /\ (W64.bits2w arg.`2{1}) = (arg.`2{2})  /\ size n{1} = 64 /\  0 < size n{1} ==> ={res}].
proc.
wp.
while (={ctr,  x1,x2,  x3, x4, d, p}  
   /\ W64.bits2w n{1} = n{2}
   /\ size n{1} = 64).
wp. skip. progress. 
smt (qqq www).
smt (qqq www).
smt (qqq www).
smt (qqq www).
smt (qqq www).
wp. 
skip. 
progress.
smt().
smt (qqq www).
smt (qqq www).
smt (qqq www).
smt (qqq www).
smt (qqq www).
smt (qqq www).
smt().
smt (qqq www).
qed.



lemma exp_3_4_2 :
 equiv[ M3.expm ~ M4.expm : arg{1}.`1 = arg{2}.`1 /\ (arg.`2{1}) = (W64.w2bits arg.`2{2})    /\  0 < size n{1} ==> ={res}].
proc.
wp.
while (={ctr,  x1,x2,  x3, x4, d, p}  
   /\ n{1} = W64.w2bits n{2}
   /\ size n{1} = 64).
wp. skip. progress. 
smt (qqq www).
smt (qqq www).
smt (qqq www).
smt (qqq www).
smt (qqq www).
wp. 
skip. 
progress.
smt (qqq www).
smt (qqq www).
smt (qqq www).
smt (qqq www).
smt (qqq www).
smt (qqq www).
smt (qqq www).
qed.





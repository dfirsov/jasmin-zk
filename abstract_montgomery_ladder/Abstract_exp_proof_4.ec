require import AllCore IntDiv CoreMap List.

require import JModel.
require import BitEncoding.
import BS2Int.


require Abstract_exp_proof_3.
clone include Abstract_exp_proof_3.


import IterOp.

module M4 = {

    proc expm (x:R, n:R) : R = {
    
    var x1, x2, x3, x4, bit : R;
    var par, p, d : W64.t;
    var ctr:int;

    d <- ith_bitR n (Rsize - 1);
    (x1,x2,x3, x4) <- (oneR,oneR,x,x *** x);

    ctr <- Rsize - 1;
    p <- d;
    (x1,x3) <- as_bool d ? (x3,x1) : (x1,x3);
    (x2,x4) <- as_bool d ? (x4,x2) : (x2,x4);

    while (0 < ctr) {
      ctr <- (ctr - 1);
      p <- d;
      d <-  d `|` ith_bitR n ctr;
      par <- ith_bitR n (ctr + 1) `^` ith_bitR n ctr;
      (x1,x2) <- if as_bool par then (x2,x1) else (x1, x2);
      x1 <- x1 *** x2;
      x2 <- x2 *** x2;
      (x1,x3) <- as_bool (d `^` p) ? (x3,x1) : (x1,x3);
      (x2,x4) <- as_bool (d `^` p)  ? (x4,x2) : (x2,x4);
    }
    (x1,x2) <- if ! as_bool (ith_bitR n 0)  then (x2,x1) else (x1, x2);    
    return x1;
  }  


}.



lemma exp_3_4_1 :
 equiv[ M3.expm ~ M4.expm : arg{1}.`1 = arg{2}.`1 /\ (bitsR arg.`2{1}) = (arg.`2{2})  /\ size n{1} = Rsize /\  0 < size n{1} ==> ={res}].
proc.
wp.
while (={ctr,  x1,x2,  x3, x4, d, p}  
   /\ bitsR n{1} = n{2}
   /\ size n{1} = Rsize).
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
smt (qqq www).
qed.



lemma exp_3_4_2 :
 equiv[ M3.expm ~ M4.expm : arg{1}.`1 = arg{2}.`1 /\ (arg.`2{1}) = (Rbits arg.`2{2})    /\  0 < size n{1} ==> ={res}].
proc.
wp.
while (={ctr,  x1,x2,  x3, x4, d, p}  
   /\ n{1} = Rbits n{2}
   /\ size n{1} = Rsize).
wp. skip. progress. 
(* smt (qqq www). *)
(* smt (qqq www). *)
(* smt (qqq www). *)
(* smt (qqq www). *)
(* smt (qqq www). *)
wp. 
skip. 
progress.  rewrite iii. auto.
smt (qqq www iii).
smt (qqq www iii).
smt (qqq www iii).
smt (qqq www iii).
smt (qqq www iii).
smt (qqq www iii).
smt (qqq www iii).
smt (qqq www iii).
smt (qqq www iii).
qed.





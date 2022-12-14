require import AllCore IntDiv CoreMap List.

require import JModel.
require import BitEncoding.
import BS2Int.

require ML_step_4.
clone include ML_step_4.

import IterOp.


module M5 = {

  proc iterop (x:R, n:R) : R = {
    
    var x1, x2, x3, x4, bit : R;
    var t1,t2,par, p, d : W64.t;
    var ctr: int;

    d <@ Spec.ith_bit(n,  (Rsize - 1));
    (x1,x2,x3) <- (idR,idR,x);
    x4 <@ Spec.mul(x,x);

    ctr <- Rsize - 1;
    p <- d;
    (x1,x3) <@ Spec.swapr (x1,x3,as_bool d);
    (x2,x4) <@ Spec.swapr (x2,x4,as_bool d); 

    while (0 < ctr) {
      ctr <- (ctr - 1);
      p <- d;
      t1 <@ Spec.ith_bit(n,  (ctr + 1));
      t2 <@ Spec.ith_bit(n, ctr);
      d <-  d `|` t2;
      par <- t1 `^` t2;
      (x1,x2) <@ Spec.swapr (x1,x2,as_bool par); 
      x1 <@ Spec.mul(x1,x2); 
      x2 <@ Spec.mul(x2,x2);  
      (x1,x3) <@ Spec.swapr (x1,x3,as_bool (d `^` p));  
      (x2,x4) <@ Spec.swapr (x2,x4,as_bool (d `^` p));   
    }
    par <@ Spec.ith_bit(n,0);
    (x1,x2) <@ Spec.swapr (x2,x1, as_bool par);
    return x1;
  }  
}.


lemma iterop_4_5 :
 equiv[ M4.iterop ~ M5.iterop  : ={arg} ==> ={res}].
proc.
inline Spec.mul.
inline Spec.swapr.
inline Spec.ith_bit.
    wp.
    wp.
while (={ctr, n,  x1,x2,  x3, x4, d, p} ).
 wp. skip. progress. 
wp.  skip. progress. 
smt().
qed.



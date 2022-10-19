require import AllCore IntDiv CoreMap List.

require import JModel.
require import BitEncoding.
import BS2Int.


require Abstract_exp_proof_6.
clone include Abstract_exp_proof_6.

import IterOp.


module M7(M : BasicOps) = {

  proc expm (m : R, x:R, n:R) : R = {
   
    var x1, x2, x3, x4, bit : R;
    var t1, t2, par, p, d, ctr : W64.t;

    d <@ M.ith_bit(n,  W64.of_int (Rsize - 1));
    (x1,x2,x3) <- (oneR,oneR,x);
    x4 <@ M.mulm(m,x,x);

    ctr <- W64.of_int (Rsize - 1);
    p <- d;
    (x1,x3) <@ M.swapr(x1,x3,d);
    (x2,x4) <@ M.swapr(x2,x4,d);

    while (W64.zero \ult ctr) {
      ctr <- (ctr - W64.of_int 1);
      p <- d;
      t1 <@ M.ith_bit(n,  (ctr +  W64.of_int 1));
      t2 <@ M.ith_bit(n,  ctr);
      d <-  d `|` t2;
      par <- t1 `^` t2;
      (x1,x2) <@ M.swapr(x1,x2,par);  
      x1 <@ M.mulm(m,x1,x2); 
      x2 <@ M.mulm(m,x2,x2);  
      (x1,x3) <@ M.swapr(x1,x3,(d `^` p));
      (x2,x4) <@ M.swapr(x2,x4,(d `^` p)); 
    }
    par <@ M.ith_bit(n,W64.of_int 0);
    (x1,x2) <@ M.swapr (x2,x1,par);

    return x1;

  }  
}.

section.

declare module M <: BasicOps.

lemma exp_6_7 :
 equiv[ M6(M).expm ~ M7(M).expm : ={arg, glob M} ==> ={res}].
proc. sim.
while (={n, m, x1,x2,  x3, x4, d, p, glob M} 
  /\ W64.of_int ctr{1} = ctr{2} /\ ctr{1} < Rsize).
call (_:true). 
call (_:true). 
call (_:true). 
call (_:true). 
call (_:true). 
wp.
call (_:true).
call (_:true). wp. skip. progress.
smt().
smt(Rsize_pos Rsize_max @W64).
smt().
call (_:true). wp. 
call (_:true). wp. 
call (_:true). wp. 
call (_:true).  skip. progress. 
smt().
smt(Rsize_pos Rsize_max @W64).
smt(Rsize_pos).
qed.


end section.

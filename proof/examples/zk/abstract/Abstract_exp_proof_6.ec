require import AllCore IntDiv CoreMap List.

require import JModel.
require import BitEncoding.
import BS2Int.

require import Abstract_exp_proof_1.
require import Abstract_exp_proof_2.
require import Abstract_exp_proof_3.
require import Abstract_exp_proof_4.
require import Abstract_exp_proof_5.

import IterOp.

module M6(M : BasicOps) = {

  proc expm (m : R, x:R, n:R) : R = {
    
    var x1, x2, x3, x4, bit : R;
    var t1, t2, par, p, d : W64.t;
    var ctr:int;

    d <@ M.ith_bit(n,  W64.of_int (Rsize - 1));
    (x1,x2,x3) <- (oneR,oneR,x);
    x4 <@ M.mulm(m,x,x);

    ctr <- Rsize - 1;
    p <- d;
    (x1,x3) <@ M.swapr(x1,x3,d);
    (x2,x4) <@ M.swapr(x2,x4,d);

    while (0 < ctr) {
      ctr <- (ctr - 1);
      p <- d;
      t1 <@ M.ith_bit(n, W64.of_int (ctr + 1));
      t2 <@ M.ith_bit(n, W64.of_int ctr);
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

declare axiom exp_swap :
 equiv[ M.swapr ~ Spec.swapr    : arg{2}.`1 = arg{1}.`1 /\ arg{2}.`2 = arg{1}.`2 /\   arg{1}.`3 = as_w64 arg{2}.`3
    ==> ={res}].

declare axiom exp_ithbit :
 equiv[ M.ith_bit ~ Spec.ith_bit    : arg{2}.`1 = arg{1}.`1 /\  arg{2}.`2 = W64.to_uint arg{1}.`2 
    /\ 0 <= ctr{2} < Rsize ==> ={res} /\ (res{2} = W64.one \/ res{2} = W64.zero) ].

declare axiom exp_mulm : 
  equiv [ M.mulm ~ Spec.mul: arg{1}.`2 = arg{2}.`1 /\ arg{1}.`3 = arg{2}.`2 /\   ImplR p{1} P  ==> ={res} ].

    
lemma exp_5_6 :
 equiv[ M5.expm ~ M6(M).expm  : arg{2}.`2 = arg{1}.`1 /\ arg{2}.`3 = arg{1}.`2 /\   ImplR m{2} P ==> ={res}].
symmetry.
proc. 
wp. 
call exp_swap.
call exp_ithbit.
while ((d{2} = W64.one \/ d{2} = W64.zero) /\ ={ctr, n,  x1,x2,  x3, x4, d, p} /\ ImplR m{1} P /\  0 <= ctr{1} < Rsize).
call exp_swap.
call exp_swap.
 wp. 
call exp_mulm.
call exp_mulm. 
call exp_swap.
wp. 
call exp_ithbit.
call exp_ithbit.
wp.
skip. 
progress. smt. smt. smt(). smt().  smt(@W64).
rewrite /as_word.
rewrite /as_bool.  smt(@W64). smt(@W64).
wp. 
call exp_swap.
call exp_swap.
wp.
call exp_mulm. 
wp.
call exp_ithbit. 
skip.
progress.
rewrite /as_word.
rewrite /as_bool.
smt. smt(Rsize_pos). smt().
rewrite /as_w64.
rewrite /as_bool.
smt().
smt().
smt().
qed.

end section.

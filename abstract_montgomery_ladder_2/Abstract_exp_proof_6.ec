require import AllCore IntDiv CoreMap List.

require import JModel.
require import BitEncoding.
import BS2Int.

require Abstract_exp_proof_5.
clone include Abstract_exp_proof_5.

import IterOp.

module M6(M : BasicOps) = {

  proc iterop' (m : R, x:R, n:R) : R = {
    
    var x1, x2, x3, x4, bit : R;
    var t1, t2, par, p, d : W64.t;
    var ctr:int;

    d <@ Spec.ith_bit(n,  (Rsize - 1));
    (x1,x2,x3) <- (idR,idR,x);
    x4 <@ M.opr(m,x,x);

    ctr <- Rsize - 1;
    p <- d;
    (x1,x3) <@ Spec.swapr(x1,x3,as_bool d);
    (x2,x4) <@ Spec.swapr(x2,x4,as_bool d);

    while (0 < ctr) {
      ctr <- (ctr - 1);
      p <- d;
      t1 <@ Spec.ith_bit(n,  (ctr + 1));
      t2 <@ Spec.ith_bit(n,  ctr);
      d <-  d `|` t2;
      par <- t1 `^` t2;
      (x1,x2) <@ Spec.swapr(x1,x2,as_bool par);  
      x1 <@ M.opr(m,x1,x2); 
      x2 <@ M.opr(m,x2,x2);  
      (x1,x3) <@ Spec.swapr(x1,x3,as_bool (d `^` p));
      (x2,x4) <@ Spec.swapr(x2,x4,as_bool (d `^` p)); 
    }
    par <@ Spec.ith_bit(n, 0);
    (x1,x2) <@ Spec.swapr (x2,x1,as_bool par);
    return x1;
  }  
  
  proc iterop (m : R, x:R, n:R) : R = {
    
    var x1, x2, x3, x4, bit : R;
    var t1, t2, par, p, d : W64.t;
    var ctr:int;

    d <@ M.ith_bit(n,  W64.of_int (Rsize - 1));
    (x1,x2,x3) <- (idR,idR,x);
    x4 <@ M.opr(m,x,x);

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
      x1 <@ M.opr(m,x1,x2); 
      x2 <@ M.opr(m,x2,x2);  
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
  equiv [ M.opr ~ Spec.mul: arg{1}.`2 = arg{2}.`1 /\ arg{1}.`3 = arg{2}.`2 /\ ImplR p{1} P /\ valR a{1} < P /\ valR b{1} < P ==> ={res} /\ valR res{1} < P  ].


declare axiom stateless_M (x y : glob M) : x = y.
    
lemma iterop_5_6' :
 equiv[ M5.iterop ~ M6(M).iterop'  : arg{2}.`2 = arg{1}.`1 /\ arg{2}.`3 = arg{1}.`2 /\ valR x{1} < P /\   ImplR m{2} P ==> ={res}].
symmetry.
proc. 
inline Spec.swapr.
inline Spec.ith_bit.
wp. 

while ((d{2} = W64.one \/ d{2} = W64.zero) /\ ={ctr, n,  x1,x2,  x3, x4, d, p} /\ ImplR m{1} P /\  0 <= ctr{1} < Rsize
  /\ valR x1{1} < P /\ valR x2{1} < P /\ valR x4{1} < P /\ valR x3{1} < P).
wp.
 wp. 
call exp_mulm.
call exp_mulm. 
wp. 
wp.
skip. 
progress. smt. smt. smt(@W64). smt().  smt(@W64). smt(@W64). smt(@W64). smt(@W64). smt(@W64). 
wp. 
call exp_mulm. 
wp.
skip.
progress. smt. smt. smt.  smt. smt. smt. smt. 
qed.


lemma iterop_5_6'' :
 equiv[ M6(M).iterop' ~ M6(M).iterop  : ={arg, glob M} ==> ={res}].
proc.
wp.
symmetry.
call exp_swap.
wp. 
call exp_ithbit.
while ((d{2} = W64.one \/ d{2} = W64.zero) /\ ={m, ctr, n,  x1,x2,  x3, x4, d, p, glob M} /\  0 <= ctr{1} < Rsize).
call exp_swap.
wp.
call exp_swap. wp.
call (_:true).
call (_:true).
call exp_swap. wp.
call exp_ithbit.
call exp_ithbit.
wp. skip. progress. 
smt. smt. smt. smt. smt (@W64).
smt (stateless_M).
smt (@W64). smt (@W64).
smt (stateless_M).
call exp_swap. wp.
call exp_swap. wp.
call (_:true).
wp. 
call exp_ithbit.
skip. progress.
smt.
smt. smt. 
smt (stateless_M).
smt. smt (stateless_M). smt.
smt ().
qed.


lemma iterop_5_6 :
 equiv[ M5.iterop ~ M6(M).iterop  : arg{2}.`2 = arg{1}.`1 /\ arg{2}.`3 = arg{1}.`2 /\ valR x{1} < P /\  ImplR m{2} P ==> ={res}].
transitivity M6(M).iterop'
  (arg{2}.`2 = arg{1}.`1 /\ arg{2}.`3 = arg{1}.`2 /\ valR x{1} < P /\   ImplR m{2} P ==> ={res})
  (={arg, glob M} ==> ={res}).
progress. smt(). smt().
conseq iterop_5_6'.
conseq iterop_5_6''.
qed.

end section.

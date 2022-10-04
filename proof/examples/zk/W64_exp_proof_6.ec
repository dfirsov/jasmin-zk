require import AllCore IntDiv CoreMap List.

require import JModel.
require import BitEncoding.
import BS2Int.

require import Fp_small.
require import Fp_small_proof.
require import W64_exp_proof_1.
require import W64_exp_proof_2.
require import W64_exp_proof_3.
require import W64_exp_proof_4.
require import W64_exp_proof_5.

import Zp.
import IterOp.




module M6 = {


  proc expm (m : W64.t, x:W64.t, n:W64.t) : W64.t = {
    
    var x1, x2, x3, x4, bit, d, p, par, t1, t2 : W64.t;
    var ctr:W64.t;

    d <@ M.__ith_bit64(n,  W64.of_int (W64.size - 1));
    (x1,x2,x3) <- (W64.one,W64.one,x);
    x4 <@ M.mulm(m,x,x);

    ctr <- W64.of_int (W64.size - 1);
    p <- d;
    (x1,x3) <@ M.swap_0(x1,x3,d);
    (x2,x4) <@ M.swap_0(x2,x4,d);

    while (W64.zero \ult ctr) {
      ctr <- (ctr - W64.of_int 1);
      p <- d;
      t1 <@ M.__ith_bit64(n,  (ctr +  W64.of_int 1));
      t2 <@ M.__ith_bit64(n,  ctr);
      d <-  d `|` t2;
      par <- t1 `^` t2;
      (x1,x2) <@ M.swap_0(x1,x2,par);  
      x1 <@ M.mulm(m,x1,x2); 
      x2 <@ M.mulm(m,x2,x2);  
      (x1,x3) <@ M.swap_0(x1,x3,(d `^` p));
      (x2,x4) <@ M.swap_0(x2,x4,(d `^` p)); 
    }

    par <@ M.__ith_bit64(n,W64.of_int 0);
    (x1,x2) <@ M.swap_0 (x1,x2, (par = W64.one) ? W64.zero : W64.one);

    return x1;

  }  
}.

lemma exp_5_6 :
 equiv[ M5.expm ~ M6.expm  : ={arg} ==> ={res}].
proc. sim.
while (={n, m, x1,x2,  x3, x4, d, p} /\ W64.of_int ctr{1} = ctr{2} /\ ctr{1} < 64).
wp.
call (_:true). wp. skip. progress.
call (_:true). wp. skip. progress.
call (_:true). wp. skip. progress.
call (_:true). wp. skip. progress.
call (_:true). wp. skip. progress.
wp.
call (_:true). wp. skip. progress.
call (_:true). wp. skip. progress.
wp. 
skip. progress. smt.
smt. smt.
call (_:true). wp. skip. progress.
call (_:true). wp. skip. progress.
wp. 
call (_:true). wp. skip. progress. wp.
call (_:true). wp. skip. progress. 
skip. progress.
qed.


lemma exp_6_real :
 equiv[ M6.expm ~ M.expm  : ={arg} ==> ={res}].
proc. 
seq 9 11 :(={x1,x2}).
wp.
call (_:true). wp. progress. wp.

while (={n, m, x1,x2,  x3, x4, d, p, ctr}).

call (_:true). wp. progress. wp.
call (_:true). wp. progress. wp.
call (_:true). wp. progress. wp.
call (_:true). wp. progress. wp.
call (_:true). wp. progress. wp.
call (_:true). wp. progress. wp.
call (_:true). wp. progress. wp.
skip. progress. smt (@W64).
call (_:true). wp. progress. wp.
call (_:true). wp. progress. wp.
call (_:true). wp. progress. wp.
call (_:true). wp. progress. wp.
skip. progress.
admit.
qed.


lemma exp_real_speac :
 equiv[ M1.expm_spec ~ M.expm  : ImplWord arg{2}.`1 P 
   /\  arg{1}.`1 = arg{2}.`2
   /\ tonat arg{1}.`2 = W64.to_uint arg{2}.`3
   /\ size arg{1}.`2 = 64
     ==> ={res}].
transitivity M2.expm
   (={arg} /\  0 < size arg{1}.`2 ==> ={res}) 
  (ImplWord arg{2}.`1 P 
   /\  arg{1}.`1 = arg{2}.`2
   /\ tonat arg{1}.`2 = W64.to_uint arg{2}.`3
   /\ size arg{1}.`2 = 64
     ==> ={res} ).
progress. smt(). smt().
symmetry.
conseq expm_correct.
auto. auto.
transitivity M3.expm
  (={arg} /\  0 < size n{1} ==> ={res})
  (ImplWord arg{2}.`1 P 
   /\  arg{1}.`1 = arg{2}.`2
   /\ tonat arg{1}.`2 = W64.to_uint arg{2}.`3
   /\ size arg{1}.`2 = 64
     ==> ={res} ).
progress. smt(). smt().
conseq exp_2_3.
transitivity M4.expm
  (arg{1}.`1 = arg{2}.`1 /\ (W64.bits2w arg.`2{1}) = (arg.`2{2})  /\ size n{1} = 64 /\  0 < size n{1} ==> ={res})
  (ImplWord arg{2}.`1 P 
   /\  arg{1}.`1 = arg{2}.`2
   /\ arg{1}.`2 = arg{2}.`3
     ==> ={res} ).
progress. 
exists (x{1} , (W64.bits2w n{1})). progress. 
smt(). smt. auto.
conseq exp_3_4_1. 
transitivity M5.expm
 (arg{2}.`2 = arg{1}.`1 /\ arg{2}.`3 = arg{1}.`2 /\   ImplWord m{2} P ==> ={res})
  (={arg} ==> ={res}).
progress. smt(). smt().
conseq exp_4_5.   
transitivity M6.expm
  (={arg} ==> ={res})
    (={arg} ==> ={res}).
smt(). smt().
conseq exp_5_6.
conseq exp_6_real.
qed.

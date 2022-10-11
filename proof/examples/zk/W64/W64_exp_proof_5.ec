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

import Zp.
import IterOp.




module M5 = {

    proc expm' (x:W64.t, n:W64.t) : W64.t = {
    
    var x1, x2, x3, x4, bit, d, p, par, t1, t2 : W64.t;
    var ctr: int;

    d <@ ASpecFp.ith_bit(n,  (W64.size - 1));
    (x1,x2,x3) <- (W64.one,W64.one,x);
    x4 <@ ASpecFp.mulmw64(x,x);

    ctr <- W64.size - 1;
    p <- d;
    (x1,x3) <@ ASpecFp.swapw (x1,x3,as_bool d);
    (x2,x4) <@ ASpecFp.swapw (x2,x4,as_bool d); 

    while (0 < ctr) {
      ctr <- (ctr - 1);
      p <- d;
      t1 <@ ASpecFp.ith_bit(n,  (ctr + 1));
      t2 <@ ASpecFp.ith_bit(n, ctr);
      d <-  d `|` t2;
      par <- t1 `^` t2;
      (x1,x2) <@ ASpecFp.swapw (x1,x2,as_bool par); 
      x1 <@ ASpecFp.mulmw64(x1,x2); 
      x2 <@ ASpecFp.mulmw64(x2,x2);  
      (x1,x3) <@ ASpecFp.swapw (x1,x3,as_bool (d `^` p));  
      (x2,x4) <@ ASpecFp.swapw (x2,x4,as_bool (d `^` p));   
    }
    par <@ ASpecFp.ith_bit(n,0);
    (x1,x2) <@ ASpecFp.swapw (x1,x2, ! as_bool par);
    return x1;
  }  

    proc expm (m : W64.t, x:W64.t, n:W64.t) : W64.t = {
    
    var x1, x2, x3, x4, bit, d, p, par, t1, t2 : W64.t;
    var ctr:int;

    d <@ M.__ith_bit64(n,  W64.of_int (W64.size - 1));
    (x1,x2,x3) <- (W64.one,W64.one,x);
    x4 <@ M.mulm(m,x,x);

    ctr <- W64.size - 1;
    p <- d;
    (x1,x3) <@ M.swap_0(x1,x3,d);
    (x2,x4) <@ M.swap_0(x2,x4,d);

    while (0 < ctr) {
      ctr <- (ctr - 1);
      p <- d;
      t1 <@ M.__ith_bit64(n, W64.of_int (ctr + 1));
      t2 <@ M.__ith_bit64(n, W64.of_int ctr);
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


lemma exp_4_5' :
 equiv[ M4.expm ~ M5.expm'  : ={arg} ==> ={res}].
proc.
inline ASpecFp.mulmw64.
inline ASpecFp.swapw.
inline ASpecFp.ith_bit.
    wp.
    wp.
while (={ctr, n,  x1,x2,  x3, x4, d, p} ).
 wp. skip. progress. 
wp.  skip. progress. 
qed.



lemma exp_swap :
 equiv[ M.swap_0 ~ ASpecFp.swapw    : arg{2}.`1 = arg{1}.`1 /\ arg{2}.`2 = arg{1}.`2 /\   arg{1}.`3 = as_word arg{2}.`3
    ==> ={res}].
proof. 
proc.  wp. skip.
progress.
rewrite /set0_64. simplify.
case (toswap{2}). progress.
rewrite /as_word. simplify.
smt (@W64).
rewrite /as_word. simplify.
smt (@W64).
progress.
rewrite /as_word. simplify.
smt (@W64).  
rewrite /as_word. simplify.
smt (@W64).  
qed.



(* minu_one  twos_compl to_uint_and_mod*)
lemma qqq x : 0 < x < 64 => W64.one.[x] = false.
admit. (* progress. timeout 20. smt. *)
qed.

lemma exp_ithbit :
 equiv[ M.__ith_bit64 ~ ASpecFp.ith_bit    : arg{2}.`1 = arg{1}.`1 /\  arg{2}.`2 = W64.to_uint arg{1}.`2 
    /\ 0 <= ctr{2} < 64 ==> ={res} /\ (res{2} = W64.one \/ res{2} = W64.zero) ].
    symmetry.
proc. 
wp. skip. 
progress.
rewrite /ith_bitword64.
rewrite /as_word.
rewrite /truncateu8.
have -> : (to_uint (ctr{2} `&` (of_int 63)%W64))
  = (to_uint ctr{2} %% 2 ^ 6).
rewrite - to_uint_and_mod. auto.
smt. simplify.
have -> : (of_int (to_uint ctr{2} %% 64))%W8 = (of_int (to_uint ctr{2}))%W8.
smt.
rewrite /(`>>`).
rewrite /(`>>>`).
rewrite /W64.(`&`).
rewrite /map2.
case (k{2}.[to_uint ctr{2}]).
progress.
apply W64.ext_eq.
progress.
rewrite initiE. auto.
simplify.
rewrite initiE. auto.
simplify.
case (x = 0).
progress. smt. 
progress.
have -> : W64.one.[x] = false. 
smt (qqq).
auto.
progress.
apply W64.ext_eq.
progress.
rewrite initiE. auto.
simplify.
rewrite initiE. auto.
simplify.
case (x = 0).
progress. smt. 
progress. 
smt (qqq).
smt().
qed.    


lemma exp_4_5'' :
 equiv[ M5.expm' ~ M5.expm  : arg{2}.`2 = arg{1}.`1 /\ arg{2}.`3 = arg{1}.`2 /\   ImplWord m{2} P ==> ={res}].
symmetry.
proc. 
wp. 
call exp_swap.
call exp_ithbit.
while ((d{2} = W64.one \/ d{2} = W64.zero) /\ ={ctr, n,  x1,x2,  x3, x4, d, p} /\ ImplWord m{1} P /\  0 <= ctr{1} < 64).
call exp_swap.
call exp_swap.
 wp. 
call mulm_specw64.
call mulm_specw64. 
call exp_swap.
wp. 
call exp_ithbit.
call exp_ithbit.
wp.
skip. 
progress. smt . smt. smt(). smt().  smt(@W64).
rewrite /as_word.
rewrite /as_bool.  smt(@W64). smt(@W64).
wp. 
call exp_swap.
call exp_swap.
wp.
call mulm_specw64. 
wp.
call exp_ithbit. 
skip.
progress.
rewrite /as_word.
rewrite /as_bool.
smt().
rewrite /as_word.
rewrite /as_bool.
smt().
qed.



lemma exp_4_5 :
 equiv[ M4.expm ~ M5.expm : arg{2}.`2 = arg{1}.`1 /\ arg{2}.`3 = arg{1}.`2 /\   ImplWord m{2} P ==> ={res}].
transitivity M5.expm'
 (={arg} ==> ={res})
 (arg{2}.`2 = arg{1}.`1 /\ arg{2}.`3 = arg{1}.`2 /\   ImplWord m{2} P ==> ={res}).
 progress. smt(). smt().
conseq exp_4_5'.
conseq exp_4_5''.
qed.

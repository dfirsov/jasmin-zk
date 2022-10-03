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
    
    var x1, x2, x3, x4, bit, d, p, par : W64.t;
    var ctr:int;

    d <- ith_bitword64 n (W64.size - 1);
    (x1,x2,x3) <- (W64.one,W64.one,x);
    x4 <@ ASpecFp.mulmw64(x,x);

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
      x1 <@ ASpecFp.mulmw64(x1,x2); 
      x2 <@ ASpecFp.mulmw64(x2,x2);  
      (x1,x3) <- as_bool (d `^` p) ? (x3,x1) : (x1,x3);
      (x2,x4) <- as_bool (d `^` p)  ? (x4,x2) : (x2,x4);
    }
    (x1,x2) <- if ! as_bool (ith_bitword64 n 0)  then (x2,x1) else (x1, x2);    
    return x1;
  }  

    proc expm (m : W64.t, x:W64.t, n:W64.t) : W64.t = {
    
    var x1, x2, x3, x4, bit, d, p, par : W64.t;
    var ctr:int;

    d <- ith_bitword64 n (W64.size - 1);
    (x1,x2,x3) <- (W64.one,W64.one,x);
    x4 <@ M.mulm(m,x,x);

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
      x1 <@ M.mulm(m,x1,x2); 
      x2 <@ M.mulm(m,x2,x2);  
      (x1,x3) <- as_bool (d `^` p) ? (x3,x1) : (x1,x3);
      (x2,x4) <- as_bool (d `^` p)  ? (x4,x2) : (x2,x4);
    }
    (x1,x2) <- if ! as_bool (ith_bitword64 n 0)  then (x2,x1) else (x1, x2);    
    return x1;
  }  


}.



lemma exp_4_5' :
 equiv[ M4.expm ~ M5.expm'  : ={arg} ==> ={res}].
proc.
inline ASpecFp.mulmw64.
    wp.
    wp.
while (={ctr, n,  x1,x2,  x3, x4, d, p}).
 wp. skip. progress. 
wp.  
skip. 
progress.
qed.




lemma exp_4_5'' :
 equiv[ M5.expm' ~ M5.expm  : arg{2}.`2 = arg{1}.`1 /\ arg{2}.`3 = arg{1}.`2 /\   ImplWord m{2} P ==> ={res}].
symmetry.
proc. 
wp. 
while (={ctr, n,  x1,x2,  x3, x4, d, p} /\ ImplWord m{1} P).
 wp. 
call mulm_specw64.
call mulm_specw64. 
wp. 
skip. 
progress.
wp. 
call mulm_specw64. 
wp. 
skip.
progress.
qed.










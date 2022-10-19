require import Fp_w64_extract_ct.


equiv fp_w64_ct :
  M.expm ~ M.expm :
  ={M.leakages, glob M} ==> ={M.leakages}.
proof. proc; inline *; sim. qed.

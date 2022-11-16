require import Ring_ops_extract_ct.


equiv expm_ct :
  M.expm ~ M.expm :
  ={M.leakages, glob M} ==> ={M.leakages}.
proof. proc; inline *; sim. qed.

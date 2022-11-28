require import Ring_ops_extract_ct.
require import JModel List Int AllCore.



equiv expm_ct :
  M(Syscall).expm ~ M(Syscall).expm :
  ={M.leakages, glob M} ==> ={M.leakages}.
proof. 

    proc; inline *; sim. qed.



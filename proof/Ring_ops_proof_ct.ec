require import Ring_ops_extract_ct.
require import JModel List Int AllCore.



equiv expm_ct :
  M(Syscall).expm ~ M(Syscall).expm :
  ={M.leakages, glob M} ==> ={M.leakages}.
  proof.  proc.

    progress.
    inline*. sim. qed.

(*

f(x);  -->  EC: _ <- f(x);
x = f(x) ---> aux <- f(x); x <- aux;
x = f(y)



    f(x)
    f(x)


    Testsuite:

x = f(x)

y = f(x)

    f(x)

    f(x)
    f(x)

    x <- f(y)
    f(x)

    x <- f(y)
    f(y)

(x,y) <- id(y,x)

if (c)
(x,y) <- id(y,x)
  else
(x,y) <- id(x,y)

*)

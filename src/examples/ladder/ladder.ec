require import AllCore IntDiv CoreMap List.
require import JModel.




module M = {
  var leakages : leakages_t
  
  proc __ith_bit64 (k:W64.t, ctr:W64.t) : W64.t = {
    var aux: W64.t;
    
    var bit:W64.t;
    var p:W64.t;
    
    leakages <- LeakAddr([]) :: leakages;
    aux <- k;
    bit <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux <- ctr;
    p <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux <- (p `&` (W64.of_int 7));
    p <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux <- (bit `>>` (truncateu8 p));
    bit <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux <- (bit `&` (W64.of_int 1));
    bit <- aux;
    return (bit);
  }
  
  proc mulm (p:W64.t, a:W64.t, b:W64.t) : W64.t = {
    var aux_4: bool;
    var aux_3: bool;
    var aux_2: bool;
    var aux_1: bool;
    var aux_0: bool;
    var aux_5: W64.t;
    var aux: W64.t;
    
    var x:W64.t;
    var ax:W64.t;
    var bx:W64.t;
    var mh:W64.t;
    var ml:W64.t;
    var q:W64.t;
    var r:W64.t;
    var  _0:bool;
    var  _1:bool;
    var  _2:bool;
    var  _3:bool;
    var  _4:bool;
    var  _5:bool;
    var  _6:bool;
    var  _7:bool;
    var  _8:bool;
    var  _9:bool;
    
    leakages <- LeakAddr([]) :: leakages;
    aux_5 <- a;
    ax <- aux_5;
    leakages <- LeakAddr([]) :: leakages;
    aux_5 <- b;
    bx <- aux_5;
    leakages <- LeakAddr([]) :: leakages;
    (aux_4, aux_3, aux_2, aux_1, aux_0, aux_5, aux) <- MUL_64 ax bx;
     _0 <- aux_4;
     _1 <- aux_3;
     _2 <- aux_2;
     _3 <- aux_1;
     _4 <- aux_0;
    mh <- aux_5;
    ml <- aux;
    leakages <- LeakAddr([]) :: leakages;
    (aux_4, aux_3, aux_2, aux_1, aux_0, aux_5, aux) <- DIV_64 mh ml p;
     _5 <- aux_4;
     _6 <- aux_3;
     _7 <- aux_2;
     _8 <- aux_1;
     _9 <- aux_0;
    q <- aux_5;
    r <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux_5 <- r;
    x <- aux_5;
    return (x);
  }
  
  proc expm (p:W64.t, x:W64.t, n:W64.t) : W64.t = {
    var aux: W64.t;
    
    var x1:W64.t;
    var ctr:W64.t;
    var x2:W64.t;
    var bit:W64.t;
    
    leakages <- LeakAddr([]) :: leakages;
    aux <- (W64.of_int 4);
    ctr <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux <- x;
    x1 <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux <@ mulm (p, x1, x1);
    x2 <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux <- (ctr - (W64.of_int 1));
    ctr <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux <@ __ith_bit64 (n, ctr);
    bit <- aux;
    leakages <- LeakCond((bit = (W64.of_int 0))) :: LeakAddr([]) :: leakages;
    if ((bit = (W64.of_int 0))) {
      leakages <- LeakAddr([]) :: leakages;
      aux <@ mulm (p, x1, x2);
      x2 <- aux;
      leakages <- LeakAddr([]) :: leakages;
      aux <@ mulm (p, x1, x1);
      x1 <- aux;
    } else {
      leakages <- LeakAddr([]) :: leakages;
      aux <@ mulm (p, x1, x2);
      x1 <- aux;
      leakages <- LeakAddr([]) :: leakages;
      aux <@ mulm (p, x2, x2);
      x2 <- aux;
    }
    leakages <- LeakCond(((W64.of_int 0) \ult ctr)) :: LeakAddr([]) :: leakages;
    
    while (((W64.of_int 0) \ult ctr)) {
      leakages <- LeakAddr([]) :: leakages;
      aux <- (ctr - (W64.of_int 1));
      ctr <- aux;
      leakages <- LeakAddr([]) :: leakages;
      aux <@ __ith_bit64 (n, ctr);
      bit <- aux;
      leakages <- LeakCond((bit = (W64.of_int 0))) :: LeakAddr([]) :: leakages;
      if ((bit = (W64.of_int 0))) {
        leakages <- LeakAddr([]) :: leakages;
        aux <@ mulm (p, x1, x2);
        x2 <- aux;
        leakages <- LeakAddr([]) :: leakages;
        aux <@ mulm (p, x1, x1);
        x1 <- aux;
      } else {
        leakages <- LeakAddr([]) :: leakages;
        aux <@ mulm (p, x1, x2);
        x1 <- aux;
        leakages <- LeakAddr([]) :: leakages;
        aux <@ mulm (p, x2, x2);
        x2 <- aux;
      }
    leakages <- LeakCond(((W64.of_int 0) \ult ctr)) :: LeakAddr([]) :: leakages;
    
    }
    return (x1);
  }
  
  proc main () : W64.t = {
    var aux: W64.t;
    
    var r:W64.t;
    var p:W64.t;
    var x:W64.t;
    var n:W64.t;
    
    leakages <- LeakAddr([]) :: leakages;
    aux <- (W64.of_int 13);
    p <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux <- (W64.of_int 5);
    x <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux <- (W64.of_int 19);
    n <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux <@ expm (p, x, n);
    r <- aux;
    return (r);
  }
}.


equiv mulm_ct :
  M.mulm ~ M.mulm :
  ={M.leakages} ==> ={M.leakages}.
proof. proc. inline *. sim. qed.


equiv ith_bit_ct :
  M.__ith_bit64 ~ M.__ith_bit64 :
  ={M.leakages} ==> ={M.leakages}.
proof. proc. inline *. sim. qed.


equiv expm_ct :
  M.expm ~ M.expm :
  ={M.leakages, n} ==> ={M.leakages}.
  proof. proc. inline*. sim.  qed.

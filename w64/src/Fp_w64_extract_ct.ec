require import AllCore IntDiv CoreMap List Distr.
from Jasmin require import JModel.




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
    aux <- (p `&` (W64.of_int 63));
    p <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux <- (bit `>>` (truncateu8 p));
    bit <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux <- (bit `&` (W64.of_int 1));
    bit <- aux;
    return (bit);
  }
  
  proc swap_0 (x1:W64.t, x2:W64.t, toswap:W64.t) : W64.t * W64.t = {
    var aux_3: bool;
    var aux_2: bool;
    var aux_1: bool;
    var aux_0: bool;
    var aux: bool;
    var aux_4: W64.t;
    
    var _of_:bool;
    var _cf_:bool;
    var _sf_:bool;
    var _zf_:bool;
    var mask:W64.t;
    var x2r:W64.t;
    var x1r:W64.t;
    var t:W64.t;
    var  _0:bool;
    
    leakages <- LeakAddr([]) :: leakages;
    (aux_3, aux_2, aux_1, aux_0, aux, aux_4) <- set0_64 ;
    _of_ <- aux_3;
    _cf_ <- aux_2;
    _sf_ <- aux_1;
     _0 <- aux_0;
    _zf_ <- aux;
    mask <- aux_4;
    leakages <- LeakAddr([]) :: leakages;
    aux_4 <- (mask - toswap);
    mask <- aux_4;
    leakages <- LeakAddr([]) :: leakages;
    aux_4 <- x2;
    x2r <- aux_4;
    leakages <- LeakAddr([]) :: leakages;
    aux_4 <- x1;
    x1r <- aux_4;
    leakages <- LeakAddr([]) :: leakages;
    aux_4 <- x2r;
    t <- aux_4;
    leakages <- LeakAddr([]) :: leakages;
    aux_4 <- (t `^` x1r);
    t <- aux_4;
    leakages <- LeakAddr([]) :: leakages;
    aux_4 <- (t `&` mask);
    t <- aux_4;
    leakages <- LeakAddr([]) :: leakages;
    aux_4 <- (x1r `^` t);
    x1r <- aux_4;
    leakages <- LeakAddr([]) :: leakages;
    aux_4 <- (x2r `^` t);
    x2r <- aux_4;
    leakages <- LeakAddr([]) :: leakages;
    aux_4 <- x1r;
    x1 <- aux_4;
    leakages <- LeakAddr([]) :: leakages;
    aux_4 <- x2r;
    x2 <- aux_4;
    return (x1, x2);
  }
  
  proc addm (p:W64.t, a:W64.t, b:W64.t) : W64.t = {
    var aux_0: bool;
    var aux: W64.t;
    
    var x:W64.t;
    var k1:W64.t;
    var k2:W64.t;
    var _cf:bool;
    
    leakages <- LeakAddr([]) :: leakages;
    aux <- (W64.of_int 0);
    k1 <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux <- (W64.of_int 0);
    k2 <- aux;
    leakages <- LeakAddr([]) :: leakages;
    (aux_0, aux) <- adc_64 a b false;
    _cf <- aux_0;
    x <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux <- (_cf ? p : k1);
    k1 <- aux;
    leakages <- LeakAddr([]) :: leakages;
    (aux_0, aux) <- sbb_64 x p false;
    _cf <- aux_0;
    x <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux <- (_cf ? p : k2);
    k2 <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux <- (x + k2);
    x <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux <- (x - k1);
    x <- aux;
    return (x);
  }
  
  proc subm (p:W64.t, a:W64.t, b:W64.t) : W64.t = {
    var aux_0: bool;
    var aux: W64.t;
    
    var x:W64.t;
    var k:W64.t;
    var _cf:bool;
    
    leakages <- LeakAddr([]) :: leakages;
    aux <- (W64.of_int 0);
    k <- aux;
    leakages <- LeakAddr([]) :: leakages;
    (aux_0, aux) <- sbb_64 a b false;
    _cf <- aux_0;
    x <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux <- (_cf ? p : k);
    k <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux <- (x + k);
    x <- aux;
    return (x);
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
  
  proc expm (m:W64.t, x:W64.t, n:W64.t) : W64.t = {
    var aux_0: W64.t;
    var aux: W64.t;
    
    var x1:W64.t;
    var ctr:W64.t;
    var d:W64.t;
    var x2:W64.t;
    var x3:W64.t;
    var x4:W64.t;
    var p:W64.t;
    var lbit:W64.t;
    var t1:W64.t;
    var t2:W64.t;
    var q:W64.t;
    var par:W64.t;
    var cbit:W64.t;
    
    leakages <- LeakAddr([]) :: leakages;
    aux_0 <- (W64.of_int 63);
    ctr <- aux_0;
    leakages <- LeakAddr([]) :: leakages;
    aux_0 <@ __ith_bit64 (n, ctr);
    d <- aux_0;
    leakages <- LeakAddr([]) :: leakages;
    aux_0 <- (W64.of_int 1);
    x1 <- aux_0;
    leakages <- LeakAddr([]) :: leakages;
    aux_0 <- (W64.of_int 1);
    x2 <- aux_0;
    leakages <- LeakAddr([]) :: leakages;
    aux_0 <- x;
    x3 <- aux_0;
    leakages <- LeakAddr([]) :: leakages;
    aux_0 <@ mulm (m, x, x);
    x4 <- aux_0;
    leakages <- LeakAddr([]) :: leakages;
    aux_0 <- d;
    p <- aux_0;
    leakages <- LeakAddr([]) :: leakages;
    (aux_0, aux) <@ swap_0 (x1, x3, d);
    x1 <- aux_0;
    x3 <- aux;
    leakages <- LeakAddr([]) :: leakages;
    (aux_0, aux) <@ swap_0 (x2, x4, d);
    x2 <- aux_0;
    x4 <- aux;
    
    leakages <- LeakCond(((W64.of_int 0) \ult ctr)) :: LeakAddr([]) :: leakages;
    
    while (((W64.of_int 0) \ult ctr)) {
      leakages <- LeakAddr([]) :: leakages;
      aux_0 <- ctr;
      lbit <- aux_0;
      leakages <- LeakAddr([]) :: leakages;
      aux_0 <- (ctr - (W64.of_int 1));
      ctr <- aux_0;
      leakages <- LeakAddr([]) :: leakages;
      aux_0 <@ __ith_bit64 (n, lbit);
      t1 <- aux_0;
      leakages <- LeakAddr([]) :: leakages;
      aux_0 <@ __ith_bit64 (n, ctr);
      t2 <- aux_0;
      leakages <- LeakAddr([]) :: leakages;
      aux_0 <- d;
      p <- aux_0;
      leakages <- LeakAddr([]) :: leakages;
      aux_0 <- d;
      q <- aux_0;
      leakages <- LeakAddr([]) :: leakages;
      aux_0 <- (d `|` t2);
      d <- aux_0;
      leakages <- LeakAddr([]) :: leakages;
      aux_0 <- (t1 `^` t2);
      par <- aux_0;
      leakages <- LeakAddr([]) :: leakages;
      (aux_0, aux) <@ swap_0 (x1, x2, par);
      x1 <- aux_0;
      x2 <- aux;
      leakages <- LeakAddr([]) :: leakages;
      aux_0 <@ mulm (m, x1, x2);
      x1 <- aux_0;
      leakages <- LeakAddr([]) :: leakages;
      aux_0 <@ mulm (m, x2, x2);
      x2 <- aux_0;
      leakages <- LeakAddr([]) :: leakages;
      aux_0 <- (q `|` t2);
      q <- aux_0;
      leakages <- LeakAddr([]) :: leakages;
      aux_0 <- (q `^` p);
      cbit <- aux_0;
      leakages <- LeakAddr([]) :: leakages;
      (aux_0, aux) <@ swap_0 (x1, x3, cbit);
      x1 <- aux_0;
      x3 <- aux;
      leakages <- LeakAddr([]) :: leakages;
      (aux_0, aux) <@ swap_0 (x2, x4, cbit);
      x2 <- aux_0;
      x4 <- aux;
    leakages <- LeakCond(((W64.of_int 0) \ult ctr)) :: LeakAddr([]) :: leakages;
    
    }
    leakages <- LeakAddr([]) :: leakages;
    aux_0 <@ __ith_bit64 (n, (W64.of_int 0));
    par <- aux_0;
    leakages <- LeakAddr([]) :: leakages;
    (aux_0, aux) <@ swap_0 (x2, x1, par);
    x1 <- aux_0;
    x2 <- aux;
    return (x1);
  }
  
  proc toEC () : unit = {
    var aux: W64.t;
    
    var p:W64.t;
    var a:W64.t;
    var b:W64.t;
    var r:W64.t;
    
    leakages <- LeakAddr([]) :: leakages;
    aux <@ addm (p, a, b);
    r <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux <@ subm (p, a, b);
    r <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux <@ mulm (p, a, b);
    r <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux <@ expm (p, a, b);
    r <- aux;
    return ();
  }
}.


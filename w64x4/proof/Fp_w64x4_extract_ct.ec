require import AllCore IntDiv CoreMap List Distr.
from Jasmin require import JModel.

require import Array32.
require import WArray256.



module M = {
  var leakages : leakages_t
  
  proc bn_subc (a:W64.t Array32.t, b:W64.t Array32.t) : bool *
                                                        W64.t Array32.t = {
    var aux_0: bool;
    var aux_1: int;
    var aux: W64.t;
    
    var cf:bool;
    var x1:W64.t;
    var x2:W64.t;
    var i:int;
    
    leakages <- LeakAddr([0]) :: leakages;
    aux <- a.[0];
    x1 <- aux;
    leakages <- LeakAddr([0]) :: leakages;
    aux <- b.[0];
    x2 <- aux;
    leakages <- LeakAddr([]) :: leakages;
    (aux_0, aux) <- sbb_64 x1 x2 false;
    cf <- aux_0;
    x1 <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux <- x1;
    leakages <- LeakAddr([0]) :: leakages;
    a.[0] <- aux;
    leakages <- LeakFor(1,32) :: LeakAddr([]) :: leakages;
    i <- 1;
    while (i < 32) {
      leakages <- LeakAddr([i]) :: leakages;
      aux <- a.[i];
      x1 <- aux;
      leakages <- LeakAddr([i]) :: leakages;
      aux <- b.[i];
      x2 <- aux;
      leakages <- LeakAddr([]) :: leakages;
      (aux_0, aux) <- sbb_64 x1 x2 cf;
      cf <- aux_0;
      x1 <- aux;
      leakages <- LeakAddr([]) :: leakages;
      aux <- x1;
      leakages <- LeakAddr([i]) :: leakages;
      a.[i] <- aux;
      i <- i + 1;
    }
    return (cf, a);
  }
  
  proc bn_copy (a:W64.t Array32.t) : W64.t Array32.t = {
    var aux: int;
    var aux_0: W64.t;
    
    var r:W64.t Array32.t;
    var i:int;
    var t:W64.t;
    r <- witness;
    leakages <- LeakFor(0,32) :: LeakAddr([]) :: leakages;
    i <- 0;
    while (i < 32) {
      leakages <- LeakAddr([i]) :: leakages;
      aux_0 <- a.[i];
      t <- aux_0;
      leakages <- LeakAddr([]) :: leakages;
      aux_0 <- t;
      leakages <- LeakAddr([i]) :: leakages;
      r.[i] <- aux_0;
      i <- i + 1;
    }
    return (r);
  }
  
  proc bn_set0 (a:W64.t Array32.t) : W64.t Array32.t = {
    var aux: int;
    var aux_0: W64.t;
    
    var i:int;
    
    leakages <- LeakFor(0,32) :: LeakAddr([]) :: leakages;
    i <- 0;
    while (i < 32) {
      leakages <- LeakAddr([]) :: leakages;
      aux_0 <- (W64.of_int 0);
      leakages <- LeakAddr([i]) :: leakages;
      a.[i] <- aux_0;
      i <- i + 1;
    }
    return (a);
  }
  
  proc bn_addc (a:W64.t Array32.t, b:W64.t Array32.t) : bool *
                                                        W64.t Array32.t = {
    var aux_0: bool;
    var aux_1: int;
    var aux: W64.t;
    
    var cf:bool;
    var x1:W64.t;
    var x2:W64.t;
    var i:int;
    
    leakages <- LeakAddr([0]) :: leakages;
    aux <- a.[0];
    x1 <- aux;
    leakages <- LeakAddr([0]) :: leakages;
    aux <- b.[0];
    x2 <- aux;
    leakages <- LeakAddr([]) :: leakages;
    (aux_0, aux) <- adc_64 x1 x2 false;
    cf <- aux_0;
    x1 <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux <- x1;
    leakages <- LeakAddr([0]) :: leakages;
    a.[0] <- aux;
    leakages <- LeakFor(1,32) :: LeakAddr([]) :: leakages;
    i <- 1;
    while (i < 32) {
      leakages <- LeakAddr([i]) :: leakages;
      aux <- a.[i];
      x1 <- aux;
      leakages <- LeakAddr([i]) :: leakages;
      aux <- b.[i];
      x2 <- aux;
      leakages <- LeakAddr([]) :: leakages;
      (aux_0, aux) <- adc_64 x1 x2 cf;
      cf <- aux_0;
      x1 <- aux;
      leakages <- LeakAddr([]) :: leakages;
      aux <- x1;
      leakages <- LeakAddr([i]) :: leakages;
      a.[i] <- aux;
      i <- i + 1;
    }
    return (cf, a);
  }
  
  proc swapr (x:W64.t Array32.t, y:W64.t Array32.t, swap_0:W64.t) : W64.t Array32.t *
                                                                    W64.t Array32.t = {
    var aux_0: int;
    var aux: W64.t;
    
    var mask:W64.t;
    var i:int;
    var tmp1:W64.t;
    var tmp2:W64.t;
    
    leakages <- LeakAddr([]) :: leakages;
    aux <- (swap_0 * (W64.of_int 18446744073709551615));
    mask <- aux;
    leakages <- LeakFor(0,32) :: LeakAddr([]) :: leakages;
    i <- 0;
    while (i < 32) {
      leakages <- LeakAddr([i]) :: leakages;
      aux <- x.[i];
      tmp1 <- aux;
      leakages <- LeakAddr([i]) :: leakages;
      aux <- (tmp1 `^` y.[i]);
      tmp1 <- aux;
      leakages <- LeakAddr([]) :: leakages;
      aux <- (tmp1 `&` mask);
      tmp1 <- aux;
      leakages <- LeakAddr([i]) :: leakages;
      aux <- (x.[i] `^` tmp1);
      leakages <- LeakAddr([i]) :: leakages;
      x.[i] <- aux;
      leakages <- LeakAddr([i]) :: leakages;
      aux <- y.[i];
      tmp2 <- aux;
      leakages <- LeakAddr([]) :: leakages;
      aux <- (tmp2 `^` tmp1);
      tmp2 <- aux;
      leakages <- LeakAddr([]) :: leakages;
      aux <- tmp2;
      leakages <- LeakAddr([i]) :: leakages;
      y.[i] <- aux;
      i <- i + 1;
    }
    return (x, y);
  }
  
  proc ith_bit64 (k:W64.t, ctr:W64.t) : W64.t = {
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
  
  proc ith_bit (kk:W64.t Array32.t, ctr:W64.t) : W64.t = {
    var aux: W64.t;
    
    var bit:W64.t;
    var ctr2:W64.t;
    var ctr3:W64.t;
    var c1:W64.t;
    var c2:W64.t;
    var r:W64.t;
    
    leakages <- LeakAddr([]) :: leakages;
    aux <- ctr;
    ctr2 <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux <- ctr;
    ctr3 <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux <- (ctr2 `>>` (W8.of_int 6));
    c1 <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux <- (ctr3 `&` (W64.of_int 63));
    c2 <- aux;
    leakages <- LeakAddr([(W64.to_uint c1)]) :: leakages;
    aux <- kk.[(W64.to_uint c1)];
    r <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux <@ ith_bit64 (r, c2);
    bit <- aux;
    return (bit);
  }
  
  proc cminusP (p:W64.t Array32.t, x:W64.t Array32.t) : W64.t Array32.t = {
    var aux_0: bool;
    var aux_1: int;
    var aux_2: W64.t;
    var aux: W64.t Array32.t;
    
    var z:W64.t Array32.t;
    var cf:bool;
    var i:int;
    var r1:W64.t;
    var r2:W64.t;
    z <- witness;
    leakages <- LeakAddr([]) :: leakages;
    aux <@ bn_copy (x);
    z <- aux;
    leakages <- LeakAddr([]) :: leakages;
    (aux_0, aux) <@ bn_subc (z, p);
    cf <- aux_0;
    z <- aux;
    leakages <- LeakFor(0,32) :: LeakAddr([]) :: leakages;
    i <- 0;
    while (i < 32) {
      leakages <- LeakAddr([i]) :: leakages;
      aux_2 <- z.[i];
      r1 <- aux_2;
      leakages <- LeakAddr([i]) :: leakages;
      aux_2 <- x.[i];
      r2 <- aux_2;
      leakages <- LeakAddr([]) :: leakages;
      aux_2 <- (cf ? r2 : r1);
      r1 <- aux_2;
      leakages <- LeakAddr([]) :: leakages;
      aux_2 <- r1;
      leakages <- LeakAddr([i]) :: leakages;
      x.[i] <- aux_2;
      i <- i + 1;
    }
    return (x);
  }
  
  proc addm (p:W64.t Array32.t, a:W64.t Array32.t, b:W64.t Array32.t) : 
  W64.t Array32.t = {
    var aux: bool;
    var aux_0: W64.t Array32.t;
    
    var  _0:bool;
    
    leakages <- LeakAddr([]) :: leakages;
    (aux, aux_0) <@ bn_addc (a, b);
     _0 <- aux;
    a <- aux_0;
    leakages <- LeakAddr([]) :: leakages;
    aux_0 <@ cminusP (p, a);
    a <- aux_0;
    return (a);
  }
  
  proc mulm (m:W64.t Array32.t, x:W64.t Array32.t, n:W64.t Array32.t) : 
  W64.t Array32.t = {
    var aux: W64.t;
    var aux_1: W64.t Array32.t;
    var aux_0: W64.t Array32.t;
    
    var x1:W64.t Array32.t;
    var ctr:W64.t;
    var x2:W64.t Array32.t;
    var d:W64.t;
    var x3:W64.t Array32.t;
    var x4:W64.t Array32.t;
    var p:W64.t;
    var lbit:W64.t;
    var t1:W64.t;
    var t2:W64.t;
    var q:W64.t;
    var par:W64.t;
    x1 <- witness;
    x2 <- witness;
    x3 <- witness;
    x4 <- witness;
    leakages <- LeakAddr([]) :: leakages;
    aux <- (W64.of_int ((32 * 64) - 1));
    ctr <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux_1 <@ bn_set0 (x1);
    x1 <- aux_1;
    leakages <- LeakAddr([]) :: leakages;
    aux_1 <@ bn_set0 (x2);
    x2 <- aux_1;
    leakages <- LeakAddr([]) :: leakages;
    aux <@ ith_bit (n, ctr);
    d <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux_1 <@ bn_copy (x);
    x3 <- aux_1;
    leakages <- LeakAddr([]) :: leakages;
    aux_1 <@ addm (m, x, x);
    x4 <- aux_1;
    leakages <- LeakAddr([]) :: leakages;
    aux <- d;
    p <- aux;
    leakages <- LeakAddr([]) :: leakages;
    (aux_1, aux_0) <@ swapr (x1, x3, d);
    x1 <- aux_1;
    x3 <- aux_0;
    leakages <- LeakAddr([]) :: leakages;
    (aux_1, aux_0) <@ swapr (x2, x4, d);
    x2 <- aux_1;
    x4 <- aux_0;
    
    leakages <- LeakCond(((W64.of_int 0) \ult ctr)) :: LeakAddr([]) :: leakages;
    
    while (((W64.of_int 0) \ult ctr)) {
      leakages <- LeakAddr([]) :: leakages;
      aux <- ctr;
      lbit <- aux;
      leakages <- LeakAddr([]) :: leakages;
      aux <- (ctr - (W64.of_int 1));
      ctr <- aux;
      leakages <- LeakAddr([]) :: leakages;
      aux <@ ith_bit (n, lbit);
      t1 <- aux;
      leakages <- LeakAddr([]) :: leakages;
      aux <@ ith_bit (n, ctr);
      t2 <- aux;
      leakages <- LeakAddr([]) :: leakages;
      aux <- d;
      p <- aux;
      leakages <- LeakAddr([]) :: leakages;
      aux <- d;
      q <- aux;
      leakages <- LeakAddr([]) :: leakages;
      aux <- (d `|` t2);
      d <- aux;
      leakages <- LeakAddr([]) :: leakages;
      aux <- (t1 `^` t2);
      par <- aux;
      leakages <- LeakAddr([]) :: leakages;
      (aux_1, aux_0) <@ swapr (x1, x2, par);
      x1 <- aux_1;
      x2 <- aux_0;
      leakages <- LeakAddr([]) :: leakages;
      aux_1 <@ addm (m, x1, x2);
      x1 <- aux_1;
    leakages <- LeakCond(((W64.of_int 0) \ult ctr)) :: LeakAddr([]) :: leakages;
    
    }
    leakages <- LeakAddr([]) :: leakages;
    aux <@ ith_bit (n, (W64.of_int 0));
    par <- aux;
    leakages <- LeakAddr([]) :: leakages;
    (aux_1, aux_0) <@ swapr (x2, x1, par);
    x1 <- aux_1;
    x2 <- aux_0;
    return (x1);
  }
  
  proc toEC () : unit = {
    var aux_0: W64.t;
    var aux_1: W64.t Array32.t;
    var aux: W64.t Array32.t;
    
    var p:W64.t Array32.t;
    var a:W64.t Array32.t;
    var b:W64.t Array32.t;
    var r:W64.t Array32.t;
    var x:W64.t;
    var  _0:W64.t Array32.t;
     _0 <- witness;
    a <- witness;
    b <- witness;
    p <- witness;
    r <- witness;
    leakages <- LeakAddr([]) :: leakages;
    aux_1 <@ addm (p, a, b);
    r <- aux_1;
    leakages <- LeakAddr([]) :: leakages;
    aux_1 <@ mulm (p, a, b);
    r <- aux_1;
    leakages <- LeakAddr([]) :: leakages;
    aux_0 <@ ith_bit (a, x);
    x <- aux_0;
    leakages <- LeakAddr([]) :: leakages;
    (aux_1, aux) <@ swapr (a, a, x);
     _0 <- aux_1;
    a <- aux;
    return ();
  }
}.


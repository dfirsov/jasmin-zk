require import AllCore IntDiv CoreMap List Distr.
require import JModel.

require import Array4.
require import WArray32.



module M = {
  var leakages : leakages_t
  
  proc bn_subc (a:W64.t Array4.t, b:W64.t Array4.t) : bool * W64.t Array4.t = {
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
    (aux_0, aux) <- subc_64 x1 x2 false;
    cf <- aux_0;
    x1 <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux <- x1;
    leakages <- LeakAddr([0]) :: leakages;
    a.[0] <- aux;
    leakages <- LeakFor(1,4) :: LeakAddr([]) :: leakages;
    i <- 1;
    while (i < 4) {
      leakages <- LeakAddr([i]) :: leakages;
      aux <- a.[i];
      x1 <- aux;
      leakages <- LeakAddr([i]) :: leakages;
      aux <- b.[i];
      x2 <- aux;
      leakages <- LeakAddr([]) :: leakages;
      (aux_0, aux) <- subc_64 x1 x2 cf;
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
  
  proc bn_addc (a:W64.t Array4.t, b:W64.t Array4.t) : bool * W64.t Array4.t = {
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
    (aux_0, aux) <- addc_64 x1 x2 false;
    cf <- aux_0;
    x1 <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux <- x1;
    leakages <- LeakAddr([0]) :: leakages;
    a.[0] <- aux;
    leakages <- LeakFor(1,4) :: LeakAddr([]) :: leakages;
    i <- 1;
    while (i < 4) {
      leakages <- LeakAddr([i]) :: leakages;
      aux <- a.[i];
      x1 <- aux;
      leakages <- LeakAddr([i]) :: leakages;
      aux <- b.[i];
      x2 <- aux;
      leakages <- LeakAddr([]) :: leakages;
      (aux_0, aux) <- addc_64 x1 x2 cf;
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
  
  proc ith_bit (kk:W64.t Array4.t, ctr:W64.t) : W64.t = {
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
  
  proc swapr (x:W64.t Array4.t, y:W64.t Array4.t, swap_0:W64.t) : W64.t Array4.t *
                                                                  W64.t Array4.t = {
    var aux_0: int;
    var aux: W64.t;
    
    var mask:W64.t;
    var i:int;
    var tmp1:W64.t;
    var tmp2:W64.t;
    
    leakages <- LeakAddr([]) :: leakages;
    aux <- (swap_0 * (W64.of_int 18446744073709551615));
    mask <- aux;
    leakages <- LeakFor(0,4) :: LeakAddr([]) :: leakages;
    i <- 0;
    while (i < 4) {
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
  
  proc cminusP (p:W64.t Array4.t, x:W64.t Array4.t) : W64.t Array4.t = {
    var aux_0: bool;
    var aux: W64.t;
    var aux_1: W64.t Array4.t;
    
    var t:W64.t Array4.t;
    var z:W64.t Array4.t;
    var cf:bool;
    var r1:W64.t;
    var r2:W64.t;
    t <- witness;
    z <- witness;
    leakages <- LeakAddr([0]) :: leakages;
    aux <- x.[0];
    leakages <- LeakAddr([0]) :: leakages;
    z.[0] <- aux;
    leakages <- LeakAddr([1]) :: leakages;
    aux <- x.[1];
    leakages <- LeakAddr([1]) :: leakages;
    z.[1] <- aux;
    leakages <- LeakAddr([2]) :: leakages;
    aux <- x.[2];
    leakages <- LeakAddr([2]) :: leakages;
    z.[2] <- aux;
    leakages <- LeakAddr([3]) :: leakages;
    aux <- x.[3];
    leakages <- LeakAddr([3]) :: leakages;
    z.[3] <- aux;
    leakages <- LeakAddr([]) :: leakages;
    (aux_0, aux_1) <@ bn_subc (z, p);
    cf <- aux_0;
    t <- aux_1;
    leakages <- LeakAddr([0]) :: leakages;
    aux <- t.[0];
    r1 <- aux;
    leakages <- LeakAddr([0]) :: leakages;
    aux <- x.[0];
    r2 <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux <- (cf ? r2 : r1);
    r1 <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux <- r1;
    leakages <- LeakAddr([0]) :: leakages;
    t.[0] <- aux;
    leakages <- LeakAddr([1]) :: leakages;
    aux <- t.[1];
    r1 <- aux;
    leakages <- LeakAddr([1]) :: leakages;
    aux <- x.[1];
    r2 <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux <- (cf ? r2 : r1);
    r1 <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux <- r1;
    leakages <- LeakAddr([1]) :: leakages;
    t.[1] <- aux;
    leakages <- LeakAddr([2]) :: leakages;
    aux <- t.[2];
    r1 <- aux;
    leakages <- LeakAddr([2]) :: leakages;
    aux <- x.[2];
    r2 <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux <- (cf ? r2 : r1);
    r1 <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux <- r1;
    leakages <- LeakAddr([2]) :: leakages;
    t.[2] <- aux;
    leakages <- LeakAddr([3]) :: leakages;
    aux <- t.[3];
    r1 <- aux;
    leakages <- LeakAddr([3]) :: leakages;
    aux <- x.[3];
    r2 <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux <- (cf ? r2 : r1);
    r1 <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux <- r1;
    leakages <- LeakAddr([3]) :: leakages;
    t.[3] <- aux;
    return (t);
  }
  
  proc addm (p:W64.t Array4.t, a:W64.t Array4.t, b:W64.t Array4.t) : 
  W64.t Array4.t = {
    var aux: bool;
    var aux_1: W64.t;
    var aux_0: W64.t Array4.t;
    
    var f:W64.t Array4.t;
    var z:W64.t Array4.t;
    var  _0:bool;
    f <- witness;
    z <- witness;
    leakages <- LeakAddr([]) :: leakages;
    (aux, aux_0) <@ bn_addc (a, b);
     _0 <- aux;
    f <- aux_0;
    leakages <- LeakAddr([0]) :: leakages;
    aux_1 <- f.[0];
    leakages <- LeakAddr([0]) :: leakages;
    z.[0] <- aux_1;
    leakages <- LeakAddr([1]) :: leakages;
    aux_1 <- f.[1];
    leakages <- LeakAddr([1]) :: leakages;
    z.[1] <- aux_1;
    leakages <- LeakAddr([2]) :: leakages;
    aux_1 <- f.[2];
    leakages <- LeakAddr([2]) :: leakages;
    z.[2] <- aux_1;
    leakages <- LeakAddr([3]) :: leakages;
    aux_1 <- f.[3];
    leakages <- LeakAddr([3]) :: leakages;
    z.[3] <- aux_1;
    leakages <- LeakAddr([]) :: leakages;
    aux_0 <@ cminusP (p, z);
    f <- aux_0;
    return (f);
  }
  
  proc mulm (m:W64.t Array4.t, x:W64.t Array4.t, n:W64.t Array4.t) : 
  W64.t Array4.t = {
    var aux: W64.t;
    var aux_1: W64.t Array4.t;
    var aux_0: W64.t Array4.t;
    
    var x1:W64.t Array4.t;
    var ctr:W64.t;
    var x2:W64.t Array4.t;
    var d:W64.t;
    var x3:W64.t Array4.t;
    var x4:W64.t Array4.t;
    var p:W64.t;
    var lbit:W64.t;
    var t1:W64.t;
    var t2:W64.t;
    var q:W64.t;
    var par:W64.t;
    var cbit:W64.t;
    x1 <- witness;
    x2 <- witness;
    x3 <- witness;
    x4 <- witness;
    leakages <- LeakAddr([]) :: leakages;
    aux <- (W64.of_int ((4 * 64) - 1));
    ctr <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux <- (W64.of_int 0);
    leakages <- LeakAddr([0]) :: leakages;
    x1.[0] <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux <- (W64.of_int 0);
    leakages <- LeakAddr([1]) :: leakages;
    x1.[1] <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux <- (W64.of_int 0);
    leakages <- LeakAddr([2]) :: leakages;
    x1.[2] <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux <- (W64.of_int 0);
    leakages <- LeakAddr([3]) :: leakages;
    x1.[3] <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux <- (W64.of_int 0);
    leakages <- LeakAddr([0]) :: leakages;
    x2.[0] <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux <- (W64.of_int 0);
    leakages <- LeakAddr([1]) :: leakages;
    x2.[1] <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux <- (W64.of_int 0);
    leakages <- LeakAddr([2]) :: leakages;
    x2.[2] <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux <- (W64.of_int 0);
    leakages <- LeakAddr([3]) :: leakages;
    x2.[3] <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux <@ ith_bit (n, ctr);
    d <- aux;
    leakages <- LeakAddr([0]) :: leakages;
    aux <- x.[0];
    leakages <- LeakAddr([0]) :: leakages;
    x3.[0] <- aux;
    leakages <- LeakAddr([1]) :: leakages;
    aux <- x.[1];
    leakages <- LeakAddr([1]) :: leakages;
    x3.[1] <- aux;
    leakages <- LeakAddr([2]) :: leakages;
    aux <- x.[2];
    leakages <- LeakAddr([2]) :: leakages;
    x3.[2] <- aux;
    leakages <- LeakAddr([3]) :: leakages;
    aux <- x.[3];
    leakages <- LeakAddr([3]) :: leakages;
    x3.[3] <- aux;
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
      leakages <- LeakAddr([]) :: leakages;
      aux_1 <@ addm (m, x2, x2);
      x2 <- aux_1;
      leakages <- LeakAddr([]) :: leakages;
      aux <- (q `|` t2);
      q <- aux;
      leakages <- LeakAddr([]) :: leakages;
      aux <- (q `^` p);
      cbit <- aux;
      leakages <- LeakAddr([]) :: leakages;
      (aux_1, aux_0) <@ swapr (x1, x3, cbit);
      x1 <- aux_1;
      x3 <- aux_0;
      leakages <- LeakAddr([]) :: leakages;
      (aux_1, aux_0) <@ swapr (x2, x4, cbit);
      x2 <- aux_1;
      x4 <- aux_0;
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
    var aux: W64.t Array4.t;
    
    var p:W64.t Array4.t;
    var a:W64.t Array4.t;
    var b:W64.t Array4.t;
    var r:W64.t Array4.t;
    a <- witness;
    b <- witness;
    p <- witness;
    r <- witness;
    leakages <- LeakAddr([]) :: leakages;
    aux <@ mulm (p, a, b);
    r <- aux;
    return ();
  }
}.


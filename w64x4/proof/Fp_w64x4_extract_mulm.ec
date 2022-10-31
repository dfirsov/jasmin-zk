require import AllCore IntDiv CoreMap List Distr.
require import JModel.

require import Array4.
require import WArray32.



module M = {
  proc ith_bit64 (k:W64.t, ctr:W64.t) : W64.t = {
    
    var bit:W64.t;
    var p:W64.t;
    
    bit <- k;
    p <- ctr;
    p <- (p `&` (W64.of_int 63));
    bit <- (bit `>>` (truncateu8 p));
    bit <- (bit `&` (W64.of_int 1));
    return (bit);
  }
  
  proc ith_bit (kk:W64.t Array4.t, ctr:W64.t) : W64.t = {
    
    var bit:W64.t;
    var ctr2:W64.t;
    var ctr3:W64.t;
    var c1:W64.t;
    var c2:W64.t;
    var r:W64.t;
    
    ctr2 <- ctr;
    ctr3 <- ctr;
    c1 <- (ctr2 `>>` (W8.of_int 6));
    c2 <- (ctr3 `&` (W64.of_int 63));
    r <- kk.[(W64.to_uint c1)];
    bit <@ ith_bit64 (r, c2);
    return (bit);
  }
  
  proc swapr (x:W64.t Array4.t, y:W64.t Array4.t, swap_0:W64.t) : W64.t Array4.t *
                                                                  W64.t Array4.t = {
    var aux: int;
    
    var mask:W64.t;
    var i:int;
    var tmp1:W64.t;
    var tmp2:W64.t;
    
    mask <- (swap_0 * (W64.of_int 18446744073709551615));
    i <- 0;
    while (i < 4) {
      tmp1 <- x.[i];
      tmp1 <- (tmp1 `^` y.[i]);
      tmp1 <- (tmp1 `&` mask);
      x.[i] <- (x.[i] `^` tmp1);
      tmp2 <- y.[i];
      tmp2 <- (tmp2 `^` tmp1);
      y.[i] <- tmp2;
      i <- i + 1;
    }
    return (x, y);
  }
  
  proc bn_subc (a:W64.t Array4.t, b:W64.t Array4.t) : bool * W64.t Array4.t = {
    var aux: bool;
    var aux_1: int;
    var aux_0: W64.t;
    
    var cf:bool;
    var i:int;
    
    (aux, aux_0) <- subc_64 a.[0] b.[0] false;
    cf <- aux;
    a.[0] <- aux_0;
    i <- 1;
    while (i < 4) {
      (aux, aux_0) <- subc_64 a.[i] b.[i] cf;
      cf <- aux;
      a.[i] <- aux_0;
      i <- i + 1;
    }
    return (cf, a);
  }
  
  proc bn_addc (a:W64.t Array4.t, b:W64.t Array4.t) : bool * W64.t Array4.t = {
    var aux: int;
    
    var cf:bool;
    var x1:W64.t;
    var x2:W64.t;
    var i:int;
    
    x1 <- a.[0];
    x2 <- b.[0];
    (cf, x1) <- addc_64 x1 x2 false;
    a.[0] <- x1;
    i <- 1;
    while (i < 4) {
      x1 <- a.[i];
      x2 <- b.[i];
      (cf, x1) <- addc_64 x1 x2 cf;
      a.[i] <- x1;
      i <- i + 1;
    }
    return (cf, a);
  }
  
  proc cminusP (x:W64.t Array4.t) : W64.t Array4.t = {
    
    var t:W64.t Array4.t;
    var p:W64.t Array4.t;
    var cf:bool;
    p <- witness;
    t <- witness;
    p.[0] <- (W64.of_int 18446744073709551597);
    p.[1] <- (W64.of_int 18446744073709551615);
    p.[2] <- (W64.of_int 18446744073709551615);
    p.[3] <- (W64.of_int 9223372036854775807);
    (cf, t) <@ bn_subc (x, p);
    t.[0] <- (cf ? x.[0] : t.[0]);
    t.[1] <- (cf ? x.[1] : t.[1]);
    t.[2] <- (cf ? x.[2] : t.[2]);
    t.[3] <- (cf ? x.[3] : t.[3]);
    return (t);
  }
  
  proc addm (a:W64.t Array4.t, b:W64.t Array4.t) : W64.t Array4.t = {
    
    var f:W64.t Array4.t;
    var  _0:bool;
    f <- witness;
    ( _0, f) <@ bn_addc (a, b);
    f <@ cminusP (f);
    return (f);
  }
  
  proc addm3 (m:W64.t Array4.t, a:W64.t Array4.t, b:W64.t Array4.t) : 
  W64.t Array4.t = {
    
    var f:W64.t Array4.t;
    f <- witness;
    f <@ addm (a, b);
    return (f);
  }
  
  proc mulm_ladder (m:W64.t Array4.t, x:W64.t Array4.t, n:W64.t Array4.t) : 
  W64.t Array4.t = {
    
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
    ctr <- (W64.of_int ((4 * 64) - 1));
    x1.[0] <- (W64.of_int 0);
    x1.[1] <- (W64.of_int 0);
    x1.[2] <- (W64.of_int 0);
    x1.[3] <- (W64.of_int 0);
    x2.[0] <- (W64.of_int 0);
    x2.[1] <- (W64.of_int 0);
    x2.[2] <- (W64.of_int 0);
    x2.[3] <- (W64.of_int 0);
    d <@ ith_bit (n, ctr);
    x3 <- x;
    x4 <@ addm3 (m, x, x);
    p <- d;
    (x1, x3) <@ swapr (x1, x3, d);
    (x2, x4) <@ swapr (x2, x4, d);
    
    while (((W64.of_int 0) \ult ctr)) {
      lbit <- ctr;
      ctr <- (ctr - (W64.of_int 1));
      t1 <@ ith_bit (n, lbit);
      t2 <@ ith_bit (n, ctr);
      p <- d;
      q <- d;
      d <- (d `|` t2);
      par <- (t1 `^` t2);
      (x1, x2) <@ swapr (x1, x2, par);
      x1 <@ addm3 (m, x1, x2);
      x2 <@ addm3 (m, x2, x2);
      q <- (q `|` t2);
      cbit <- (q `^` p);
      (x1, x3) <@ swapr (x1, x3, cbit);
      (x2, x4) <@ swapr (x2, x4, cbit);
    }
    par <@ ith_bit (n, (W64.of_int 0));
    (x1, x2) <@ swapr (x2, x1, par);
    return (x1);
  }
  
  proc toEC2 () : unit = {
    
    var a:W64.t Array4.t;
    var b:W64.t Array4.t;
    var r:W64.t Array4.t;
    a <- witness;
    b <- witness;
    r <- witness;
    r <@ mulm_ladder (a, a, b);
    return ();
  }
}.


require import AllCore IntDiv CoreMap List Distr.
(* from Jasmin *) require import JModel.

require import Array4 Array8 Array16.
(* require import WArray32 WArray64 WArray128. *)



module M = {
  proc dbn_subc (a:W64.t Array8.t, b:W64.t Array8.t) : bool * W64.t Array8.t = {
    var aux: int;
    
    var cf:bool;
    var x1:W64.t;
    var x2:W64.t;
    var i:int;
    
    x1 <- a.[0];
    x2 <- b.[0];
    (cf, x1) <- subc_64 x1 x2 false;
    a.[0] <- x1;
    i <- 1;
    while (i < 8) {
      x1 <- a.[i];
      x2 <- b.[i];
      (cf, x1) <- subc_64 x1 x2 cf;
      a.[i] <- x1;
      i <- i + 1;
    }
    return (cf, a);
  }
  
  proc bn_copy (a:W64.t Array4.t) : W64.t Array4.t = {
    var aux: int;
    
    var r:W64.t Array4.t;
    var i:int;
    var t:W64.t;
    r <- witness;
    i <- 0;
    while (i < 4) {
      t <- a.[i];
      r.[i] <- t;
      i <- i + 1;
    }
    return (r);
  }
  
  proc dbn_copy (a:W64.t Array8.t) : W64.t Array8.t = {
    var aux: int;
    
    var r:W64.t Array8.t;
    var i:int;
    var t:W64.t;
    r <- witness;
    i <- 0;
    while (i < 8) {
      t <- a.[i];
      r.[i] <- t;
      i <- i + 1;
    }
    return (r);
  }
  
  proc bn_set0 (a:W64.t Array4.t) : W64.t Array4.t = {
    var aux: int;
    
    var i:int;
    
    i <- 0;
    while (i < 4) {
      a.[i] <- (W64.of_int 0);
      i <- i + 1;
    }
    return (a);
  }
  
  proc bn2_set0 (a:W64.t Array8.t) : W64.t Array8.t = {
    var aux: int;
    
    var i:int;
    
    aux <- (2 * 4);
    i <- 0;
    while (i < aux) {
      a.[i] <- (W64.of_int 0);
      i <- i + 1;
    }
    return (a);
  }
  
  proc mul1 (a:W64.t, b:W64.t Array4.t) : W64.t * bool * bool *
                                          W64.t Array8.t = {
    var aux: int;
    
    var _zero:W64.t;
    var of_0:bool;
    var cf:bool;
    var r:W64.t Array8.t;
    var x1:W64.t;
    var x2:W64.t;
    var i:int;
    var lo:W64.t;
    var  _0:bool;
    var  _1:bool;
    var  _2:bool;
    r <- witness;
    (of_0, cf,  _0,  _1,  _2, _zero) <- set0_64 ;
    x1 <- a;
    x2 <- b.[0];
    (x1, x2) <- MULX_64 x1 x2;
    r.[1] <- x1;
    r.[0] <- x2;
    i <- 1;
    while (i < 4) {
      x1 <- a;
      x2 <- b.[i];
      (x1, x2) <- MULX_64 x1 x2;
      r.[(i + 1)] <- x1;
      lo <- x2;
      x1 <- r.[i];
      x2 <- lo;
      (cf, x1) <- ADCX_64 x1 x2 cf;
      r.[i] <- x1;
      i <- i + 1;
    }
    x1 <- r.[4];
    (cf, x1) <- ADCX_64 x1 _zero cf;
    r.[4] <- x1;
    return (_zero, of_0, cf, r);
  }
  
  proc mul1acc (k:W64.t, a:W64.t, b:W64.t Array4.t, r:W64.t Array8.t,
                _zero:W64.t, of_0:bool, cf:bool) : W64.t * bool * bool *
                                                   W64.t Array8.t = {
    var aux: int;
    
    var kk:int;
    var x1:W64.t;
    var i:int;
    var x2:W64.t;
    var hi:W64.t;
    var lo:W64.t;
    
    kk <- (W64.to_uint k);
    aux <- (4 - 1);
    i <- 0;
    while (i < aux) {
      x1 <- a;
      x2 <- b.[i];
      (x1, x2) <- MULX_64 x1 x2;
      hi <- x1;
      lo <- x2;
      x1 <- r.[(kk + i)];
      (of_0, x1) <- ADOX_64 x1 lo of_0;
      r.[(kk + i)] <- x1;
      x1 <- r.[((kk + i) + 1)];
      (cf, x1) <- ADCX_64 x1 hi cf;
      r.[((kk + i) + 1)] <- x1;
      i <- i + 1;
    }
    x1 <- a;
    x2 <- b.[(4 - 1)];
    (x1, x2) <- MULX_64 x1 x2;
    r.[(4 + kk)] <- x1;
    lo <- x2;
    x1 <- r.[((4 + kk) - 1)];
    (of_0, x1) <- ADOX_64 x1 lo of_0;
    r.[((4 + kk) - 1)] <- x1;
    x1 <- r.[(4 + kk)];
    (cf, x1) <- ADCX_64 x1 _zero cf;
    r.[(4 + kk)] <- x1;
    x1 <- r.[(4 + kk)];
    (of_0, x1) <- ADOX_64 x1 _zero of_0;
    r.[(4 + kk)] <- x1;
    return (_zero, of_0, cf, r);
  }
  
  proc bn_muln (a:W64.t Array4.t, b:W64.t Array4.t) : W64.t * bool * bool *
                                                      W64.t Array8.t = {
    var aux: int;
    
    var _zero:W64.t;
    var of_0:bool;
    var cf:bool;
    var r:W64.t Array8.t;
    var ai:W64.t;
    var i:int;
    var z:W64.t;
    r <- witness;
    ai <- a.[0];
    (_zero, of_0, cf, r) <@ mul1 (ai, b);
    i <- 1;
    while (i < 4) {
      ai <- a.[i];
      z <- (W64.of_int i);
      (_zero, of_0, cf, r) <@ mul1acc (z, ai, b, r, _zero, of_0, cf);
      i <- i + 1;
    }
    return (_zero, of_0, cf, r);
  }
  
  proc dmul1 (a:W64.t, b:W64.t Array8.t) : W64.t * bool * bool *
                                           W64.t Array16.t = {
    var aux: int;
    
    var _zero:W64.t;
    var of_0:bool;
    var cf:bool;
    var r:W64.t Array16.t;
    var x1:W64.t;
    var x2:W64.t;
    var i:int;
    var lo:W64.t;
    var  _0:bool;
    var  _1:bool;
    var  _2:bool;
    r <- witness;
    (of_0, cf,  _0,  _1,  _2, _zero) <- set0_64 ;
    x1 <- a;
    x2 <- b.[0];
    (x1, x2) <- MULX_64 x1 x2;
    r.[1] <- x1;
    r.[0] <- x2;
    i <- 1;
    while (i < 8) {
      x1 <- a;
      x2 <- b.[i];
      (x1, x2) <- MULX_64 x1 x2;
      r.[(i + 1)] <- x1;
      lo <- x2;
      x1 <- r.[i];
      x2 <- lo;
      (cf, x1) <- ADCX_64 x1 x2 cf;
      r.[i] <- x1;
      i <- i + 1;
    }
    x1 <- r.[8];
    (cf, x1) <- ADCX_64 x1 _zero cf;
    r.[8] <- x1;
    return (_zero, of_0, cf, r);
  }
  
  proc dmul1acc (k:W64.t, a:W64.t, b:W64.t Array8.t, r:W64.t Array16.t,
                 _zero:W64.t, of_0:bool, cf:bool) : W64.t * bool * bool *
                                                    W64.t Array16.t = {
    var aux: int;
    
    var kk:int;
    var x1:W64.t;
    var i:int;
    var x2:W64.t;
    var hi:W64.t;
    var lo:W64.t;
    
    kk <- (W64.to_uint k);
    aux <- (8 - 1);
    i <- 0;
    while (i < aux) {
      x1 <- a;
      x2 <- b.[i];
      (x1, x2) <- MULX_64 x1 x2;
      hi <- x1;
      lo <- x2;
      x1 <- r.[(kk + i)];
      (of_0, x1) <- ADOX_64 x1 lo of_0;
      r.[(kk + i)] <- x1;
      x1 <- r.[((kk + i) + 1)];
      (cf, x1) <- ADCX_64 x1 hi cf;
      r.[((kk + i) + 1)] <- x1;
      i <- i + 1;
    }
    x1 <- a;
    x2 <- b.[(8 - 1)];
    (x1, x2) <- MULX_64 x1 x2;
    r.[(8 + kk)] <- x1;
    lo <- x2;
    x1 <- r.[((8 + kk) - 1)];
    (of_0, x1) <- ADOX_64 x1 lo of_0;
    r.[((8 + kk) - 1)] <- x1;
    x1 <- r.[(8 + kk)];
    (cf, x1) <- ADCX_64 x1 _zero cf;
    r.[(8 + kk)] <- x1;
    x1 <- r.[(8 + kk)];
    (of_0, x1) <- ADOX_64 x1 _zero of_0;
    r.[(8 + kk)] <- x1;
    return (_zero, of_0, cf, r);
  }
  
  proc dbn_muln (a:W64.t Array8.t, b:W64.t Array8.t) : W64.t * bool * bool *
                                                       W64.t Array16.t = {
    var aux: int;
    
    var _zero:W64.t;
    var of_0:bool;
    var cf:bool;
    var r:W64.t Array16.t;
    var ai:W64.t;
    var i:int;
    var z:W64.t;
    r <- witness;
    ai <- a.[0];
    (_zero, of_0, cf, r) <@ dmul1 (ai, b);
    i <- 1;
    while (i < 8) {
      ai <- a.[i];
      z <- (W64.of_int i);
      (_zero, of_0, cf, r) <@ dmul1acc (z, ai, b, r, _zero, of_0, cf);
      i <- i + 1;
    }
    return (_zero, of_0, cf, r);
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
  
  proc dcminusP (p:W64.t Array8.t, x:W64.t Array8.t) : W64.t Array8.t = {
    var aux: int;
    
    var z:W64.t Array8.t;
    var cf:bool;
    var i:int;
    var r1:W64.t;
    var r2:W64.t;
    z <- witness;
    z <@ dbn_copy (x);
    (cf, z) <@ dbn_subc (z, p);
    i <- 0;
    while (i < 8) {
      r1 <- z.[i];
      r2 <- x.[i];
      r1 <- (cf ? r2 : r1);
      x.[i] <- r1;
      i <- i + 1;
    }
    return (x);
  }
  
  proc bn_expand (x:W64.t Array4.t) : W64.t Array8.t = {
    var aux: int;
    
    var r:W64.t Array8.t;
    var i:int;
    r <- witness;
    i <- 0;
    while (i < 4) {
      r.[i] <- x.[i];
      i <- i + 1;
    }
    i <- 4;
    while (i < 8) {
      r.[i] <- (W64.of_int 0);
      i <- i + 1;
    }
    return (r);
  }
  
  proc bn_shrink (x:W64.t Array8.t) : W64.t Array4.t = {
    var aux: int;
    
    var r:W64.t Array4.t;
    var i:int;
    r <- witness;
    i <- 0;
    while (i < 4) {
      r.[i] <- x.[i];
      i <- i + 1;
    }
    return (r);
  }
  
  proc div2 (x:W64.t Array16.t, k:int) : W64.t Array8.t = {
    var aux: int;
    
    var r:W64.t Array8.t;
    var i:int;
    r <- witness;
    aux <- k;
    i <- 0;
    while (i < aux) {
      r.[i] <- x.[(8 + i)];
      i <- i + 1;
    }
    return (r);
  }
  
  proc bnreduce (a:W64.t Array8.t, r:W64.t Array8.t, p:W64.t Array4.t) : 
  W64.t Array4.t = {
    
    var res_0:W64.t Array4.t;
    var xr:W64.t Array16.t;
    var xrf:W64.t Array8.t;
    var xrfd:W64.t Array4.t;
    var xrfn:W64.t Array8.t;
    var t:W64.t Array8.t;
    var pp:W64.t Array8.t;
    var  _0:W64.t;
    var  _1:bool;
    var  _2:bool;
    var  _3:W64.t;
    var  _4:bool;
    var  _5:bool;
    var  _6:bool;
    pp <- witness;
    res_0 <- witness;
    t <- witness;
    xr <- witness;
    xrf <- witness;
    xrfd <- witness;
    xrfn <- witness;
    ( _0,  _1,  _2, xr) <@ dbn_muln (a, r);
    xrf <@ div2 (xr, (2 * 4));
    xrfd <@ bn_shrink (xrf);
    ( _3,  _4,  _5, xrfn) <@ bn_muln (xrfd, p);
    ( _6, t) <@ dbn_subc (a, xrfn);
    pp <@ bn_expand (p);
    t <@ dcminusP (pp, t);
    res_0 <@ bn_shrink (t);
    return (res_0);
  }
  
  proc mulmr (p:W64.t Array4.t, a:W64.t Array4.t, b:W64.t Array4.t) : 
  W64.t Array4.t = {
    
    var d:W64.t Array8.t;
    var _of:bool;
    var _cf:bool;
    var c:W64.t Array8.t;
    var  _0:W64.t;
    c <- witness;
    d <- witness;
    d <@ bn2_set0 (d);
    d.[0] <- (W64.of_int 4);
    ( _0, _of, _cf, c) <@ bn_muln (a, b);
    a <@ bnreduce (c, d, p);
    return (a);
  }
  
  proc expm (m:W64.t Array4.t, x:W64.t Array4.t, n:W64.t Array4.t) : 
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
    var par:W64.t;
    var q:W64.t;
    var cbit:W64.t;
    x1 <- witness;
    x2 <- witness;
    x3 <- witness;
    x4 <- witness;
    ctr <- (W64.of_int ((4 * 64) - 1));
    x1 <@ bn_set0 (x1);
    x2 <@ bn_set0 (x2);
    d <@ ith_bit (n, ctr);
    x3 <@ bn_copy (x);
    x4 <@ mulmr (m, x, x3);
    p <- d;
    (x1, x3) <@ swapr (x1, x3, d);
    (x2, x4) <@ swapr (x2, x4, d);
    
    while (((W64.of_int 0) \ult ctr)) {
      lbit <- ctr;
      ctr <- (ctr - (W64.of_int 1));
      t1 <@ ith_bit (n, lbit);
      t2 <@ ith_bit (n, ctr);
      p <- d;
      d <- (d `|` t2);
      par <- (t1 `^` t2);
      (x1, x2) <@ swapr (x1, x2, par);
      x1 <@ mulmr (m, x1, x2);
      x2 <@ mulmr (m, x2, x2);
      q <- d;
      cbit <- (q `^` p);
      (x1, x3) <@ swapr (x1, x3, cbit);
      (x2, x4) <@ swapr (x2, x4, cbit);
    }
    p <@ ith_bit (n, (W64.of_int 0));
    (x1, x2) <@ swapr (x2, x1, p);
    return (x1);
  }
  
  proc toEC () : unit = {
    
    var a:W64.t Array4.t;
    var b:W64.t Array4.t;
    var p:W64.t Array4.t;
    var r:W64.t Array4.t;
    a <- witness;
    b <- witness;
    p <- witness;
    r <- witness;
    r <@ expm (a, b, p);
    return ();
  }
}.


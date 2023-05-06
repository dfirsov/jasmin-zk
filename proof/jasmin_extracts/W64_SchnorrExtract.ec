require import AllCore IntDiv CoreMap List Distr.
require import JModel.

require import Array32 Array64 Array128 Array256.
require import WArray256 WArray512 WArray1024.



module type Syscall_t = {
  proc randombytes_256(_:W8.t Array256.t) : W8.t Array256.t
}.

module Syscall : Syscall_t = {
  proc randombytes_256(a:W8.t Array256.t) : W8.t Array256.t = {
    a <$ dmap WArray256.darray
         (fun a => Array256.init (fun i => WArray256.get8 a i));
    return a;
  }
}.

module M(SC:Syscall_t) = {
  proc bn_subc (a:W64.t Array32.t, b:W64.t Array32.t) : bool *
                                                        W64.t Array32.t = {
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
    while (i < 32) {
      x1 <- a.[i];
      x2 <- b.[i];
      (cf, x1) <- subc_64 x1 x2 cf;
      a.[i] <- x1;
      i <- i + 1;
    }
    return (cf, a);
  }
  
  proc dbn_subc (a:W64.t Array64.t, b:W64.t Array64.t) : bool *
                                                         W64.t Array64.t = {
    var aux: int;
    
    var cf:bool;
    var x1:W64.t;
    var x2:W64.t;
    var i:int;
    
    x1 <- a.[0];
    x2 <- b.[0];
    (cf, x1) <- subc_64 x1 x2 false;
    a.[0] <- x1;
    aux <- (32 * 2);
    i <- 1;
    while (i < aux) {
      x1 <- a.[i];
      x2 <- b.[i];
      (cf, x1) <- subc_64 x1 x2 cf;
      a.[i] <- x1;
      i <- i + 1;
    }
    return (cf, a);
  }
  
  proc bn_copy (a:W64.t Array32.t) : W64.t Array32.t = {
    var aux: int;
    
    var r:W64.t Array32.t;
    var i:int;
    var t:W64.t;
    r <- witness;
    i <- 0;
    while (i < 32) {
      t <- a.[i];
      r.[i] <- t;
      i <- i + 1;
    }
    return (r);
  }
  
  proc dbn_copy (a:W64.t Array64.t) : W64.t Array64.t = {
    var aux: int;
    
    var r:W64.t Array64.t;
    var i:int;
    var t:W64.t;
    r <- witness;
    aux <- (32 * 2);
    i <- 0;
    while (i < aux) {
      t <- a.[i];
      r.[i] <- t;
      i <- i + 1;
    }
    return (r);
  }
  
  proc bn_cmov (cond:bool, a:W64.t Array32.t, b:W64.t Array32.t) : W64.t Array32.t = {
    var aux: int;
    
    var i:int;
    var r1:W64.t;
    var r2:W64.t;
    
    i <- 0;
    while (i < 32) {
      r1 <- a.[i];
      r2 <- b.[i];
      r1 <- (cond ? r2 : r1);
      a.[i] <- r1;
      i <- i + 1;
    }
    return (a);
  }
  
  proc dbn_cmov (cond:bool, a:W64.t Array64.t, b:W64.t Array64.t) : W64.t Array64.t = {
    var aux: int;
    
    var i:int;
    var r1:W64.t;
    var r2:W64.t;
    
    aux <- (32 * 2);
    i <- 0;
    while (i < aux) {
      r1 <- a.[i];
      r2 <- b.[i];
      r1 <- (cond ? r2 : r1);
      a.[i] <- r1;
      i <- i + 1;
    }
    return (a);
  }
  
  proc bn_set0 (a:W64.t Array32.t) : W64.t Array32.t = {
    var aux: int;
    
    var i:int;
    
    i <- 0;
    while (i < 32) {
      a.[i] <- (W64.of_int 0);
      i <- i + 1;
    }
    return (a);
  }
  
  proc bn_set1 (a:W64.t Array32.t) : W64.t Array32.t = {
    var aux: int;
    
    var i:int;
    
    a.[0] <- (W64.of_int 1);
    i <- 1;
    while (i < 32) {
      a.[i] <- (W64.of_int 0);
      i <- i + 1;
    }
    return (a);
  }
  
  proc bn_addc (a:W64.t Array32.t, b:W64.t Array32.t) : bool *
                                                        W64.t Array32.t = {
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
    while (i < 32) {
      x1 <- a.[i];
      x2 <- b.[i];
      (cf, x1) <- addc_64 x1 x2 cf;
      a.[i] <- x1;
      i <- i + 1;
    }
    return (cf, a);
  }
  
  proc mul1 (a:W64.t, b:W64.t Array32.t) : W64.t * bool * bool *
                                           W64.t Array64.t = {
    var aux: int;
    
    var _zero:W64.t;
    var of_0:bool;
    var cf:bool;
    var r:W64.t Array64.t;
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
    while (i < 32) {
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
    x1 <- r.[32];
    (cf, x1) <- ADCX_64 x1 _zero cf;
    r.[32] <- x1;
    return (_zero, of_0, cf, r);
  }
  
  proc mul1acc (k:W64.t, a:W64.t, b:W64.t Array32.t, r:W64.t Array64.t,
                _zero:W64.t, of_0:bool, cf:bool) : W64.t * bool * bool *
                                                   W64.t Array64.t = {
    var aux: int;
    
    var kk:int;
    var x1:W64.t;
    var i:int;
    var x2:W64.t;
    var hi:W64.t;
    var lo:W64.t;
    
    kk <- (W64.to_uint k);
    aux <- (32 - 1);
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
    x2 <- b.[(32 - 1)];
    (x1, x2) <- MULX_64 x1 x2;
    r.[(32 + kk)] <- x1;
    lo <- x2;
    x1 <- r.[((32 + kk) - 1)];
    (of_0, x1) <- ADOX_64 x1 lo of_0;
    r.[((32 + kk) - 1)] <- x1;
    x1 <- r.[(32 + kk)];
    (cf, x1) <- ADCX_64 x1 _zero cf;
    r.[(32 + kk)] <- x1;
    x1 <- r.[(32 + kk)];
    (of_0, x1) <- ADOX_64 x1 _zero of_0;
    r.[(32 + kk)] <- x1;
    return (_zero, of_0, cf, r);
  }
  
  proc bn_muln (a:W64.t Array32.t, b:W64.t Array32.t) : W64.t * bool * bool *
                                                        W64.t Array64.t = {
    var aux: int;
    
    var _zero:W64.t;
    var of_0:bool;
    var cf:bool;
    var r:W64.t Array64.t;
    var ai:W64.t;
    var i:int;
    var z:W64.t;
    r <- witness;
    ai <- a.[0];
    (_zero, of_0, cf, r) <@ mul1 (ai, b);
    i <- 1;
    while (i < 32) {
      ai <- a.[i];
      z <- (W64.of_int i);
      (_zero, of_0, cf, r) <@ mul1acc (z, ai, b, r, _zero, of_0, cf);
      i <- i + 1;
    }
    return (_zero, of_0, cf, r);
  }
  
  proc dmul1 (a:W64.t, b:W64.t Array64.t) : W64.t * bool * bool *
                                            W64.t Array128.t = {
    var aux: int;
    
    var _zero:W64.t;
    var of_0:bool;
    var cf:bool;
    var r:W64.t Array128.t;
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
    aux <- (32 * 2);
    i <- 1;
    while (i < aux) {
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
    x1 <- r.[(32 * 2)];
    (cf, x1) <- ADCX_64 x1 _zero cf;
    r.[(32 * 2)] <- x1;
    return (_zero, of_0, cf, r);
  }
  
  proc dmul1acc (k:W64.t, a:W64.t, b:W64.t Array64.t, r:W64.t Array128.t,
                 _zero:W64.t, of_0:bool, cf:bool) : W64.t * bool * bool *
                                                    W64.t Array128.t = {
    var aux: int;
    
    var kk:int;
    var x1:W64.t;
    var i:int;
    var x2:W64.t;
    var hi:W64.t;
    var lo:W64.t;
    
    kk <- (W64.to_uint k);
    aux <- ((32 * 2) - 1);
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
    x2 <- b.[((32 * 2) - 1)];
    (x1, x2) <- MULX_64 x1 x2;
    r.[((32 * 2) + kk)] <- x1;
    lo <- x2;
    x1 <- r.[(((32 * 2) + kk) - 1)];
    (of_0, x1) <- ADOX_64 x1 lo of_0;
    r.[(((32 * 2) + kk) - 1)] <- x1;
    x1 <- r.[((32 * 2) + kk)];
    (cf, x1) <- ADCX_64 x1 _zero cf;
    r.[((32 * 2) + kk)] <- x1;
    x1 <- r.[((32 * 2) + kk)];
    (of_0, x1) <- ADOX_64 x1 _zero of_0;
    r.[((32 * 2) + kk)] <- x1;
    return (_zero, of_0, cf, r);
  }
  
  proc dbn_muln (a:W64.t Array64.t, b:W64.t Array64.t) : W64.t * bool *
                                                         bool *
                                                         W64.t Array128.t = {
    var aux: int;
    
    var _zero:W64.t;
    var of_0:bool;
    var cf:bool;
    var r:W64.t Array128.t;
    var ai:W64.t;
    var i:int;
    var z:W64.t;
    r <- witness;
    ai <- a.[0];
    (_zero, of_0, cf, r) <@ dmul1 (ai, b);
    aux <- (32 * 2);
    i <- 1;
    while (i < aux) {
      ai <- a.[i];
      z <- (W64.of_int i);
      (_zero, of_0, cf, r) <@ dmul1acc (z, ai, b, r, _zero, of_0, cf);
      i <- i + 1;
    }
    return (_zero, of_0, cf, r);
  }
  
  proc rsample (byte_z:W64.t Array32.t) : int * W64.t Array32.t = {
    var aux: W8.t Array256.t;
    
    var i:int;
    var byte_p:W64.t Array32.t;
    var cf:bool;
    var byte_q:W64.t Array32.t;
    var  _0:bool;
    var  _1:bool;
    var  _2:bool;
    var  _3:bool;
    var  _4:W64.t;
    byte_p <- witness;
    byte_q <- witness;
    i <- 0;
    byte_p <@ bn_set0 (byte_p);
    ( _0, cf,  _1,  _2,  _3,  _4) <- set0_64 ;
    
    while ((! cf)) {
      aux <@ SC.randombytes_256 ((Array256.init (fun i_0 => get8
                                 (WArray256.init64 (fun i_0 => byte_p.[i_0]))
                                 i_0)));
      byte_p <-
      (Array32.init (fun i_0 => get64
      (WArray256.init8 (fun i_0 => aux.[i_0])) i_0));
      byte_q <@ bn_copy (byte_p);
      (cf, byte_q) <@ bn_subc (byte_q, byte_z);
      i <- (i + 1);
    }
    return (i, byte_p);
  }
  
  proc usample (byte_z:W64.t Array32.t) : W64.t Array32.t = {
    
    var byte_p:W64.t Array32.t;
    var  _0:int;
    byte_p <- witness;
    ( _0, byte_p) <@ rsample (byte_z);
    return (byte_p);
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
  
  proc ith_bit (kk:W64.t Array32.t, ctr:W64.t) : W64.t = {
    
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
  
  proc swapr (x:W64.t Array32.t, y:W64.t Array32.t, swap_0:W64.t) : W64.t Array32.t *
                                                                    W64.t Array32.t = {
    var aux: int;
    
    var mask:W64.t;
    var i:int;
    var tmp1:W64.t;
    var tmp2:W64.t;
    
    mask <- (swap_0 * (W64.of_int 18446744073709551615));
    i <- 0;
    while (i < 32) {
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
  
  proc cminusP (p:W64.t Array32.t, x:W64.t Array32.t) : W64.t Array32.t = {
    
    var z:W64.t Array32.t;
    var cf:bool;
    z <- witness;
    z <@ bn_copy (x);
    (cf, z) <@ bn_subc (z, p);
    x <@ bn_cmov (cf, z, x);
    return (x);
  }
  
  proc dcminusP (p:W64.t Array64.t, x:W64.t Array64.t) : W64.t Array64.t = {
    
    var z:W64.t Array64.t;
    var cf:bool;
    z <- witness;
    z <@ dbn_copy (x);
    (cf, z) <@ dbn_subc (z, p);
    x <@ dbn_cmov (cf, z, x);
    return (x);
  }
  
  proc addm (p:W64.t Array32.t, a:W64.t Array32.t, b:W64.t Array32.t) : 
  W64.t Array32.t = {
    
    var  _0:bool;
    
    ( _0, a) <@ bn_addc (a, b);
    a <@ cminusP (p, a);
    return (a);
  }
  
  proc bn_expand (x:W64.t Array32.t) : W64.t Array64.t = {
    var aux: int;
    
    var r:W64.t Array64.t;
    var i:int;
    r <- witness;
    i <- 0;
    while (i < 32) {
      r.[i] <- x.[i];
      i <- i + 1;
    }
    aux <- (32 * 2);
    i <- 32;
    while (i < aux) {
      r.[i] <- (W64.of_int 0);
      i <- i + 1;
    }
    return (r);
  }
  
  proc bn_shrink (x:W64.t Array64.t) : W64.t Array32.t = {
    var aux: int;
    
    var r:W64.t Array32.t;
    var i:int;
    r <- witness;
    i <- 0;
    while (i < 32) {
      r.[i] <- x.[i];
      i <- i + 1;
    }
    return (r);
  }
  
  proc div2 (x:W64.t Array128.t, k:int) : W64.t Array64.t = {
    var aux: int;
    
    var r:W64.t Array64.t;
    var i:int;
    r <- witness;
    aux <- k;
    i <- 0;
    while (i < aux) {
      r.[i] <- x.[((32 * 2) + i)];
      i <- i + 1;
    }
    return (r);
  }
  
  proc bn_breduce (a:W64.t Array64.t, r:W64.t Array64.t, p:W64.t Array32.t) : 
  W64.t Array32.t = {
    
    var res_0:W64.t Array32.t;
    var xr:W64.t Array128.t;
    var xrf:W64.t Array64.t;
    var xrfd:W64.t Array32.t;
    var xrfn:W64.t Array64.t;
    var t:W64.t Array64.t;
    var pp:W64.t Array64.t;
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
    xrf <@ div2 (xr, (2 * 32));
    xrfd <@ bn_shrink (xrf);
    ( _3,  _4,  _5, xrfn) <@ bn_muln (xrfd, p);
    ( _6, t) <@ dbn_subc (a, xrfn);
    pp <@ bn_expand (p);
    t <@ dcminusP (pp, t);
    res_0 <@ bn_shrink (t);
    return (res_0);
  }
  
  proc bn_breduce_small (a:W64.t Array32.t, r:W64.t Array64.t,
                         p:W64.t Array32.t) : W64.t Array32.t = {
    
    var res_0:W64.t Array32.t;
    var aa:W64.t Array64.t;
    aa <- witness;
    res_0 <- witness;
    aa <@ bn_expand (a);
    res_0 <@ bn_breduce (aa, r, p);
    return (res_0);
  }
  
  proc mulm (r:W64.t Array64.t, p:W64.t Array32.t, a:W64.t Array32.t,
             b:W64.t Array32.t) : W64.t Array32.t = {
    
    var _of:bool;
    var _cf:bool;
    var c:W64.t Array64.t;
    var  _0:W64.t;
    c <- witness;
    ( _0, _of, _cf, c) <@ bn_muln (a, b);
    a <@ bn_breduce (c, r, p);
    return (a);
  }
  
  proc expm (r:W64.t Array64.t, m:W64.t Array32.t, x:W64.t Array32.t,
             n:W64.t Array32.t) : W64.t Array32.t = {
    
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
    var par:W64.t;
    var q:W64.t;
    var cbit:W64.t;
    x1 <- witness;
    x2 <- witness;
    x3 <- witness;
    x4 <- witness;
    ctr <- (W64.of_int ((32 * 64) - 1));
    x1 <@ bn_set1 (x1);
    x2 <@ bn_set1 (x2);
    d <@ ith_bit (n, ctr);
    x3 <@ bn_copy (x);
    x4 <@ mulm (r, m, x, x3);
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
      x1 <@ mulm (r, m, x1, x2);
      x2 <@ mulm (r, m, x2, x2);
      q <- d;
      cbit <- (q `^` p);
      (x1, x3) <@ swapr (x1, x3, cbit);
      (x2, x4) <@ swapr (x2, x4, cbit);
    }
    p <@ ith_bit (n, (W64.of_int 0));
    (x1, x2) <@ swapr (x2, x1, p);
    return (x1);
  }
  
  proc bn_set_gg (a:W64.t Array32.t) : W64.t Array32.t = {
    var aux: int;
    
    var i:int;
    
    a.[0] <- (W64.of_int 1);
    i <- 1;
    while (i < 32) {
      a.[i] <- (W64.of_int 1);
      i <- i + 1;
    }
    return (a);
  }
  
  proc bn_set_bf (a:W64.t Array64.t) : W64.t Array64.t = {
    var aux: int;
    
    var i:int;
    
    a.[0] <- (W64.of_int 1);
    aux <- (32 * 2);
    i <- 1;
    while (i < aux) {
      a.[i] <- (W64.of_int 1);
      i <- i + 1;
    }
    return (a);
  }
  
  proc bn_eq (a:W64.t Array32.t, b:W64.t Array32.t) : W64.t = {
    var aux: int;
    
    var result:W64.t;
    var i:int;
    var c1:W64.t;
    var c2:W64.t;
    
    result <- (W64.of_int 0);
    i <- 0;
    while (i < 32) {
      c1 <- a.[i];
      c2 <- b.[i];
      c1 <- (c1 `^` c2);
      result <- (result `|` c1);
      i <- i + 1;
    }
    return (result);
  }
  
  proc bn_set_eo (a:W64.t Array32.t) : W64.t Array32.t = {
    var aux: int;
    
    var i:int;
    
    a.[0] <- (W64.of_int 1);
    i <- 1;
    while (i < 32) {
      a.[i] <- (W64.of_int 1);
      i <- i + 1;
    }
    return (a);
  }
  
  proc bn_set_eb (a:W64.t Array64.t) : W64.t Array64.t = {
    var aux: int;
    
    var i:int;
    
    a.[0] <- (W64.of_int 1);
    aux <- (32 * 2);
    i <- 1;
    while (i < aux) {
      a.[i] <- (W64.of_int 1);
      i <- i + 1;
    }
    return (a);
  }
  
  proc bn_set_go (a:W64.t Array32.t) : W64.t Array32.t = {
    var aux: int;
    
    var i:int;
    
    a.[0] <- (W64.of_int 1);
    i <- 1;
    while (i < 32) {
      a.[i] <- (W64.of_int 1);
      i <- i + 1;
    }
    return (a);
  }
  
  proc commitment () : W64.t Array32.t * W64.t Array32.t = {
    
    var commitment_0:W64.t Array32.t;
    var secret_power:W64.t Array32.t;
    var exp_order:W64.t Array32.t;
    var group_order:W64.t Array32.t;
    var group_generator:W64.t Array32.t;
    var barrett_parameter:W64.t Array64.t;
    barrett_parameter <- witness;
    commitment_0 <- witness;
    exp_order <- witness;
    group_generator <- witness;
    group_order <- witness;
    secret_power <- witness;
    exp_order <@ bn_set_eo (exp_order);
    group_order <@ bn_set_go (group_order);
    group_generator <@ bn_set_gg (group_generator);
    barrett_parameter <@ bn_set_bf (barrett_parameter);
    secret_power <@ usample (exp_order);
    commitment_0 <@ expm (barrett_parameter, group_order, group_generator,
    secret_power);
    return (commitment_0, secret_power);
  }
  
  proc response (witness0:W64.t Array32.t, secret_power:W64.t Array32.t,
                 challenge_0:W64.t Array32.t) : W64.t Array32.t = {
    
    var response_0:W64.t Array32.t;
    var exp_order:W64.t Array32.t;
    var exp_barrett:W64.t Array64.t;
    var product:W64.t Array32.t;
    exp_barrett <- witness;
    exp_order <- witness;
    product <- witness;
    response_0 <- witness;
    exp_order <@ bn_set_eo (exp_order);
    exp_barrett <@ bn_set_eb (exp_barrett);
    challenge_0 <@ bn_breduce_small (challenge_0, exp_barrett, exp_order);
    secret_power <@ bn_breduce_small (secret_power, exp_barrett, exp_order);
    witness0 <@ bn_breduce_small (witness0, exp_barrett, exp_order);
    product <@ mulm (exp_barrett, exp_order, challenge_0, witness0);
    response_0 <@ addm (exp_order, secret_power, product);
    return (response_0);
  }
  
  proc challenge () : W64.t Array32.t = {
    
    var challenge_0:W64.t Array32.t;
    var exp_order:W64.t Array32.t;
    challenge_0 <- witness;
    exp_order <- witness;
    exp_order <@ bn_set_eo (exp_order);
    challenge_0 <@ usample (exp_order);
    return (challenge_0);
  }
  
  proc verify (statement:W64.t Array32.t, commitment_0:W64.t Array32.t,
               challenge_0:W64.t Array32.t, response_0:W64.t Array32.t) : 
  W64.t = {
    
    var result:W64.t;
    var exp_order:W64.t Array32.t;
    var exp_barrett:W64.t Array64.t;
    var group_order:W64.t Array32.t;
    var group_barrett:W64.t Array64.t;
    var group_generator:W64.t Array32.t;
    var tmp:W64.t Array32.t;
    var v1:W64.t Array32.t;
    var v2:W64.t Array32.t;
    exp_barrett <- witness;
    exp_order <- witness;
    group_barrett <- witness;
    group_generator <- witness;
    group_order <- witness;
    tmp <- witness;
    v1 <- witness;
    v2 <- witness;
    exp_order <@ bn_set_eo (exp_order);
    exp_barrett <@ bn_set_eb (exp_barrett);
    group_order <@ bn_set_go (group_order);
    group_barrett <@ bn_set_bf (group_barrett);
    group_generator <@ bn_set_gg (group_generator);
    statement <@ bn_breduce_small (statement, group_barrett, group_order);
    commitment_0 <@ bn_breduce_small (commitment_0, group_barrett,
    group_order);
    challenge_0 <@ bn_breduce_small (challenge_0, exp_barrett, exp_order);
    response_0 <@ bn_breduce_small (response_0, exp_barrett, exp_order);
    tmp <@ expm (group_barrett, group_order, statement, challenge_0);
    v1 <@ mulm (group_barrett, group_order, commitment_0, tmp);
    v2 <@ expm (group_barrett, group_order, group_generator, response_0);
    result <@ bn_eq (v1, v2);
    return (result);
  }
}.


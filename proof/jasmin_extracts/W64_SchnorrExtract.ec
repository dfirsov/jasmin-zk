require import AllCore IntDiv CoreMap List Distr.
from Jasmin require import JModel.

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
    (cf, x1) <- sbb_64 x1 x2 false;
    a.[0] <- x1;
    i <- 1;
    while (i < 32) {
      x1 <- a.[i];
      x2 <- b.[i];
      (cf, x1) <- sbb_64 x1 x2 cf;
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
    (cf, x1) <- sbb_64 x1 x2 false;
    a.[0] <- x1;
    aux <- (32 * 2);
    i <- 1;
    while (i < aux) {
      x1 <- a.[i];
      x2 <- b.[i];
      (cf, x1) <- sbb_64 x1 x2 cf;
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
    (cf, x1) <- adc_64 x1 x2 false;
    a.[0] <- x1;
    i <- 1;
    while (i < 32) {
      x1 <- a.[i];
      x2 <- b.[i];
      (cf, x1) <- adc_64 x1 x2 cf;
      a.[i] <- x1;
      i <- i + 1;
    }
    return (cf, a);
  }
  
  proc dbn_addc (a:W64.t Array64.t, b:W64.t Array64.t) : bool *
                                                         W64.t Array64.t = {
    var aux: int;
    
    var cf:bool;
    var x1:W64.t;
    var x2:W64.t;
    var i:int;
    
    x1 <- a.[0];
    x2 <- b.[0];
    (cf, x1) <- adc_64 x1 x2 false;
    a.[0] <- x1;
    aux <- (32 * 2);
    i <- 1;
    while (i < aux) {
      x1 <- a.[i];
      x2 <- b.[i];
      (cf, x1) <- adc_64 x1 x2 cf;
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
  
  proc sn_cmov (cond:bool, a:W64.t, b:W64.t) : W64.t = {
    
    var r1:W64.t;
    var r2:W64.t;
    
    r1 <- a;
    r2 <- b;
    r1 <- (cond ? r2 : r1);
    a <- r1;
    return (a);
  }
  
  proc bn_eq (a:W64.t Array32.t, b:W64.t Array32.t) : W64.t = {
    var aux: int;
    
    var output:W64.t;
    var result:W64.t;
    var i:int;
    var c1:W64.t;
    var c2:W64.t;
    var cf:bool;
    
    result <- (W64.of_int 0);
    i <- 0;
    while (i < 32) {
      c1 <- a.[i];
      c2 <- b.[i];
      c1 <- (c1 `^` c2);
      result <- (result `|` c1);
      i <- i + 1;
    }
    cf <- (result = (W64.of_int 0));
    output <@ sn_cmov (cf, (W64.of_int 0), (W64.of_int 1));
    return (output);
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
  
  proc daddm (p:W64.t Array64.t, a:W64.t Array64.t, b:W64.t Array64.t) : 
  W64.t Array64.t = {
    
    var  _0:bool;
    
    ( _0, a) <@ dbn_addc (a, b);
    a <@ dcminusP (p, a);
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
  
  proc addm (p:W64.t Array32.t, a:W64.t Array32.t, b:W64.t Array32.t) : 
  W64.t Array32.t = {
    
    var  _0:bool;
    
    ( _0, a) <@ bn_addc (a, b);
    a <@ cminusP (p, a);
    return (a);
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
  
  proc addm2 (p:W64.t Array32.t, a:W64.t Array32.t, b:W64.t Array32.t) : 
  W64.t Array32.t = {
    
    var d:W64.t Array32.t;
    var aa:W64.t Array64.t;
    var bb:W64.t Array64.t;
    var pp:W64.t Array64.t;
    var cc:W64.t Array64.t;
    aa <- witness;
    bb <- witness;
    cc <- witness;
    d <- witness;
    pp <- witness;
    aa <@ bn_expand (a);
    bb <@ bn_expand (b);
    pp <@ bn_expand (p);
    cc <@ daddm (pp, aa, bb);
    d <@ bn_shrink (cc);
    return (d);
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
    var x2:W64.t Array32.t;
    var x11:W64.t Array32.t;
    var i:W64.t;
    var b:W64.t;
    x1 <- witness;
    x11 <- witness;
    x2 <- witness;
    x1 <@ bn_set1 (x1);
    x2 <@ bn_copy (x);
    x11 <@ bn_copy (x1);
    i <- (W64.of_int (32 * 64));
    b <- (W64.of_int 0);
    
    while (((W64.of_int 0) \ult i)) {
      i <- (i - (W64.of_int 1));
      b <@ ith_bit (n, i);
      (x1, x2) <@ swapr (x1, x2, b);
      x11 <@ bn_copy (x1);
      x1 <@ mulm (r, m, x1, x1);
      x2 <@ mulm (r, m, x11, x2);
      (x1, x2) <@ swapr (x1, x2, b);
    }
    return (x1);
  }
  
  proc bn_set_p (p:W64.t Array32.t) : W64.t Array32.t = {
    
    var tmp:W64.t;
    
    tmp <- (W64.of_int 18446744073709551615);
    p.[0] <- tmp;
    tmp <- (W64.of_int 1545454141666273896);
    p.[1] <- tmp;
    tmp <- (W64.of_int 1572361106993317136);
    p.[2] <- tmp;
    tmp <- (W64.of_int 4149303432552213221);
    p.[3] <- tmp;
    tmp <- (W64.of_int 16009113560346531608);
    p.[4] <- tmp;
    tmp <- (W64.of_int 13097978378517762761);
    p.[5] <- tmp;
    tmp <- (W64.of_int 11180049335738409615);
    p.[6] <- tmp;
    tmp <- (W64.of_int 16401677924195796483);
    p.[7] <- tmp;
    tmp <- (W64.of_int 3643515754058796603);
    p.[8] <- tmp;
    tmp <- (W64.of_int 17398650045445185916);
    p.[9] <- tmp;
    tmp <- (W64.of_int 7425368496004700164);
    p.[10] <- tmp;
    tmp <- (W64.of_int 11445099139962410605);
    p.[11] <- tmp;
    tmp <- (W64.of_int 2045464732017971899);
    p.[12] <- tmp;
    tmp <- (W64.of_int 9468076200223288726);
    p.[13] <- tmp;
    tmp <- (W64.of_int 7572309818504171359);
    p.[14] <- tmp;
    tmp <- (W64.of_int 11014195235928789914);
    p.[15] <- tmp;
    tmp <- (W64.of_int 13979310375781515013);
    p.[16] <- tmp;
    tmp <- (W64.of_int 5271575865889938237);
    p.[17] <- tmp;
    tmp <- (W64.of_int 12582815541414797286);
    p.[18] <- tmp;
    tmp <- (W64.of_int 17165588707022577573);
    p.[19] <- tmp;
    tmp <- (W64.of_int 864511594326308845);
    p.[20] <- tmp;
    tmp <- (W64.of_int 17603518614767922539);
    p.[21] <- tmp;
    tmp <- (W64.of_int 16466767132611215046);
    p.[22] <- tmp;
    tmp <- (W64.of_int 5755940542857986629);
    p.[23] <- tmp;
    tmp <- (W64.of_int 3470879405153129527);
    p.[24] <- tmp;
    tmp <- (W64.of_int 17263733006627652379);
    p.[25] <- tmp;
    tmp <- (W64.of_int 5857503583518590173);
    p.[26] <- tmp;
    tmp <- (W64.of_int 147421033984662306);
    p.[27] <- tmp;
    tmp <- (W64.of_int 2955010104097229940);
    p.[28] <- tmp;
    tmp <- (W64.of_int 14179128828124470481);
    p.[29] <- tmp;
    tmp <- (W64.of_int 14488038916154245684);
    p.[30] <- tmp;
    tmp <- (W64.of_int 18446744073709551615);
    p.[31] <- tmp;
    return (p);
  }
  
  proc bn_set_q (q:W64.t Array32.t) : W64.t Array32.t = {
    
    var tmp:W64.t;
    
    tmp <- (W64.of_int 9223372036854775807);
    q.[0] <- tmp;
    tmp <- (W64.of_int 772727070833136948);
    q.[1] <- tmp;
    tmp <- (W64.of_int 10009552590351434376);
    q.[2] <- tmp;
    tmp <- (W64.of_int 2074651716276106610);
    q.[3] <- tmp;
    tmp <- (W64.of_int 17227928817028041612);
    q.[4] <- tmp;
    tmp <- (W64.of_int 15772361226113657188);
    q.[5] <- tmp;
    tmp <- (W64.of_int 14813396704723980615);
    q.[6] <- tmp;
    tmp <- (W64.of_int 17424210998952674049);
    q.[7] <- tmp;
    tmp <- (W64.of_int 1821757877029398301);
    q.[8] <- tmp;
    tmp <- (W64.of_int 8699325022722592958);
    q.[9] <- tmp;
    tmp <- (W64.of_int 12936056284857125890);
    q.[10] <- tmp;
    tmp <- (W64.of_int 14945921606835981110);
    q.[11] <- tmp;
    tmp <- (W64.of_int 1022732366008985949);
    q.[12] <- tmp;
    tmp <- (W64.of_int 13957410136966420171);
    q.[13] <- tmp;
    tmp <- (W64.of_int 3786154909252085679);
    q.[14] <- tmp;
    tmp <- (W64.of_int 14730469654819170765);
    q.[15] <- tmp;
    tmp <- (W64.of_int 16213027224745533314);
    q.[16] <- tmp;
    tmp <- (W64.of_int 2635787932944969118);
    q.[17] <- tmp;
    tmp <- (W64.of_int 15514779807562174451);
    q.[18] <- tmp;
    tmp <- (W64.of_int 17806166390366064594);
    q.[19] <- tmp;
    tmp <- (W64.of_int 9655627834017930230);
    q.[20] <- tmp;
    tmp <- (W64.of_int 8801759307383961269);
    q.[21] <- tmp;
    tmp <- (W64.of_int 17456755603160383331);
    q.[22] <- tmp;
    tmp <- (W64.of_int 12101342308283769122);
    q.[23] <- tmp;
    tmp <- (W64.of_int 10958811739431340571);
    q.[24] <- tmp;
    tmp <- (W64.of_int 17855238540168601997);
    q.[25] <- tmp;
    tmp <- (W64.of_int 2928751791759295086);
    q.[26] <- tmp;
    tmp <- (W64.of_int 73710516992331153);
    q.[27] <- tmp;
    tmp <- (W64.of_int 10700877088903390778);
    q.[28] <- tmp;
    tmp <- (W64.of_int 7089564414062235240);
    q.[29] <- tmp;
    tmp <- (W64.of_int 16467391494931898650);
    q.[30] <- tmp;
    tmp <- (W64.of_int 9223372036854775807);
    q.[31] <- tmp;
    return (q);
  }
  
  proc bn_set_g (g:W64.t Array32.t) : W64.t Array32.t = {
    
    var tmp:W64.t;
    
    tmp <- (W64.of_int 2);
    g.[0] <- tmp;
    tmp <- (W64.of_int 0);
    g.[1] <- tmp;
    tmp <- (W64.of_int 0);
    g.[2] <- tmp;
    tmp <- (W64.of_int 0);
    g.[3] <- tmp;
    tmp <- (W64.of_int 0);
    g.[4] <- tmp;
    tmp <- (W64.of_int 0);
    g.[5] <- tmp;
    tmp <- (W64.of_int 0);
    g.[6] <- tmp;
    tmp <- (W64.of_int 0);
    g.[7] <- tmp;
    tmp <- (W64.of_int 0);
    g.[8] <- tmp;
    tmp <- (W64.of_int 0);
    g.[9] <- tmp;
    tmp <- (W64.of_int 0);
    g.[10] <- tmp;
    tmp <- (W64.of_int 0);
    g.[11] <- tmp;
    tmp <- (W64.of_int 0);
    g.[12] <- tmp;
    tmp <- (W64.of_int 0);
    g.[13] <- tmp;
    tmp <- (W64.of_int 0);
    g.[14] <- tmp;
    tmp <- (W64.of_int 0);
    g.[15] <- tmp;
    tmp <- (W64.of_int 0);
    g.[16] <- tmp;
    tmp <- (W64.of_int 0);
    g.[17] <- tmp;
    tmp <- (W64.of_int 0);
    g.[18] <- tmp;
    tmp <- (W64.of_int 0);
    g.[19] <- tmp;
    tmp <- (W64.of_int 0);
    g.[20] <- tmp;
    tmp <- (W64.of_int 0);
    g.[21] <- tmp;
    tmp <- (W64.of_int 0);
    g.[22] <- tmp;
    tmp <- (W64.of_int 0);
    g.[23] <- tmp;
    tmp <- (W64.of_int 0);
    g.[24] <- tmp;
    tmp <- (W64.of_int 0);
    g.[25] <- tmp;
    tmp <- (W64.of_int 0);
    g.[26] <- tmp;
    tmp <- (W64.of_int 0);
    g.[27] <- tmp;
    tmp <- (W64.of_int 0);
    g.[28] <- tmp;
    tmp <- (W64.of_int 0);
    g.[29] <- tmp;
    tmp <- (W64.of_int 0);
    g.[30] <- tmp;
    tmp <- (W64.of_int 0);
    g.[31] <- tmp;
    return (g);
  }
  
  proc bn_set_bp (bp:W64.t Array64.t) : W64.t Array64.t = {
    
    var tmp:W64.t;
    
    tmp <- (W64.of_int 5147934117528057444);
    bp.[0] <- tmp;
    tmp <- (W64.of_int 10407519109700454935);
    bp.[1] <- tmp;
    tmp <- (W64.of_int 16583539182667929086);
    bp.[2] <- tmp;
    tmp <- (W64.of_int 1492440688257385106);
    bp.[3] <- tmp;
    tmp <- (W64.of_int 10066832793016919264);
    bp.[4] <- tmp;
    tmp <- (W64.of_int 11339370997029172680);
    bp.[5] <- tmp;
    tmp <- (W64.of_int 4675869585930362320);
    bp.[6] <- tmp;
    tmp <- (W64.of_int 16918262430485393797);
    bp.[7] <- tmp;
    tmp <- (W64.of_int 13728506818757698388);
    bp.[8] <- tmp;
    tmp <- (W64.of_int 13772906965603576095);
    bp.[9] <- tmp;
    tmp <- (W64.of_int 3156528908874584491);
    bp.[10] <- tmp;
    tmp <- (W64.of_int 1231154113365505725);
    bp.[11] <- tmp;
    tmp <- (W64.of_int 17718551243857757924);
    bp.[12] <- tmp;
    tmp <- (W64.of_int 16667871902385732453);
    bp.[13] <- tmp;
    tmp <- (W64.of_int 8054682061035653787);
    bp.[14] <- tmp;
    tmp <- (W64.of_int 12145378267626961546);
    bp.[15] <- tmp;
    tmp <- (W64.of_int 14175206944198899882);
    bp.[16] <- tmp;
    tmp <- (W64.of_int 1872412834642272634);
    bp.[17] <- tmp;
    tmp <- (W64.of_int 10293871819984421175);
    bp.[18] <- tmp;
    tmp <- (W64.of_int 8837694422794646872);
    bp.[19] <- tmp;
    tmp <- (W64.of_int 9711310516503218385);
    bp.[20] <- tmp;
    tmp <- (W64.of_int 6633261091277544380);
    bp.[21] <- tmp;
    tmp <- (W64.of_int 6086011487233213371);
    bp.[22] <- tmp;
    tmp <- (W64.of_int 14468328207451868826);
    bp.[23] <- tmp;
    tmp <- (W64.of_int 15312291203922875661);
    bp.[24] <- tmp;
    tmp <- (W64.of_int 10847478293144797667);
    bp.[25] <- tmp;
    tmp <- (W64.of_int 12824558171927804903);
    bp.[26] <- tmp;
    tmp <- (W64.of_int 7264247675481435729);
    bp.[27] <- tmp;
    tmp <- (W64.of_int 12023220503046567441);
    bp.[28] <- tmp;
    tmp <- (W64.of_int 5117160642964443543);
    bp.[29] <- tmp;
    tmp <- (W64.of_int 3958705157555305931);
    bp.[30] <- tmp;
    tmp <- (W64.of_int 0);
    bp.[31] <- tmp;
    tmp <- (W64.of_int 1);
    bp.[32] <- tmp;
    tmp <- (W64.of_int 0);
    bp.[33] <- tmp;
    tmp <- (W64.of_int 0);
    bp.[34] <- tmp;
    tmp <- (W64.of_int 0);
    bp.[35] <- tmp;
    tmp <- (W64.of_int 0);
    bp.[36] <- tmp;
    tmp <- (W64.of_int 0);
    bp.[37] <- tmp;
    tmp <- (W64.of_int 0);
    bp.[38] <- tmp;
    tmp <- (W64.of_int 0);
    bp.[39] <- tmp;
    tmp <- (W64.of_int 0);
    bp.[40] <- tmp;
    tmp <- (W64.of_int 0);
    bp.[41] <- tmp;
    tmp <- (W64.of_int 0);
    bp.[42] <- tmp;
    tmp <- (W64.of_int 0);
    bp.[43] <- tmp;
    tmp <- (W64.of_int 0);
    bp.[44] <- tmp;
    tmp <- (W64.of_int 0);
    bp.[45] <- tmp;
    tmp <- (W64.of_int 0);
    bp.[46] <- tmp;
    tmp <- (W64.of_int 0);
    bp.[47] <- tmp;
    tmp <- (W64.of_int 0);
    bp.[48] <- tmp;
    tmp <- (W64.of_int 0);
    bp.[49] <- tmp;
    tmp <- (W64.of_int 0);
    bp.[50] <- tmp;
    tmp <- (W64.of_int 0);
    bp.[51] <- tmp;
    tmp <- (W64.of_int 0);
    bp.[52] <- tmp;
    tmp <- (W64.of_int 0);
    bp.[53] <- tmp;
    tmp <- (W64.of_int 0);
    bp.[54] <- tmp;
    tmp <- (W64.of_int 0);
    bp.[55] <- tmp;
    tmp <- (W64.of_int 0);
    bp.[56] <- tmp;
    tmp <- (W64.of_int 0);
    bp.[57] <- tmp;
    tmp <- (W64.of_int 0);
    bp.[58] <- tmp;
    tmp <- (W64.of_int 0);
    bp.[59] <- tmp;
    tmp <- (W64.of_int 0);
    bp.[60] <- tmp;
    tmp <- (W64.of_int 0);
    bp.[61] <- tmp;
    tmp <- (W64.of_int 0);
    bp.[62] <- tmp;
    tmp <- (W64.of_int 0);
    bp.[63] <- tmp;
    return (bp);
  }
  
  proc bn_set_bq (bq:W64.t Array64.t) : W64.t Array64.t = {
    
    var tmp:W64.t;
    
    tmp <- (W64.of_int 10295868235056114890);
    bq.[0] <- tmp;
    tmp <- (W64.of_int 2368294145691358254);
    bq.[1] <- tmp;
    tmp <- (W64.of_int 14720334291626306557);
    bq.[2] <- tmp;
    tmp <- (W64.of_int 2984881376514770213);
    bq.[3] <- tmp;
    tmp <- (W64.of_int 1686921512324286912);
    bq.[4] <- tmp;
    tmp <- (W64.of_int 4231997920348793745);
    bq.[5] <- tmp;
    tmp <- (W64.of_int 9351739171860724641);
    bq.[6] <- tmp;
    tmp <- (W64.of_int 15389780787261235978);
    bq.[7] <- tmp;
    tmp <- (W64.of_int 9010269563805845161);
    bq.[8] <- tmp;
    tmp <- (W64.of_int 9099069857497600575);
    bq.[9] <- tmp;
    tmp <- (W64.of_int 6313057817749168983);
    bq.[10] <- tmp;
    tmp <- (W64.of_int 2462308226731011450);
    bq.[11] <- tmp;
    tmp <- (W64.of_int 16990358414005964232);
    bq.[12] <- tmp;
    tmp <- (W64.of_int 14888999731061913291);
    bq.[13] <- tmp;
    tmp <- (W64.of_int 16109364122071307575);
    bq.[14] <- tmp;
    tmp <- (W64.of_int 5844012461544371476);
    bq.[15] <- tmp;
    tmp <- (W64.of_int 9903669814688248149);
    bq.[16] <- tmp;
    tmp <- (W64.of_int 3744825669284545269);
    bq.[17] <- tmp;
    tmp <- (W64.of_int 2140999566259290734);
    bq.[18] <- tmp;
    tmp <- (W64.of_int 17675388845589293745);
    bq.[19] <- tmp;
    tmp <- (W64.of_int 975876959296885154);
    bq.[20] <- tmp;
    tmp <- (W64.of_int 13266522182555088761);
    bq.[21] <- tmp;
    tmp <- (W64.of_int 12172022974466426742);
    bq.[22] <- tmp;
    tmp <- (W64.of_int 10489912341194186036);
    bq.[23] <- tmp;
    tmp <- (W64.of_int 12177838334136199707);
    bq.[24] <- tmp;
    tmp <- (W64.of_int 3248212512580043719);
    bq.[25] <- tmp;
    tmp <- (W64.of_int 7202372270146058191);
    bq.[26] <- tmp;
    tmp <- (W64.of_int 14528495350962871459);
    bq.[27] <- tmp;
    tmp <- (W64.of_int 5599696932383583266);
    bq.[28] <- tmp;
    tmp <- (W64.of_int 10234321285928887087);
    bq.[29] <- tmp;
    tmp <- (W64.of_int 7917410315110611862);
    bq.[30] <- tmp;
    tmp <- (W64.of_int 0);
    bq.[31] <- tmp;
    tmp <- (W64.of_int 2);
    bq.[32] <- tmp;
    tmp <- (W64.of_int 0);
    bq.[33] <- tmp;
    tmp <- (W64.of_int 0);
    bq.[34] <- tmp;
    tmp <- (W64.of_int 0);
    bq.[35] <- tmp;
    tmp <- (W64.of_int 0);
    bq.[36] <- tmp;
    tmp <- (W64.of_int 0);
    bq.[37] <- tmp;
    tmp <- (W64.of_int 0);
    bq.[38] <- tmp;
    tmp <- (W64.of_int 0);
    bq.[39] <- tmp;
    tmp <- (W64.of_int 0);
    bq.[40] <- tmp;
    tmp <- (W64.of_int 0);
    bq.[41] <- tmp;
    tmp <- (W64.of_int 0);
    bq.[42] <- tmp;
    tmp <- (W64.of_int 0);
    bq.[43] <- tmp;
    tmp <- (W64.of_int 0);
    bq.[44] <- tmp;
    tmp <- (W64.of_int 0);
    bq.[45] <- tmp;
    tmp <- (W64.of_int 0);
    bq.[46] <- tmp;
    tmp <- (W64.of_int 0);
    bq.[47] <- tmp;
    tmp <- (W64.of_int 0);
    bq.[48] <- tmp;
    tmp <- (W64.of_int 0);
    bq.[49] <- tmp;
    tmp <- (W64.of_int 0);
    bq.[50] <- tmp;
    tmp <- (W64.of_int 0);
    bq.[51] <- tmp;
    tmp <- (W64.of_int 0);
    bq.[52] <- tmp;
    tmp <- (W64.of_int 0);
    bq.[53] <- tmp;
    tmp <- (W64.of_int 0);
    bq.[54] <- tmp;
    tmp <- (W64.of_int 0);
    bq.[55] <- tmp;
    tmp <- (W64.of_int 0);
    bq.[56] <- tmp;
    tmp <- (W64.of_int 0);
    bq.[57] <- tmp;
    tmp <- (W64.of_int 0);
    bq.[58] <- tmp;
    tmp <- (W64.of_int 0);
    bq.[59] <- tmp;
    tmp <- (W64.of_int 0);
    bq.[60] <- tmp;
    tmp <- (W64.of_int 0);
    bq.[61] <- tmp;
    tmp <- (W64.of_int 0);
    bq.[62] <- tmp;
    tmp <- (W64.of_int 0);
    bq.[63] <- tmp;
    return (bq);
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
    exp_order <@ bn_set_q (exp_order);
    group_order <@ bn_set_p (group_order);
    group_generator <@ bn_set_g (group_generator);
    barrett_parameter <@ bn_set_bp (barrett_parameter);
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
    exp_order <@ bn_set_q (exp_order);
    exp_barrett <@ bn_set_bq (exp_barrett);
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
    exp_order <@ bn_set_q (exp_order);
    challenge_0 <@ usample (exp_order);
    return (challenge_0);
  }
  
  proc verify (statement:W64.t Array32.t, commitment_0:W64.t Array32.t,
               challenge_0:W64.t Array32.t, response_0:W64.t Array32.t) : 
  W64.t = {
    
    var result1:W64.t;
    var exp_order:W64.t Array32.t;
    var exp_barrett:W64.t Array64.t;
    var group_order:W64.t Array32.t;
    var group_barrett:W64.t Array64.t;
    var group_generator:W64.t Array32.t;
    var tmp:W64.t Array32.t;
    var v1:W64.t Array32.t;
    var v2:W64.t Array32.t;
    var v3:W64.t Array32.t;
    var v4:W64.t Array32.t;
    var result2:W64.t;
    exp_barrett <- witness;
    exp_order <- witness;
    group_barrett <- witness;
    group_generator <- witness;
    group_order <- witness;
    tmp <- witness;
    v1 <- witness;
    v2 <- witness;
    v3 <- witness;
    v4 <- witness;
    exp_order <@ bn_set_q (exp_order);
    exp_barrett <@ bn_set_bq (exp_barrett);
    group_order <@ bn_set_p (group_order);
    group_barrett <@ bn_set_bp (group_barrett);
    group_generator <@ bn_set_g (group_generator);
    statement <@ bn_breduce_small (statement, group_barrett, group_order);
    commitment_0 <@ bn_breduce_small (commitment_0, group_barrett,
    group_order);
    challenge_0 <@ bn_breduce_small (challenge_0, exp_barrett, exp_order);
    response_0 <@ bn_breduce_small (response_0, exp_barrett, exp_order);
    tmp <@ expm (group_barrett, group_order, statement, challenge_0);
    v1 <@ mulm (group_barrett, group_order, commitment_0, tmp);
    v2 <@ expm (group_barrett, group_order, group_generator, response_0);
    result1 <@ bn_eq (v1, v2);
    v3 <@ expm (group_barrett, group_order, statement, exp_order);
    v4 <@ bn_set1 (v4);
    result2 <@ bn_eq (v3, v4);
    result1 <- (result1 `&` result2);
    return (result1);
  }
}.


require import AllCore IntDiv CoreMap List Distr.
from Jasmin require import JModel.

require import Array4 Array8.
require import WArray32 WArray64.



module M = {
  proc bn2_unpack (a:W64.t Array8.t) : W64.t Array4.t * W64.t Array4.t = {
    var aux: int;
    
    var hi:W64.t Array4.t;
    var lo:W64.t Array4.t;
    var i:int;
    hi <- witness;
    lo <- witness;
    i <- 0;
    while (i < 4) {
      lo.[i] <- a.[i];
      hi.[i] <- a.[(4 + i)];
      i <- i + 1;
    }
    return (hi, lo);
  }
  
  proc bn_add1 (a:W64.t Array4.t, b:W64.t) : bool * W64.t Array4.t = {
    var aux: bool;
    var aux_1: int;
    var aux_0: W64.t;
    
    var cf:bool;
    var i:int;
    
    (aux, aux_0) <- adc_64 a.[0] b false;
    cf <- aux;
    a.[0] <- aux_0;
    i <- 1;
    while (i < 4) {
      (aux, aux_0) <- adc_64 a.[i] (W64.of_int 0) cf;
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
    (cf, x1) <- adc_64 x1 x2 false;
    a.[0] <- x1;
    i <- 1;
    while (i < 4) {
      x1 <- a.[i];
      x2 <- b.[i];
      (cf, x1) <- adc_64 x1 x2 cf;
      a.[i] <- x1;
      i <- i + 1;
    }
    return (cf, a);
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
  
  proc mul1acc (k:int, a:W64.t, b:W64.t Array4.t, r:W64.t Array8.t,
                _zero:W64.t, of_0:bool, cf:bool) : W64.t * bool * bool *
                                                   W64.t Array8.t = {
    var aux: int;
    
    var x1:W64.t;
    var i:int;
    var x2:W64.t;
    var hi:W64.t;
    var lo:W64.t;
    
    aux <- (4 - 1);
    i <- 0;
    while (i < aux) {
      x1 <- a;
      x2 <- b.[i];
      (x1, x2) <- MULX_64 x1 x2;
      hi <- x1;
      lo <- x2;
      x1 <- r.[(k + i)];
      (of_0, x1) <- ADOX_64 x1 lo of_0;
      r.[(k + i)] <- x1;
      x1 <- r.[((k + i) + 1)];
      (cf, x1) <- ADCX_64 x1 hi cf;
      r.[((k + i) + 1)] <- x1;
      i <- i + 1;
    }
    x1 <- a;
    x2 <- b.[(4 - 1)];
    (x1, x2) <- MULX_64 x1 x2;
    r.[(4 + k)] <- x1;
    lo <- x2;
    x1 <- r.[((4 + k) - 1)];
    (of_0, x1) <- ADOX_64 x1 lo of_0;
    r.[((4 + k) - 1)] <- x1;
    x1 <- r.[(4 + k)];
    (cf, x1) <- ADCX_64 x1 _zero cf;
    r.[(4 + k)] <- x1;
    x1 <- r.[(4 + k)];
    (of_0, x1) <- ADOX_64 x1 _zero of_0;
    r.[(4 + k)] <- x1;
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
    r <- witness;
    ai <- a.[0];
    (_zero, of_0, cf, r) <@ mul1 (ai, b);
    i <- 1;
    while (i < 4) {
      ai <- a.[i];
      (_zero, of_0, cf, r) <@ mul1acc (i, ai, b, r, _zero, of_0, cf);
      i <- i + 1;
    }
    return (_zero, of_0, cf, r);
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
  
  proc maskOnCarry (mask:int, r:W64.t, _cf:bool) : W64.t = {
    
    
    
    (_cf, r) <- sbb_64 r r _cf;
    r <- (r `&` (W64.of_int mask));
    return (r);
  }
  
  proc x2r (x0:W64.t, x1:W64.t, x2:W64.t, x3:W64.t) : W64.t Array4.t = {
    
    var r:W64.t Array4.t;
    r <- witness;
    r.[0] <- x0;
    r.[1] <- x1;
    r.[2] <- x2;
    r.[3] <- x3;
    return (r);
  }
  
  proc r2x (x:W64.t Array4.t) : W64.t * W64.t * W64.t * W64.t = {
    
    var r0:W64.t;
    var r1:W64.t;
    var r2:W64.t;
    var r3:W64.t;
    
    r0 <- x.[0];
    r1 <- x.[1];
    r2 <- x.[2];
    r3 <- x.[3];
    return (r0, r1, r2, r3);
  }
  
  proc cminusP (xx:W64.t Array4.t) : W64.t Array4.t = {
    var aux: bool;
    var aux_0: W64.t;
    
    var x:W64.t Array4.t;
    var t:W64.t Array4.t;
    var twop63:W64.t;
    var cf:bool;
    t <- witness;
    x <- witness;
    x.[0] <- xx.[0];
    x.[1] <- xx.[1];
    x.[2] <- xx.[2];
    x.[3] <- xx.[3];
    t <- copy_64 x;
    twop63 <- (W64.of_int 1);
    twop63 <- (twop63 `<<` (W8.of_int 63));
    (aux, aux_0) <- adc_64 t.[0] (W64.of_int 19) false;
    cf <- aux;
    t.[0] <- aux_0;
    (aux, aux_0) <- adc_64 t.[1] (W64.of_int 0) cf;
    cf <- aux;
    t.[1] <- aux_0;
    (aux, aux_0) <- adc_64 t.[2] (W64.of_int 0) cf;
    cf <- aux;
    t.[2] <- aux_0;
    (aux, aux_0) <- adc_64 t.[3] twop63 cf;
    cf <- aux;
    t.[3] <- aux_0;
    x.[0] <- (cf ? t.[0] : x.[0]);
    x.[1] <- (cf ? t.[1] : x.[1]);
    x.[2] <- (cf ? t.[2] : x.[2]);
    x.[3] <- (cf ? t.[3] : x.[3]);
    xx.[0] <- x.[0];
    xx.[1] <- x.[1];
    xx.[2] <- x.[2];
    xx.[3] <- x.[3];
    return (xx);
  }
  
  proc redp25519 (_of:bool, _cf:bool, a:W64.t Array8.t) : W64.t Array4.t = {
    
    var al:W64.t Array4.t;
    var tmp:W64.t;
    var _zero:W64.t;
    var ah:W64.t Array4.t;
    var  _0:W64.t Array4.t;
    var  _1:bool;
    var  _2:bool;
    var  _3:bool;
    var  _4:bool;
    var  _5:bool;
    var  _6:W64.t Array4.t;
     _0 <- witness;
     _6 <- witness;
    ah <- witness;
    al <- witness;
    tmp <- (W64.of_int 38);
    _zero <- (W64.of_int 0);
    (ah,  _0) <@ bn2_unpack (a);
    (_zero, _of, _cf, a) <@ mul1acc (0, tmp, ah, a, _zero, _of, _cf);
    ( _1,  _2,  _3,  _4,  _5, tmp) <- IMULri_64 a.[4] (W64.of_int 38);
    ( _6, al) <@ bn2_unpack (a);
    (_cf, al) <@ bn_add1 (al, tmp);
    tmp <@ maskOnCarry (38, tmp, _cf);
    al.[0] <- (al.[0] + tmp);
    return (al);
  }
  
  proc freeze (x:W64.t Array4.t) : W64.t Array4.t = {
    
    
    
    x <@ cminusP (x);
    x <@ cminusP (x);
    return (x);
  }
  
  proc _mulm (f:W64.t Array4.t, g0:W64.t, g1:W64.t, g2:W64.t, g3:W64.t) : 
  W64.t * W64.t * W64.t * W64.t = {
    
    var g:W64.t Array4.t;
    var _zero:W64.t;
    var of_0:bool;
    var cf:bool;
    var h:W64.t Array8.t;
    g <- witness;
    h <- witness;
    g <@ x2r (g0, g1, g2, g3);
    (_zero, of_0, cf, h) <@ bn_muln (f, g);
    g <@ redp25519 (of_0, cf, h);
    g <@ freeze (g);
    (g0, g1, g2, g3) <@ r2x (g);
    return (g0, g1, g2, g3);
  }
  
  proc mulm (p:W64.t Array4.t, a:W64.t Array4.t, b:W64.t Array4.t) : 
  W64.t Array4.t = {
    
    var g0:W64.t;
    var g1:W64.t;
    var g2:W64.t;
    var g3:W64.t;
    
    (g0, g1, g2, g3) <@ r2x (b);
    (g0, g1, g2, g3) <@ _mulm (a, g0, g1, g2, g3);
    b <@ x2r (g0, g1, g2, g3);
    return (b);
  }
  
  proc addm (a:W64.t Array4.t, b:W64.t Array4.t) : W64.t Array4.t = {
    
    var f:W64.t Array4.t;
    var  _0:bool;
    f <- witness;
    ( _0, f) <@ bn_addc (a, b);
    f <@ cminusP (f);
    return (f);
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
    var q:W64.t;
    var par:W64.t;
    var cbit:W64.t;
    x1 <- witness;
    x2 <- witness;
    x3 <- witness;
    x4 <- witness;
    ctr <- (W64.of_int ((4 * 64) - 1));
    x1.[0] <- (W64.of_int 1);
    x1.[1] <- (W64.of_int 0);
    x1.[2] <- (W64.of_int 0);
    x1.[3] <- (W64.of_int 0);
    x2.[0] <- (W64.of_int 1);
    x2.[1] <- (W64.of_int 0);
    x2.[2] <- (W64.of_int 0);
    x2.[3] <- (W64.of_int 0);
    d <@ ith_bit (n, ctr);
    x3 <- x;
    x4 <@ mulm (m, x, x);
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
      x1 <@ mulm (m, x1, x2);
      x2 <@ mulm (m, x2, x2);
      q <- (q `|` t2);
      cbit <- (q `^` p);
      (x1, x3) <@ swapr (x1, x3, cbit);
      (x2, x4) <@ swapr (x2, x4, cbit);
    }
    par <@ ith_bit (n, (W64.of_int 0));
    (x1, x2) <@ swapr (x2, x1, par);
    return (x1);
  }
  
  proc toEC () : unit = {
    
    var a:W64.t Array4.t;
    var b:W64.t Array4.t;
    var r:W64.t Array4.t;
    var x:W64.t;
    var  _0:W64.t Array4.t;
     _0 <- witness;
    a <- witness;
    b <- witness;
    r <- witness;
    r <@ addm (a, b);
    r <@ mulm (a, a, b);
    r <@ expm (a, a, b);
    x <@ ith_bit (a, x);
    ( _0, a) <@ swapr (a, a, x);
    return ();
  }
}.


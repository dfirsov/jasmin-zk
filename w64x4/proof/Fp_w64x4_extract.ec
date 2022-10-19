require import AllCore IntDiv CoreMap List Distr.
require import JModel.

require import Array4 Array8 Array32.
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
  
  proc bn_eq (a:W64.t Array4.t, b:W64.t Array4.t) : W64.t = {
    var aux: int;
    
    var res_0:W64.t;
    var are_equal:W64.t;
    var acc:W64.t;
    var i:int;
    var t:W64.t;
    var zf:bool;
    var  _0:bool;
    var  _1:bool;
    var  _2:bool;
    var  _3:bool;
    var  _4:W64.t;
    
    res_0 <- (W64.of_int 0);
    are_equal <- (W64.of_int 1);
    acc <- (W64.of_int 0);
    i <- 0;
    while (i < 4) {
      t <- a.[i];
      t <- (t `^` b.[i]);
      acc <- (acc `|` t);
      i <- i + 1;
    }
    ( _0,  _1,  _2,  _3, zf,  _4) <- AND_64 acc acc;
    res_0 <- (zf ? are_equal : res_0);
    return (res_0);
  }
  
  proc bn_test0 (a:W64.t Array4.t) : W64.t = {
    var aux: int;
    
    var res_0:W64.t;
    var is_zero:W64.t;
    var acc:W64.t;
    var i:int;
    var zf:bool;
    var  _0:bool;
    var  _1:bool;
    var  _2:bool;
    var  _3:bool;
    var  _4:W64.t;
    
    res_0 <- (W64.of_int 0);
    is_zero <- (W64.of_int 1);
    acc <- a.[0];
    i <- 1;
    while (i < 4) {
      acc <- (acc `|` a.[i]);
      i <- i + 1;
    }
    ( _0,  _1,  _2,  _3, zf,  _4) <- AND_64 acc acc;
    res_0 <- (zf ? is_zero : res_0);
    return (res_0);
  }
  
  proc bn_add1 (a:W64.t Array4.t, b:W64.t) : bool * W64.t Array4.t = {
    var aux: bool;
    var aux_1: int;
    var aux_0: W64.t;
    
    var cf:bool;
    var i:int;
    
    (aux, aux_0) <- addc_64 a.[0] b false;
    cf <- aux;
    a.[0] <- aux_0;
    i <- 1;
    while (i < 4) {
      (aux, aux_0) <- addc_64 a.[i] (W64.of_int 0) cf;
      cf <- aux;
      a.[i] <- aux_0;
      i <- i + 1;
    }
    return (cf, a);
  }
  
  proc bn_addc (a:W64.t Array4.t, b:W64.t Array4.t) : bool * W64.t Array4.t = {
    var aux: bool;
    var aux_1: int;
    var aux_0: W64.t;
    
    var cf:bool;
    var i:int;
    
    (aux, aux_0) <- addc_64 a.[0] b.[0] false;
    cf <- aux;
    a.[0] <- aux_0;
    i <- 1;
    while (i < 4) {
      (aux, aux_0) <- addc_64 a.[i] b.[i] cf;
      cf <- aux;
      a.[i] <- aux_0;
      i <- i + 1;
    }
    return (cf, a);
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
  
  proc mul1 (a:W64.t, b:W64.t Array4.t) : W64.t * bool * bool *
                                          W64.t Array8.t = {
    var aux_2: bool;
    var aux_1: int;
    var aux_0: W64.t;
    var aux: W64.t;
    
    var _zero:W64.t;
    var of_0:bool;
    var cf:bool;
    var r:W64.t Array8.t;
    var i:int;
    var lo:W64.t;
    var  _0:bool;
    var  _1:bool;
    var  _2:bool;
    r <- witness;
    (of_0, cf,  _0,  _1,  _2, _zero) <- set0_64 ;
    (aux_0, aux) <- MULX_64 a b.[0];
    r.[1] <- aux_0;
    r.[0] <- aux;
    i <- 1;
    while (i < 4) {
      (aux_0, aux) <- MULX_64 a b.[i];
      r.[(i + 1)] <- aux_0;
      lo <- aux;
      (aux_2, aux_0) <- ADCX_64 r.[i] lo cf;
      cf <- aux_2;
      r.[i] <- aux_0;
      i <- i + 1;
    }
    (aux_2, aux_0) <- ADCX_64 r.[4] _zero cf;
    cf <- aux_2;
    r.[4] <- aux_0;
    return (_zero, of_0, cf, r);
  }
  
  proc mul1acc (k:int, a:W64.t, b:W64.t Array4.t, r:W64.t Array8.t,
                _zero:W64.t, of_0:bool, cf:bool) : W64.t * bool * bool *
                                                   W64.t Array8.t = {
    var aux_0: bool;
    var aux: int;
    var aux_2: W64.t;
    var aux_1: W64.t;
    
    var i:int;
    var hi:W64.t;
    var lo:W64.t;
    
    aux <- (4 - 1);
    i <- 0;
    while (i < aux) {
      (hi, lo) <- MULX_64 a b.[i];
      (aux_0, aux_2) <- ADOX_64 r.[(k + i)] lo of_0;
      of_0 <- aux_0;
      r.[(k + i)] <- aux_2;
      (aux_0, aux_2) <- ADCX_64 r.[((k + i) + 1)] hi cf;
      cf <- aux_0;
      r.[((k + i) + 1)] <- aux_2;
      i <- i + 1;
    }
    (aux_2, aux_1) <- MULX_64 a b.[(4 - 1)];
    r.[(4 + k)] <- aux_2;
    lo <- aux_1;
    (aux_0, aux_2) <- ADOX_64 r.[((4 + k) - 1)] lo of_0;
    of_0 <- aux_0;
    r.[((4 + k) - 1)] <- aux_2;
    (aux_0, aux_2) <- ADCX_64 r.[(4 + k)] _zero cf;
    cf <- aux_0;
    r.[(4 + k)] <- aux_2;
    (aux_0, aux_2) <- ADOX_64 r.[(4 + k)] _zero of_0;
    of_0 <- aux_0;
    r.[(4 + k)] <- aux_2;
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
    var c1:W64.t;
    var c2:W64.t;
    var r:W64.t;
    
    c1 <- (ctr `>>` (W8.of_int 6));
    c2 <- (ctr - (c1 * (W64.of_int 64)));
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
    
    
    
    (_cf, r) <- subc_64 r r _cf;
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
  
  proc cminusP (x:W64.t Array4.t) : W64.t Array4.t = {
    var aux: bool;
    var aux_0: W64.t;
    
    var t:W64.t Array4.t;
    var twop63:W64.t;
    var cf:bool;
    t <- witness;
    t <- x;
    twop63 <- (W64.of_int 1);
    twop63 <- (twop63 `<<` (W8.of_int 63));
    (aux, aux_0) <- addc_64 t.[0] (W64.of_int 19) false;
    cf <- aux;
    t.[0] <- aux_0;
    (aux, aux_0) <- addc_64 t.[1] (W64.of_int 0) cf;
    cf <- aux;
    t.[1] <- aux_0;
    (aux, aux_0) <- addc_64 t.[2] (W64.of_int 0) cf;
    cf <- aux;
    t.[2] <- aux_0;
    (aux, aux_0) <- addc_64 t.[3] twop63 cf;
    cf <- aux;
    t.[3] <- aux_0;
    x.[0] <- (cf ? t.[0] : x.[0]);
    x.[1] <- (cf ? t.[1] : x.[1]);
    x.[2] <- (cf ? t.[2] : x.[2]);
    x.[3] <- (cf ? t.[3] : x.[3]);
    return (x);
  }
  
  proc caddP (cf:bool, x:W64.t Array4.t) : W64.t Array4.t = {
    
    var p:W64.t Array4.t;
    var _zero:W64.t;
    var  _0:bool;
    p <- witness;
    p.[0] <- (W64.of_int 18446744073709551597);
    p.[1] <- (W64.of_int 18446744073709551615);
    p.[2] <- (W64.of_int 18446744073709551615);
    p.[3] <- (W64.of_int 9223372036854775807);
    _zero <- (W64.of_int 0);
    p.[0] <- ((! cf) ? _zero : p.[0]);
    p.[1] <- ((! cf) ? _zero : p.[1]);
    p.[2] <- ((! cf) ? _zero : p.[2]);
    p.[3] <- ((! cf) ? _zero : p.[3]);
    ( _0, x) <@ bn_addc (x, p);
    return (x);
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
  
  proc _addm (f0:W64.t, f1:W64.t, f2:W64.t, f3:W64.t, g0:W64.t, g1:W64.t,
              g2:W64.t, g3:W64.t) : W64.t * W64.t * W64.t * W64.t = {
    
    var f:W64.t Array4.t;
    var g:W64.t Array4.t;
    var  _0:bool;
    f <- witness;
    g <- witness;
    f <@ x2r (f0, f1, f2, f3);
    g <@ x2r (g0, g1, g2, g3);
    ( _0, f) <@ bn_addc (f, g);
    f <@ cminusP (f);
    (f0, f1, f2, f3) <@ r2x (f);
    return (f0, f1, f2, f3);
  }
  
  proc addm (a:W64.t Array4.t, b:W64.t Array4.t) : W64.t Array4.t = {
    
    var f0:W64.t;
    var f1:W64.t;
    var f2:W64.t;
    var f3:W64.t;
    var g0:W64.t;
    var g1:W64.t;
    var g2:W64.t;
    var g3:W64.t;
    
    (f0, f1, f2, f3) <@ r2x (a);
    (g0, g1, g2, g3) <@ r2x (b);
    (f0, f1, f2, f3) <@ _addm (f0, f1, f2, f3, g0, g1, g2, g3);
    a <@ x2r (f0, f1, f2, f3);
    return (a);
  }
  
  proc _subm (f0:W64.t, f1:W64.t, f2:W64.t, f3:W64.t, g0:W64.t, g1:W64.t,
              g2:W64.t, g3:W64.t) : W64.t * W64.t * W64.t * W64.t = {
    
    var f:W64.t Array4.t;
    var g:W64.t Array4.t;
    var cf:bool;
    f <- witness;
    g <- witness;
    f <@ x2r (f0, f1, f2, f3);
    g <@ x2r (g0, g1, g2, g3);
    (cf, f) <@ bn_subc (f, g);
    f <@ caddP (cf, f);
    (f0, f1, f2, f3) <@ r2x (f);
    return (f0, f1, f2, f3);
  }
  
  proc subm (a:W64.t Array4.t, b:W64.t Array4.t) : W64.t Array4.t = {
    
    var f0:W64.t;
    var f1:W64.t;
    var f2:W64.t;
    var f3:W64.t;
    var g0:W64.t;
    var g1:W64.t;
    var g2:W64.t;
    var g3:W64.t;
    
    (f0, f1, f2, f3) <@ r2x (a);
    (g0, g1, g2, g3) <@ r2x (b);
    (f0, f1, f2, f3) <@ _subm (f0, f1, f2, f3, g0, g1, g2, g3);
    a <@ x2r (f0, f1, f2, f3);
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
    var _cf:bool;
    var  _0:W64.t Array4.t;
     _0 <- witness;
    a <- witness;
    b <- witness;
    r <- witness;
    r <@ addm (a, b);
    r <@ subm (a, b);
    r <@ mulm (a, a, b);
    r <@ expm (a, a, b);
    x <@ ith_bit (a, x);
    ( _0, a) <@ swapr (a, a, x);
    x <@ bn_eq (a, b);
    x <@ bn_test0 (a);
    _cf <- false;
    x <@ maskOnCarry (7, x, _cf);
    return ();
  }
}.


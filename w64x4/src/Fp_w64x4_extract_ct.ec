require import AllCore IntDiv CoreMap List Distr.
from Jasmin require import JModel.

require import Array4 Array8 Array32.
require import WArray32 WArray64.



module M = {
  var leakages : leakages_t
  
  proc bn2_unpack (a:W64.t Array8.t) : W64.t Array4.t * W64.t Array4.t = {
    var aux: int;
    var aux_0: W64.t;
    
    var hi:W64.t Array4.t;
    var lo:W64.t Array4.t;
    var i:int;
    hi <- witness;
    lo <- witness;
    leakages <- LeakFor(0,4) :: LeakAddr([]) :: leakages;
    i <- 0;
    while (i < 4) {
      leakages <- LeakAddr([i]) :: leakages;
      aux_0 <- a.[i];
      leakages <- LeakAddr([i]) :: leakages;
      lo.[i] <- aux_0;
      leakages <- LeakAddr([(4 + i)]) :: leakages;
      aux_0 <- a.[(4 + i)];
      leakages <- LeakAddr([i]) :: leakages;
      hi.[i] <- aux_0;
      i <- i + 1;
    }
    return (hi, lo);
  }
  
  proc bn_eq (a:W64.t Array4.t, b:W64.t Array4.t) : W64.t = {
    var aux_5: bool;
    var aux_4: bool;
    var aux_3: bool;
    var aux_2: bool;
    var aux_1: bool;
    var aux_0: int;
    var aux: W64.t;
    
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
    
    leakages <- LeakAddr([]) :: leakages;
    aux <- (W64.of_int 0);
    res_0 <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux <- (W64.of_int 1);
    are_equal <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux <- (W64.of_int 0);
    acc <- aux;
    leakages <- LeakFor(0,4) :: LeakAddr([]) :: leakages;
    i <- 0;
    while (i < 4) {
      leakages <- LeakAddr([i]) :: leakages;
      aux <- a.[i];
      t <- aux;
      leakages <- LeakAddr([i]) :: leakages;
      aux <- (t `^` b.[i]);
      t <- aux;
      leakages <- LeakAddr([]) :: leakages;
      aux <- (acc `|` t);
      acc <- aux;
      i <- i + 1;
    }
    leakages <- LeakAddr([]) :: leakages;
    (aux_5, aux_4, aux_3, aux_2, aux_1, aux) <- AND_64 acc acc;
     _0 <- aux_5;
     _1 <- aux_4;
     _2 <- aux_3;
     _3 <- aux_2;
    zf <- aux_1;
     _4 <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux <- (zf ? are_equal : res_0);
    res_0 <- aux;
    return (res_0);
  }
  
  proc bn_test0 (a:W64.t Array4.t) : W64.t = {
    var aux_5: bool;
    var aux_4: bool;
    var aux_3: bool;
    var aux_2: bool;
    var aux_1: bool;
    var aux_0: int;
    var aux: W64.t;
    
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
    
    leakages <- LeakAddr([]) :: leakages;
    aux <- (W64.of_int 0);
    res_0 <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux <- (W64.of_int 1);
    is_zero <- aux;
    leakages <- LeakAddr([0]) :: leakages;
    aux <- a.[0];
    acc <- aux;
    leakages <- LeakFor(1,4) :: LeakAddr([]) :: leakages;
    i <- 1;
    while (i < 4) {
      leakages <- LeakAddr([i]) :: leakages;
      aux <- (acc `|` a.[i]);
      acc <- aux;
      i <- i + 1;
    }
    leakages <- LeakAddr([]) :: leakages;
    (aux_5, aux_4, aux_3, aux_2, aux_1, aux) <- AND_64 acc acc;
     _0 <- aux_5;
     _1 <- aux_4;
     _2 <- aux_3;
     _3 <- aux_2;
    zf <- aux_1;
     _4 <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux <- (zf ? is_zero : res_0);
    res_0 <- aux;
    return (res_0);
  }
  
  proc bn_add1 (a:W64.t Array4.t, b:W64.t) : bool * W64.t Array4.t = {
    var aux: bool;
    var aux_1: int;
    var aux_0: W64.t;
    
    var cf:bool;
    var i:int;
    
    leakages <- LeakAddr([0]) :: leakages;
    (aux, aux_0) <- adc_64 a.[0] b false;
    cf <- aux;
    leakages <- LeakAddr([0]) :: leakages;
    a.[0] <- aux_0;
    leakages <- LeakFor(1,4) :: LeakAddr([]) :: leakages;
    i <- 1;
    while (i < 4) {
      leakages <- LeakAddr([i]) :: leakages;
      (aux, aux_0) <- adc_64 a.[i] (W64.of_int 0) cf;
      cf <- aux;
      leakages <- LeakAddr([i]) :: leakages;
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
    
    leakages <- LeakAddr([0; 0]) :: leakages;
    (aux, aux_0) <- adc_64 a.[0] b.[0] false;
    cf <- aux;
    leakages <- LeakAddr([0]) :: leakages;
    a.[0] <- aux_0;
    leakages <- LeakFor(1,4) :: LeakAddr([]) :: leakages;
    i <- 1;
    while (i < 4) {
      leakages <- LeakAddr([i; i]) :: leakages;
      (aux, aux_0) <- adc_64 a.[i] b.[i] cf;
      cf <- aux;
      leakages <- LeakAddr([i]) :: leakages;
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
    
    leakages <- LeakAddr([0; 0]) :: leakages;
    (aux, aux_0) <- sbb_64 a.[0] b.[0] false;
    cf <- aux;
    leakages <- LeakAddr([0]) :: leakages;
    a.[0] <- aux_0;
    leakages <- LeakFor(1,4) :: LeakAddr([]) :: leakages;
    i <- 1;
    while (i < 4) {
      leakages <- LeakAddr([i; i]) :: leakages;
      (aux, aux_0) <- sbb_64 a.[i] b.[i] cf;
      cf <- aux;
      leakages <- LeakAddr([i]) :: leakages;
      a.[i] <- aux_0;
      i <- i + 1;
    }
    return (cf, a);
  }
  
  proc mul1 (a:W64.t, b:W64.t Array4.t) : W64.t * bool * bool *
                                          W64.t Array8.t = {
    var aux_3: bool;
    var aux_2: bool;
    var aux_1: bool;
    var aux_0: bool;
    var aux: bool;
    var aux_6: int;
    var aux_5: W64.t;
    var aux_4: W64.t;
    
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
    leakages <- LeakAddr([]) :: leakages;
    (aux_3, aux_2, aux_1, aux_0, aux, aux_5) <- set0_64 ;
    of_0 <- aux_3;
    cf <- aux_2;
     _0 <- aux_1;
     _1 <- aux_0;
     _2 <- aux;
    _zero <- aux_5;
    leakages <- LeakAddr([0]) :: leakages;
    (aux_5, aux_4) <- MULX_64 a b.[0];
    leakages <- LeakAddr([1]) :: leakages;
    r.[1] <- aux_5;
    leakages <- LeakAddr([0]) :: leakages;
    r.[0] <- aux_4;
    leakages <- LeakFor(1,4) :: LeakAddr([]) :: leakages;
    i <- 1;
    while (i < 4) {
      leakages <- LeakAddr([i]) :: leakages;
      (aux_5, aux_4) <- MULX_64 a b.[i];
      leakages <- LeakAddr([(i + 1)]) :: leakages;
      r.[(i + 1)] <- aux_5;
      lo <- aux_4;
      leakages <- LeakAddr([i]) :: leakages;
      (aux_3, aux_5) <- ADCX_64 r.[i] lo cf;
      cf <- aux_3;
      leakages <- LeakAddr([i]) :: leakages;
      r.[i] <- aux_5;
      i <- i + 1;
    }
    leakages <- LeakAddr([4]) :: leakages;
    (aux_3, aux_5) <- ADCX_64 r.[4] _zero cf;
    cf <- aux_3;
    leakages <- LeakAddr([4]) :: leakages;
    r.[4] <- aux_5;
    return (_zero, of_0, cf, r);
  }
  
  proc mul1acc (k:int, a:W64.t, b:W64.t Array4.t, r:W64.t Array8.t,
                _zero:W64.t, of_0:bool, cf:bool) : W64.t * bool * bool *
                                                   W64.t Array8.t = {
    var aux_2: bool;
    var aux: int;
    var aux_1: W64.t;
    var aux_0: W64.t;
    
    var i:int;
    var hi:W64.t;
    var lo:W64.t;
    
    leakages <- LeakFor(0,(4 - 1)) :: LeakAddr([]) :: leakages;
    aux <- (4 - 1);
    i <- 0;
    while (i < aux) {
      leakages <- LeakAddr([i]) :: leakages;
      (aux_1, aux_0) <- MULX_64 a b.[i];
      hi <- aux_1;
      lo <- aux_0;
      leakages <- LeakAddr([(k + i)]) :: leakages;
      (aux_2, aux_1) <- ADOX_64 r.[(k + i)] lo of_0;
      of_0 <- aux_2;
      leakages <- LeakAddr([(k + i)]) :: leakages;
      r.[(k + i)] <- aux_1;
      leakages <- LeakAddr([((k + i) + 1)]) :: leakages;
      (aux_2, aux_1) <- ADCX_64 r.[((k + i) + 1)] hi cf;
      cf <- aux_2;
      leakages <- LeakAddr([((k + i) + 1)]) :: leakages;
      r.[((k + i) + 1)] <- aux_1;
      i <- i + 1;
    }
    leakages <- LeakAddr([(4 - 1)]) :: leakages;
    (aux_1, aux_0) <- MULX_64 a b.[(4 - 1)];
    leakages <- LeakAddr([(4 + k)]) :: leakages;
    r.[(4 + k)] <- aux_1;
    lo <- aux_0;
    leakages <- LeakAddr([((4 + k) - 1)]) :: leakages;
    (aux_2, aux_1) <- ADOX_64 r.[((4 + k) - 1)] lo of_0;
    of_0 <- aux_2;
    leakages <- LeakAddr([((4 + k) - 1)]) :: leakages;
    r.[((4 + k) - 1)] <- aux_1;
    leakages <- LeakAddr([(4 + k)]) :: leakages;
    (aux_2, aux_1) <- ADCX_64 r.[(4 + k)] _zero cf;
    cf <- aux_2;
    leakages <- LeakAddr([(4 + k)]) :: leakages;
    r.[(4 + k)] <- aux_1;
    leakages <- LeakAddr([(4 + k)]) :: leakages;
    (aux_2, aux_1) <- ADOX_64 r.[(4 + k)] _zero of_0;
    of_0 <- aux_2;
    leakages <- LeakAddr([(4 + k)]) :: leakages;
    r.[(4 + k)] <- aux_1;
    return (_zero, of_0, cf, r);
  }
  
  proc bn_muln (a:W64.t Array4.t, b:W64.t Array4.t) : W64.t * bool * bool *
                                                      W64.t Array8.t = {
    var aux_1: bool;
    var aux_0: bool;
    var aux_3: int;
    var aux: W64.t;
    var aux_2: W64.t Array8.t;
    
    var _zero:W64.t;
    var of_0:bool;
    var cf:bool;
    var r:W64.t Array8.t;
    var ai:W64.t;
    var i:int;
    r <- witness;
    leakages <- LeakAddr([0]) :: leakages;
    aux <- a.[0];
    ai <- aux;
    leakages <- LeakAddr([]) :: leakages;
    (aux, aux_1, aux_0, aux_2) <@ mul1 (ai, b);
    _zero <- aux;
    of_0 <- aux_1;
    cf <- aux_0;
    r <- aux_2;
    leakages <- LeakFor(1,4) :: LeakAddr([]) :: leakages;
    i <- 1;
    while (i < 4) {
      leakages <- LeakAddr([i]) :: leakages;
      aux <- a.[i];
      ai <- aux;
      leakages <- LeakAddr([]) :: leakages;
      (aux, aux_1, aux_0, aux_2) <@ mul1acc (i, ai, b, r, _zero, of_0, cf);
      _zero <- aux;
      of_0 <- aux_1;
      cf <- aux_0;
      r <- aux_2;
      i <- i + 1;
    }
    return (_zero, of_0, cf, r);
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
    var c1:W64.t;
    var c2:W64.t;
    var r:W64.t;
    
    leakages <- LeakAddr([]) :: leakages;
    aux <- (ctr `>>` (W8.of_int 6));
    c1 <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux <- (ctr - (c1 * (W64.of_int 64)));
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
  
  proc maskOnCarry (mask:int, r:W64.t, _cf:bool) : W64.t = {
    var aux: bool;
    var aux_0: W64.t;
    
    
    
    leakages <- LeakAddr([]) :: leakages;
    (aux, aux_0) <- sbb_64 r r _cf;
    _cf <- aux;
    r <- aux_0;
    leakages <- LeakAddr([]) :: leakages;
    aux_0 <- (r `&` (W64.of_int mask));
    r <- aux_0;
    return (r);
  }
  
  proc x2r (x0:W64.t, x1:W64.t, x2:W64.t, x3:W64.t) : W64.t Array4.t = {
    var aux: W64.t;
    
    var r:W64.t Array4.t;
    r <- witness;
    leakages <- LeakAddr([]) :: leakages;
    aux <- x0;
    leakages <- LeakAddr([0]) :: leakages;
    r.[0] <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux <- x1;
    leakages <- LeakAddr([1]) :: leakages;
    r.[1] <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux <- x2;
    leakages <- LeakAddr([2]) :: leakages;
    r.[2] <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux <- x3;
    leakages <- LeakAddr([3]) :: leakages;
    r.[3] <- aux;
    return (r);
  }
  
  proc r2x (x:W64.t Array4.t) : W64.t * W64.t * W64.t * W64.t = {
    var aux: W64.t;
    
    var r0:W64.t;
    var r1:W64.t;
    var r2:W64.t;
    var r3:W64.t;
    
    leakages <- LeakAddr([0]) :: leakages;
    aux <- x.[0];
    r0 <- aux;
    leakages <- LeakAddr([1]) :: leakages;
    aux <- x.[1];
    r1 <- aux;
    leakages <- LeakAddr([2]) :: leakages;
    aux <- x.[2];
    r2 <- aux;
    leakages <- LeakAddr([3]) :: leakages;
    aux <- x.[3];
    r3 <- aux;
    return (r0, r1, r2, r3);
  }
  
  proc cminusP (x:W64.t Array4.t) : W64.t Array4.t = {
    var aux_2: bool;
    var aux_1: W64.t;
    var aux: W8.t Array32.t;
    var aux_0: W64.t Array4.t;
    
    var t:W64.t Array4.t;
    var twop63:W64.t;
    var cf:bool;
    t <- witness;
    leakages <- LeakAddr([]) :: leakages;
    aux_0 <- copy_64 x;
    t <- aux_0;
    leakages <- LeakAddr([]) :: leakages;
    aux_1 <- (W64.of_int 1);
    twop63 <- aux_1;
    leakages <- LeakAddr([]) :: leakages;
    aux_1 <- (twop63 `<<` (W8.of_int 63));
    twop63 <- aux_1;
    leakages <- LeakAddr([0]) :: leakages;
    (aux_2, aux_1) <- adc_64 t.[0] (W64.of_int 19) false;
    cf <- aux_2;
    leakages <- LeakAddr([0]) :: leakages;
    t.[0] <- aux_1;
    leakages <- LeakAddr([1]) :: leakages;
    (aux_2, aux_1) <- adc_64 t.[1] (W64.of_int 0) cf;
    cf <- aux_2;
    leakages <- LeakAddr([1]) :: leakages;
    t.[1] <- aux_1;
    leakages <- LeakAddr([2]) :: leakages;
    (aux_2, aux_1) <- adc_64 t.[2] (W64.of_int 0) cf;
    cf <- aux_2;
    leakages <- LeakAddr([2]) :: leakages;
    t.[2] <- aux_1;
    leakages <- LeakAddr([3]) :: leakages;
    (aux_2, aux_1) <- adc_64 t.[3] twop63 cf;
    cf <- aux_2;
    leakages <- LeakAddr([3]) :: leakages;
    t.[3] <- aux_1;
    leakages <- LeakAddr([0; 0]) :: leakages;
    aux_1 <- (cf ? t.[0] : x.[0]);
    leakages <- LeakAddr([0]) :: leakages;
    x.[0] <- aux_1;
    leakages <- LeakAddr([1; 1]) :: leakages;
    aux_1 <- (cf ? t.[1] : x.[1]);
    leakages <- LeakAddr([1]) :: leakages;
    x.[1] <- aux_1;
    leakages <- LeakAddr([2; 2]) :: leakages;
    aux_1 <- (cf ? t.[2] : x.[2]);
    leakages <- LeakAddr([2]) :: leakages;
    x.[2] <- aux_1;
    leakages <- LeakAddr([3; 3]) :: leakages;
    aux_1 <- (cf ? t.[3] : x.[3]);
    leakages <- LeakAddr([3]) :: leakages;
    x.[3] <- aux_1;
    return (x);
  }
  
  proc caddP (cf:bool, x:W64.t Array4.t) : W64.t Array4.t = {
    var aux_0: bool;
    var aux: W64.t;
    var aux_1: W64.t Array4.t;
    
    var p:W64.t Array4.t;
    var _zero:W64.t;
    var  _0:bool;
    p <- witness;
    leakages <- LeakAddr([]) :: leakages;
    aux <- (W64.of_int 18446744073709551597);
    leakages <- LeakAddr([0]) :: leakages;
    p.[0] <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux <- (W64.of_int 18446744073709551615);
    leakages <- LeakAddr([1]) :: leakages;
    p.[1] <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux <- (W64.of_int 18446744073709551615);
    leakages <- LeakAddr([2]) :: leakages;
    p.[2] <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux <- (W64.of_int 9223372036854775807);
    leakages <- LeakAddr([3]) :: leakages;
    p.[3] <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux <- (W64.of_int 0);
    _zero <- aux;
    leakages <- LeakAddr([0]) :: leakages;
    aux <- ((! cf) ? _zero : p.[0]);
    leakages <- LeakAddr([0]) :: leakages;
    p.[0] <- aux;
    leakages <- LeakAddr([1]) :: leakages;
    aux <- ((! cf) ? _zero : p.[1]);
    leakages <- LeakAddr([1]) :: leakages;
    p.[1] <- aux;
    leakages <- LeakAddr([2]) :: leakages;
    aux <- ((! cf) ? _zero : p.[2]);
    leakages <- LeakAddr([2]) :: leakages;
    p.[2] <- aux;
    leakages <- LeakAddr([3]) :: leakages;
    aux <- ((! cf) ? _zero : p.[3]);
    leakages <- LeakAddr([3]) :: leakages;
    p.[3] <- aux;
    leakages <- LeakAddr([]) :: leakages;
    (aux_0, aux_1) <@ bn_addc (x, p);
     _0 <- aux_0;
    x <- aux_1;
    return (x);
  }
  
  proc redp25519 (_of:bool, _cf:bool, a:W64.t Array8.t) : W64.t Array4.t = {
    var aux_7: bool;
    var aux_6: bool;
    var aux_5: bool;
    var aux_3: bool;
    var aux_2: bool;
    var aux: W64.t;
    var aux_1: W64.t Array4.t;
    var aux_0: W64.t Array4.t;
    var aux_4: W64.t Array8.t;
    
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
    leakages <- LeakAddr([]) :: leakages;
    aux <- (W64.of_int 38);
    tmp <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux <- (W64.of_int 0);
    _zero <- aux;
    leakages <- LeakAddr([]) :: leakages;
    (aux_1, aux_0) <@ bn2_unpack (a);
    ah <- aux_1;
     _0 <- aux_0;
    leakages <- LeakAddr([]) :: leakages;
    (aux, aux_7, aux_6, aux_4) <@ mul1acc (0, tmp, ah, a, _zero, _of, _cf);
    _zero <- aux;
    _of <- aux_7;
    _cf <- aux_6;
    a <- aux_4;
    leakages <- LeakAddr([4]) :: leakages;
    (aux_7, aux_6, aux_5, aux_3, aux_2, aux) <- IMULri_64 a.[4]
    (W64.of_int 38);
     _1 <- aux_7;
     _2 <- aux_6;
     _3 <- aux_5;
     _4 <- aux_3;
     _5 <- aux_2;
    tmp <- aux;
    leakages <- LeakAddr([]) :: leakages;
    (aux_1, aux_0) <@ bn2_unpack (a);
     _6 <- aux_1;
    al <- aux_0;
    leakages <- LeakAddr([]) :: leakages;
    (aux_7, aux_1) <@ bn_add1 (al, tmp);
    _cf <- aux_7;
    al <- aux_1;
    leakages <- LeakAddr([]) :: leakages;
    aux <@ maskOnCarry (38, tmp, _cf);
    tmp <- aux;
    leakages <- LeakAddr([0]) :: leakages;
    aux <- (al.[0] + tmp);
    leakages <- LeakAddr([0]) :: leakages;
    al.[0] <- aux;
    return (al);
  }
  
  proc freeze (x:W64.t Array4.t) : W64.t Array4.t = {
    var aux: W64.t Array4.t;
    
    
    
    leakages <- LeakAddr([]) :: leakages;
    aux <@ cminusP (x);
    x <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux <@ cminusP (x);
    x <- aux;
    return (x);
  }
  
  proc _mulm (f:W64.t Array4.t, g0:W64.t, g1:W64.t, g2:W64.t, g3:W64.t) : 
  W64.t * W64.t * W64.t * W64.t = {
    var aux_2: bool;
    var aux_1: bool;
    var aux_6: W64.t;
    var aux_5: W64.t;
    var aux_4: W64.t;
    var aux_0: W64.t;
    var aux: W64.t Array4.t;
    var aux_3: W64.t Array8.t;
    
    var g:W64.t Array4.t;
    var _zero:W64.t;
    var of_0:bool;
    var cf:bool;
    var h:W64.t Array8.t;
    g <- witness;
    h <- witness;
    leakages <- LeakAddr([]) :: leakages;
    aux <@ x2r (g0, g1, g2, g3);
    g <- aux;
    leakages <- LeakAddr([]) :: leakages;
    (aux_6, aux_2, aux_1, aux_3) <@ bn_muln (f, g);
    _zero <- aux_6;
    of_0 <- aux_2;
    cf <- aux_1;
    h <- aux_3;
    leakages <- LeakAddr([]) :: leakages;
    aux <@ redp25519 (of_0, cf, h);
    g <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux <@ freeze (g);
    g <- aux;
    leakages <- LeakAddr([]) :: leakages;
    (aux_6, aux_5, aux_4, aux_0) <@ r2x (g);
    g0 <- aux_6;
    g1 <- aux_5;
    g2 <- aux_4;
    g3 <- aux_0;
    return (g0, g1, g2, g3);
  }
  
  proc mulm (p:W64.t Array4.t, a:W64.t Array4.t, b:W64.t Array4.t) : 
  W64.t Array4.t = {
    var aux_2: W64.t;
    var aux_1: W64.t;
    var aux_0: W64.t;
    var aux: W64.t;
    var aux_3: W64.t Array4.t;
    
    var g0:W64.t;
    var g1:W64.t;
    var g2:W64.t;
    var g3:W64.t;
    
    leakages <- LeakAddr([]) :: leakages;
    (aux_2, aux_1, aux_0, aux) <@ r2x (b);
    g0 <- aux_2;
    g1 <- aux_1;
    g2 <- aux_0;
    g3 <- aux;
    leakages <- LeakAddr([]) :: leakages;
    (aux_2, aux_1, aux_0, aux) <@ _mulm (a, g0, g1, g2, g3);
    g0 <- aux_2;
    g1 <- aux_1;
    g2 <- aux_0;
    g3 <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux_3 <@ x2r (g0, g1, g2, g3);
    b <- aux_3;
    return (b);
  }
  
  proc _addm (f0:W64.t, f1:W64.t, f2:W64.t, f3:W64.t, g0:W64.t, g1:W64.t,
              g2:W64.t, g3:W64.t) : W64.t * W64.t * W64.t * W64.t = {
    var aux_0: bool;
    var aux_4: W64.t;
    var aux_3: W64.t;
    var aux_2: W64.t;
    var aux_1: W64.t;
    var aux: W64.t Array4.t;
    
    var f:W64.t Array4.t;
    var g:W64.t Array4.t;
    var  _0:bool;
    f <- witness;
    g <- witness;
    leakages <- LeakAddr([]) :: leakages;
    aux <@ x2r (f0, f1, f2, f3);
    f <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux <@ x2r (g0, g1, g2, g3);
    g <- aux;
    leakages <- LeakAddr([]) :: leakages;
    (aux_0, aux) <@ bn_addc (f, g);
     _0 <- aux_0;
    f <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux <@ cminusP (f);
    f <- aux;
    leakages <- LeakAddr([]) :: leakages;
    (aux_4, aux_3, aux_2, aux_1) <@ r2x (f);
    f0 <- aux_4;
    f1 <- aux_3;
    f2 <- aux_2;
    f3 <- aux_1;
    return (f0, f1, f2, f3);
  }
  
  proc addm (a:W64.t Array4.t, b:W64.t Array4.t) : W64.t Array4.t = {
    var aux_2: W64.t;
    var aux_1: W64.t;
    var aux_0: W64.t;
    var aux: W64.t;
    var aux_3: W64.t Array4.t;
    
    var f0:W64.t;
    var f1:W64.t;
    var f2:W64.t;
    var f3:W64.t;
    var g0:W64.t;
    var g1:W64.t;
    var g2:W64.t;
    var g3:W64.t;
    
    leakages <- LeakAddr([]) :: leakages;
    (aux_2, aux_1, aux_0, aux) <@ r2x (a);
    f0 <- aux_2;
    f1 <- aux_1;
    f2 <- aux_0;
    f3 <- aux;
    leakages <- LeakAddr([]) :: leakages;
    (aux_2, aux_1, aux_0, aux) <@ r2x (b);
    g0 <- aux_2;
    g1 <- aux_1;
    g2 <- aux_0;
    g3 <- aux;
    leakages <- LeakAddr([]) :: leakages;
    (aux_2, aux_1, aux_0, aux) <@ _addm (f0, f1, f2, f3, g0, g1, g2, g3);
    f0 <- aux_2;
    f1 <- aux_1;
    f2 <- aux_0;
    f3 <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux_3 <@ x2r (f0, f1, f2, f3);
    a <- aux_3;
    return (a);
  }
  
  proc _subm (f0:W64.t, f1:W64.t, f2:W64.t, f3:W64.t, g0:W64.t, g1:W64.t,
              g2:W64.t, g3:W64.t) : W64.t * W64.t * W64.t * W64.t = {
    var aux_0: bool;
    var aux_4: W64.t;
    var aux_3: W64.t;
    var aux_2: W64.t;
    var aux_1: W64.t;
    var aux: W64.t Array4.t;
    
    var f:W64.t Array4.t;
    var g:W64.t Array4.t;
    var cf:bool;
    f <- witness;
    g <- witness;
    leakages <- LeakAddr([]) :: leakages;
    aux <@ x2r (f0, f1, f2, f3);
    f <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux <@ x2r (g0, g1, g2, g3);
    g <- aux;
    leakages <- LeakAddr([]) :: leakages;
    (aux_0, aux) <@ bn_subc (f, g);
    cf <- aux_0;
    f <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux <@ caddP (cf, f);
    f <- aux;
    leakages <- LeakAddr([]) :: leakages;
    (aux_4, aux_3, aux_2, aux_1) <@ r2x (f);
    f0 <- aux_4;
    f1 <- aux_3;
    f2 <- aux_2;
    f3 <- aux_1;
    return (f0, f1, f2, f3);
  }
  
  proc subm (a:W64.t Array4.t, b:W64.t Array4.t) : W64.t Array4.t = {
    var aux_2: W64.t;
    var aux_1: W64.t;
    var aux_0: W64.t;
    var aux: W64.t;
    var aux_3: W64.t Array4.t;
    
    var f0:W64.t;
    var f1:W64.t;
    var f2:W64.t;
    var f3:W64.t;
    var g0:W64.t;
    var g1:W64.t;
    var g2:W64.t;
    var g3:W64.t;
    
    leakages <- LeakAddr([]) :: leakages;
    (aux_2, aux_1, aux_0, aux) <@ r2x (a);
    f0 <- aux_2;
    f1 <- aux_1;
    f2 <- aux_0;
    f3 <- aux;
    leakages <- LeakAddr([]) :: leakages;
    (aux_2, aux_1, aux_0, aux) <@ r2x (b);
    g0 <- aux_2;
    g1 <- aux_1;
    g2 <- aux_0;
    g3 <- aux;
    leakages <- LeakAddr([]) :: leakages;
    (aux_2, aux_1, aux_0, aux) <@ _subm (f0, f1, f2, f3, g0, g1, g2, g3);
    f0 <- aux_2;
    f1 <- aux_1;
    f2 <- aux_0;
    f3 <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux_3 <@ x2r (f0, f1, f2, f3);
    a <- aux_3;
    return (a);
  }
  
  proc expm (m:W64.t Array4.t, x:W64.t Array4.t, n:W64.t Array4.t) : 
  W64.t Array4.t = {
    var aux: W64.t;
    var aux_0: W8.t Array32.t;
    var aux_2: W64.t Array4.t;
    var aux_1: W64.t Array4.t;
    
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
    aux <- (W64.of_int 1);
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
    aux <- (W64.of_int 1);
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
    leakages <- LeakAddr([]) :: leakages;
    aux_2 <- copy_64 x;
    x3 <- aux_2;
    leakages <- LeakAddr([]) :: leakages;
    aux_2 <@ mulm (m, x, x);
    x4 <- aux_2;
    leakages <- LeakAddr([]) :: leakages;
    aux <- d;
    p <- aux;
    leakages <- LeakAddr([]) :: leakages;
    (aux_2, aux_1) <@ swapr (x1, x3, d);
    x1 <- aux_2;
    x3 <- aux_1;
    leakages <- LeakAddr([]) :: leakages;
    (aux_2, aux_1) <@ swapr (x2, x4, d);
    x2 <- aux_2;
    x4 <- aux_1;
    
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
      (aux_2, aux_1) <@ swapr (x1, x2, par);
      x1 <- aux_2;
      x2 <- aux_1;
      leakages <- LeakAddr([]) :: leakages;
      aux_2 <@ mulm (m, x1, x2);
      x1 <- aux_2;
      leakages <- LeakAddr([]) :: leakages;
      aux_2 <@ mulm (m, x2, x2);
      x2 <- aux_2;
      leakages <- LeakAddr([]) :: leakages;
      aux <- (q `|` t2);
      q <- aux;
      leakages <- LeakAddr([]) :: leakages;
      aux <- (q `^` p);
      cbit <- aux;
      leakages <- LeakAddr([]) :: leakages;
      (aux_2, aux_1) <@ swapr (x1, x3, cbit);
      x1 <- aux_2;
      x3 <- aux_1;
      leakages <- LeakAddr([]) :: leakages;
      (aux_2, aux_1) <@ swapr (x2, x4, cbit);
      x2 <- aux_2;
      x4 <- aux_1;
    leakages <- LeakCond(((W64.of_int 0) \ult ctr)) :: LeakAddr([]) :: leakages;
    
    }
    leakages <- LeakAddr([]) :: leakages;
    aux <@ ith_bit (n, (W64.of_int 0));
    par <- aux;
    leakages <- LeakAddr([]) :: leakages;
    (aux_2, aux_1) <@ swapr (x2, x1, par);
    x1 <- aux_2;
    x2 <- aux_1;
    return (x1);
  }
  
  proc toEC () : unit = {
    var aux_2: bool;
    var aux_0: W64.t;
    var aux_1: W64.t Array4.t;
    var aux: W64.t Array4.t;
    
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
    leakages <- LeakAddr([]) :: leakages;
    aux_1 <@ addm (a, b);
    r <- aux_1;
    leakages <- LeakAddr([]) :: leakages;
    aux_1 <@ subm (a, b);
    r <- aux_1;
    leakages <- LeakAddr([]) :: leakages;
    aux_1 <@ mulm (a, a, b);
    r <- aux_1;
    leakages <- LeakAddr([]) :: leakages;
    aux_1 <@ expm (a, a, b);
    r <- aux_1;
    leakages <- LeakAddr([]) :: leakages;
    aux_0 <@ ith_bit (a, x);
    x <- aux_0;
    leakages <- LeakAddr([]) :: leakages;
    (aux_1, aux) <@ swapr (a, a, x);
     _0 <- aux_1;
    a <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux_0 <@ bn_eq (a, b);
    x <- aux_0;
    leakages <- LeakAddr([]) :: leakages;
    aux_0 <@ bn_test0 (a);
    x <- aux_0;
    leakages <- LeakAddr([]) :: leakages;
    aux_2 <- false;
    _cf <- aux_2;
    leakages <- LeakAddr([]) :: leakages;
    aux_0 <@ maskOnCarry (7, x, _cf);
    x <- aux_0;
    return ();
  }
}.


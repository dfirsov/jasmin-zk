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
    (aux_0, aux) <- subc_64 x1 x2 false;
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
  
  proc dbn_subc (a:W64.t Array64.t, b:W64.t Array64.t) : bool *
                                                         W64.t Array64.t = {
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
    leakages <- LeakFor(1,64) :: LeakAddr([]) :: leakages;
    i <- 1;
    while (i < 64) {
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
  
  proc dbn_copy (a:W64.t Array64.t) : W64.t Array64.t = {
    var aux: int;
    var aux_0: W64.t;
    
    var r:W64.t Array64.t;
    var i:int;
    var t:W64.t;
    r <- witness;
    leakages <- LeakFor(0,64) :: LeakAddr([]) :: leakages;
    i <- 0;
    while (i < 64) {
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
  
  proc dbn_cmov (cond:bool, a:W64.t Array64.t, b:W64.t Array64.t) : W64.t Array64.t = {
    var aux: int;
    var aux_0: W64.t;
    
    var i:int;
    var r1:W64.t;
    var r2:W64.t;
    
    leakages <- LeakFor(0,64) :: LeakAddr([]) :: leakages;
    i <- 0;
    while (i < 64) {
      leakages <- LeakAddr([i]) :: leakages;
      aux_0 <- a.[i];
      r1 <- aux_0;
      leakages <- LeakAddr([i]) :: leakages;
      aux_0 <- b.[i];
      r2 <- aux_0;
      leakages <- LeakAddr([]) :: leakages;
      aux_0 <- (cond ? r2 : r1);
      r1 <- aux_0;
      leakages <- LeakAddr([]) :: leakages;
      aux_0 <- r1;
      leakages <- LeakAddr([i]) :: leakages;
      a.[i] <- aux_0;
      i <- i + 1;
    }
    return (a);
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
  
  proc bn_set1 (a:W64.t Array32.t) : W64.t Array32.t = {
    var aux_0: int;
    var aux: W64.t;
    
    var i:int;
    
    leakages <- LeakAddr([]) :: leakages;
    aux <- (W64.of_int 1);
    leakages <- LeakAddr([0]) :: leakages;
    a.[0] <- aux;
    leakages <- LeakFor(1,32) :: LeakAddr([]) :: leakages;
    i <- 1;
    while (i < 32) {
      leakages <- LeakAddr([]) :: leakages;
      aux <- (W64.of_int 0);
      leakages <- LeakAddr([i]) :: leakages;
      a.[i] <- aux;
      i <- i + 1;
    }
    return (a);
  }
  
  proc mul1 (a:W64.t, b:W64.t Array32.t) : W64.t * bool * bool *
                                           W64.t Array64.t = {
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
    var r:W64.t Array64.t;
    var x1:W64.t;
    var x2:W64.t;
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
    leakages <- LeakAddr([]) :: leakages;
    aux_5 <- a;
    x1 <- aux_5;
    leakages <- LeakAddr([0]) :: leakages;
    aux_5 <- b.[0];
    x2 <- aux_5;
    leakages <- LeakAddr([]) :: leakages;
    (aux_5, aux_4) <- MULX_64 x1 x2;
    x1 <- aux_5;
    x2 <- aux_4;
    leakages <- LeakAddr([]) :: leakages;
    aux_5 <- x1;
    leakages <- LeakAddr([1]) :: leakages;
    r.[1] <- aux_5;
    leakages <- LeakAddr([]) :: leakages;
    aux_5 <- x2;
    leakages <- LeakAddr([0]) :: leakages;
    r.[0] <- aux_5;
    leakages <- LeakFor(1,32) :: LeakAddr([]) :: leakages;
    i <- 1;
    while (i < 32) {
      leakages <- LeakAddr([]) :: leakages;
      aux_5 <- a;
      x1 <- aux_5;
      leakages <- LeakAddr([i]) :: leakages;
      aux_5 <- b.[i];
      x2 <- aux_5;
      leakages <- LeakAddr([]) :: leakages;
      (aux_5, aux_4) <- MULX_64 x1 x2;
      x1 <- aux_5;
      x2 <- aux_4;
      leakages <- LeakAddr([]) :: leakages;
      aux_5 <- x1;
      leakages <- LeakAddr([(i + 1)]) :: leakages;
      r.[(i + 1)] <- aux_5;
      leakages <- LeakAddr([]) :: leakages;
      aux_5 <- x2;
      lo <- aux_5;
      leakages <- LeakAddr([i]) :: leakages;
      aux_5 <- r.[i];
      x1 <- aux_5;
      leakages <- LeakAddr([]) :: leakages;
      aux_5 <- lo;
      x2 <- aux_5;
      leakages <- LeakAddr([]) :: leakages;
      (aux_3, aux_5) <- ADCX_64 x1 x2 cf;
      cf <- aux_3;
      x1 <- aux_5;
      leakages <- LeakAddr([]) :: leakages;
      aux_5 <- x1;
      leakages <- LeakAddr([i]) :: leakages;
      r.[i] <- aux_5;
      i <- i + 1;
    }
    leakages <- LeakAddr([32]) :: leakages;
    aux_5 <- r.[32];
    x1 <- aux_5;
    leakages <- LeakAddr([]) :: leakages;
    (aux_3, aux_5) <- ADCX_64 x1 _zero cf;
    cf <- aux_3;
    x1 <- aux_5;
    leakages <- LeakAddr([]) :: leakages;
    aux_5 <- x1;
    leakages <- LeakAddr([32]) :: leakages;
    r.[32] <- aux_5;
    return (_zero, of_0, cf, r);
  }
  
  proc mul1acc (k:W64.t, a:W64.t, b:W64.t Array32.t, r:W64.t Array64.t,
                _zero:W64.t, of_0:bool, cf:bool) : W64.t * bool * bool *
                                                   W64.t Array64.t = {
    var aux_2: bool;
    var aux: int;
    var aux_1: W64.t;
    var aux_0: W64.t;
    
    var kk:int;
    var x1:W64.t;
    var i:int;
    var x2:W64.t;
    var hi:W64.t;
    var lo:W64.t;
    
    leakages <- LeakAddr([]) :: leakages;
    aux <- (W64.to_uint k);
    kk <- aux;
    leakages <- LeakFor(0,(32 - 1)) :: LeakAddr([]) :: leakages;
    aux <- (32 - 1);
    i <- 0;
    while (i < aux) {
      leakages <- LeakAddr([]) :: leakages;
      aux_1 <- a;
      x1 <- aux_1;
      leakages <- LeakAddr([i]) :: leakages;
      aux_1 <- b.[i];
      x2 <- aux_1;
      leakages <- LeakAddr([]) :: leakages;
      (aux_1, aux_0) <- MULX_64 x1 x2;
      x1 <- aux_1;
      x2 <- aux_0;
      leakages <- LeakAddr([]) :: leakages;
      aux_1 <- x1;
      hi <- aux_1;
      leakages <- LeakAddr([]) :: leakages;
      aux_1 <- x2;
      lo <- aux_1;
      leakages <- LeakAddr([(kk + i)]) :: leakages;
      aux_1 <- r.[(kk + i)];
      x1 <- aux_1;
      leakages <- LeakAddr([]) :: leakages;
      (aux_2, aux_1) <- ADOX_64 x1 lo of_0;
      of_0 <- aux_2;
      x1 <- aux_1;
      leakages <- LeakAddr([]) :: leakages;
      aux_1 <- x1;
      leakages <- LeakAddr([(kk + i)]) :: leakages;
      r.[(kk + i)] <- aux_1;
      leakages <- LeakAddr([((kk + i) + 1)]) :: leakages;
      aux_1 <- r.[((kk + i) + 1)];
      x1 <- aux_1;
      leakages <- LeakAddr([]) :: leakages;
      (aux_2, aux_1) <- ADCX_64 x1 hi cf;
      cf <- aux_2;
      x1 <- aux_1;
      leakages <- LeakAddr([]) :: leakages;
      aux_1 <- x1;
      leakages <- LeakAddr([((kk + i) + 1)]) :: leakages;
      r.[((kk + i) + 1)] <- aux_1;
      i <- i + 1;
    }
    leakages <- LeakAddr([]) :: leakages;
    aux_1 <- a;
    x1 <- aux_1;
    leakages <- LeakAddr([(32 - 1)]) :: leakages;
    aux_1 <- b.[(32 - 1)];
    x2 <- aux_1;
    leakages <- LeakAddr([]) :: leakages;
    (aux_1, aux_0) <- MULX_64 x1 x2;
    x1 <- aux_1;
    x2 <- aux_0;
    leakages <- LeakAddr([]) :: leakages;
    aux_1 <- x1;
    leakages <- LeakAddr([(32 + kk)]) :: leakages;
    r.[(32 + kk)] <- aux_1;
    leakages <- LeakAddr([]) :: leakages;
    aux_1 <- x2;
    lo <- aux_1;
    leakages <- LeakAddr([((32 + kk) - 1)]) :: leakages;
    aux_1 <- r.[((32 + kk) - 1)];
    x1 <- aux_1;
    leakages <- LeakAddr([]) :: leakages;
    (aux_2, aux_1) <- ADOX_64 x1 lo of_0;
    of_0 <- aux_2;
    x1 <- aux_1;
    leakages <- LeakAddr([]) :: leakages;
    aux_1 <- x1;
    leakages <- LeakAddr([((32 + kk) - 1)]) :: leakages;
    r.[((32 + kk) - 1)] <- aux_1;
    leakages <- LeakAddr([(32 + kk)]) :: leakages;
    aux_1 <- r.[(32 + kk)];
    x1 <- aux_1;
    leakages <- LeakAddr([]) :: leakages;
    (aux_2, aux_1) <- ADCX_64 x1 _zero cf;
    cf <- aux_2;
    x1 <- aux_1;
    leakages <- LeakAddr([]) :: leakages;
    aux_1 <- x1;
    leakages <- LeakAddr([(32 + kk)]) :: leakages;
    r.[(32 + kk)] <- aux_1;
    leakages <- LeakAddr([(32 + kk)]) :: leakages;
    aux_1 <- r.[(32 + kk)];
    x1 <- aux_1;
    leakages <- LeakAddr([]) :: leakages;
    (aux_2, aux_1) <- ADOX_64 x1 _zero of_0;
    of_0 <- aux_2;
    x1 <- aux_1;
    leakages <- LeakAddr([]) :: leakages;
    aux_1 <- x1;
    leakages <- LeakAddr([(32 + kk)]) :: leakages;
    r.[(32 + kk)] <- aux_1;
    return (_zero, of_0, cf, r);
  }
  
  proc bn_muln (a:W64.t Array32.t, b:W64.t Array32.t) : W64.t * bool * bool *
                                                        W64.t Array64.t = {
    var aux_1: bool;
    var aux_0: bool;
    var aux_3: int;
    var aux: W64.t;
    var aux_2: W64.t Array64.t;
    
    var _zero:W64.t;
    var of_0:bool;
    var cf:bool;
    var r:W64.t Array64.t;
    var ai:W64.t;
    var i:int;
    var z:W64.t;
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
    leakages <- LeakFor(1,32) :: LeakAddr([]) :: leakages;
    i <- 1;
    while (i < 32) {
      leakages <- LeakAddr([i]) :: leakages;
      aux <- a.[i];
      ai <- aux;
      leakages <- LeakAddr([]) :: leakages;
      aux <- (W64.of_int i);
      z <- aux;
      leakages <- LeakAddr([]) :: leakages;
      (aux, aux_1, aux_0, aux_2) <@ mul1acc (z, ai, b, r, _zero, of_0, cf);
      _zero <- aux;
      of_0 <- aux_1;
      cf <- aux_0;
      r <- aux_2;
      i <- i + 1;
    }
    return (_zero, of_0, cf, r);
  }
  
  proc dmul1 (a:W64.t, b:W64.t Array64.t) : W64.t * bool * bool *
                                            W64.t Array128.t = {
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
    var r:W64.t Array128.t;
    var x1:W64.t;
    var x2:W64.t;
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
    leakages <- LeakAddr([]) :: leakages;
    aux_5 <- a;
    x1 <- aux_5;
    leakages <- LeakAddr([0]) :: leakages;
    aux_5 <- b.[0];
    x2 <- aux_5;
    leakages <- LeakAddr([]) :: leakages;
    (aux_5, aux_4) <- MULX_64 x1 x2;
    x1 <- aux_5;
    x2 <- aux_4;
    leakages <- LeakAddr([]) :: leakages;
    aux_5 <- x1;
    leakages <- LeakAddr([1]) :: leakages;
    r.[1] <- aux_5;
    leakages <- LeakAddr([]) :: leakages;
    aux_5 <- x2;
    leakages <- LeakAddr([0]) :: leakages;
    r.[0] <- aux_5;
    leakages <- LeakFor(1,64) :: LeakAddr([]) :: leakages;
    i <- 1;
    while (i < 64) {
      leakages <- LeakAddr([]) :: leakages;
      aux_5 <- a;
      x1 <- aux_5;
      leakages <- LeakAddr([i]) :: leakages;
      aux_5 <- b.[i];
      x2 <- aux_5;
      leakages <- LeakAddr([]) :: leakages;
      (aux_5, aux_4) <- MULX_64 x1 x2;
      x1 <- aux_5;
      x2 <- aux_4;
      leakages <- LeakAddr([]) :: leakages;
      aux_5 <- x1;
      leakages <- LeakAddr([(i + 1)]) :: leakages;
      r.[(i + 1)] <- aux_5;
      leakages <- LeakAddr([]) :: leakages;
      aux_5 <- x2;
      lo <- aux_5;
      leakages <- LeakAddr([i]) :: leakages;
      aux_5 <- r.[i];
      x1 <- aux_5;
      leakages <- LeakAddr([]) :: leakages;
      aux_5 <- lo;
      x2 <- aux_5;
      leakages <- LeakAddr([]) :: leakages;
      (aux_3, aux_5) <- ADCX_64 x1 x2 cf;
      cf <- aux_3;
      x1 <- aux_5;
      leakages <- LeakAddr([]) :: leakages;
      aux_5 <- x1;
      leakages <- LeakAddr([i]) :: leakages;
      r.[i] <- aux_5;
      i <- i + 1;
    }
    leakages <- LeakAddr([64]) :: leakages;
    aux_5 <- r.[64];
    x1 <- aux_5;
    leakages <- LeakAddr([]) :: leakages;
    (aux_3, aux_5) <- ADCX_64 x1 _zero cf;
    cf <- aux_3;
    x1 <- aux_5;
    leakages <- LeakAddr([]) :: leakages;
    aux_5 <- x1;
    leakages <- LeakAddr([64]) :: leakages;
    r.[64] <- aux_5;
    return (_zero, of_0, cf, r);
  }
  
  proc dmul1acc (k:W64.t, a:W64.t, b:W64.t Array64.t, r:W64.t Array128.t,
                 _zero:W64.t, of_0:bool, cf:bool) : W64.t * bool * bool *
                                                    W64.t Array128.t = {
    var aux_2: bool;
    var aux: int;
    var aux_1: W64.t;
    var aux_0: W64.t;
    
    var kk:int;
    var x1:W64.t;
    var i:int;
    var x2:W64.t;
    var hi:W64.t;
    var lo:W64.t;
    
    leakages <- LeakAddr([]) :: leakages;
    aux <- (W64.to_uint k);
    kk <- aux;
    leakages <- LeakFor(0,(64 - 1)) :: LeakAddr([]) :: leakages;
    aux <- (64 - 1);
    i <- 0;
    while (i < aux) {
      leakages <- LeakAddr([]) :: leakages;
      aux_1 <- a;
      x1 <- aux_1;
      leakages <- LeakAddr([i]) :: leakages;
      aux_1 <- b.[i];
      x2 <- aux_1;
      leakages <- LeakAddr([]) :: leakages;
      (aux_1, aux_0) <- MULX_64 x1 x2;
      x1 <- aux_1;
      x2 <- aux_0;
      leakages <- LeakAddr([]) :: leakages;
      aux_1 <- x1;
      hi <- aux_1;
      leakages <- LeakAddr([]) :: leakages;
      aux_1 <- x2;
      lo <- aux_1;
      leakages <- LeakAddr([(kk + i)]) :: leakages;
      aux_1 <- r.[(kk + i)];
      x1 <- aux_1;
      leakages <- LeakAddr([]) :: leakages;
      (aux_2, aux_1) <- ADOX_64 x1 lo of_0;
      of_0 <- aux_2;
      x1 <- aux_1;
      leakages <- LeakAddr([]) :: leakages;
      aux_1 <- x1;
      leakages <- LeakAddr([(kk + i)]) :: leakages;
      r.[(kk + i)] <- aux_1;
      leakages <- LeakAddr([((kk + i) + 1)]) :: leakages;
      aux_1 <- r.[((kk + i) + 1)];
      x1 <- aux_1;
      leakages <- LeakAddr([]) :: leakages;
      (aux_2, aux_1) <- ADCX_64 x1 hi cf;
      cf <- aux_2;
      x1 <- aux_1;
      leakages <- LeakAddr([]) :: leakages;
      aux_1 <- x1;
      leakages <- LeakAddr([((kk + i) + 1)]) :: leakages;
      r.[((kk + i) + 1)] <- aux_1;
      i <- i + 1;
    }
    leakages <- LeakAddr([]) :: leakages;
    aux_1 <- a;
    x1 <- aux_1;
    leakages <- LeakAddr([(64 - 1)]) :: leakages;
    aux_1 <- b.[(64 - 1)];
    x2 <- aux_1;
    leakages <- LeakAddr([]) :: leakages;
    (aux_1, aux_0) <- MULX_64 x1 x2;
    x1 <- aux_1;
    x2 <- aux_0;
    leakages <- LeakAddr([]) :: leakages;
    aux_1 <- x1;
    leakages <- LeakAddr([(64 + kk)]) :: leakages;
    r.[(64 + kk)] <- aux_1;
    leakages <- LeakAddr([]) :: leakages;
    aux_1 <- x2;
    lo <- aux_1;
    leakages <- LeakAddr([((64 + kk) - 1)]) :: leakages;
    aux_1 <- r.[((64 + kk) - 1)];
    x1 <- aux_1;
    leakages <- LeakAddr([]) :: leakages;
    (aux_2, aux_1) <- ADOX_64 x1 lo of_0;
    of_0 <- aux_2;
    x1 <- aux_1;
    leakages <- LeakAddr([]) :: leakages;
    aux_1 <- x1;
    leakages <- LeakAddr([((64 + kk) - 1)]) :: leakages;
    r.[((64 + kk) - 1)] <- aux_1;
    leakages <- LeakAddr([(64 + kk)]) :: leakages;
    aux_1 <- r.[(64 + kk)];
    x1 <- aux_1;
    leakages <- LeakAddr([]) :: leakages;
    (aux_2, aux_1) <- ADCX_64 x1 _zero cf;
    cf <- aux_2;
    x1 <- aux_1;
    leakages <- LeakAddr([]) :: leakages;
    aux_1 <- x1;
    leakages <- LeakAddr([(64 + kk)]) :: leakages;
    r.[(64 + kk)] <- aux_1;
    leakages <- LeakAddr([(64 + kk)]) :: leakages;
    aux_1 <- r.[(64 + kk)];
    x1 <- aux_1;
    leakages <- LeakAddr([]) :: leakages;
    (aux_2, aux_1) <- ADOX_64 x1 _zero of_0;
    of_0 <- aux_2;
    x1 <- aux_1;
    leakages <- LeakAddr([]) :: leakages;
    aux_1 <- x1;
    leakages <- LeakAddr([(64 + kk)]) :: leakages;
    r.[(64 + kk)] <- aux_1;
    return (_zero, of_0, cf, r);
  }
  
  proc dbn_muln (a:W64.t Array64.t, b:W64.t Array64.t) : W64.t * bool *
                                                         bool *
                                                         W64.t Array128.t = {
    var aux_1: bool;
    var aux_0: bool;
    var aux_3: int;
    var aux: W64.t;
    var aux_2: W64.t Array128.t;
    
    var _zero:W64.t;
    var of_0:bool;
    var cf:bool;
    var r:W64.t Array128.t;
    var ai:W64.t;
    var i:int;
    var z:W64.t;
    r <- witness;
    leakages <- LeakAddr([0]) :: leakages;
    aux <- a.[0];
    ai <- aux;
    leakages <- LeakAddr([]) :: leakages;
    (aux, aux_1, aux_0, aux_2) <@ dmul1 (ai, b);
    _zero <- aux;
    of_0 <- aux_1;
    cf <- aux_0;
    r <- aux_2;
    leakages <- LeakFor(1,64) :: LeakAddr([]) :: leakages;
    i <- 1;
    while (i < 64) {
      leakages <- LeakAddr([i]) :: leakages;
      aux <- a.[i];
      ai <- aux;
      leakages <- LeakAddr([]) :: leakages;
      aux <- (W64.of_int i);
      z <- aux;
      leakages <- LeakAddr([]) :: leakages;
      (aux, aux_1, aux_0, aux_2) <@ dmul1acc (z, ai, b, r, _zero, of_0, cf);
      _zero <- aux;
      of_0 <- aux_1;
      cf <- aux_0;
      r <- aux_2;
      i <- i + 1;
    }
    return (_zero, of_0, cf, r);
  }
  
  proc rsample (byte_z:W64.t Array32.t) : int * W64.t Array32.t = {
    var aux_2: bool;
    var aux_1: int;
    var aux_0: W64.t;
    var aux_3: W8.t Array256.t;
    var aux: W64.t Array32.t;
    
    var i:int;
    var byte_p:W64.t Array32.t;
    var q0:W64.t;
    var q1:W64.t;
    var z:bool;
    var byte_q:W64.t Array32.t;
    var cf:bool;
    byte_p <- witness;
    byte_q <- witness;
    leakages <- LeakAddr([]) :: leakages;
    aux <@ bn_set0 (byte_p);
    byte_p <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux_0 <- (W64.of_int 0);
    q0 <- aux_0;
    leakages <- LeakAddr([]) :: leakages;
    aux_0 <- (W64.of_int 1);
    q1 <- aux_0;
    leakages <- LeakAddr([]) :: leakages;
    aux_1 <- 0;
    i <- aux_1;
    leakages <- LeakAddr([]) :: leakages;
    aux_2 <- (q0 = (W64.of_int 0));
    z <- aux_2;
    
    leakages <- LeakCond(z) :: LeakAddr([]) :: leakages;
    
    while (z) {
      leakages <- LeakAddr([]) :: leakages;
      aux_3 <@ SC.randombytes_256 ((Array256.init (fun i_0 => get8
                                   (WArray256.init64 (fun i_0 => byte_p.[i_0]))
                                   i_0)));
      byte_p <-
      (Array32.init (fun i_0 => get64
      (WArray256.init8 (fun i_0 => aux_3.[i_0])) i_0));
      leakages <- LeakAddr([]) :: leakages;
      aux <@ bn_copy (byte_p);
      byte_q <- aux;
      leakages <- LeakAddr([]) :: leakages;
      (aux_2, aux) <@ bn_subc (byte_q, byte_z);
      cf <- aux_2;
      byte_q <- aux;
      leakages <- LeakAddr([]) :: leakages;
      aux_0 <- (cf ? q1 : q0);
      q0 <- aux_0;
      leakages <- LeakAddr([]) :: leakages;
      aux_2 <- (q0 = (W64.of_int 0));
      z <- aux_2;
      leakages <- LeakAddr([]) :: leakages;
      aux_1 <- (i + 1);
      i <- aux_1;
    leakages <- LeakCond(z) :: LeakAddr([]) :: leakages;
    
    }
    return (i, byte_p);
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
  
  proc dcminusP (p:W64.t Array64.t, x:W64.t Array64.t) : W64.t Array64.t = {
    var aux_0: bool;
    var aux: W64.t Array64.t;
    
    var z:W64.t Array64.t;
    var cf:bool;
    z <- witness;
    leakages <- LeakAddr([]) :: leakages;
    aux <@ dbn_copy (x);
    z <- aux;
    leakages <- LeakAddr([]) :: leakages;
    (aux_0, aux) <@ dbn_subc (z, p);
    cf <- aux_0;
    z <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux <@ dbn_cmov (cf, z, x);
    x <- aux;
    return (x);
  }
  
  proc bn_expand (x:W64.t Array32.t) : W64.t Array64.t = {
    var aux: int;
    var aux_0: W64.t;
    
    var r:W64.t Array64.t;
    var i:int;
    r <- witness;
    leakages <- LeakFor(0,32) :: LeakAddr([]) :: leakages;
    i <- 0;
    while (i < 32) {
      leakages <- LeakAddr([i]) :: leakages;
      aux_0 <- x.[i];
      leakages <- LeakAddr([i]) :: leakages;
      r.[i] <- aux_0;
      i <- i + 1;
    }
    leakages <- LeakFor(32,64) :: LeakAddr([]) :: leakages;
    i <- 32;
    while (i < 64) {
      leakages <- LeakAddr([]) :: leakages;
      aux_0 <- (W64.of_int 0);
      leakages <- LeakAddr([i]) :: leakages;
      r.[i] <- aux_0;
      i <- i + 1;
    }
    return (r);
  }
  
  proc bn_shrink (x:W64.t Array64.t) : W64.t Array32.t = {
    var aux: int;
    var aux_0: W64.t;
    
    var r:W64.t Array32.t;
    var i:int;
    r <- witness;
    leakages <- LeakFor(0,32) :: LeakAddr([]) :: leakages;
    i <- 0;
    while (i < 32) {
      leakages <- LeakAddr([i]) :: leakages;
      aux_0 <- x.[i];
      leakages <- LeakAddr([i]) :: leakages;
      r.[i] <- aux_0;
      i <- i + 1;
    }
    return (r);
  }
  
  proc div2 (x:W64.t Array128.t, k:int) : W64.t Array64.t = {
    var aux: int;
    var aux_0: W64.t;
    
    var r:W64.t Array64.t;
    var i:int;
    r <- witness;
    leakages <- LeakFor(0,k) :: LeakAddr([]) :: leakages;
    aux <- k;
    i <- 0;
    while (i < aux) {
      leakages <- LeakAddr([(64 + i)]) :: leakages;
      aux_0 <- x.[(64 + i)];
      leakages <- LeakAddr([i]) :: leakages;
      r.[i] <- aux_0;
      i <- i + 1;
    }
    return (r);
  }
  
  proc bn_breduce (a:W64.t Array64.t, r:W64.t Array64.t, p:W64.t Array32.t) : 
  W64.t Array32.t = {
    var aux_1: bool;
    var aux_0: bool;
    var aux: W64.t;
    var aux_4: W64.t Array32.t;
    var aux_3: W64.t Array64.t;
    var aux_2: W64.t Array128.t;
    
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
    leakages <- LeakAddr([]) :: leakages;
    (aux, aux_1, aux_0, aux_2) <@ dbn_muln (a, r);
     _0 <- aux;
     _1 <- aux_1;
     _2 <- aux_0;
    xr <- aux_2;
    leakages <- LeakAddr([]) :: leakages;
    aux_3 <@ div2 (xr, (2 * 32));
    xrf <- aux_3;
    leakages <- LeakAddr([]) :: leakages;
    aux_4 <@ bn_shrink (xrf);
    xrfd <- aux_4;
    leakages <- LeakAddr([]) :: leakages;
    (aux, aux_1, aux_0, aux_3) <@ bn_muln (xrfd, p);
     _3 <- aux;
     _4 <- aux_1;
     _5 <- aux_0;
    xrfn <- aux_3;
    leakages <- LeakAddr([]) :: leakages;
    (aux_1, aux_3) <@ dbn_subc (a, xrfn);
     _6 <- aux_1;
    t <- aux_3;
    leakages <- LeakAddr([]) :: leakages;
    aux_3 <@ bn_expand (p);
    pp <- aux_3;
    leakages <- LeakAddr([]) :: leakages;
    aux_3 <@ dcminusP (pp, t);
    t <- aux_3;
    leakages <- LeakAddr([]) :: leakages;
    aux_4 <@ bn_shrink (t);
    res_0 <- aux_4;
    return (res_0);
  }
  
  proc mulm (r:W64.t Array64.t, p:W64.t Array32.t, a:W64.t Array32.t,
             b:W64.t Array32.t) : W64.t Array32.t = {
    var aux_1: bool;
    var aux_0: bool;
    var aux: W64.t;
    var aux_3: W64.t Array32.t;
    var aux_2: W64.t Array64.t;
    
    var _of:bool;
    var _cf:bool;
    var c:W64.t Array64.t;
    var  _0:W64.t;
    c <- witness;
    leakages <- LeakAddr([]) :: leakages;
    (aux, aux_1, aux_0, aux_2) <@ bn_muln (a, b);
     _0 <- aux;
    _of <- aux_1;
    _cf <- aux_0;
    c <- aux_2;
    leakages <- LeakAddr([]) :: leakages;
    aux_3 <@ bn_breduce (c, r, p);
    a <- aux_3;
    return (a);
  }
  
  proc expm (r:W64.t Array64.t, m:W64.t Array32.t, x:W64.t Array32.t,
             n:W64.t Array32.t) : W64.t Array32.t = {
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
    var par:W64.t;
    var q:W64.t;
    var cbit:W64.t;
    x1 <- witness;
    x2 <- witness;
    x3 <- witness;
    x4 <- witness;
    leakages <- LeakAddr([]) :: leakages;
    aux <- (W64.of_int ((32 * 64) - 1));
    ctr <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux_1 <@ bn_set1 (x1);
    x1 <- aux_1;
    leakages <- LeakAddr([]) :: leakages;
    aux_1 <@ bn_set1 (x2);
    x2 <- aux_1;
    leakages <- LeakAddr([]) :: leakages;
    aux <@ ith_bit (n, ctr);
    d <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux_1 <@ bn_copy (x);
    x3 <- aux_1;
    leakages <- LeakAddr([]) :: leakages;
    aux_1 <@ mulm (r, m, x, x3);
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
      aux_1 <@ mulm (r, m, x1, x2);
      x1 <- aux_1;
      leakages <- LeakAddr([]) :: leakages;
      aux_1 <@ mulm (r, m, x2, x2);
      x2 <- aux_1;
      leakages <- LeakAddr([]) :: leakages;
      aux <- d;
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
    p <- aux;
    leakages <- LeakAddr([]) :: leakages;
    (aux_1, aux_0) <@ swapr (x2, x1, p);
    x1 <- aux_1;
    x2 <- aux_0;
    return (x1);
  }
  
  proc toEC () : unit = {
    var aux_0: int;
    var aux: W64.t Array32.t;
    
    var z:W64.t Array64.t;
    var a:W64.t Array32.t;
    var b:W64.t Array32.t;
    var p:W64.t Array32.t;
    var r:W64.t Array32.t;
    var  _0:int;
    a <- witness;
    b <- witness;
    p <- witness;
    r <- witness;
    z <- witness;
    leakages <- LeakAddr([]) :: leakages;
    aux <@ expm (z, a, b, p);
    r <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux <@ mulm (z, a, b, p);
    r <- aux;
    leakages <- LeakAddr([]) :: leakages;
    (aux_0, aux) <@ rsample (a);
     _0 <- aux_0;
    r <- aux;
    return ();
  }
}.



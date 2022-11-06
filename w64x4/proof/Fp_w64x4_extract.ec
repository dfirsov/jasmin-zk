require import AllCore IntDiv CoreMap List Distr.
 require import JModel.

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
  
  proc dmul1acc (k:int, a:W64.t, b:W64.t Array8.t, r:W64.t Array16.t,
                 _zero:W64.t, of_0:bool, cf:bool) : W64.t * bool * bool *
                                                    W64.t Array16.t = {
    var aux: int;
    
    var x1:W64.t;
    var i:int;
    var x2:W64.t;
    var hi:W64.t;
    var lo:W64.t;
    
    aux <- (8 - 1);
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
    x2 <- b.[(8 - 1)];
    (x1, x2) <- MULX_64 x1 x2;
    r.[(8 + k)] <- x1;
    lo <- x2;
    x1 <- r.[((8 + k) - 1)];
    (of_0, x1) <- ADOX_64 x1 lo of_0;
    r.[((8 + k) - 1)] <- x1;
    x1 <- r.[(8 + k)];
    (cf, x1) <- ADCX_64 x1 _zero cf;
    r.[(8 + k)] <- x1;
    x1 <- r.[(8 + k)];
    (of_0, x1) <- ADOX_64 x1 _zero of_0;
    r.[(8 + k)] <- x1;
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
    r <- witness;
    ai <- a.[0];
    (_zero, of_0, cf, r) <@ dmul1 (ai, b);
    i <- 1;
    while (i < 8) {
      ai <- a.[i];
      (_zero, of_0, cf, r) <@ dmul1acc (i, ai, b, r, _zero, of_0, cf);
      i <- i + 1;
    }
    return (_zero, of_0, cf, r);
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
    return p;
    
    (* var res_0:W64.t Array4.t; *)
    (* var xr:W64.t Array16.t; *)
    (* var xrf:W64.t Array8.t; *)
    (* var xrfn:W64.t Array8.t; *)
    (* var t:W64.t Array8.t; *)
    (* var pp:W64.t Array8.t; *)
    (* var  _0:W64.t; *)
    (* var  _1:bool; *)
    (* var  _2:bool; *)
    (* var  _3:W64.t; *)
    (* var  _4:bool; *)
    (* var  _5:bool; *)
    (* var  _6:bool; *)
    (* pp <- witness; *)
    (* res_0 <- witness; *)
    (* t <- witness; *)
    (* xr <- witness; *)
    (* xrf <- witness; *)
    (* xrfn <- witness; *)
    (* ( _0,  _1,  _2, xr) <@ dbn_muln (a, r); *)
    (* xrf <@ div2 (xr, (2 * 4)); *)
    (* pp <@ bn_expand (p); *)
    (* ( _3,  _4,  _5, xrfn) <@ dbn_muln (xrf, pp); *)
    (* ( _6, t) <@ dbn_subc (a, xrfn); *)

    (* t <@ dcminusP (pp, t); *)
    (* res_0 <@ bn_shrink (t); *)
    (* return (res_0); *)
  }
  
  proc toEC () : unit = {
    
    var z:W64.t Array8.t;
    var p:W64.t Array4.t;
    var r:W64.t Array4.t;
    p <- witness;
    r <- witness;
    z <- witness;
    r <@ bnreduce (z, z, p);
    return ();
  }
}.


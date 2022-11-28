require import AllCore IntDiv CoreMap List Distr.
require import JModel.

require import Array32 Array256.
require import WArray256.



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
  
  proc rsample (byte_z:W64.t Array32.t) : int * W64.t Array32.t = {
    var aux_1: bool;
    var aux_0: int;
    var aux: W64.t;
    var aux_2: W8.t Array256.t;
    var aux_3: W64.t Array32.t;
    
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
    aux <- (W64.of_int 0);
    q0 <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux <- (W64.of_int 1);
    q1 <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux_0 <- 0;
    i <- aux_0;
    leakages <- LeakAddr([]) :: leakages;
    aux_1 <- (q0 = (W64.of_int 0));
    z <- aux_1;
    
    leakages <- LeakCond(z) :: LeakAddr([]) :: leakages;
    
    while (z) {
      leakages <- LeakAddr([]) :: leakages;
      aux_2 <@ SC.randombytes_256 ((Array256.init (fun i_0 => get8
                                   (WArray256.init64 (fun i_0 => byte_p.[i_0]))
                                   i_0)));
      byte_p <-
      (Array32.init (fun i_0 => get64
      (WArray256.init8 (fun i_0 => aux_2.[i_0])) i_0));
      leakages <- LeakAddr([]) :: leakages;
      (aux_1, aux_3) <@ bn_subc (byte_q, byte_z);
      cf <- aux_1;
      byte_q <- aux_3;
      leakages <- LeakAddr([]) :: leakages;
      aux <- (cf ? q1 : q0);
      q0 <- aux;
      leakages <- LeakAddr([]) :: leakages;
      aux_1 <- (q0 = (W64.of_int 1));
      z <- aux_1;
      leakages <- LeakAddr([]) :: leakages;
      aux_0 <- (i + 1);
      i <- aux_0;
    leakages <- LeakCond(z) :: LeakAddr([]) :: leakages;
    
    }
    return (i, byte_p);
  }
  
  proc toEC () : unit = {
    var aux: int;
    var aux_0: W64.t Array32.t;
    
    var a:W64.t Array32.t;
    var r:W64.t Array32.t;
    var  _0:int;
    a <- witness;
    r <- witness;
    leakages <- LeakAddr([]) :: leakages;
    (aux, aux_0) <@ rsample (a);
     _0 <- aux;
    r <- aux_0;
    return ();
  }
}.


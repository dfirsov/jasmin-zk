require import AllCore IntDiv CoreMap List Distr.
require import JModel.




module M = {
  proc ith_bit (k:W64.t, ctr:W64.t) : W64.t = {
    
    var bit:W64.t;
    var p:W64.t;
    
    bit <- k;
    p <- ctr;
    p <- (p `&` (W64.of_int 63));
    bit <- (bit `>>` (truncateu8 p));
    bit <- (bit `&` (W64.of_int 1));
    return (bit);
  }
  
  proc swapr (x1:W64.t, x2:W64.t, toswap:W64.t) : W64.t * W64.t = {
    
    var _of_:bool;
    var _cf_:bool;
    var _sf_:bool;
    var _zf_:bool;
    var mask:W64.t;
    var x2r:W64.t;
    var x1r:W64.t;
    var t:W64.t;
    var  _0:bool;
    
    (_of_, _cf_, _sf_,  _0, _zf_, mask) <- set0_64 ;
    mask <- (mask - toswap);
    x2r <- x2;
    x1r <- x1;
    t <- x2r;
    t <- (t `^` x1r);
    t <- (t `&` mask);
    x1r <- (x1r `^` t);
    x2r <- (x2r `^` t);
    x1 <- x1r;
    x2 <- x2r;
    return (x1, x2);
  }
  
  proc addm (p:W64.t, a:W64.t, b:W64.t) : W64.t = {
    
    var x:W64.t;
    var k1:W64.t;
    var k2:W64.t;
    var _cf:bool;
    
    k1 <- (W64.of_int 0);
    k2 <- (W64.of_int 0);
    (_cf, x) <- addc_64 a b false;
    k1 <- (_cf ? p : k1);
    (_cf, x) <- subc_64 x p false;
    k2 <- (_cf ? p : k2);
    x <- (x + k2);
    x <- (x - k1);
    return (x);
  }
  
  proc subm (p:W64.t, a:W64.t, b:W64.t) : W64.t = {
    
    var x:W64.t;
    var k:W64.t;
    var _cf:bool;
    
    k <- (W64.of_int 0);
    (_cf, x) <- subc_64 a b false;
    k <- (_cf ? p : k);
    x <- (x + k);
    return (x);
  }
  
  proc mulm (p:W64.t, a:W64.t, b:W64.t) : W64.t = {
    
    var x:W64.t;
    var ax:W64.t;
    var bx:W64.t;
    var mh:W64.t;
    var ml:W64.t;
    var q:W64.t;
    var r:W64.t;
    var  _0:bool;
    var  _1:bool;
    var  _2:bool;
    var  _3:bool;
    var  _4:bool;
    var  _5:bool;
    var  _6:bool;
    var  _7:bool;
    var  _8:bool;
    var  _9:bool;
    
    ax <- a;
    bx <- b;
    ( _0,  _1,  _2,  _3,  _4, mh, ml) <- MUL_64 ax bx;
    ( _5,  _6,  _7,  _8,  _9, q, r) <- DIV_64 mh ml p;
    x <- r;
    return (x);
  }
  
  proc expm (m:W64.t, x:W64.t, n:W64.t) : W64.t = {
    
    var x1:W64.t;
    var ctr:W64.t;
    var d:W64.t;
    var x2:W64.t;
    var x3:W64.t;
    var x4:W64.t;
    var p:W64.t;
    var lbit:W64.t;
    var t1:W64.t;
    var t2:W64.t;
    var q:W64.t;
    var par:W64.t;
    var cbit:W64.t;
    
    ctr <- (W64.of_int 63);
    d <@ ith_bit (n, ctr);
    x1 <- (W64.of_int 1);
    x2 <- (W64.of_int 1);
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
    
    var p:W64.t;
    var a:W64.t;
    var b:W64.t;
    var r:W64.t;
    
    r <@ addm (p, a, b);
    r <@ subm (p, a, b);
    r <@ mulm (p, a, b);
    r <@ expm (p, a, b);
    return ();
  }
}.


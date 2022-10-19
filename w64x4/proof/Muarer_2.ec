require import AllCore IntDiv CoreMap List Distr.
require import JModel.

require import Array4 Array8 Array32.
require import WArray32 WArray64.



module MMM = {
  
  proc ith_bit (kk:W64.t Array4.t, ctr:W64.t) : W64.t = {
    
    var bit:W64.t;
    var k:W8.t Array32.t;
    var p:W64.t;
    k <- witness;
    k <-
    (Array32.init (fun i => get8 (WArray32.init64 (fun i => kk.[i])) i));
    p <- ctr;
    p <- (p `>>` (W8.of_int 3));
    bit <- (zeroextu64 k.[(W64.to_uint p)]);
    p <- ctr;
    p <- (p `&` (W64.of_int 7));
    bit <- (bit `>>` (truncateu8 p));
    bit <- (bit `&` (W64.of_int 1));
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
  


}.


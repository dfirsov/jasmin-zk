require import AllCore IntDiv CoreMap List Distr.
require import JModel.

require import Array4 Array8 Array32.
require import WArray32 WArray64.



module MMM = {

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
  

}.


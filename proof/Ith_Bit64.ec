require import AllCore IntDiv CoreMap List.
from Jasmin require import JModel.


op as_word (x : bool) : W64.t  = x ? W64.one : W64.zero.
op ith_bitword64 (n : W64.t) (x : int)  : W64.t = as_word (n.[x]).

module IB = {
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
}.

section.

local lemma qqq x : 0 < x < 64 => W64.one.[x] = false.
progress. timeout 20. smt.
qed.

  
lemma ithbit64 a b :
 phoare[ IB.ith_bit64   : arg = (a,b) /\
     0 <= to_uint ctr < 64 ==> res = ith_bitword64 a (to_uint b) ] = 1%r.
proc. wp.  skip. progress.
rewrite /ith_bitword64.
rewrite /as_word.
rewrite /truncateu8.
have -> : (to_uint (ctr{hr} `&` (of_int 63)%W64))
  = (to_uint ctr{hr} %% 2 ^ 6).
rewrite - to_uint_and_mod. auto.
smt. simplify.
have -> : (of_int (to_uint ctr{hr} %% 64))%W8 = (of_int (to_uint ctr{hr}))%W8.
smt.
rewrite /(`>>`).
rewrite /(`>>>`).
rewrite /W64.(`&`).
rewrite /map2.
case (k{hr}.[to_uint ctr{hr}]).
progress.
apply W64.ext_eq.
progress.
rewrite initiE. auto.
simplify.
rewrite initiE. auto.
simplify.
case (x = 0).
progress. smt.
progress.
have -> : W64.one.[x] = false.
smt (qqq).
auto.
progress.
apply W64.ext_eq.
progress.
rewrite initiE. auto.
simplify.
rewrite initiE. auto.
simplify.
case (x = 0).
progress. smt.
progress.
smt (qqq).
qed.

end section.

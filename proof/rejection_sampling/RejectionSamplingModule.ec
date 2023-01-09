
require import AllCore Distr.

type X.

abbrev Impl P Q = (forall (x : X), P x => Q x).

op d : X distr.
axiom dll : is_lossless d.
op defX : X.

module RS = {
  var flag : bool

  proc sample(P : X -> bool,c:int) = {
    var b : bool;
    var x : X;
    x <- defX;
    b <- false;
    while(!b){
     x <$ d;
     b <- P x;
     c <- c + 1;
    }
    return (c,x);
  }
  
  proc sample1(P : X -> bool, c: int) = {
    var x : X;

    flag <- false;
    x <$ d;
    c <- c + 1;
    if(! P x){
      flag <- true;
      (c, x) <@ sample(P,c);
    }    
    return (c,x);
  }  

}.

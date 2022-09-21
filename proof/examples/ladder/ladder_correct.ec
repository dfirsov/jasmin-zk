require import AllCore IntDiv CoreMap List.



op ith_bit : int -> int -> bool.
op parity : int -> int -> bool.

axiom prop1 n x: parity x (n-1)  => ith_bit x (n-1)  => !ith_bit x n.
axiom prop2 n x: parity x (n-1)  => !ith_bit x (n-1)  => ith_bit x n.
axiom prop3 n x: !parity x (n - 1)  => ith_bit x (n-1) = ith_bit  x n.


module M = {
  
  proc expm_naive (p:int, x:int, n:int) : int = {
    
    var x1:int;
    var ctr:int;
    var x2:int;
    var bit:bool;
    
    ctr <- 4;
    x1 <- x;
    x2 <- x1 * x1; 

    while (0 <= ctr) {
      ctr <- (ctr - 1);
      (x1,x2) <- (ith_bit n ctr) ? ((x1 * x2), (x2 * x2)) : ((x1*x1),(x1*x2));
    }
    return x1;
  }
  

  proc expm (p:int, x:int, n:int) : int = {
    
    var x1:int;
    var ctr:int;
    var x2:int;
    var bit:bool;
    
    ctr <- 4;
    x1 <- x;
    x2 <- x1 * x1; 

    while (0 <= ctr) {
      ctr <- (ctr - 1);
      (x1,x2) <- if parity n ctr then (x2,x1) else (x1, x2);
      x1 <- x1 * x2;
      x2 <- x2 * x2;
    }

    (x1,x2) <- if ! ith_bit n ctr then (x2,x1) else (x1, x2);    
    return x1;
    
 } 

  
}.





lemma exp_eq : 
  equiv[ M.expm_naive ~ M.expm : ={arg} /\ ith_bit n{1} 4 = true ==> ={res}].
proc.
seq 3 3 : (={x1,x2,ctr,n} /\ ctr{1} = 4 /\ ith_bit n{1} 4 = true).  wp.  skip.  progress. 

seq 1 1 : (={ctr, n} /\ (ith_bit n{2} ctr{2} => x2{2} = x2{1} /\ x1{2} = x1{1})  /\ ((!ith_bit n{2} ctr{2}) =>  (x1{1} = x2{2} /\ x2{1} = x1{2})) /\ ith_bit n{1} 4 = true).



while (={ctr, n} /\ (ith_bit n{2} ctr{2} => x2{2} = x2{1} /\ x1{2} = x1{1})  /\ ((!ith_bit n{2} ctr{2}) =>  (x1{1} = x2{2} /\ x2{1} = x1{2}) )).
wp. skip. progress.
rewrite H3. simplify.  

smt(prop1 prop2 prop3).

rewrite H3. simplify.
smt(prop1 prop2 prop3).


rewrite H3. simplify.
smt(prop1 prop2 prop3).

rewrite H3. simplify.
smt(prop1 prop2 prop3).

skip. progress.  smt. smt.
wp. skip. progress.
smt(prop1 prop2 prop3).
qed.


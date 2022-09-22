require import AllCore IntDiv CoreMap List.


require import StdOrder.
import IntOrder.


type bits = bool list.

op ith_bit : bits -> int -> bool.
op parity : bits -> int -> bool.

op tonat : bits -> int.
op fromnat : int -> bits.

axiom prop1 n x: parity x (n-1)  => nth witness x (n-1)  => !nth witness x n.
axiom prop2 n x: parity x (n-1)  => !nth witness x (n-1)  => nth witness x n.
axiom prop3 n x: !parity x (n - 1)  => nth witness x (n-1) = nth witness x n.
axiom prop4 : tonat[true] = 1.
axiom prop5 : tonat[false] = 0.


axiom prop6 s :  tonat (true :: s) = 2 * (tonat s) + 1.
axiom prop7 s :  tonat (false :: s) = 2 * (tonat s).
axiom prop8 s :  0 <= tonat s  .


module M = {
  (* simple to prove correctness *)
  proc expm_naive (x:int, n:bits) : int = {
    
    var x1:int;
    var ctr:int;
    var x2:int;
    var bit:bool;    
    ctr <- size n;
    x1 <- 1;
    x2 <- x; 
    while (0 < ctr) {
      ctr <- (ctr - 1);
      (x1,x2) <- (nth witness n ctr) ? ((x1*x2), (x2*x2)) : ((x1*x1), (x1*x2));
    }
    return x1;
  }  

  (* constant time  *)
  proc expm (x:int, n:bits) : int = {  
    var x1:int;
    var ctr:int;
    var x2:int;
    var bit:bool;
    
    ctr <- size n;
    x1 <- 1;
    x2 <- x ; 

    while (0 < ctr) {
      ctr <- (ctr - 1);
      (x1,x2) <- if parity n ctr then (x2,x1) else (x1, x2);
      x1 <- x1 * x2;
      x2 <- x2 * x2;
    }

    (x1,x2) <- if ! nth witness n ctr then (x2,x1) else (x1, x2);    
    return x1;
    
 } 
}.

lemma exp_correct xx nn : 
  hoare[ M.expm_naive : arg = (xx, nn) /\  0 < size nn /\ nth witness nn (size nn) = true ==> res = xx ^ (tonat nn)].
proof. 
proc. 
seq 3 : (ctr = size n /\ x1 = 1 /\ x2 = x /\  0 < size n /\ x = xx /\ n = nn /\ ctr <= size n   ). wp.  skip. progress. 
while (x1 = x ^ tonat (drop ctr n) /\ x2 = x1 * x /\ ctr <= size n).
wp. skip.  progress.
case (nth witness n{hr} (ctr{hr} - 1)). progress.
  have -> : (drop (ctr{hr} - 1) n{hr}) = true :: (drop (ctr{hr} ) n{hr}).  
  rewrite (drop_nth witness). progress. smt(). smt().
  rewrite H1. auto.
rewrite prop6. 
pose n := tonat (drop ctr{hr} n{hr}). 
have ->: x{hr} ^ n * (x{hr} ^ n * x{hr}) 
  = (x{hr} ^ n * x{hr} ^ n) * x{hr}. smt.
have -> : x{hr} ^ n * x{hr} ^ n  = x{hr} ^ (2 * n). smt.
smt.
progress. 
have -> : (drop (ctr{hr} - 1) n{hr}) = false :: (drop (ctr{hr} ) n{hr}).  
rewrite (drop_nth witness). progress. smt(). smt(). rewrite H1.
auto. rewrite prop7. smt. 
case (nth witness n{hr} (ctr{hr} - 1)). progress. smt().
progress. smt().
smt().
skip. progress. smt.
smt.
qed.


lemma exp_eq : 
  equiv[ M.expm_naive ~ M.expm : ={arg} /\ nth witness n{1} (size n{1}) = true ==> ={res}].
proc.
seq 3 3 : (={x1,x2,ctr,n} /\ ctr{1} = (size n{1}) /\ nth witness n{1} (size n{1}) = true).  wp.  skip.  progress. 

seq 1 1 : (={ctr, n} /\ (nth witness n{2} ctr{2} => x2{2} = x2{1} /\ x1{2} = x1{1})  /\ ((!nth witness n{2} ctr{2}) =>  (x1{1} = x2{2} /\ x2{1} = x1{2})) /\ nth witness n{1} (size n{1}) = true).

while (={ctr, n} /\ (nth witness n{2} ctr{2} => x2{2} = x2{1} /\ x1{2} = x1{1})  /\ ((!nth witness n{2} ctr{2}) =>  (x1{1} = x2{2} /\ x2{1} = x1{2}) )).
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


require import AllCore IntDiv CoreMap List.

require import JModel.
require import BitEncoding.
import BS2Int.


require import StdOrder.
import IntOrder.

type bits = bool list.


op tonat : bits -> int = bs2int.
op ith_bit (n : bits) (x : int) : bool = nth witness n x.

lemma prop1   : tonat[true] = 1.
proof. smt. qed.

lemma prop2   : tonat[false] = 0.
proof. smt. qed.

lemma prop3 s : tonat (true :: s) = 2 * (tonat s) + 1.
proof. smt. qed.

lemma prop4 s : tonat (false :: s) = 2 * (tonat s).
proof. smt. qed.

lemma prop5 s : 0 <= tonat s.
proof. smt. qed.


module M = {

  proc expm_spec (x:int, n:bits) : int = {
    return x ^ (tonat n);
  }  

  proc expm_naive (x:int, n:bits) : int = {
    
    var x1:int;
    var ctr:int;
    var x2:int;
    var bit:bool;    
    ctr <- size n - 1;
    (x1, x2) <- (x,x * x);
    while (0 < ctr) {
      ctr <- (ctr - 1);
      (x1,x2) <- (ith_bit n ctr) ? ((x1*x2), (x2*x2)) : ((x1*x1), (x1*x2));
    }
    return x1;
  }  

  proc expm (x:int, n:bits) : int = {  
    var x1:int;
    var ctr:int;
    var x2:int;
    var bit:bool;
    var par: bool;
    ctr <- size n - 1;
    (x1, x2) <- (x,x * x);

    while (0 < ctr) {
      ctr <- (ctr - 1);
      par <- ith_bit n (ctr + 1) ^ ith_bit n ctr;
      (x1,x2) <- if par then (x2,x1) else (x1, x2);
      x1 <- x1 * x2;
      x2 <- x2 * x2;
    }
    (x1,x2) <- if ! ith_bit n 0 then (x2,x1) else (x1, x2);    
    return x1;
    
 }
}.


lemma exp_eq_naive :
 equiv[ M.expm_naive ~ M.expm : ={arg} /\  0 < size n{1} /\ ith_bit n{2} (size n{1} - 1) ==> ={res}].
proc.
seq 2 2 : (={x1,x2,ctr,n} /\ par{2} = true /\ ctr{1} + 1 = (size n{1}) /\  0 < size n{1} /\ ith_bit n{2} (size n{1} - 1) ).  wp.  skip.  progress.
seq 1 1 : (={ctr, n} /\ ctr{1} = 0 /\ (ith_bit n{2} ctr{2} => x2{2} = x2{1} /\ x1{2} = x1{1})  /\ ((!ith_bit n{2} ctr{2}) =>  (x1{1} = x2{2} /\ x2{1} = x1{2})) /\  0 < size n{1} /\ ith_bit n{2} (size n{1} - 1) ).
while (={ctr, n} /\ 0 < ctr{2} + 1 <= size n{2}
   /\ (ith_bit n{2} (ctr{2}  ) => x2{2} = x2{1} /\ x1{2} = x1{1})
   /\ ((!ith_bit n{2} (ctr{2} ) ) => (x1{1} = x2{2} /\ x2{1} = x1{2}))
   ).
wp. skip. progress. smt().    
rewrite H5. simplify. smt().
rewrite H5. simplify. smt().
rewrite H5. simplify. smt().
rewrite H5. simplify. smt().
skip. progress. smt(). smt(). smt(). smt(). smt().
wp. skip. progress. smt().
qed.



lemma exp_naive_correct xx nn : 
  equiv[ M.expm_naive ~ M.expm_spec : ={arg} /\ arg{1} = (xx, nn){1} /\  0 < size nn /\ ith_bit nn (size nn - 1){1}  ==> ={res}].
    proof.
proc. 
seq 2 0 : ((ctr + 1 = size n /\ x1 = x /\ x2 = x * x /\  0 < size n /\ x = xx /\ n = nn /\ ctr <= size n 
  /\ ith_bit n (size n - 1)){1} /\ ={x,n}). wp.  skip. progress. smt().
while {1} ((x1 = x ^ tonat (drop ctr n) /\ x2 = x1 * x /\ ctr <= size n)){1} (ctr{1}). progress.
wp. skip.  progress.
case (ith_bit n{hr} (ctr{hr} - 1 )). progress.
  have -> : (drop (ctr{hr} - 1) n{hr}) = true :: (drop (ctr{hr} ) n{hr}).  
  rewrite (drop_nth witness (ctr{hr} - 1)). smt(). simplify.
rewrite /ith_bit in H1. rewrite H1. auto.
rewrite prop3. 
pose n := tonat (drop ctr{hr} n{hr}). 
have ->: x{hr} ^ n * (x{hr} ^ n * x{hr}) 
  = (x{hr} ^ n * x{hr} ^ n) * x{hr}. smt.
have -> : x{hr} ^ n * x{hr} ^ n  = x{hr} ^ (2 * n). smt.
smt.
progress. 
have -> : (drop (ctr{hr} - 1) n{hr}) = false :: (drop ctr{hr} n{hr}).
  rewrite (drop_nth witness (ctr{hr} - 1)). smt(). simplify.  
rewrite /ith_bit in H1. rewrite H1. auto.
rewrite prop4. smt. 
case (ith_bit n{hr} (ctr{hr} - 1)). progress. smt().
progress. smt().
smt(). smt().
    skip. progress.
have ->: ctr{1} = size n{2} - 1. smt().
rewrite  (drop_nth witness). smt().
simplify. smt.
smt().
smt.    
qed.
    


lemma exp_correct xx nn : 
  equiv[ M.expm ~ M.expm_spec : ={arg} /\ arg{1} = (xx, nn){1} /\  0 < size nn /\ ith_bit nn (size nn - 1) = true ==> ={res}].
proof. 
transitivity M.expm_naive ( ={arg} /\  0 < size n{1} /\ ith_bit n{2} (size n{1} - 1) ==> ={res}) 
  ( ={arg} /\ arg{1} = (xx, nn){1} /\  0 < size nn /\ ith_bit nn (size nn - 1) = true ==> ={res}).
progress. smt().  auto. symmetry. conseq exp_eq_naive. progress. progress.
conseq (exp_naive_correct xx nn). progress.
rewrite H0. 
qed.

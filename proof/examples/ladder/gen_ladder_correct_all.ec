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
admitted. (* proof. smt. qed. *)

lemma prop2   : tonat[false] = 0.
admitted. (* proof. smt. qed. *)

lemma prop3 s : tonat (true :: s) = 2 * (tonat s) + 1.
admitted. (* proof. smt. qed. *)

lemma prop4 s : tonat (false :: s) = 2 * (tonat s).
admitted. (* proof. smt. qed. *)

lemma prop5 s : 0 <= tonat s.
admitted. (* proof. smt. qed. *)


module M = {

  proc expm_spec (x:int, n:bits) : int = {
    return x ^ (tonat n);
  }  

  proc expm_naive (x:int, n:bits) : int = {
    
    var x1, x2, x3, x4 : int;
    var ctr:int;
    var bit, d, p :bool;    
    d <- ith_bit n (size n - 1);
    (x1,x2,x3, x4) <- (1,1,x,x * x);

    ctr <- size n - 1;
    p <- d;
    (x1,x3) <- d ? (x3,x1) : (x1,x3);
    (x2,x4) <- d ? (x4,x2) : (x2,x4);

    while (0 < ctr) {
      ctr <- (ctr - 1);
      p <- d;
      d <- d || ith_bit n ctr;
      (x1,x2) <- (ith_bit n ctr) ? ((x1*x2), (x2*x2)) : ((x1*x1), (x1*x2));
      (x1,x3) <- d ^ p ? (x3,x1) : (x1,x3);
      (x2,x4) <- d ^ p ? (x4,x2) : (x2,x4);
    }
    return x1;
  }  

}.


op has_true (bs : bits) : bool = has (fun x => x = true) bs.


lemma hast1 : forall xs ctr, 0 <= ctr <= size xs => (has_true (drop ctr xs) || ith_bit xs (ctr - 1)) = has_true (drop (ctr - 1) xs).
admitted.


lemma hast3 xs :  drop (size xs - 1) xs = [ith_bit xs (size xs - 1) ] .
admitted.
lemma hast2 xs :  ith_bit xs (size xs - 1) = has_true (drop (size xs - 1) xs).
admitted.

lemma hast4  : forall xs (x : int), ! (has_true xs) => x ^ (tonat xs) = 1.
elim. smt.
smt.
qed.

lemma hast5  : forall xs, ! (has_true xs) => (bs2int xs) = 0.
elim. smt.
smt.
qed.



lemma exp_naive_correct xx nn : 
  equiv[ M.expm_naive ~ M.expm_spec : ={arg} /\ arg{1} = (xx, nn){1} /\  0 < size nn ==> ={res}].
proof.
proc. 

while {1} (d{1} = has_true (drop ctr n) /\ ctr < size n /\ (has_true (drop ctr n) =>
  (x1 = x ^ tonat (drop ctr n) 
    /\ x2 = x1 * x  /\ (x3,x4){1} = (1, 1)) ) /\ (!has_true (drop ctr n) => x1 = 1 /\ x2 = 1 /\ x3 = x /\ x4 = x * x) ){1} (ctr{1}). 

progress.
wp. skip.  progress. apply hast1. progress. smt().
smt(). smt().


case (ith_bit n{hr} (ctr{hr} - 1 )). progress.
  case (!has_true (drop ctr{hr} n{hr})). move => casef.  
   rewrite casef.
  have -> : true ^ false  = true. smt(@Bool). simplify.
  have -> : x3{hr} = x{hr}. smt(). 
  have -> : (drop (ctr{hr} - 1) n{hr}) = true :: (drop (ctr{hr} ) n{hr}).  
  rewrite (drop_nth witness (ctr{hr} - 1)).  smt(). smt().
   rewrite /tonat. 
rewrite  bs2int_cons.
rewrite /b2i. simplify.
have -> : x{hr} ^ (1 + 2 * bs2int (drop ctr{hr} n{hr}))
  = x{hr} * x{hr} ^ (2 * bs2int (drop ctr{hr} n{hr})).
smt.
have ->: x{hr} ^ (2 * bs2int (drop ctr{hr} n{hr}))
 = x{hr} ^ (bs2int (drop ctr{hr} n{hr})) * x{hr} ^ (bs2int (drop ctr{hr} n{hr})).
smt.
have -> : bs2int (drop ctr{hr} n{hr})  = 0.
rewrite  hast5. auto. auto. smt.
simplify.
move => casef. rewrite casef. 
  have -> : true ^ true  = false. smt(@Bool). simplify.
  have -> : (drop (ctr{hr} - 1) n{hr}) = true :: (drop (ctr{hr} ) n{hr}).  
  rewrite (drop_nth witness (ctr{hr} - 1)). 
progress. smt().
smt(). 


  simplify.
rewrite /ith_bit in H4. rewrite H4. auto.
rewrite prop3. 
have -> : x1{hr} * x2{hr} = x{hr} ^ tonat (drop ctr{hr} n{hr}) * x{hr} ^ tonat (drop ctr{hr} n{hr}) * x{hr}.
smt(). smt.

progress.

have z: has_true (drop ctr{hr} n{hr}) = true. 
have x : drop (ctr{hr} - 1) n{hr} = ith_bit n{hr} (ctr{hr} - 1) :: drop ctr{hr} n{hr}.
rewrite (drop_nth witness (ctr{hr} - 1)).  smt(). rewrite H4.
simplify. rewrite - H4. rewrite /ith_bit. auto.
smt.

rewrite z.
have -> : true ^ true  = false. smt(@Bool). simplify.

have -> : x1{hr} * x1{hr} = x{hr} ^ tonat (drop ctr{hr} n{hr}) * x{hr} ^ tonat (drop ctr{hr} n{hr}).
smt. 

rewrite (drop_nth witness (ctr{hr} - 1)).  smt(). smt.
smt.
smt.
smt.
smt.
smt.
smt.
smt.
smt.

wp.  skip.  progress.


rewrite (drop_nth witness (size n{2} - 1)). smt(). simplify.
smt.
smt.

rewrite hast2. rewrite H0. simplify.
rewrite hast3. rewrite hast2. rewrite H0. smt.
rewrite hast2. rewrite H0. simplify. auto.

rewrite hast2 H0 =>//. 
rewrite hast2 H0 =>//. 
rewrite hast2 H0 =>//. 
rewrite hast2 H0 =>//. 
rewrite hast2 H0 =>//. 
rewrite hast2 H0 =>//.
smt. 

have : ctr_L <= 0. smt().

case (has_true (drop ctr_L n{2})).
smt.
progress.
have -> : x1_L = 1. smt().
have x : (drop ctr_L n{2}) = n{2}.  smt.
have y : !has_true n{2}. smt.
rewrite hast4. auto. auto.
qed.

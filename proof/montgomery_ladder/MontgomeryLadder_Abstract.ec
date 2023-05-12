require import AllCore IntDiv CoreMap List.
require import BitEncoding.
import BS2Int.
from Jasmin require import JModel. (* only properties of bs2int function *)


type R.
type bits = bool list.


op idR : R.
op ( *** ) (a b : R) : R.

axiom op_assoc (a b c : R) :  (a *** b) *** c = a *** (b *** c).
axiom op_id (x : R) :  x *** idR = x.
axiom op_id' (x : R) : idR *** x = x.

op ith_bit (n : bits) (x : int) : bool = nth false n x.
op has_true (bs : bits) : bool = has (fun x => x = true) bs.
op (^) (x : R) (n : int) : R = if n < 0 then iterop (-n) ( *** ) x idR else iterop n ( *** ) x idR.


lemma mod_lemm (a b c m : int) : ((a * b %% m) * c) %% m = ((a * b) * c) %% m. 
smt (modzMml modzMm modzMmr).
qed.

lemma iteropi : forall i, 0 <= i => forall  b, 
  iterop (i + 1) ( *** ) b idR = b *** iterop i ( *** ) b idR.
apply intind.
progress. 
 have ->: iterop 0 ( *** ) b idR = idR.
smt(@IterOp).
  have ->: iterop 1 ( *** ) b idR = b.
smt(@IterOp).
smt (op_id op_id'). auto.
progress. progress.
rewrite /iterop. 
simplify. rewrite iteriS. auto. simplify. 
have ->: (i + 2) = (i+1) + 1. smt().
rewrite iteriS. smt().
rewrite iteriS. smt().
simplify. smt().
qed.

lemma bs2int_true : bs2int [true] = 1.
rewrite bs2int_cons. rewrite bs2int_nil. simplify. 
  auto. 
qed.

lemma bsint_false   : bs2int [false] = 0.
rewrite bs2int_cons. rewrite bs2int_nil. simplify. 
  auto. 
qed.

lemma exp_prop1 x : x ^ 0 = idR.
smt (@IterOp). qed.

lemma exp_prop2 x : x ^ 1 = x.
smt (@IterOp). qed.

lemma exp_prop3' x : forall i, 0 <= i => x ^ (1 + i) = x *** x ^ i.
progress. rewrite /(^).
have -> : 1 + i < 0 = false. smt().
simplify.
have -> : i < 0 = false. smt(). simplify.
rewrite - iteropi. auto. auto.
smt().
qed.


lemma exp_prop3'' x : forall i, 0 <= i => x ^ (1 + i) = x ^ i *** x.
apply intind. smt.
progress. smt.
qed.


lemma exp_prop3 (x : R) : forall (a : int), 0 <= a => forall b,  0 <= b => x ^ (a + b) = x ^ a *** x ^ b.
apply intind. progress. rewrite exp_prop1.   smt (op_id' op_id).
progress.
have ->: (i + 1) = (1 + i). smt().
have ->: x ^ (1 + i) = x *** x ^ i.
rewrite /(^).  
have ->: 1 + i < 0 = false. smt(). simplify.
have ->: i < 0 = false. smt(). simplify.
have ->: 1 + i = i + 1. smt().
rewrite iteropi. auto. auto. auto.
rewrite op_assoc.
rewrite - H0. auto. auto.
smt (exp_prop3').
qed.

(* lemma exp_prop4' a b : forall i, 0 <= i => (a *** b) ^ i = a ^ i *** b ^ i. *)
(* apply intind. progress. smt. *)
(* progress. *)
(* have -> : (i + 1) = (1 + i). smt(). *)
(* rewrite exp_prop3'. auto. *)
(* rewrite exp_prop3'. auto.  *)
(* rewrite exp_prop3'. auto.  *)
(* rewrite H0. auto. auto. *)
(* smt. *)
(* qed. *)

lemma oner_exp : forall b, 0 <= b => idR = idR ^ b.
apply intind. progress. smt(exp_prop1).
progress. 
have -> : (i+1) = 1 + i. smt().
rewrite exp_prop3'. auto. 
smt.
qed.

lemma exp_prop4 (x : R)  : forall (b : int), 0 <= b => forall a, 
  0 <= a =>  x ^ (a * b) = (x ^ a) ^ b.
apply intind.
progress. rewrite exp_prop1. smt.
move => i ip ih1.
apply intind.
progress. smt.
progress.
have -> : x ^ a ^ (i0 + 1)
 = (x ^ a) ^ i0 *** (x ^ a). smt.
have -> : x ^ (a * (i0 + 1))
 = x ^ (a * i0 + a). smt.
rewrite exp_prop3. auto. smt(). smt().
smt.
smt().
qed.

lemma hast3 xs :  0 < size xs => drop (size xs - 1) xs = [ith_bit xs (size xs - 1) ].
progress. rewrite (drop_nth witness). progress. smt(). smt().
simplify. smt(@List).
qed.
    
lemma hast2 xs :  0 < size xs => ith_bit xs (size xs - 1) = has_true (drop (size xs - 1) xs).
progress. rewrite hast3;auto. smt().
qed.

lemma hast1 : forall xs ctr, 0 <= ctr -1 < size xs
  => (has_true (drop ctr xs) || ith_bit xs (ctr - 1)) = has_true (drop (ctr - 1) xs).
progress. 
rewrite ( drop_nth false (ctr - 1) ). progress. smt(). 
qed.


lemma hast5  : forall xs, ! (has_true xs) => (bs2int xs) = 0.
elim. smt. smt. qed.


lemma hast4  : forall xs (x : R), ! (has_true xs) => x ^ (bs2int xs) = idR.
progress. rewrite hast5. auto.
rewrite /(^). simplify. smt.
qed.

lemma hast6  : forall xs (x : int), ! (has_true xs) => x ^ (bs2int xs) = 1.
progress. rewrite hast5. auto.
smt.
qed.

module ML_Abstract = {

  proc iterop_spec (x:R, n:bits) : R = {
    return x ^ (bs2int n); 
  }  

  proc mladder (x :R , n : bits ) : R = {
    var x1 , x2 , i , b ;
    (x1,x2) <- (idR , x);
    i <- size n;
    b <- false;
    while (0 < i ) {
      i <- i - 1;
      b <- ith_bit n i ;
      (x1,x2) <- b ? (x2,x1) : (x1,x2 );
      (x1,x2) <- b ? (x1 *** x2, x1 *** x1) : (x1 *** x1, x1 *** x2);
    }
    return x1 ;
  } 
}.
  
lemma mladder_correct_ph xx nn : 
  phoare[ ML_Abstract.mladder : arg = (xx, nn)  /\  0 < size nn  ==> res = xx ^ (bs2int nn) ]  = 1%r.
proc. sp.
while (i <= size n 
  /\ x1 = x ^ bs2int (drop i n)
  /\ x2 = x1 *** x) i. 
move => z. 
wp. skip. progress.
smt(). 
case (ith_bit n{hr} (i{hr} - 1 )). progress.
  case (!has_true (drop i{hr} n{hr})). move => casef.  
  rewrite (drop_nth false (i{hr} - 1)).  smt(). 
rewrite  bs2int_cons.
rewrite /b2i. simplify.
simplify.
print ith_bit.
have ->: nth false n{hr} (i{hr} - 1) = true. smt().
simplify.
have -> : x{hr} ^ (1 + 2 * bs2int (drop i{hr} n{hr}))
  = x{hr} *** x{hr} ^ (2 * bs2int (drop i{hr} n{hr})).
rewrite exp_prop3. auto. smt(bs2int_ge0). auto. rewrite exp_prop2. auto.
have ->: x{hr} ^ (2 * bs2int (drop i{hr} n{hr}))
 = x{hr} ^ (bs2int (drop i{hr} n{hr})) *** x{hr} ^ (bs2int (drop i{hr} n{hr})).
smt(exp_prop3). 
have -> : bs2int (drop i{hr} n{hr})  = 0.
rewrite  hast5. auto. auto. rewrite exp_prop1. rewrite op_id. smt.  
simplify.
move => casef. 
  rewrite (drop_nth false (i{hr} - 1)). 
progress. smt().
smt(). 
   simplify.
pose m := bs2int (drop i{hr} n{hr}).
have ->: (nth false n{hr} (i{hr} - 1))  = true. smt(). 
rewrite bs2int_cons.
rewrite exp_prop3. smt (bs2int_ge0). auto. auto. smt (bs2int_ge0). rewrite exp_prop2.
have ->: (2 * m) = m + m. smt().
rewrite exp_prop3. smt. smt.
smt(op_assoc exp_prop3' exp_prop3).
have x : drop (i{hr} - 1) n{hr} = ith_bit n{hr} (i{hr} - 1) :: drop i{hr} n{hr}.
rewrite (drop_nth false (i{hr} - 1)).  smt(). simplify. auto.
simplify.  
move => ifalse.  rewrite x. rewrite ifalse. 
rewrite bs2int_cons. rewrite/b2i. simplify. smt(exp_prop3).
case (has_true (drop i{hr} n{hr})). progress. 
case ( ith_bit n{hr} (i{hr} - 1)).
progress. 
smt(exp_prop1 exp_prop2 exp_prop3 exp_prop4 op_id op_assoc).
smt(exp_prop1 exp_prop2 exp_prop3 exp_prop4 op_id op_assoc).
progress.
smt(exp_prop1 exp_prop2 exp_prop3 exp_prop4 op_id op_assoc).
smt(). 
skip.  progress. 
have ->  : (drop (size n{hr}) n{hr}) = []. smt(@List).
have -> : bs2int [] = 0. smt(@BS2Int).
smt(exp_prop1).
 smt(op_id op_id').
smt().
have i0_prop : i0 <= 0. smt().
smt (@List).
qed.

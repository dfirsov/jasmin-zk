require import AllCore IntDiv CoreMap List.

require import JModel.
require import BitEncoding.
import BS2Int.

type R.


module type BasicOps = {
  proc ith_bit (r : R, p : W64.t) : W64.t
  proc mulm (p : R, a : R, b : R) : R
  proc swapr (a : R, b : R, c : W64.t) : R * R
}.

type bits = bool list.


op tonat : bits -> int = bs2int.
op ith_bit (n : bits) (x : int) : bool = nth witness n x.
op has_true (bs : bits) : bool = has (fun x => x = true) bs.

op P : int.
op ( *** ) (a b : R) : R.
op (^) (x : R) (n : int) : R.
op oneR : R.
op Rsize : int.
op Rbits (r : R) : bits.
op bitsR (r : bits) : R.
op as_w64 (x : bool) : W64.t  = x ? W64.one : W64.zero.
op ith_bitR (r : R) (x : int) : W64.t = as_w64 (ith_bit (Rbits r) x).
op as_bool (x : W64.t) : bool  = (x = W64.one).
op ith_bitlist (n : bits) (x : int)  : W64.t = as_w64 (ith_bit n x).
op valR (x : R) : int = tonat (Rbits x).
op ImplR (p : R) (P : int) = (valR p = P).


axiom P_prime: prime P.
axiom qqq n x : ith_bitlist (Rbits n) x = ith_bitR n x.
axiom www n x : size n = Rsize => ith_bitlist n x = ith_bitR (bitsR n) x.
axiom iii n : size (Rbits n) = Rsize.
axiom Rsize_max : Rsize < W64.max_uint.
axiom Rsize_pos : 0 < Rsize.
axiom prop1   : tonat[true] = 1.
axiom prop2   : tonat[false] = 0.
axiom prop3 s : tonat (true :: s) = 2 * (tonat s) + 1.
axiom prop4 s : tonat (false :: s) = 2 * (tonat s).
axiom prop5 s : 0 <= tonat s.
axiom exp_prop1 x : x ^ 0 = oneR.
axiom exp_prop2 x : x ^ 1 = x.
axiom exp_prop3 (x : R) (a b : int) :  x ^ (a + b) = x ^ a *** x ^ b.
axiom exp_prop4 (x : R) (a b : int) :  x ^ (a * b) = (x ^ a) ^ b.
axiom exp_prop5 (x : R) :  x *** oneR = x.
axiom exp_prop6 (a b c : R) :  (a *** b) *** c = a *** (b *** c).
axiom exp_prop7 (a b : R) :  (a *** b) = b *** a.
axiom to_uintP: forall (x y : R), valR (x *** y) = valR x * valR y %% P.
axiom rsize_prop (r : R) : size (Rbits r) = Rsize.
axiom bitsR_prop a b : tonat a = valR b => size a = Rsize => bitsR a = b.
axiom valR_one : valR oneR = 1.



(* Embedding into ring theory *)
require ZModP.
clone import ZModP.ZModField as Zp with
        op p <= P
        rename "zmod" as "zp"
        proof prime_p by exact P_prime.

op (^^) (x : zp)(n : int) : zp = inzp (asint x ^ n).

abbrev ImplFp x y = valR x = asint y.

module Spec = {
  proc ith_bit(r : R, ctr : int) = { 
    return (ith_bitR r ctr);
  }
  proc mul(a : R, b : R) = { 
    return (a *** b);
  }

  proc swapr(a : R, b : R, c : bool) = { 
    return c ? (b,a) : (a, b);
  }

 proc mulm(a b: zp): zp = {
    var r;
    r <- a * b;
    return r;
 }

 proc expm(a : zp,  b: int): zp = {
    var r;
    r <- a ^^ b;
    return r;
 }

}.

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
rewrite ( drop_nth witness (ctr - 1) ). progress. smt(). 
qed.


lemma hast5  : forall xs, ! (has_true xs) => (bs2int xs) = 0.
elim. smt. smt. qed.


lemma hast4  : forall xs (x : R), ! (has_true xs) => x ^ (tonat xs) = oneR.
progress. rewrite /tonat. rewrite hast5. auto.
rewrite /(^). simplify. smt.
qed.

lemma hast6  : forall xs (x : int), ! (has_true xs) => x ^ (tonat xs) = 1.
progress. rewrite /tonat. rewrite hast5. auto.
smt.
qed.



module M1 = {

  proc expm_spec (x:R, n:bits) : R = {
    return x ^ (tonat n); 
  }  

  proc expm_naive (x:R, n:bits) : R = {
    
    var x1, x2, x3, x4 : R;
    var ctr:int;
    var bit, d, p :bool;    
    d <- ith_bit n (size n - 1);
    (x1,x2,x3, x4) <- (oneR,oneR,x,x *** x);

    ctr <- size n - 1;
    p <- d;
    (x1,x3) <- d ? (x3,x1) : (x1,x3);
    (x2,x4) <- d ? (x4,x2) : (x2,x4);

    while (0 < ctr) {
      ctr <- (ctr - 1);
      p <- d;
      d <- d || ith_bit n ctr;
      (x1,x2) <- (ith_bit n ctr) ? ((x1***x2), (x2***x2)) : ((x1***x1), (x1***x2));
      (x1,x3) <- d ^ p ? (x3,x1) : (x1,x3);
      (x2,x4) <- d ^ p ? (x4,x2) : (x2,x4);
    }
    return x1;
  }  
}.



lemma exp_naive_correct xx nn : 
  equiv[ M1.expm_naive ~ M1.expm_spec : ={arg} /\ arg{1} = (xx, nn){1} /\  0 < size nn ==> ={res}].
proof. proc. 
while {1} (d{1} = has_true (drop ctr n) /\ ctr < size n /\ (has_true (drop ctr n) =>
  (x1 = x ^ tonat (drop ctr n) 
    /\ x2 = x1 *** x  /\ (x3,x4){1} = (oneR, oneR)) ) /\ (!has_true (drop ctr n) => x1 = oneR /\ x2 = oneR /\ x3 = x /\ x4 = x *** x) ){1} (ctr{1}). 
progress.
wp. skip.  progress. 
rewrite (drop_nth witness (ctr{hr} - 1)). smt(). simplify. rewrite /ith_bit. smt().
smt(). 
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
  = x{hr} *** x{hr} ^ (2 * bs2int (drop ctr{hr} n{hr})).
rewrite exp_prop3. rewrite exp_prop2. auto.
have ->: x{hr} ^ (2 * bs2int (drop ctr{hr} n{hr}))
 = x{hr} ^ (bs2int (drop ctr{hr} n{hr})) *** x{hr} ^ (bs2int (drop ctr{hr} n{hr})).
smt.
have -> : bs2int (drop ctr{hr} n{hr})  = 0.
rewrite  hast5. auto. auto. rewrite exp_prop1. rewrite exp_prop5. rewrite exp_prop5. auto.
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
have -> : x1{hr} *** x2{hr} = x{hr} ^ tonat (drop ctr{hr} n{hr}) *** x{hr} ^ tonat (drop ctr{hr} n{hr}) *** x{hr}.
rewrite H0. auto.
rewrite H0. auto. 
rewrite H0. auto.  
pose n := tonat (drop ctr{hr} n{hr}).
smt (exp_prop6).
pose n := tonat (drop ctr{hr} n{hr}).
rewrite exp_prop3. rewrite exp_prop2. smt.
progress.
have z: has_true (drop ctr{hr} n{hr}) = true. 
have x : drop (ctr{hr} - 1) n{hr} = ith_bit n{hr} (ctr{hr} - 1) :: drop ctr{hr} n{hr}.
rewrite (drop_nth witness (ctr{hr} - 1)).  smt(). rewrite H4.
simplify. rewrite - H4. rewrite /ith_bit. auto.
smt.
rewrite z.
have -> : true ^ true  = false. smt(@Bool). simplify.
have -> : x1{hr} *** x1{hr} = x{hr} ^ tonat (drop ctr{hr} n{hr}) *** x{hr} ^ tonat (drop ctr{hr} n{hr}).
smt. 
rewrite (drop_nth witness (ctr{hr} - 1)).  smt(). smt.
have -> : (has_true (drop ctr{hr} n{hr}) || ith_bit n{hr} (ctr{hr} - 1)) = true.
rewrite (hast1 n{hr} ctr{hr} _). progress. smt().
smt(). rewrite H3. auto.
case (has_true (drop ctr{hr} n{hr})). progress. 
have -> : true ^ true = false. smt().
simplify. 
case ( ith_bit n{hr} (ctr{hr} - 1)).
progress. rewrite H0. auto.
rewrite H0. auto. rewrite H0. auto.
smt(exp_prop1 exp_prop2 exp_prop3 exp_prop4 exp_prop5 exp_prop6).
smt(exp_prop1 exp_prop2 exp_prop3 exp_prop4 exp_prop5 exp_prop6).
progress.
smt(exp_prop1 exp_prop2 exp_prop3 exp_prop4 exp_prop5 exp_prop6).
rewrite hast1. smt(). rewrite H3.
case (has_true (drop ctr{hr} n{hr})).
progress.
smt(exp_prop1 exp_prop2 exp_prop3 exp_prop4 exp_prop5 exp_prop6).
smt(exp_prop1 exp_prop2 exp_prop3 exp_prop4 exp_prop5 exp_prop6).

rewrite hast1. smt(). rewrite H3.
case (has_true (drop ctr{hr} n{hr})).
progress.
smt(exp_prop1 exp_prop2 exp_prop3 exp_prop4 exp_prop5 exp_prop6).
smt(exp_prop1 exp_prop2 exp_prop3 exp_prop4 exp_prop5 exp_prop6).

rewrite hast1. smt(). rewrite H3.
case (has_true (drop ctr{hr} n{hr})).
progress.
smt(exp_prop1 exp_prop2 exp_prop3 exp_prop4 exp_prop5 exp_prop6).
smt(exp_prop1 exp_prop2 exp_prop3 exp_prop4 exp_prop5 exp_prop6).
rewrite hast1. smt(). rewrite H3.
case (has_true (drop ctr{hr} n{hr})).
progress.
smt(exp_prop1 exp_prop2 exp_prop3 exp_prop4 exp_prop5 exp_prop6).
smt(exp_prop1 exp_prop2 exp_prop3 exp_prop4 exp_prop5 exp_prop6).
rewrite hast1. smt(). rewrite H3.
smt.
rewrite hast1. smt(). rewrite H3.
smt.
smt().
wp.  skip.  progress.
rewrite (drop_nth witness (size n{2} - 1)). smt(). simplify.
rewrite /ith_bit. smt(@List).
smt().
rewrite hast2. smt(). rewrite H0. simplify.
rewrite hast3. smt(). rewrite hast2. smt(). rewrite H0. rewrite prop1. simplify. rewrite /(^). simplify. smt.
rewrite hast2. smt(). rewrite H0. simplify. auto.
rewrite hast2. smt(). rewrite H0. auto.
   rewrite hast2. smt(). rewrite H0. auto.
   rewrite hast2. smt(). rewrite H0. auto.
   rewrite hast2. smt(). rewrite H0. auto.
 rewrite hast2. smt(). rewrite H0. auto.
rewrite hast2. smt(). rewrite H0. auto.
smt(). 
have : ctr_L <= 0. smt().
case (has_true (drop ctr_L n{2})).
progress.
rewrite H2. auto.
have -> : (drop ctr_L n{2}) = n{2}. smt.
auto.
progress.
have -> : x1_L = oneR. smt. 
have y : !has_true n{2}. smt. 
rewrite  hast4. auto. auto.
qed.

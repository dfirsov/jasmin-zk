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

op ith_bit (n : bits) (x : int) : bool = nth witness n x.
op has_true (bs : bits) : bool = has (fun x => x = true) bs.

op P : int.

op Rsize : int.
op Rbits (r : R) : bits.
op bitsR (r : bits) : R.
op as_w64 (x : bool) : W64.t  = x ? W64.one : W64.zero.
op ith_bitR (r : R) (x : int) : W64.t = as_w64 (ith_bit (Rbits r) x).
op as_bool (x : W64.t) : bool  = (x = W64.one).
op ith_bitlist (n : bits) (x : int)  : W64.t = as_w64 (ith_bit n x).
op valR (x : R) : int = bs2int (Rbits x).
op of_int (x : int) : R = bitsR (int2bs Rsize x).
op ImplR (p : R) (P : int) = (valR p = P).

op oneR : R = of_int 1.

op ( *** ) (a b : R) : R = of_int (valR a * valR b %% P).
op (^) (x : R) (n : int) : R = if n < 0 then iterop (-n) ( *** ) x oneR else iterop n ( *** ) x oneR.


lemma iteropi : forall i, 0 <= i => forall  b,
  iterop (i + 1) ( *** ) b oneR = b *** iterop i ( *** ) b oneR.
apply intind.
progress. 
 have ->: iterop 0 ( *** ) b oneR = oneR.
smt(@IterOp).
  have ->: iterop 1 ( *** ) b oneR = b.
smt(@IterOp).
admit.
progress. 
rewrite /iterop. 
simplify. rewrite iteriS. auto. simplify. 
have ->: (i + 2) = (i+1) + 1. smt().
rewrite iteriS. smt().
rewrite iteriS. smt().
simplify. smt().
qed.


lemma prop1 : bs2int [true] = 1.
rewrite - (bs2int1 0). rewrite /nseq. rewrite iter0.  auto. auto. 
qed.

lemma prop2   : bs2int [false] = 0.
rewrite - (bs2int_nseq_false 1).
rewrite nseq1. auto.
qed.

lemma prop3 s : bs2int (true :: s) = 2 * (bs2int s) + 1.
smt(bs2int_cons).
qed.

lemma prop4 s : bs2int (false :: s) = 2 * (bs2int s).
smt(bs2int_cons).
qed.

lemma prop5 s : 0 <= bs2int s.
apply bs2int_ge0.
qed.

axiom Rsize_max : Rsize < W64.max_uint.
axiom Rsize_pos : 0 < Rsize.
axiom P_prime: prime P.

axiom qqq n x : ith_bitlist (Rbits n) x = ith_bitR n x.
axiom www n x : size n = Rsize => ith_bitlist n x = ith_bitR (bitsR n) x.
axiom iii n : size (Rbits n) = Rsize.

lemma exp_prop1 x : x ^ 0 = oneR.
smt (@IterOp). qed.

lemma exp_prop2 x : x ^ 1 = x.
smt (@IterOp). qed.



axiom exp_prop5 (x : R) : valR x < P =>  x *** oneR = x. 



axiom exp_prop6 (a b c : R) :  (a *** b) *** c = a *** (b *** c).
axiom exp_prop7 (a b : R) :  a *** b = b *** a.

axiom to_uintP: forall (x y : R), valR (x *** y) = valR x * valR y %% P.
axiom rsize_prop (r : R) : size (Rbits r) = Rsize.
axiom bitsR_prop a b : bs2int a = valR b => size a = Rsize => bitsR a = b.
axiom valR_one : valR oneR = 1.


lemma exp_prop3' x : forall i, 0 <= i =>  x ^ (1 + i) = x *** x ^ i.
progress. rewrite /(^).
have -> : 1 + i < 0 = false. smt().
simplify.
have -> : i < 0 = false. smt(). simplify.
rewrite - iteropi. auto.
smt().
qed.

    

lemma exp_prop3 (x : R) : forall (a : int), 0 <= a => forall b,  0 <= b => x ^ (a + b) = x ^ a *** x ^ b.
apply intind. progress. rewrite exp_prop1. admit.
progress.
have ->: (i + 1) = (1 + i). smt().
have ->: x ^ (1 + i) = x *** x ^ i.
smt (@IterOp).
rewrite exp_prop6.
rewrite - H0.
smt (exp_prop3').
have ->:  (1 + i + b) =  (1 + (i + b)). smt().
smt (exp_prop3').
qed.


lemma exp_prop4' a b : forall i, 0 <= i => (a *** b) ^ i = a ^ i *** b ^ i.
apply intind. progress. smt.
progress.
have -> : (i + 1) = (1 + i). smt().
rewrite exp_prop3'. auto.
rewrite exp_prop3'. auto.
rewrite exp_prop3'. auto.
rewrite H0.
smt (exp_prop7 exp_prop6).
qed.

lemma exp_prop4 (x : R)  : forall (a : int), 0 <= a => forall b, 0 <= b =>  x ^ (a * b) = (x ^ a) ^ b.
apply intind.
progress. rewrite exp_prop1. admit.
progress. 
have -> : ((i + 1) * b) = (i * b + b). smt().
rewrite  exp_prop3. smt(). auto.
rewrite H0. auto.
have -> : (i + 1) = 1 + i. smt().
rewrite  exp_prop3'. auto.
rewrite exp_prop4'. auto. smt(exp_prop7).
qed.


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


lemma hast4  : forall xs (x : R), ! (has_true xs) => x ^ (bs2int xs) = oneR.
progress. rewrite hast5. auto.
rewrite /(^). simplify. smt.
qed.

lemma hast6  : forall xs (x : int), ! (has_true xs) => x ^ (bs2int xs) = 1.
progress. rewrite hast5. auto.
smt.
qed.



module M1 = {

  proc expm_spec (x:R, n:bits) : R = {
    return x ^ (bs2int n); 
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
  equiv[ M1.expm_naive ~ M1.expm_spec : ={arg} /\ arg{1} = (xx, nn){1}  /\  0 < size nn ==> ={res}].
proof. proc. 
while {1} (d{1} = has_true (drop ctr n) /\ ctr < size n /\ (has_true (drop ctr n) =>
  (x1 = x ^ bs2int (drop ctr n) 
    /\ x2 = x1 *** x  /\ (x3,x4){1} = (oneR, oneR)) ) /\ (!has_true (drop ctr n) => x1 = oneR /\ x2 = oneR /\ x3 = x /\ x4 = x *** x) /\ valR x1 < P){1}   (ctr{1}). 
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
rewrite  bs2int_cons.
rewrite /b2i. simplify.
have -> : x{hr} ^ (1 + 2 * bs2int (drop ctr{hr} n{hr}))
  = x{hr} *** x{hr} ^ (2 * bs2int (drop ctr{hr} n{hr})).
rewrite exp_prop3. auto. smt(prop5). rewrite exp_prop2. auto.
have ->: x{hr} ^ (2 * bs2int (drop ctr{hr} n{hr}))
 = x{hr} ^ (bs2int (drop ctr{hr} n{hr})) *** x{hr} ^ (bs2int (drop ctr{hr} n{hr})).
smt.
have -> : bs2int (drop ctr{hr} n{hr})  = 0.
rewrite  hast5. auto. auto. rewrite exp_prop1. rewrite exp_prop5. smt. rewrite exp_prop5. admit. auto.
simplify.
move => casef. rewrite casef. 
  have -> : true ^ true  = false. smt(@Bool). simplify.
  have -> : (drop (ctr{hr} - 1) n{hr}) = true :: (drop (ctr{hr} ) n{hr}).  
  rewrite (drop_nth witness (ctr{hr} - 1)). 
progress. smt().
smt(). 
simplify.
rewrite /ith_bit in H5. rewrite H5. auto.
rewrite prop3. 
have -> : x1{hr} *** x2{hr} = x{hr} ^ bs2int (drop ctr{hr} n{hr}) *** x{hr} ^ bs2int (drop ctr{hr} n{hr}) *** x{hr}.
rewrite H0. auto.
rewrite H0. auto. 
rewrite H0. auto.  
pose n := bs2int (drop ctr{hr} n{hr}).
smt (exp_prop6).
pose n := bs2int (drop ctr{hr} n{hr}).
rewrite exp_prop3. smt (prop5). auto. rewrite exp_prop2. smt.
progress.
have z: has_true (drop ctr{hr} n{hr}) = true. 
have x : drop (ctr{hr} - 1) n{hr} = ith_bit n{hr} (ctr{hr} - 1) :: drop ctr{hr} n{hr}.
rewrite (drop_nth witness (ctr{hr} - 1)).  smt(). rewrite H5.
simplify. rewrite - H5. rewrite /ith_bit. auto.
smt.
rewrite z.
have -> : true ^ true  = false. smt(@Bool). simplify.
have -> : x1{hr} *** x1{hr} = x{hr} ^ bs2int (drop ctr{hr} n{hr}) *** x{hr} ^ bs2int (drop ctr{hr} n{hr}).
smt. 
rewrite (drop_nth witness (ctr{hr} - 1)).  smt(). timeout 20. smt.
have -> : (has_true (drop ctr{hr} n{hr}) || ith_bit n{hr} (ctr{hr} - 1)) = true.
rewrite (hast1 n{hr} ctr{hr} _). progress. smt().
smt(). rewrite H4. auto.
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
rewrite hast1. smt(). rewrite H4.
case (has_true (drop ctr{hr} n{hr})).
progress.
smt(exp_prop1 exp_prop2 exp_prop3 exp_prop4 exp_prop5 exp_prop6).
smt(exp_prop1 exp_prop2 exp_prop3 exp_prop4 exp_prop5 exp_prop6).

rewrite hast1. smt(). rewrite H4.
case (has_true (drop ctr{hr} n{hr})).
progress.
smt(exp_prop1 exp_prop2 exp_prop3 exp_prop4 exp_prop5 exp_prop6).
smt(exp_prop1 exp_prop2 exp_prop3 exp_prop4 exp_prop5 exp_prop6).

rewrite hast1. smt(). rewrite H4.
case (has_true (drop ctr{hr} n{hr})).
progress.
smt(exp_prop1 exp_prop2 exp_prop3 exp_prop4 exp_prop5 exp_prop6).
smt(exp_prop1 exp_prop2 exp_prop3 exp_prop4 exp_prop5 exp_prop6).
rewrite hast1. smt(). rewrite H4.
case (has_true (drop ctr{hr} n{hr})).
progress.
smt(exp_prop1 exp_prop2 exp_prop3 exp_prop4 exp_prop5 exp_prop6).
smt(exp_prop1 exp_prop2 exp_prop3 exp_prop4 exp_prop5 exp_prop6).
rewrite hast1. smt(). rewrite H4.
smt.
rewrite hast1. smt(). rewrite H4.
smt.
admit.
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
admit.
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

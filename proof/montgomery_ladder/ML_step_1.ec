require import AllCore IntDiv CoreMap List.

require import JModel.
require import BitEncoding.
import BS2Int.

type R.
type bits = bool list.


op P : int.
op Rsize : int.
op valR (x : R) : int.
op of_int (x : int) : R.

op idR : R.
op ( ** ) : int -> int -> int.

op ( *** ) (a b : R) : R. (* = of_int ((valR a ** valR b) %% P). *)

op Rbits (r : R) : bits = int2bs Rsize (valR r).
op bitsR (r : bits) : R = of_int (bs2int r).

module type BasicOps = {
  proc ith_bit (r : R, p : W64.t) : W64.t
  proc opr (p : R, a : R, b : R) : R
  proc swapr (a : R, b : R, c : W64.t) : R * R
}.



op ith_bit (n : bits) (x : int) : bool = nth false n x.
op has_true (bs : bits) : bool = has (fun x => x = true) bs.


op as_w64 (x : bool) : W64.t  = x ? W64.one : W64.zero.
op ith_bitR (r : R) (x : int) : W64.t = as_w64 (ith_bit (Rbits r) x).
op as_bool (x : W64.t) : bool  = (x = W64.one).
op ith_bitlist (n : bits) (x : int)  : W64.t = as_w64 (ith_bit n x).
op ImplR (p : R) (P : int) = (valR p = P).
op (^) (x : R) (n : int) : R = if n < 0 then iterop (-n) ( *** ) x idR else iterop n ( *** ) x idR.


lemma qqq n x : ith_bitlist (Rbits n) x = ith_bitR n x.
rewrite /ith_bitR.
rewrite /ith_bitlist. auto.
qed.



axiom Rsize_max : Rsize < W64.max_uint.
axiom Rsize_pos : 0 < Rsize.
axiom P_pos: 1 < P.
axiom valr_pos x : 0 <= valR x.
axiom iii n : size (Rbits n) = Rsize.
axiom valr_ofint x : 0 <= x < P => valR (of_int x) = x.
axiom ofint_valr x : of_int (valR x) = x.
axiom rbits_bitsr x : size x = Rsize => Rbits (bitsR x) = x.
axiom bitsr_rbits x : bitsR (Rbits x) = x.
axiom exp_prop7 (a b : R) :  a *** b = b *** a.
axiom exp_prop6 (a b c : R) :  (a *** b) *** c = a *** (b *** c).
axiom exp_prop5 (x : R) : valR x < P => x *** idR = x. 
axiom idR_leP :  valR idR < P.
axiom mult_valr a b : valR (a *** b) < P.



lemma mod_lemm (a b c m : int) : ((a * b %% m) * c) %% m = ((a * b) * c) %% m. 
smt (modzMml modzMm modzMmr).
qed.

    


(* lemma to_uintP: forall (x y : R), valR (x *** y) = (valR x ** valR y) %% P. *)
(* progress. rewrite /( *** ). smt. *)
(* qed. *)

lemma bitsR_prop a b : bs2int a = valR b => size a = Rsize => bitsR a = b.
proof. rewrite /valR.
progress.
have ->: a = Rbits b. smt.
smt(bitsr_rbits).
qed.


lemma www n x : size n = Rsize => ith_bitlist n x = ith_bitR (bitsR n) x.
rewrite /ith_bitR.
rewrite /ith_bitlist. auto.
smt(rbits_bitsr).
qed.

(* lemma valR_one : valR idR = 0. *)
(* rewrite /oneR. rewrite valr_ofint. auto. *)
(* smt. auto. *)
(* qed. *)



(* progress. rewrite /( *** ).  *)
(* have -> : valR idR = 0. smt. simplify. *)
(* have ->: (valR x %% P) = valR x.  *)
(* have : 0 <= valR x. smt(valr_pos). *)
(* smt. *)
(* smt(ofint_valr). *)
(* qed. *)


lemma iteropi : forall i, 0 <= i => forall  b, valR b < P =>
  iterop (i + 1) ( *** ) b idR = b *** iterop i ( *** ) b idR.
apply intind.
progress. 
 have ->: iterop 0 ( *** ) b idR = idR.
smt(@IterOp).
  have ->: iterop 1 ( *** ) b idR = b.
smt(@IterOp).
rewrite exp_prop5. auto.
progress. progress.
rewrite /iterop. 
simplify. rewrite iteriS. auto. simplify. 
have ->: (i + 2) = (i+1) + 1. smt().
rewrite iteriS. smt().
rewrite iteriS. smt().
simplify. smt().
qed.

search bs2int.
lemma prop1 : bs2int [true] = 1.
rewrite bs2int_cons. rewrite bs2int_nil. simplify. 
  auto. 
qed.

lemma prop2   : bs2int [false] = 0.
rewrite bs2int_cons. rewrite bs2int_nil. simplify. 
  auto. 
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


lemma exp_prop1 x : x ^ 0 = idR.
smt (@IterOp). qed.

lemma exp_prop2 x : x ^ 1 = x.
smt (@IterOp). qed.







(* rewrite /( *** ). *)
(* have : (valR a ** valR b %% P) < P. smt. *)
(* progress. smt.  *)
(* qed. *)



lemma exp_prop3' x : forall i, 0 <= i => valR x < P => x ^ (1 + i) = x *** x ^ i.
progress. rewrite /(^).
have -> : 1 + i < 0 = false. smt().
simplify.
have -> : i < 0 = false. smt(). simplify.
rewrite - iteropi. auto. auto.
smt().
qed.

    


lemma exp_valr x : forall i, 0 <= i => valR x < P =>  valR (x ^ i) < P.
apply intind.
progress. rewrite exp_prop1. smt(idR_leP).
progress. 
have -> : i + 1 = 1 + i. smt().
rewrite exp_prop3'. auto. auto.
smt(mult_valr).
qed.

lemma exp_prop3 (x : R) : forall (a : int), 0 <= a => forall b,  0 <= b => valR x < P => x ^ (a + b) = x ^ a *** x ^ b.
apply intind. progress. rewrite exp_prop1.   smt (exp_prop7 exp_prop5 exp_valr).
progress.
have ->: (i + 1) = (1 + i). smt().
have ->: x ^ (1 + i) = x *** x ^ i.
rewrite /(^).  
have ->: 1 + i < 0 = false. smt(). simplify.
have ->: i < 0 = false. smt(). simplify.
have ->: 1 + i = i + 1. smt().
rewrite iteropi. auto. auto. auto.
rewrite exp_prop6.
rewrite - H0. auto. auto.
smt (exp_prop3').
qed.


lemma exp_prop4' a b : forall i, 0 <= i => valR a < P => valR b < P => (a *** b) ^ i = a ^ i *** b ^ i.
apply intind. progress. smt.
progress.
have -> : (i + 1) = (1 + i). smt().
rewrite exp_prop3'. auto. smt.
rewrite exp_prop3'. auto. auto.
rewrite exp_prop3'. auto. auto.
rewrite H0. auto. auto.
smt (exp_prop7 exp_prop6).
qed.


lemma oner_exp : forall b, 0 <= b => idR = idR ^ b.
apply intind. progress. smt(exp_prop1).
progress. 
have -> : (i+1) = 1 + i. smt().
rewrite exp_prop3'. auto. smt.
rewrite - H0.
rewrite exp_prop5. smt.
auto.
qed.


lemma exp_prop4 (x : R)  : forall (a : int), 0 <= a => forall b, 
  0 <= b => valR x < P =>  x ^ (a * b) = (x ^ a) ^ b.
apply intind.
progress. rewrite exp_prop1. smt(oner_exp).
progress. 
have -> : ((i + 1) * b) = (i * b + b). smt().
rewrite  exp_prop3. smt(). auto. auto.
rewrite H0. auto. auto.
have -> : (i + 1) = 1 + i. smt().
rewrite  exp_prop3'. auto. auto.
rewrite exp_prop4'. auto. auto. smt (exp_valr). smt(exp_prop7).
qed.


require import Ith_Bit64.
(* op as_word (x : bool) : W64.t  = x ? W64.one : W64.zero. *)
(* op ith_bitword64 (n : W64.t) (x : int)  : W64.t = as_word (n.[x]). *)

module Spec = {
  proc ith_bit(r : R, ctr : int) = {
    return (ith_bitR r ctr);
  }
  proc mul(a : R, b : R) = {
    return (a *** b);
  }


  proc ith_bit64 (k:W64.t, ctr:int) : W64.t = {
    return ith_bitword64 k ctr;
  }


  proc swapr(a : R, b : R, c : bool) = {
    return c ? (b,a) : (a, b);
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


module M1 = {

  proc iterop_spec (x:R, n:bits) : R = {
    return x ^ (bs2int n); 
  }  

  proc iterop_naive (x:R, n:bits) : R = {
    
    var x1, x2, x3, x4 : R;
    var ctr:int;
    var bit, d, p :bool;    
    d <- ith_bit n (size n - 1);
    (x1,x2,x3, x4) <- (idR,idR,x,x *** x);

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



lemma iterop_spec_naive xx nn : 
  equiv[ M1.iterop_naive ~ M1.iterop_spec : ={arg} /\ arg{1} = (xx, nn){1}  /\  0 < size nn
  /\ valR x{1} < P ==> ={res}].
proof. proc. 
while {1} (d{1} = has_true (drop ctr n) /\ ctr < size n /\ (has_true (drop ctr n) =>
  (x1 = x ^ bs2int (drop ctr n) 
    /\ x2 = x1 *** x  /\ (x3,x4){1} = (idR, idR)) ) /\ (!has_true (drop ctr n) => x1 = idR /\ x2 = idR /\ x3 = x /\ x4 = x *** x) /\ valR x1 < P /\  valR x < P){1}   (ctr{1}). 
progress.
wp. skip.  progress. 
rewrite (drop_nth false (ctr{hr} - 1)). smt(). simplify. rewrite /ith_bit. smt().
smt(). 
case (ith_bit n{hr} (ctr{hr} - 1 )). progress.
  case (!has_true (drop ctr{hr} n{hr})). move => casef.  
   rewrite casef.
  have -> : true ^ false  = true. smt(@Bool). simplify.
  have -> : x3{hr} = x{hr}. smt(). 
  have -> : (drop (ctr{hr} - 1) n{hr}) = true :: (drop (ctr{hr} ) n{hr}).  
  rewrite (drop_nth false (ctr{hr} - 1)).  smt(). smt(). 
rewrite  bs2int_cons.
rewrite /b2i. simplify.
have -> : x{hr} ^ (1 + 2 * bs2int (drop ctr{hr} n{hr}))
  = x{hr} *** x{hr} ^ (2 * bs2int (drop ctr{hr} n{hr})).
rewrite exp_prop3. auto. smt(prop5). auto. rewrite exp_prop2. auto.
have ->: x{hr} ^ (2 * bs2int (drop ctr{hr} n{hr}))
 = x{hr} ^ (bs2int (drop ctr{hr} n{hr})) *** x{hr} ^ (bs2int (drop ctr{hr} n{hr})).
smt.
have -> : bs2int (drop ctr{hr} n{hr})  = 0.
rewrite  hast5. auto. auto. rewrite exp_prop1. rewrite exp_prop5. smt. rewrite exp_prop5. auto. auto.
simplify.
move => casef. rewrite casef. 
  have -> : true ^ true  = false. smt(@Bool). simplify.
  have -> : (drop (ctr{hr} - 1) n{hr}) = true :: (drop (ctr{hr} ) n{hr}).  
  rewrite (drop_nth false (ctr{hr} - 1)). 
progress. smt().
smt(). 
simplify.
rewrite /ith_bit in H6. rewrite H6. auto.
rewrite prop3. 
have -> : x1{hr} *** x2{hr} = x{hr} ^ bs2int (drop ctr{hr} n{hr}) *** x{hr} ^ bs2int (drop ctr{hr} n{hr}) *** x{hr}.
rewrite H0. auto.
rewrite H0. auto. 
rewrite H0. auto.  
pose n := bs2int (drop ctr{hr} n{hr}).
smt (exp_prop6).
pose n := bs2int (drop ctr{hr} n{hr}).
rewrite exp_prop3. smt (prop5). auto. auto. rewrite exp_prop2.
have ->: (2 * n) = n + n. smt().
rewrite exp_prop3. smt. smt. auto. auto.
progress.
have z: has_true (drop ctr{hr} n{hr}) = true. 
have x : drop (ctr{hr} - 1) n{hr} = ith_bit n{hr} (ctr{hr} - 1) :: drop ctr{hr} n{hr}.
rewrite (drop_nth false (ctr{hr} - 1)).  smt(). rewrite H6.
simplify. rewrite - H6. rewrite /ith_bit. smt. smt.
rewrite z.
have -> : true ^ true  = false. smt(@Bool). simplify.
have -> : x1{hr} *** x1{hr} = x{hr} ^ bs2int (drop ctr{hr} n{hr}) *** x{hr} ^ bs2int (drop ctr{hr} n{hr}).
smt. 
rewrite (drop_nth false (ctr{hr} - 1)).  smt(). timeout 20. smt.
have -> : (has_true (drop ctr{hr} n{hr}) || ith_bit n{hr} (ctr{hr} - 1)) = true.
rewrite (hast1 n{hr} ctr{hr} _). progress. smt().
smt(). rewrite H5. auto.
case (has_true (drop ctr{hr} n{hr})). progress. 
have -> : true ^ true = false. smt().
simplify. 
case ( ith_bit n{hr} (ctr{hr} - 1)).
progress. rewrite H0. auto.
rewrite H0. auto. rewrite H0. auto.
smt(exp_prop1 exp_prop2 exp_prop3 exp_prop4 exp_prop5 exp_prop6 exp_prop7).
smt(exp_prop1 exp_prop2 exp_prop3 exp_prop4 exp_prop5 exp_prop6 exp_prop7).
progress.
smt(exp_prop1 exp_prop2 exp_prop3 exp_prop4 exp_prop5 exp_prop6 exp_prop7).
rewrite hast1. smt(). rewrite H5.
case (has_true (drop ctr{hr} n{hr})).
progress.
smt(exp_prop1 exp_prop2 exp_prop3 exp_prop4 exp_prop5 exp_prop6 exp_prop7).
smt(exp_prop1 exp_prop2 exp_prop3 exp_prop4 exp_prop5 exp_prop6 exp_prop7).
rewrite hast1. smt(). rewrite H5.
case (has_true (drop ctr{hr} n{hr})).
progress.
smt(exp_prop1 exp_prop2 exp_prop3 exp_prop4 exp_prop5 exp_prop6 exp_prop7).
smt(exp_prop1 exp_prop2 exp_prop3 exp_prop4 exp_prop5 exp_prop6 exp_prop7).
rewrite hast1. smt(). rewrite H5.
case (has_true (drop ctr{hr} n{hr})).
progress.
smt(exp_prop1 exp_prop2 exp_prop3 exp_prop4 exp_prop5 exp_prop6 exp_prop7).
smt(exp_prop1 exp_prop2 exp_prop3 exp_prop4 exp_prop5 exp_prop6 exp_prop7).
rewrite hast1. smt(). rewrite H5.
case (has_true (drop ctr{hr} n{hr})).
progress.
smt(exp_prop1 exp_prop2 exp_prop3 exp_prop4 exp_prop5 exp_prop6 exp_prop7).
smt(exp_prop1 exp_prop2 exp_prop3 exp_prop4 exp_prop5 exp_prop6 exp_prop7).
rewrite hast1. smt(). rewrite H5.
smt.
rewrite hast1. smt(). rewrite H5.
smt.
smt.
smt (mult_valr).
wp.  skip.  progress.
rewrite (drop_nth false (size n{2} - 1)). smt(). simplify.
rewrite /ith_bit. smt(@List).
smt().
rewrite hast2. smt(). rewrite H1. simplify.
rewrite hast3. smt(). rewrite hast2. smt(). rewrite H1. rewrite prop1. simplify. rewrite /(^). simplify. smt.
rewrite hast2. smt(). rewrite H1. simplify. auto.
rewrite hast2. smt(). rewrite H1. auto.
   rewrite hast2. smt(). rewrite H1. auto.
   rewrite hast2. smt(). rewrite H1. auto.
   rewrite hast2. smt(). rewrite H1. auto.
 rewrite hast2. smt(). rewrite H1. auto.
rewrite hast2. smt(). rewrite H1. auto.
smt.
smt(). 
have : ctr_L <= 0. smt().
case (has_true (drop ctr_L n{2})).
progress.
rewrite H3. auto.
have -> : (drop ctr_L n{2}) = n{2}. smt.
auto.
progress.
have -> : x1_L = idR. smt. 
have y : !has_true n{2}. smt. 
rewrite  hast4. auto. auto.
qed.

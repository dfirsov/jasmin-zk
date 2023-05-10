require import AllCore IntDiv CoreMap List.

from Jasmin require import JModel.
(* require import JBigNum. *)
(* require import Fp_w64x4_extract_mulm. *)




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

  
  (* proc ith_bit (kk:W64.t Array4.t, ctr:W64.t) : W64.t = { *)
    
  (*   var bit:W64.t; *)
  (*   var c1:W64.t; *)
  (*   var c2:W64.t; *)
  (*   var r:W64.t; *)
    
  (*   c1 <- (ctr `>>` (W8.of_int 6)); *)
  (*   c2 <- (ctr - (c1 * (W64.of_int 64))); *)
  (*   r <- kk.[(W64.to_uint c1)]; *)
  (*   bit <@ ith_bit64 (r, c2); *)
  (*   return (bit); *)
  (* } *)

  
}.



lemma qqq x : 0 < x < 64 => W64.one.[x] = false.
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


(* lemma ith_bit_lemmaEq : *)
(*       equiv[ MM.ith_bit ~ M.ith_bit : ={arg} ==> ={res}]. *)
(* proc. *)
(* seq 2 4 : (={c1, c2,kk}). wp. *)
(* skip. progress. *)
(* have -> : 63 = 2^6 - 1. smt(). *)
(* rewrite and_mod. auto. simplify. *)
(* have x:  to_uint (ctr{2} `>>` (of_int 6)%W8) = to_uint ctr{2} %/ 64. smt. *)
(* rewrite to_uint_eq. *)
(* auto. *)
(* rewrite to_uintB. smt. *)
(* rewrite to_uintM_small.  smt. *)
(* rewrite  shr_div_le. *)
(* auto. simplify. smt. *)
(* sim. *)
(* qed. *)



(* lemma ith_bit_lemma' : *)
(*       equiv[ M.ith_bit ~ Spec.ith_bit : arg{1}.`1 = arg{2}.`1 /\  W64.to_uint arg{1}.`2 = arg{2}.`2 /\ *)
(*  0 <= ctr{2} && ctr{2} < 256 ==> *)
(*               ={res} /\ (res{2} = W64.one \/ res{2} = W64.zero)]. *)
(* transitivity MM.ith_bit *)
(*    (={arg} ==> ={res}) *)
(*    (arg{1}.`1 = arg{2}.`1 /\  W64.to_uint arg{1}.`2 = arg{2}.`2 /\ *)
(*  0 <= ctr{2} && ctr{2} < 256 ==> *)
(*               ={res} /\ (res{2} = W64.one \/ res{2} = W64.zero)). *)
(* progress. smt(). smt(). *)
(* symmetry. conseq ith_bit_lemmaEq. auto. auto. *)
(* proc. *)
(* seq 3 0 : (to_uint c1{1} = (to_uint ctr{1} %/ 64) /\ to_uint c2{1} = (to_uint ctr{1} %% 64) /\ to_uint ctr{1} = ctr{2} *)
(*   /\ r{1} = kk{1}.[(to_uint ctr{1} %/ 64)]%Array4 /\ r{2} = kk{1} /\ 0 <= ctr{2} && ctr{2} < 256 ). *)
(* wp.  skip. progress.  *)
(* smt.  *)
(* rewrite modzE.  *)
(* have <-: to_uint (ctr{1} `>>` (of_int 6)%W8) = to_uint ctr{1} %/ 64. smt. *)
(* rewrite to_uintB. *)
(* smt. *)
(* smt. *)
(* smt. *)
(* exists* r{1}, c2{1}. elim*. progress. *)
(* call {1} (exp_ithbit r_L c2_L). skip. *)
(* progress. smt. smt.  *)
(* rewrite /ith_bitword64.  rewrite H0.  *)
(* rewrite /ith_bitR. rewrite /Rbits. rewrite /valR. *)
(* rewrite /ith_bit. *)
(* rewrite /as_word. *)
(* rewrite /as_w64. *)
(* have ->: (kk{1}.[to_uint ctr{1} %/ 64])%Array4.[to_uint ctr{1} %% 64]  *)
(*   = nth false (int2bs 256 ((valR kk{1}))%W64x4) (to_uint ctr{1}) . *)
(* rewrite - get_w2bits. *)
(* rewrite - get_to_list. *)
(* have -> : (W64.w2bits (nth witness ((to_list kk{1}))%Array4 (to_uint ctr{1} %/ 64)))  *)
(*  = ((nth witness (map W64.w2bits (to_list kk{1}))%Array4 (to_uint ctr{1} %/ 64))). *)
(* rewrite - (nth_map witness witness W64.w2bits). progress.   smt. smt. *)
(* auto. *)
(* have -> : (nth witness (map W64.w2bits ((to_list kk{1}))%Array4) *)
(*      (to_uint ctr{1} %/ 64)) *)
(*  = (nth [] (map W64.w2bits ((to_list kk{1}))%Array4) *)
(*      (to_uint ctr{1} %/ 64)).  *)
(* rewrite (nth_change_dfl [] witness). progress.  smt. smt. auto. *)
(* rewrite - (BitChunking.nth_flatten false 64 (map W64.w2bits ((to_list kk{1}))%Array4) (to_uint ctr{1})). *)
(* rewrite  List.allP. progress. timeout 5.  *)
(* have : exists z, z \in ((to_list kk{1}))%Array4 /\ x = W64.w2bits z. *)
(* apply mapP. auto. elim. progress. *)
(* have ->: (flatten (map W64.w2bits ((to_list kk{1}))%Array4))  = (int2bs 256 ((valR kk{1}))%W64x4). *)
(* have -> : (valR kk{1})%W64x4 = bs2int (flatten (map W64.w2bits ((to_list kk{1}))%Array4)).  *)
(* rewrite /bnk.  *)
(* have ->: range 0 4 = [0;1;2;3].  rewrite range_ltn. auto. *)
(* rewrite range_ltn. auto. rewrite range_ltn. auto.  *)
(* simplify. rewrite range_ltn. auto.  *)
(* simplify. rewrite range_geq. auto. auto. *)
(* rewrite big_consT. *)
(* rewrite big_consT. *)
(* rewrite big_consT. *)
(* rewrite big_consT.  *)
(* rewrite big_nil. *)
(* rewrite /to_list. *)
(* search mkseq. *)
(* print mkseqSr. *)
(* have ->: 4 = 0 + 1 + 1 + 1 + 1 . smt(). *)
(* rewrite   mkseqS. auto. *)
(* rewrite   mkseqS. auto. *)
(* rewrite   mkseqS. auto. *)
(* rewrite   mkseqS. auto. *)
(* search mkseq. *)
(* rewrite mkseq0. simplify. *)
(* search flatten. *)
(* rewrite flatten_cons. *)
(* rewrite flatten_cons. *)
(* rewrite flatten_cons. *)
(* rewrite flatten_cons.  *)
(* rewrite flatten_nil.  *)
(* rewrite cats0. *)
(* rewrite bs2int_cat. *)
(* rewrite bs2int_cat. *)
(* rewrite bs2int_cat. simplify. *)
(* smt. *)
(* have ->: 256 = size (flatten (map W64.w2bits ((to_list kk{1}))%Array4)).  *)
(* rewrite /to_list. *)
(* have ->: 4 = 0 + 1 + 1 + 1 + 1 . smt(). *)
(* rewrite   mkseqS. auto. *)
(* rewrite   mkseqS. auto. *)
(* rewrite   mkseqS. auto. *)
(* rewrite   mkseqS. auto. *)
(* rewrite mkseq0. simplify. *)
(* rewrite flatten_cons. *)
(* rewrite flatten_cons. *)
(* rewrite flatten_cons. *)
(* rewrite flatten_cons.  *)
(* rewrite flatten_nil.  *)
(* rewrite size_cat. *)
(* rewrite size_cat. *)
(* rewrite size_cat. *)
(* rewrite size_cat. *)
(* simplify. auto. *)
(* rewrite  bs2intK. auto. auto. *)
(* auto. smt(). *)
(* qed. *)

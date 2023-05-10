require import AllCore Distr Finite List.

op LessThan (n x : int) = 0 <= x < n.

lemma inveq a b : 1%r / a = 1%r / b => a = b.
smt(@Real).
qed.

lemma d_uni_sum (d : int distr) n : is_uniform d 
  => is_lossless d
  => (forall x, LessThan n x => x \in d)
  => forall (i : int),
   0 <= i => i < n =>
  mu d (LessThan i) = i%r / (size (to_seq (support d)))%r.
move => isfu isll sup.
apply intind.
simplify. rewrite /LessThan. simplify. smt(@Distr).  
progress.
have -> : 
 (i + 1)%r / (size (to_seq (support d)))%r
 = (i )%r / (size (to_seq (support d)))%r
   + 1%r / (size (to_seq (support d)))%r.
smt. 
have ->: LessThan (i + 1) = (fun x => LessThan i x \/ x = i).
apply fun_ext. move => x. simplify. rewrite /P. smt. 
rewrite mu_or. simplify.
rewrite H0. clear H0. smt(). 
rewrite /predI. rewrite /LessThan.
have -> : (fun (x : int) => (0 <= x && x < i) /\ x = i)
 = (fun (x : int) => false). smt.
have ->: mu d (fun (_ : int) => false) = 0%r. smt. simplify.
congr. 
rewrite mu1_uni_ll. smt(). 
auto. smt.
qed.

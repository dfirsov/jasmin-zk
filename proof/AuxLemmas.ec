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


op inv ['a 'b] : 'a -> ('a -> 'b) -> 'b -> 'a
 = fun d f b => 
    choiceb (fun x => f x = b) 
            d.

lemma invP ['a 'b] d (f : 'a -> 'b)  : 
    injective f 
    => forall x,  (inv d f)  (f x) = x. 
proof. move => ip x.
rewrite /inv.
pose P := fun x' => (f x' = f x). 
have : P (choiceb P d). 
apply choicebP. exists x. auto.
rewrite /P. apply ip.
qed.


lemma choiceb_dfl_cp ['a]:
  forall (P : 'a -> bool) (x0 : 'a),
 choiceb P x0 <> x0
  =>   (exists (x : 'a), P x).
smt (choiceb_dfl).
qed.

lemma choiceEx ['a 'b] d (f : 'a -> 'b) x y :  
    (inv d f) x = y
    => y <> d
    => exists z, f z = x.
proof. 
rewrite /inv.
pose P := fun x' => (f x' = x). 
move => q. rewrite -q.
move => h.
apply (choiceb_dfl_cp  P d). auto.
qed.
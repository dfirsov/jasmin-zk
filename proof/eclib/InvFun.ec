require import AllCore.

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

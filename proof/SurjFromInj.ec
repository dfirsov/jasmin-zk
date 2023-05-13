require import AllCore List.

abstract theory SurjFromInj.
type a.
type b.

op alist : a list.
op blist : b list.

op f : a -> b.

section.
declare axiom alist_uniq : uniq alist.
declare axiom blist_uniq : uniq blist.
declare axiom alist_blist_size : size alist = size blist.
declare axiom alist_full a : a \in alist.
declare axiom blist_full b : b \in blist.
declare axiom f_inj : injective f.

lemma f_surj : surjective f.
rewrite /surjective.
pose fmaped := map f alist.
have claim1 : size fmaped = size blist. smt(@List alist_blist_size).
have claim2 : uniq fmaped. rewrite /fmaped.
 apply map_inj_in_uniq. smt(f_inj). apply alist_uniq.
have claim3 : forall b, b \in fmaped. 
  have : (exists y, !(y \in fmaped )) => false. 
  elim. move => y h.
  have f1 : uniq (y :: fmaped).  smt(@List).
  have f2 : size (y :: fmaped) = size blist + 1. simplify. smt().
  have : size (y :: fmaped) <= size blist.
  apply uniq_leq_size. auto.
  smt(blist_full).
  smt().  
  smt().
move => x. 
have z : x \in map f alist. smt().
smt(@List).
qed.

end section.
end SurjFromInj.

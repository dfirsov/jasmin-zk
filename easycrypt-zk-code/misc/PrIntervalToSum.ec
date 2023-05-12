require import AllCore Distr FSet StdRing StdOrder StdBigop List.
(*---*) import RField RealOrder Bigreal BRA. 
require import Int. 

type rt, iat.

module type RunMain = {
  proc run(i:iat) : rt
}.

section.

declare module A <: RunMain.
local lemma pr_interval_to_sum_lemma' &m : forall (a : iat) (f : (glob A) -> int) 
  (P : iat -> rt -> (glob A) -> bool) (s e : int),
  0 <= e =>
  Pr[ A.run(a) @ &m : s <= f (glob A) <= s + e /\ P a res (glob A) ]
  = big predT
        (fun i => Pr[ A.run(a) @ &m : f (glob A) = i /\ P a res (glob A) ])
        (range s (s + e + 1)).
move => a f P s. apply ge0ind.
smt().
progress . 
have ->: Pr[A.run(a) @ &m : s <= f (glob A)  <= s /\ P a res (glob A)]
  = Pr[A.run(a) @ &m : s  = f (glob A) /\ P a res (glob A)].
rewrite Pr[mu_eq]. smt(). auto.
have ->: bigi predT 
              (fun (i : int) => Pr[A.run(a) @ &m : f (glob A) = i /\ P a res (glob A)]) 
              s (s + 1)
       = Pr[A.run(a) @ &m : f (glob A) = s /\ P a res (glob A) ].
rewrite big_int1. auto. 
rewrite Pr[mu_eq]. auto. auto.
progress.
have ->: 
  Pr[A.run(a) @ &m : s <= f (glob A) <= s + (n + 1) /\ P a res (glob A)]
  = Pr[A.run(a) @ &m : (s <= f (glob A) <= s + n) /\ P a res (glob A)
          \/ f (glob A) = s + (n + 1) /\ P a res (glob A) ].
rewrite Pr[mu_eq]. smt(). auto.
have ->: Pr[A.run(a) @ &m : (s <= f (glob A) <= s + n) /\ P a res (glob A)
          \/ f (glob A) = s + (n + 1) /\ P a res (glob A) ]
 = Pr[A.run(a) @ &m : (s <= f (glob A) <= s + n) /\ P a res (glob A) ]
 + Pr[A.run(a) @ &m : f (glob A) = s + (n + 1) /\ P a res (glob A) ].
rewrite Pr[mu_disjoint]. progress. smt().
auto.
have ->: bigi predT (fun (i : int) => Pr[A.run(a) @ &m : f (glob A) = i /\ P a res (glob A)] ) s (s + (n + 1) + 1)
 = Pr[A.run(a) @ &m : s <= f (glob A) <= s + n /\ P a res (glob A)] +
Pr[A.run(a) @ &m : f (glob A) = s + (n + 1) /\ P a res (glob A)].
rewrite (big_int_recr). smt().  simplify.
rewrite H0. auto. 
have ->: (s + n + 1) = (s + (n + 1)).
smt().
auto. auto.
qed.


lemma pr_interval_to_sum_lemma &m : forall (a : iat) 
  (f : (glob A) -> int) 
  (P : iat -> rt -> (glob A) -> bool) 
  (s e : int),
  Pr[ A.run(a) @ &m : s <= f (glob A) <= e /\ P a res (glob A) ]
   = big predT
      (fun i => Pr[ A.run(a) @ &m : f (glob A) = i 
                                   /\ P a res (glob A) ])
      (range s (e + 1)).
proof. progress.
case (s <= e). move => sep.
have : exists e', 0 <= e' /\ e = s + e'.
exists (e - s). progress.
smt(). smt(). elim. progress.
apply (pr_interval_to_sum_lemma' &m a). auto. 
progress.
rewrite range_geq. smt(). 
rewrite big_nil.
have ->:  Pr[A.run(a) @ &m : (s <= f (glob A) && f (glob A) <= e) /\ P a res (glob A)]
 = Pr[A.run(a) @ &m : false ].
rewrite Pr[mu_eq]. smt(). auto.
rewrite Pr[mu_false]. auto.
qed.

end section.

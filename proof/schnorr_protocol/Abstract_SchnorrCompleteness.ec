pragma Goals:printall.
require import AllCore DBool Bool List Distr.

require import Abstract_SchnorrBasics.

section.

(* lemma pow_pow: forall (g : zp) (x y : int), (g ^^ x) ^^ y = g ^^ (x * y). progress.  rewrite /(^^). smt(@ZModpRing). qed. *)
(* lemma pow_plus (g : zp) (a b : int) : unit g => g ^^ (a + b) = (g ^^ a) * (g ^^ b). progress.  rewrite /(^^). smt(@ZModpRing). qed. *)
(* lemma pow_inv (g : zp) (a: int) :  g ^^ - a = inv (g ^^ a). progress.  rewrite /(^^). smt(@ZModpRing). qed. *)
(* lemma nosmt pow_opp: forall (x : zp) (p : int), x ^^ -p = inv (x ^^ p). progress.  rewrite /(^^). smt(@ZModpRing). qed. *)

local lemma dl_complete_h (p : dl_stat) (w : dl_wit) : 
  completeness_relation p w =>
   hoare [ Completeness(HP,HV).run : arg = (p,w) ==> res ].
progress.
proc. inline*.  wp. 
rnd. wp.  rnd.  wp. 
skip. progress.
rewrite /verify_transcript. simplify.
rewrite /dl_verify. simplify.  
smt(@CG).
smt(@CG g_is_generator).
qed. 

(* one-round completeness  *)
lemma dl_completeness: forall (statement : dl_stat) (witness : dl_wit) &m,
  completeness_relation statement witness =>
     Pr[Completeness(HP, HV).run(statement, witness) 
            @ &m : res] = 1%r.
move => ya wa &m  isdl .
 byphoare (_: arg = (ya, wa) ==> _);auto.
proc*.
seq 1 : true 1%r 1%r 1%r 0%r r.
call (dl_complete_h ya wa). auto.
conseq (_: true ==> true). inline*. sp.
wp.  progress. rnd. simplify.
conseq (_: true ==> true). progress. apply duniform_ll. smt(challenge_set_size).
wp.  rnd. skip. simplify.
smt(@Distr q_prime). skip. auto. skip. auto. auto.
qed.


(* iterated completeness *)
lemma dl_completeness_iter: forall (statement:dl_stat) (witness:dl_wit) &m n,
        1 <= n =>
       completeness_relation statement witness =>
      Pr[CompletenessAmp(HP,HV).run(statement, witness,n) @ &m : res] = 1%r.
progress.
apply (PerfectCompleteness.completeness_seq HP HV).
progress.
apply dl_completeness. auto. auto. auto.
qed.

  
end section.

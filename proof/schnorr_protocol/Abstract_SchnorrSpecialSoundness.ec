require import Int IntDiv Real Distr.

require import Abstract_SchnorrBasics.
import CG.



lemma pow_mod  (a : int) : g ^ a  = g ^ (a %% q).  
admitted.



(* import ZModpRing. *)
(* op inv (a : int) : int. *)
(* axiom inv_mul1 (g : zp) (a : int) : a %% (p-1) <> 0 => (a * (inv a)) %% p = 1. *)


(* lemma inv_mul (g : zp) (a : int) : a %% (p-1) <> 0 => (g ^^ ((a * inv a) %% p)) = g.   *)
(* smt(inv_mul1 @Zp). *)
(* qed. *)

op inv : int -> int.
axiom inv_lemma a : a <> 0 => a * (inv a) %% q = 1.

(* perfect witness extraction from two valid transcripts  *)
op special_soundness_extract (s : dl_stat) (t1 t2 : transcript): dl_wit
 = ((inv  (t1.`2 - t2.`2)) * (t1.`3  - t2.`3)) %% q.

clone export SpecialSoundness with op special_soundness_extract <- special_soundness_extract
proof *.



(* lemma pow_pow: forall (g : zp) (x y : int), (g ^^ x) ^^ y = g ^^ (x * y). progress.  rewrite /(^^). smt(@ZModpRing). qed. *)
(* lemma pow_plus  (g : zp) (a b : int) : unit g => g ^^ (a + b) = (g ^^ a) * (g ^^ b). progress.  rewrite /(^^). smt(@ZModpRing). qed. *)
(* lemma pow_inv  (a: int) :  g ^^ - a = inv  (g ^^ a). progress.  rewrite /(^^). smt(@ZModpRing). qed. *)
(* lemma nosmt pow_opp: forall (x : zp) (p : int), x ^^ -p = inv (x ^^ p). progress.  rewrite /(^^). smt(@ZModpRing). qed. *)

lemma zz (x y z : group) : y * (inv x) = e => z * (inv x) = e => z = y.
smt(@CG). qed.

lemma ass : forall (x y : int), exists k, (x * k) %% q = y %% q.

lemma ww (x s : group) i j : g ^ i = s ^ j => exists k, g ^ k = s.
move => H.
have : exists c, 1 = (i * c) %% q . admit.
elim. progress.
exists (i * c). 




section. 

(* proof of perfect special soundness  *)
lemma dl_perfect_special_soundness (statement:dl_stat) 
 (transcript1 transcript2: transcript):
        valid_transcript_pair statement transcript1 transcript2 =>
   soundness_relation statement 
    (special_soundness_extract statement transcript1 transcript2).
proof. 
rewrite /valid_transcript_pair. rewrite /verify_transcript.
rewrite /dl_verify. 
progress. 
have H1' : g ^ transcript1.`3 = statement ^ transcript1.`2 * transcript1.`1. smt().
have H1'' : transcript1.`1 ^ q = e. smt().

have H2' : g ^ transcript2.`3 = statement ^ transcript2.`2 * transcript2.`1. smt().
have H2'' : transcript2.`1 ^ q = e. smt().

rewrite /special_soundness_extract /my_extract. 
rewrite /soundness_relation /IsDL.
rewrite H in H1'.

have ->:
(inv (transcript1.`2 - transcript2.`2) * (transcript1.`3 - transcript2.`3))
  = ((transcript1.`3 - transcript2.`3) * inv (transcript1.`2 - transcript2.`2) ). smt.
rewrite - pow_mod. 
have ->: g ^ ((transcript1.`3 - transcript2.`3) * inv (transcript1.`2 - transcript2.`2)) 
  = (g ^ ((transcript1.`3 - transcript2.`3)) ^ (inv (transcript1.`2 - transcript2.`2))). smt(@CG). 
have -> : 
 g ^ (transcript1.`3 - transcript2.`3) = 
  (statement ^ (transcript1.`2 - transcript2.`2)).
  have ->: g ^ (transcript1.`3 - transcript2.`3)
    = g ^ transcript1.`3 * g ^ (- transcript2.`3).
      have ->: (transcript1.`3 - transcript2.`3) = (transcript1.`3 + (- transcript2.`3)).
      smt(). smt(@CG).
  have ->: g ^ - transcript2.`3 = 
    inv (g ^ transcript2.`3). smt(@CG).
rewrite /c in H1'.
   rewrite H1' H2'.
  have ->: inv ((statement ^ transcript2.`2) * transcript2.`1)  = (inv (statement ^ transcript2.`2)) * (inv transcript2.`1). smt(@CG).
have ->: statement ^ transcript1.`2 * transcript2.`1 *
  (inv (statement ^ transcript2.`2) * inv transcript2.`1) =
  statement ^ transcript1.`2 *
  (inv (statement ^ transcript2.`2)). smt(@CG). 
have ->: inv (statement ^ transcript2.`2)
  = (statement ^ - transcript2.`2).
smt(@CG).
smt(@CG).
have j : statement ^ transcript1.`2 * transcript2.`1 =
                (statement ^ transcript1.`2) * transcript2.`1. auto.
have ->: statement ^ (transcript1.`2 - transcript2.`2) ^ inv (transcript1.`2 - transcript2.`2)
 = statement ^ ((transcript1.`2 - transcript2.`2) * inv (transcript1.`2 - transcript2.`2)). smt(@CG).
have ->: statement ^
((transcript1.`2 - transcript2.`2) * inv (transcript1.`2 - transcript2.`2))
  = statement ^
(((transcript1.`2 - transcript2.`2) * inv (transcript1.`2 - transcript2.`2)) %% q).


rewrite pow_opp. auto.
rewrite pow_plus. smt(g_unit @Zp). auto.
rewrite pow_pow.
(* apply inv_mul.  *)
admit.                          (* in progress *)
qed.


end section.

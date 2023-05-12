pragma Goals:printall.
require import AllCore Bool.
require import CyclicGroup.
import FDistr.

require import Schnorr_Basics.

(* perfect witness extraction from two valid transcripts  *)
op special_soundness_extract (p : dl_stat) (t1 t2 : transcript): dl_wit
 = (inv (t1.`2 - t2.`2)) * (t1.`3  - t2.`3).

clone export SpecialSoundness with op special_soundness_extract <- special_soundness_extract
proof *.


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
clear H1.
have H2' : g ^ transcript2.`3 = statement ^ transcript2.`2 * transcript2.`1. smt().
clear H2.
rewrite /special_soundness_extract /my_extract. 
rewrite /soundness_relation /IsDL.
rewrite H in H1'.
clear H.
have ->:
(inv (transcript1.`2 - transcript2.`2) * (transcript1.`3 - transcript2.`3))
  = ((transcript1.`3 - transcript2.`3) * inv (transcript1.`2 - transcript2.`2)). smt (@CyclicGroup).
rewrite - pow_pow.
have -> : 
 g ^ (transcript1.`3 - transcript2.`3) = 
  (statement ^ (transcript1.`2 - transcript2.`2)).
  have ->: g ^ (transcript1.`3 - transcript2.`3)
    = g ^ transcript1.`3 * g ^ (- transcript2.`3).
  smt(@CyclicGroup).
  have ->: g ^ - transcript2.`3 = 
    inv (g ^ transcript2.`3). smt(@CyclicGroup).
rewrite /c in H1'.
   rewrite H1' H2'.
  have ->: inv (statement ^ transcript2.`2 * transcript2.`1)  = inv (statement ^ transcript2.`2) * (inv transcript2.`1). smt (@CyclicGroup).
have ->: statement ^ transcript1.`2 * transcript2.`1 *
  (inv (statement ^ transcript2.`2) * inv transcript2.`1) =
  statement ^ transcript1.`2 *
  (inv (statement ^ transcript2.`2)).
smt (mulN mulA mul1 mulC).
have ->: inv (statement ^ transcript2.`2)
  = (statement ^ - transcript2.`2).
rewrite pow_opp. auto.
smt (@CyclicGroup).
rewrite  pow_pow.
rewrite  mulfV. smt(@CyclicGroup).
smt (@CyclicGroup).
qed.

end section.

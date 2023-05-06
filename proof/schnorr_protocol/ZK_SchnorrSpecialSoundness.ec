
require import Int IntDiv.
require import Real.
require import Distr.

require (*--*) SigmaProtocol.
require import StdOrder.


require import ZK_SchnorrBasics.
require import Ring_ops_spec Ring_ops_proof.
import Zp DZmodP.

import Ring.IntID IntOrder.

op inv : int -> int.
axiom inv_mul (g : zp) (a : int) : a <> 0 => g ^^ (a * inv a) = g. 
axiom pow_mod (g : zp) (a : int) : g ^^ a  = g ^^ (a %% (p-1)). 





(* perfect witness extraction from two valid transcripts  *)
op special_soundness_extract (_ : dl_stat) (t1 t2 : transcript): dl_wit
 = ((inv (t1.`2 - t2.`2)) * (t1.`3  - t2.`3)) %% (p-1).

clone export SpecialSoundness with op special_soundness_extract <- special_soundness_extract
proof *.




lemma pow_pow: forall (g : zp) (x y : int), (g ^^ x) ^^ y = g ^^ (x * y). progress.  rewrite /(^^). smt(@ZModpRing). qed.
lemma pow_plus (g : zp) (a b : int) : unit g => g ^^ (a + b) = (g ^^ a) * (g ^^ b). progress.  rewrite /(^^). smt(@ZModpRing). qed.
lemma pow_inv (g : zp) (a: int) :  g ^^ - a = inv (g ^^ a). progress.  rewrite /(^^). smt(@ZModpRing). qed.
lemma nosmt pow_opp: forall (x : zp) (p : int), x ^^ -p = inv (x ^^ p). progress.  rewrite /(^^). smt(@ZModpRing). qed.

axiom g_nonz : g <> zero.



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
have H1' : g ^^ transcript1.`3 = statement ^^ transcript1.`2 * transcript1.`1. smt().
clear H1.
have H2' : g ^^ transcript2.`3 = statement ^^ transcript2.`2 * transcript2.`1. smt().
clear H2.
rewrite /special_soundness_extract /my_extract. 
rewrite /soundness_relation /IsDL.
rewrite H in H1'.
clear H.
have ->:
(inv (transcript1.`2 - transcript2.`2) * (transcript1.`3 - transcript2.`3))
  = ((transcript1.`3 - transcript2.`3) * inv (transcript1.`2 - transcript2.`2)). smt.
rewrite - pow_mod. 
rewrite - pow_pow.
have -> : 
 g ^^ (transcript1.`3 - transcript2.`3) = 
  (statement ^^ (transcript1.`2 - transcript2.`2)).
  have ->: g ^^ (transcript1.`3 - transcript2.`3)
    = g ^^ transcript1.`3 * g ^^ (- transcript2.`3).
      have ->: (transcript1.`3 - transcript2.`3) = (transcript1.`3 + (- transcript2.`3)).
      smt().
    rewrite pow_plus. smt.
 auto.
  have ->: g ^^ - transcript2.`3 = 
    inv (g ^^ transcript2.`3). apply pow_inv.
rewrite /c in H1'.
   rewrite H1' H2'.
  have ->: inv ((statement ^^ transcript2.`2) * transcript2.`1)  = (inv (statement ^^ transcript2.`2)) * (inv transcript2.`1). smt(@Zp).
have ->: statement ^^ transcript1.`2 * transcript2.`1 *
  (inv (statement ^^ transcript2.`2) * inv transcript2.`1) =
  statement ^^ transcript1.`2 *
  (inv (statement ^^ transcript2.`2)). timeout 15. smt.
(* smt (mulN mulA mul1 mulC). *)
have ->: inv (statement ^^ transcript2.`2)
  = (statement ^^ - transcript2.`2).
rewrite pow_opp. auto.
rewrite   pow_plus. smt. auto.
rewrite pow_pow.
apply inv_mul. smt().
qed.

end section.

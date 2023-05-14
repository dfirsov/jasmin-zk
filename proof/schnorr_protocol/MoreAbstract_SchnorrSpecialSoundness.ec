require import Int IntDiv Real Distr.

require import MoreAbstract_SchnorrBasics.
import CG EG.



(* axiom inv_lemma a : a <> 0 => a * (inv a) %% q = 1. *)
axiom pow_mod  (a : int)  : forall (g : group), g ^ a  = g ^ (a %% q).






(* perfect witness extraction from two valid transcripts  *)
op special_soundness_extract (s : dl_stat) (t1 t2 : transcript): dl_wit
 = ((t1.`3  - t2.`3) / (t1.`2 - t2.`2)).

clone export SpecialSoundness with op special_soundness_extract <- special_soundness_extract
proof *.

lemma qqq : forall (z a b : group),  (z * a) / (z * b) = (a / b).
smt(@CG). qed.

lemma iii : forall i p, 0 < p => i %% p = 1 => exists k, i = 1 + p * k.
smt(@IntDiv).
qed.




section. 

(* proof of perfect special soundness  *)
lemma dl_perfect_special_soundness (statement:dl_stat) 
 (transcript1 transcript2: transcript):
        valid_transcript_pair statement transcript1 transcript2 =>
   soundness_relation statement 
    (special_soundness_extract statement transcript1 transcript2).
proof.

rewrite /valid_transcript_pair.
rewrite /verify_transcript.
rewrite /soundness_relation.
rewrite /IsDL.
rewrite /special_soundness_extract.
rewrite /(^^).

pose s := statement.

pose z := transcript1.`1.
pose c := transcript1.`2.
pose t := transcript1.`3.

pose z' := transcript2.`1.
pose c' := transcript2.`2.
pose t' := transcript2.`3.
simplify. progress.

have fact1 : g ^ (asint t) = z * s ^ (asint c). 
 smt(@CG).
have fact2 : g ^ (asint t') = z * s ^ (asint c'). 
 smt(@CG).
have : (g ^ asint t) / g ^ (asint t') = (z * s ^ (asint c)) / (z * s ^ (asint c')).
smt.
have -> : g ^ asint t / g ^ asint t' = g ^ (asint t - asint t'). smt.
have -> : (z * s ^ asint c) / (z * s ^ asint c') =  (s ^ asint c) / (s ^ asint c'). smt(qqq).
have -> : (s ^ asint c) / (s ^ asint c') = s ^ (asint c - asint c'). smt.
pose d := one /(c-c').
have : asint (d * (c-c')) = 1. 
  have : (c - c') <> zero. 
    smt(@EG).
 rewrite /d. simplify. smt.
move => H3.
have : exists k, asint  d * ((asint c) - (asint c'))   = 1 + q * k.
apply (iii (asint d * ((asint c) - (asint c'))) q _ _) .   smt. 
have ->: (asint d * (asint c - asint c')) %% q = (asint d)* ((asint c - asint c') %% q) %% q. smt(@IntDiv).
have -> : (asint c - asint c') %% q = asint (c - c'). smt.
rewrite - mulE. auto.
elim. progress.
pose w := d*(t-t').
have ->: g ^ asint ((t - t') / (c - c')) = g ^ (asint w).
smt.
rewrite /w.
have -> : g ^ asint (d * (t - t')) = g ^ (asint d * asint (t - t')). smt.
have -> : g ^ (asint d * asint (t - t')) = g ^ asint (t - t') ^ asint d. smt.
have ->: g ^ asint (t - t') = g ^ ((asint t) - (asint t')). 
  rewrite addE.
  have -> : g ^ ((asint t + asint (-t')) %% q) = g ^ ((asint t + asint (-t')) ). smt.
  have ->: g ^ (asint t - asint t') = g ^ ((asint t - asint t')%% q ). smt.
  have ->: ((asint t - asint t')%% q ) = ((asint t %%q  + (- asint t') %% q  ) ) %% q. 
  rewrite modzDm. auto.
  have ->: g ^ (asint t + asint (-t')) = g ^ ((asint t + asint (-t')) %% q). smt.
  rewrite oppE.
  rewrite modzDm.
  have -> : ((asint t + (- asint t') %% q) %% q)  = ((asint t + (- asint t')) %% q). smt(@IntDiv). auto.
rewrite H5.
have ->: (s ^ (asint c - asint c')) ^ asint d = s ^ ((asint c - asint c') * asint d). smt(@CG).
have ->: ((asint c - asint c') * asint d) = ((asint d)  * (asint c - asint c') ). smt.
rewrite  H4. 
have ->: s ^ (1 + q * k) = s  * (s ^ (q * k)). smt.
have ->: s ^ (q * k) = e. 
have ->: s ^ (q * k) = s ^ q ^ k. smt(@CG).
have ->: s ^ q = e. rewrite pow_mod. smt(@IntDiv @CG). smt(@CG). smt(@CG).
qed.


end section.

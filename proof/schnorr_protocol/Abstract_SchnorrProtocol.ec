require import Int IntDiv Real Distr StdOrder List.
(* import Ring.IntID IntOrder. *)

require GenericSigmaProtocol.

require import Group ZModP.
   
clone import ComGroup as CG.

op q : int.
axiom q_prime : prime q.

clone import ZModField as EG with op p <- q
proof prime_p.  realize prime_p. apply q_prime. qed.



(* synonyms for readability  *)
type dl_stat = group.            (* statement *)
type dl_wit  = zmod.              (* witness *)
type dl_com  = group.            (* commitment *)
type dl_resp = zmod.              (* response *)
type dl_chal = zmod.              (* challenge *)

op (^^) (g : group)(p : zmod): group = g ^ (asint p).


(* generator  *)
op g : group.

(* axiom g_not_ine : g <> e. *)
axiom g_is_generator : g ^ q = e.

(* the language of Schnorr protocol consists of discrete logarithms  *)
op IsDL (p : dl_stat) (w : dl_wit) : bool = g ^^ w = p.

op soundness_relation    = IsDL.
op completeness_relation = IsDL.
op zk_relation           = IsDL.


(* transcript verification for Honest Vrifier  *)
op verify_transcript (p : dl_stat) (x : dl_com * dl_chal * dl_resp) = 
 (let (c,b,r) = x in ((g ^^ r) = (p ^^ b) * c)) /\ (p ^ q = e).

(* instantiating generic definitions for Schnorr protocol  *)
clone include GenericSigmaProtocol with 
  type statement       <= dl_stat,
  type commitment      <= dl_com,  
  type witness         <= dl_wit,
  type response        <= dl_resp,
  type challenge       <= dl_chal,
  op challenge_set     <=  DZmodP.Support.enum,
  op verify_transcript     <- verify_transcript,
  op soundness_relation    <- soundness_relation,
  op completeness_relation <- completeness_relation,
  op zk_relation           <- zk_relation.
  (* TODO proof* or make this theory abstract *)


(* Honest Prover *)
module HP : HonestProver = {
 var pa : dl_stat
 var wa : dl_wit
 var r : zmod

 proc commitment(s : dl_stat, w : dl_wit) : dl_com = {  
    (pa, wa) <- (s,w);
    r <$ DZmodP.dunifin;
    return g ^^ r;
 }

 proc response(b : dl_chal) : dl_resp = {
    return r + b * wa;
 }  
}.


lemma qqq : forall (z a b : group),  (z * a) / (z * b) = (a / b).
smt(@CG). qed.

lemma jjj : forall i p, 0 < p => i = (i %% p) + p * (i %/ p).
smt(@IntDiv).
qed.


lemma iii : forall i p, 0 < p => i %% p = 1 => exists k, i = 1 + p * k.
smt(jjj).
qed.



lemma pow_mod (a : int) :  g ^ a  = g ^ (a %% q).
have ->: g ^ a = g ^ (a %% q + q * (a %/ q)). 
have : 0 < q. smt.
smt(jjj). 
have ->: g ^ (a %% q + q * (a %/ q))
 = g ^ (a %% q) * (g ^ (q * (a %/ q))). smt(@CG).
have ->:  g ^ (q * (a %/ q)) = e. 
smt(@CG @EG @Int g_is_generator).
smt(@CG).
qed.


(* Honest Verifier is derived automatically from "challenge_set" and "verify_transcript" *)


section.

local lemma dl_complete_h (p : dl_stat) (w : dl_wit) : 
  completeness_relation p w =>
   hoare [ Completeness(HP,HV).run : arg = (p,w) ==> res ].
progress.
proc. inline*.  wp. 
rnd. wp.  rnd.  wp. 
skip. progress.
rewrite /verify_transcript. simplify.
rewrite /dl_verify. simplify.   rewrite /(^^).
pose ch := x2.
have ->: asint (r0 + ch * w{hr}) = (asint r0 + asint (ch * w{hr})) %% q. smt.
have <-: g ^ ((asint r0 + asint (ch * w{hr})))
 = g ^ ((asint r0 + asint (ch * w{hr})) %% q). smt (pow_mod).
have ->: g ^ (asint r0 + asint (ch * w{hr}))
 = g ^ asint r0 * g ^  asint (ch * w{hr}).
smt(@CG).
have ->: asint (ch * w{hr}) = (asint ch * asint w{hr}) %% q. smt.
have ->: g ^ (asint ch * asint w{hr} %% q) = g ^ (asint ch * asint w{hr}). smt (pow_mod).
have -> : (asint ch * asint w{hr}) = (asint w{hr} * asint ch). smt().
have ->: g ^ (asint w{hr} * asint ch) = g ^ asint w{hr} ^ asint ch. smt.
have ->: g ^ asint w{hr} = s{hr}. smt().
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


(* perfect witness extraction from two valid transcripts  *)
op special_soundness_extract (s : dl_stat) (t1 t2 : transcript): dl_wit
 = ((t1.`3  - t2.`3) / (t1.`2 - t2.`2)).

clone export SpecialSoundness as SS with op special_soundness_extract <- special_soundness_extract
proof *.

lemma qqq1 : forall (z a b : group),  (z * a) / (z * b) = (a / b).
smt(@CG). qed.

lemma jjj1 : forall i p, 0 < p => i = (i %% p) + p * (i %/ p).
smt(@IntDiv).
qed.


lemma iii1 : forall i p, 0 < p => i %% p = 1 => exists k, i = 1 + p * k.
smt(jjj1).
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
move => H5.
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
rewrite H7.
have ->: (s ^ (asint c - asint c')) ^ asint d = s ^ ((asint c - asint c') * asint d). smt(@CG).
have ->: ((asint c - asint c') * asint d) = ((asint d)  * (asint c - asint c') ). smt.
rewrite  H6. 
have ->: s ^ (1 + q * k) = s  * (s ^ (q * k)). smt.
have ->: s ^ (q * k) = e. 
have ->: s ^ (q * k) = s ^ q ^ k. smt(@CG).
have ->: s ^ q = e.
auto. 
smt(@IntDiv @CG). smt(@CG). 
qed.


end section.


section.
declare module P <: RewMaliciousProver{-HV}.
declare axiom P_response_ll : islossless P.response.
declare axiom P_commitment_ll : islossless P.commitment.


(* rewindability assumption *)
declare axiom rewindable_P_plus :
        (exists (f : glob P -> sbits),
         injective f /\
         (forall &m, Pr[ P.getState() @ &m : (glob P) = ((glob P){m})
                                          /\ res = f ((glob P){m} ) ] = 1%r) /\
         (forall &m b (x: glob P), b = f x =>
           Pr[P.setState(b) @ &m : glob P = x] = 1%r) /\
         islossless P.setState).

(* automatically implying proof-of-knowledge from special soundness  *)
lemma dl_statistical_PoK &m s: 
  Pr[Extractor(P).extract(s) @ &m : soundness_relation s res ] >=
   (Pr[Soundness(P, HV).run(s) @ &m : res]^2 -
  1%r / (size DZmodP.Support.enum)%r
           * Pr[Soundness(P, HV).run(s) @ &m : res]).

apply (Perfect.statistical_extractability P  _ _ _ _ &m s  ).
apply rewindable_P_plus. apply P_response_ll. apply P_commitment_ll.
apply dl_perfect_special_soundness.
qed.

end section.

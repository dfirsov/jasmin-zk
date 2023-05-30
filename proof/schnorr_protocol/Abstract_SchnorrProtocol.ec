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



abstract theory SchnorrZeroKnowledge.


op n : int.
axiom n_pos : 1 <= n.

clone import ZeroKnowledge as ZK with
  op n <= n                     
proof*. 
realize n_pos. apply n_pos. qed.

op N : int.
axiom N_pos : 0 <= N.
  
clone import OneShotSimulator as OSS with
  op N <= N
proof *.
realize N_pos. apply N_pos. qed.




(* one-time simulator *)
module Sim1(V : RewMaliciousVerifier)  = {
  proc sinit(y : dl_stat) : zmod * group * zmod = {
    var r,bb;
    r  <$ DZmodP.dunifin;
    bb <$ DZmodP.dunifin;
    return (bb, (g ^^ r) * (inv (y ^^ bb)), r);
  }
  proc run(Ny : dl_stat) : bool * summary  = {
    var r,z,b',b,result, vstat;
    vstat <@ V.getState();
    (b',z,r) <@ sinit(Ny);
    b  <@ V.challenge(Ny,z);
    result <@ V.summitup(Ny,r);
    if(b <> b'){
      V.setState(vstat);
    }
    return (b = b', result);
  }
}.

section.

declare module V <: RewMaliciousVerifier {-HP, -ZK.Hyb.Count, -ZK.Hyb.HybOrcl}.


declare axiom V_summitup_ll : islossless V.summitup.
declare axiom V_challenge_ll : islossless V.challenge.

(* rewindability assumption *)
declare axiom rewindable_V_plus : 
  exists (f : glob V -> sbits),
  injective f /\
  (forall (x : glob V),
    phoare[ V.getState : (glob V) = x ==> (glob V) = x  /\ res = f x ] = 1%r) /\
  (forall (x : glob V),
    hoare[ V.getState : (glob V) = x ==> (glob V) = x  /\ res = f x ]) /\
  islossless V.getState /\
  (forall (x: glob V),
    phoare[V.setState: b = f x ==> glob V = x] = 1%r) /\
  (forall (x: glob V),
    hoare[V.setState: b = f x ==> glob V = x]) /\
  islossless V.setState.

(* if good-event does not happen then Sim1(V) rewinds its state  *)
lemma sim1_rew_ph : forall (x : (glob V) * (glob Sim1)),
    phoare[ Sim1(V).run :
             ((glob V), (glob Sim1)) = x
                 ==> ! res.`1 => ((glob V), (glob Sim1)) = x] = 1%r.
proof. progress.
exists* (glob V). elim* => V_v.
progress.
elim rewindable_V_plus.
move => fA [s1 [s2 [s3]]] [s4 [ s5 [s6 s7]]].
proc.
seq 1 : (V_v = (glob V) /\ vstat = fA V_v /\
  ((glob V),tt) =
  x).
call (_: true ==> true). auto. skip. auto.
call (s2 V_v).
skip. progress.
wp.
seq 3 : (vstat = fA V_v /\ x.`1 = V_v) 1%r.
call (_:true).  call (_:true). call (_:true). rnd. rnd. skip. auto. skip. auto.
simplify. call V_summitup_ll. call V_challenge_ll.
inline*.  wp. rnd. rnd. wp. skip. progress. smt (@DZmodP @Distr). smt (@DZmodP @Distr).
case (b = b').
rcondf 1. skip. auto. skip. auto.
rcondt 1. skip. auto. call (s5 V_v). skip. auto. 
progress. 
have -> : tt = x.`2. smt().
smt().
hoare. simplify.
call (_:true). call (_:true). call (_:true). rnd. rnd. skip. auto.
skip. auto. auto.  hoare. simplify. 
call (s3 V_v). skip. progress. auto.
qed.


end section.


section.

declare module V <: RewMaliciousVerifier {-HP, -ZK.Hyb.Count, -ZK.Hyb.HybOrcl}.
declare module D <: ZKDistinguisher.

(* rewindability assumption  *)
declare axiom rewindable_V_plus2 : 
  exists (f : glob V -> sbits),
  injective f /\
  (forall (x : glob V),
    phoare[ V.getState : (glob V) = x ==> (glob V) = x  /\ res = f x ] = 1%r) /\
  (forall (x : glob V),
    hoare[ V.getState : (glob V) = x ==> (glob V) = x  /\ res = f x ]) /\
  islossless V.getState /\
  (forall (x: glob V),
    phoare[V.setState: b = f x ==> glob V = x] = 1%r) /\
  (forall (x: glob V),
    hoare[V.setState: b = f x ==> glob V = x]) /\
  islossless V.setState.

declare axiom summitup_ll  :  islossless V.summitup.
declare axiom challenge_ll :  islossless V.challenge.
declare axiom D_guess_ll : islossless D.guess.
declare axiom D_guess_prop : equiv [ D.guess ~ D.guess : ={arg, glob V, glob ZK.Hyb.Count, glob ZK.Hyb.HybOrcl} ==> ={res} ].

(* transformed simulator with independent coin flip *)

local module Sim1'  = {
  var result : bool list

  proc sinit() : zmod * group * zmod  = {
    var r,bb;
    r  <$ DZmodP.dunifin;
    bb <$ DZmodP.dunifin;
    return (bb, g ^^ r,r);
  }
    
  proc run(Ny : dl_stat, w : dl_wit) : bool * bool  = {
    var z,r,b',b,ryb,result, rd;
    (b',z,r) <@ sinit();
    b  <@ V.challenge(Ny,z);
    ryb  <- r + b * w;
    result <@ V.summitup(Ny,ryb);
    rd <@ D.guess(Ny, w, result);    
    return (b = b', rd);
  }

 proc allinone(Ny : dl_stat, w : dl_wit) = {
    var r,bb,b',b,ryb,result, rd;
    r  <$ DZmodP.dunifin;
    bb <$ DZmodP.dunifin;
    b' <- bb;
    b  <@ V.challenge(Ny,g ^^ r);
    ryb  <- r + b * w;
    result <@ V.summitup(Ny,ryb);
    rd <@ D.guess(Ny, w, result);
    return (b = b', rd);
  } 

 proc allinone'(Ny : dl_stat, w : dl_wit) = {
    var r,b,ryb,result, rd;
    r  <$ DZmodP.dunifin;
    b  <@ V.challenge(Ny,g ^^ r);
    ryb  <- r + b * w;
    result <@ V.summitup(Ny,ryb);
    rd <@ D.guess(Ny, w, result);
    return (b, rd);
 } 

 proc allinone''(Ny : dl_stat, w : dl_wit) = {
    var b,b',rd;
    (b,rd) <@ allinone'(Ny,w);
    b' <$ DZmodP.dunifin;
    return (b = b', rd);
  } 

}.




local lemma qrp_zk2_eq ya wa  : zk_relation ya wa =>
  equiv [ZKReal(HP, V, D).run ~ Sim1'.run
         : ={arg, glob V, glob ZK.Hyb.Count, glob ZK.Hyb.HybOrcl } /\ arg{1} = (ya, wa)
          ==> res{1} = res{2}.`2 ].
move => isqr. proc.
call D_guess_prop.
inline*. sp.
call (_:true).  simplify.  
wp. simplify. call (_:true).
wp. swap {2} 2 -1.
 rnd . rnd{2}.    skip. progress . 
qed.

require import IntDiv.
local lemma exss ya wa : zk_relation ya wa =>
 equiv[ Sim1(V).sinit ~ Sim1'.sinit
   : arg{1} = (ya) /\ ={glob V, glob ZK.Hyb.Count, glob ZK.Hyb.HybOrcl} ==>
    ={glob V, glob ZK.Hyb.Count, glob ZK.Hyb.HybOrcl} /\  (res{1}.`1, res{1}.`2) = (res{2}.`1, res{2}.`2) /\ res{1}.`3 - wa * res{1}.`1 = res{2}.`3  ].
proof. 
move => zk_rel. proc. swap 2 -1.
seq 1 1 : (={bb} /\ (y{1}) = (ya) /\ ={glob V, glob ZK.Hyb.Count, glob ZK.Hyb.HybOrcl}). rnd.    skip. progress. 
exists* bb{1}. elim*. progress.
wp. 
rnd (fun (x : zmod) => (x - wa * bb_L ))
      (fun (x : zmod) => (x + wa * bb_L )). skip. progress.
smt(@ZModpField). smt(@ZModpField). 
have ->: inv (y{1} ^^ bb{2}) = y{1} ^ - asint bb{2}. 
rewrite - expN. auto.
have ->: y{1} = g ^^ wa. smt().
rewrite /(^^).
have ->: g ^ asint wa ^ - asint bb{2} = g ^ ((asint wa) * - (asint bb{2})).
smt(@CG).
rewrite - expD.
have ->: (asint rL + asint wa * - asint bb{2})
 = (asint rL + asint wa * - asint bb{2}).
have ->: (asint rL + asint wa * - asint bb{2}) 
 = (asint rL - asint wa * asint bb{2}). smt().
auto.
rewrite addE.
rewrite - pow_mod.
search CG.(^).
rewrite expD. rewrite expD.
congr.
rewrite oppE. 
rewrite - pow_mod.
have ->: (asint wa * - asint bb{2})
 = (- (asint wa * asint bb{2})). smt().
rewrite mulE.
rewrite expN.
rewrite expN.
congr.
rewrite - pow_mod. auto.
qed.



local lemma qkok ya wa P : zk_relation ya wa =>
  equiv [ RD(Sim1(V),D).run ~ Sim1'.run
   :   ={glob V,arg, glob ZK.Hyb.Count, glob ZK.Hyb.HybOrcl} /\  (ya,wa) = (Ny{2},w{2})
       ==>  (fst res{1}.`2) /\ P res{1}.`1 <=> (res{2}.`1 /\ P res{2}.`2) ].
move => zk_rel. proc.
inline Sim1(V).run. sp.
seq 2 1 : (={glob V,b',z, Ny,w, glob ZK.Hyb.Count, glob ZK.Hyb.HybOrcl} 
         /\ Ny{1} = a{1}
         /\ ((ya),wa) = (Ny{2},w{2})
         /\ r0{1} - wa * b'{1}  = r{2} 
 ).
call (exss ya wa). 
elim rewindable_V_plus2.
move => fA [s1 [s2 [s3]]] [s4 [ s5 [s6 s7]]]. 
exists* (glob V){1}. elim*. progress.
call {1} (s2 V_L).
skip. progress. 
seq 1 1 : (={glob V,b',z,Ny,w, glob ZK.Hyb.Count, glob ZK.Hyb.HybOrcl} 
         /\ Ny{1} = a{1}
         /\ b0{1} = b{2}
         /\ ((ya),wa) = (Ny{2},w{2})
         /\ r0{1}  - wa * b'{1} = r{2}).
call (_:true). skip. progress. 
sp. simplify.
exists* b'{1}. elim*. progress.
exists* b0{1}. elim*. progress.
wp.  simplify.
case (b0{1} = b'{1}). 
rcondf {1} 2. progress. call (_:true). skip. auto.
call D_guess_prop. wp. call (_:true). skip. progress. smt(@ZModpField).
rcondt {1} 2. progress. call (_:true). skip. auto.
seq 0 0 : ((b0{1} <> b'{1}) /\ (b{2} <> b'{2})).  skip. auto.
call {1} D_guess_ll.
call {2} D_guess_ll.
wp.
elim rewindable_V_plus2.
move => fA [s1 [s2 [s3]]] [s4 [ s5 [s6 s7]]].  
call {1} s7.
call {1} summitup_ll.
call {2} summitup_ll. skip. 
smt().
qed.
 

local lemma ssim ya wa  : zk_relation ya wa =>
 equiv [ RD(Sim1(V),D).run ~ Sim1'.run : ={glob V, glob D, arg, glob ZK.Hyb.Count, glob ZK.Hyb.HybOrcl} 
           /\  ((ya),wa) = (Ny{2},w{2}) 
       ==> (fst res{1}.`2) = res.`1{2} ].
move => ii.
conseq (qkok ya wa (fun x => true) ii). smt().
progress. smt().
qed.

local lemma run_allinone &m ya wa P: Pr[Sim1'.run(ya, wa) @ &m :  P res] = Pr[Sim1'.allinone(ya, wa) @ &m :  P res].
byequiv (_: ={arg,glob D, glob V, glob ZK.Hyb.Count, glob ZK.Hyb.HybOrcl} ==> _). proc.
call D_guess_prop. progress.
call (_:true). wp.  simplify.
call (_:true). inline*. wp.  rnd.  rnd. skip. progress.  auto. auto.
qed.

local lemma sim1'notnot &m ya wa: 
     Pr[Sim1'.run(ya, wa) @ &m :  res.`1] = (1%r / (size DZmodP.Support.enum)%r).
proof.
have ->: Pr[Sim1'.run(ya, wa) @ &m :  res.`1] = Pr[Sim1'.allinone(ya, wa) @ &m :  res.`1].
byequiv (_: ={arg,glob D, glob V, glob ZK.Hyb.Count, glob ZK.Hyb.HybOrcl} ==> _). proc.
call D_guess_prop. progress.
call (_:true). wp.  simplify.
call (_:true). inline*. wp.  rnd.  rnd. skip. progress.  auto. auto.
byphoare. proc. inline*. simplify.
swap [2..3] 4. wp.
seq 5 : true (1%r) (1%r / (size DZmodP.Support.enum)%r) 1%r 0%r.
auto. call D_guess_ll.
call summitup_ll. wp.
call challenge_ll. wp. rnd. skip. progress. smt(@Distr @DZmodP).
rnd. skip. progress.
rewrite /DZmodP.dunifin.
have ->: ((=) b{hr}) = pred1 b{hr}.
apply fun_ext. smt().
rewrite  duniform1E.

have ->: b{hr} \in DZmodP.Support.enum. smt(@DZmodP). simplify. 
have ->: (undup DZmodP.Support.enum) = (DZmodP.Support.enum). smt(@List @DZmodP). auto.
exfalso. auto. auto.  auto. auto.
qed.


local lemma simnresnotnot ya wa : zk_relation ya wa =>
  phoare[ RD(Sim1(V),D).run : arg = (ya, wa) ==>  (fst res.`2) ] = (1%r / (size DZmodP.Support.enum)%r).
move => ii.
bypr. progress.
rewrite H. clear H.
have <-: Pr[Sim1'.run(ya,wa) @ &m :  res.`1] = inv (size DZmodP.Support.enum)%r.
apply sim1'notnot.
byequiv (_: ={glob D, glob V, arg, glob ZK.Hyb.Count, glob ZK.Hyb.HybOrcl} /\ arg{1} =  (ya,wa) ==> (fst res.`2){1} = res.`1{2}). 
conseq (ssim ya wa ii). auto. auto. smt().
qed.


  
    
local lemma qrp_zk2_pr_l &m ya wa : zk_relation ya wa =>
    Pr[ZKReal(HP, V,D).run(ya,wa) @ &m : res  ] = Pr[ Sim1'.run(ya,wa) @ &m : res.`2  ].
proof. move => isqr. byequiv (: arg{2} = (ya,wa) /\ ={glob V, glob D, arg, glob ZK.Hyb.Count, glob ZK.Hyb.HybOrcl} ==> _).
conseq (_: _ ==> res{1} = res{2}.`2). progress.
conseq (qrp_zk2_eq ya wa  _). auto. auto. auto. auto.
qed.



local lemma allinone_1 &m ya wa P: Pr[Sim1'.allinone(ya, wa) @ &m :  P res.`2] = Pr[Sim1'.allinone'(ya, wa) @ &m :  P res.`2 ].
byequiv (_: ={arg,glob D, glob V, glob ZK.Hyb.Count, glob ZK.Hyb.HybOrcl} ==> _). proc.
call D_guess_prop. progress.
call (_:true). wp.  simplify.
call (_:true). inline*. wp.  rnd {1}.  rnd. skip. progress.  auto. auto.
qed.

local lemma allinine_3 &m ya wa P : phoare [ Sim1'.allinone' : arg = (ya,wa) /\ (glob V, glob D,  glob ZK.Hyb.Count, glob ZK.Hyb.HybOrcl){m} = (glob V, glob D, glob ZK.Hyb.Count, glob ZK.Hyb.HybOrcl)  ==> P res.`2 ] = (Pr[Sim1'.allinone'(ya, wa) @ &m :  P res.`2 ]).
bypr. progress. byequiv (:  ={glob V, glob D, arg, glob ZK.Hyb.Count, glob ZK.Hyb.HybOrcl} ==> _).
proc.
call D_guess_prop.  call (_:true). wp. call (_:true). rnd. skip. progress. smt(). smt().
qed.


local lemma allinone_2 &m ya wa P: Pr[Sim1'.allinone(ya, wa) @ &m :  P res] = Pr[Sim1'.allinone''(ya, wa) @ &m :  P res ].
byequiv (_: ={arg,glob D, glob V, glob ZK.Hyb.Count, glob ZK.Hyb.HybOrcl} ==> _). proc.
inline Sim1'.allinone'.
swap {2} 9 -5.
wp. call D_guess_prop. progress.
call (_:true). wp.  simplify.
call (_:true). inline*. wp.  rnd .  rnd. wp. skip. progress.  auto. auto.
qed.


local lemma sd &m ya wa  : 
     Pr[ Sim1'.allinone(ya,wa) @ &m : res.`1 /\ res.`2 ]
    = (1%r / (size DZmodP.Support.enum)%r) * Pr[ Sim1'.run(ya,wa) @ &m : res.`2 ].
rewrite (run_allinone &m ya wa (fun (x : bool * bool) => x.`2 )). simplify.
rewrite (allinone_1 &m ya wa (fun x => x)). simplify.
rewrite (allinone_2 &m ya wa (fun (x: bool * bool) => x.`1 /\ x.`2)). simplify.
byphoare (_: arg = (ya,wa) /\ (glob V, glob D,  glob ZK.Hyb.Count, glob ZK.Hyb.HybOrcl){m} = (glob V, glob D, glob ZK.Hyb.Count, glob ZK.Hyb.HybOrcl) ==> _).
proc. simplify.
seq 1 : (rd)  Pr[Sim1'.allinone'(ya, wa) @ &m : res.`2] (1%r / (size DZmodP.Support.enum)%r) Pr[Sim1'.allinone'(ya, wa) @ &m : !res.`2] 0%r. 
auto.
call (allinine_3 &m ya wa (fun x => x) ).
skip. simplify. auto. rnd. skip. progress. rewrite H. simplify. 
rewrite /DZmodP.dunifin.
have ->: (fun (x : zmod) => b{hr} = x) = pred1 b{hr}. apply fun_ext. smt().
rewrite duniform1E. 
have ->: b{hr} \in DZmodP.Support.enum. smt(@DZmodP). simplify. 
have ->: (undup DZmodP.Support.enum) = (DZmodP.Support.enum). smt(@List @DZmodP). auto.
hoare. auto.
progress. smt().
auto. auto. auto.
qed.


local lemma sim1zk &m ya wa :
  zk_relation ya wa =>
    Pr[RD(Sim1(V), D).run(ya, wa) @ &m : fst res.`2 /\ res.`1]
     = Pr[ZKReal(HP, V, D).run(ya, wa) @ &m : res] / (size DZmodP.Support.enum)%r.
proof.     
move => ii.
have ->:     Pr[RD(Sim1(V), D).run(ya, wa) @ &m : fst res.`2 /\ res.`1]
 = Pr[Sim1'.run(ya,wa) @ &m : res.`1 /\ res.`2].
byequiv (_: ={glob D, glob V, arg, glob ZK.Hyb.Count, glob ZK.Hyb.HybOrcl} /\ arg{1} =  (ya,wa) ==> _). 
conseq (qkok ya wa (fun x => x) _). progress;smt(). auto. auto.
auto.  
rewrite  (run_allinone &m ya wa (fun (r : bool * bool) => r.`1 /\ r.`2 )). 
simplify.
rewrite  (sd &m ya wa).
rewrite (qrp_zk2_pr_l &m ya wa). auto. auto.
qed.
    

lemma sim1_succ &m stat :  in_language zk_relation stat =>
 Pr[Sim1(V).run(stat) @ &m : res.`1] = (1%r / (size DZmodP.Support.enum)%r).
proof. progress.
elim H. move => w wrel.
have ->: Pr[Sim1(V).run(stat) @ &m : res.`1] 
  = Pr[RD(Sim1(V), D).run(stat, w) @ &m : (fst res.`2) ].
byequiv (_: _ ==> (fst res{1} = fst res.`2{2})).
proc. simplify.
 inline*. 
call {2} D_guess_ll. wp. simplify.
sim. auto. smt(). auto. smt().
byphoare (_: arg = (stat, w) ==> _). 
conseq (simnresnotnot stat w  _). auto. auto.  auto.
qed.


lemma sim1_error &m (p : dl_stat) (w : dl_wit) :
   zk_relation p w =>
    `|Pr[RD(Sim1(V), D).run(p, w) @ &m : fst res.`2 /\ res.`1] /
         Pr[Sim1(V).run(p) @ &m : fst res] 
              - Pr[ ZKD(HP,V,D).main(p,w) @ &m : res ]| = 0%r. 
progress.
rewrite sim1zk.  auto.
rewrite (sim1_succ &m p ). exists w. auto.
simplify.
have ->: Pr[ZKReal(HP, V, D).run(p, w) @ &m : res] * (size DZmodP.Support.enum)%r / (size DZmodP.Support.enum)%r
 = Pr[ZKReal(HP, V, D).run(p, w) @ &m : res].
smt.
have : Pr[ZKReal(HP, V, D).run(p, w) @ &m : res] =
  Pr[ZKD(HP, V, D).main(p, w) @ &m : res] .
byequiv (_: ={glob D, glob V, arg, glob ZK.Hyb.Count, glob ZK.Hyb.HybOrcl} /\ arg{1} =  (p,w) ==> _). proc. call D_guess_prop. sim. smt(). auto. smt().
qed.


end section.



(* importing the rewinding framework *)
require  RewBasics.
clone import RewBasics as Rew with
  type sbits <- sbits.


section. (* modules and their losslessness assumptions  *)
declare module V <: RewMaliciousVerifier{-ZK.Hyb.HybOrcl,-ZK.Hyb.Count,-HP}.
declare module D <: ZKDistinguisher{-ZK.Hyb.HybOrcl,-ZK.Hyb.Count, -HP}.

declare axiom Sim1_run_ll : forall (V0 <: RewMaliciousVerifier), islossless V0.challenge 
  => islossless V0.summitup => islossless Sim1(V0).run.
declare axiom V_summitup_ll : islossless V.summitup. 
declare axiom V_challenge_ll : islossless V.challenge.
declare axiom D_guess_ll : islossless D.guess.
declare axiom P_response_ll : islossless HP.response.
declare axiom P_commitment_ll : islossless HP.commitment.
declare axiom simn_simulate_ll : forall (V0 <: RewMaliciousVerifier), islossless V0.challenge 
  => islossless V0.summitup => islossless SimN(Sim1, V0).simulate.
declare axiom D_guess_prop : equiv[ D.guess ~ D.guess : ={glob V, arg} ==> ={res} ].


(* rewindability assumption *)
declare axiom rewindable_V_plus :
        (exists (f : glob V -> sbits),
         injective f /\
         (forall &m, Pr[ V.getState() @ &m : (glob V) = ((glob V){m})
                                          /\ res = f ((glob V){m} ) ] = 1%r) /\
         (forall &m b (x: glob V), b = f x =>
           Pr[V.setState(b) @ &m : glob V = x] = 1%r) /\
         islossless V.setState).

import Statistical.
lemma qr_statistical_zk stat wit &m:
        zk_relation stat wit =>
        let real_prob = Pr[ZKReal(HP, V, D).run(stat, wit) @ &m : res] in
        let ideal_prob = Pr[ZKIdeal(SimN(Sim1), V, D).run(stat, wit) @ &m : res] in
          `|ideal_prob - real_prob| <= 2%r * (1%r - (1%r / (size DZmodP.Support.enum)%r)) ^ N.
proof.
  progress.
apply (statistical_zk 0%r (1%r / (size DZmodP.Support.enum)%r) _ HP Sim1  V D _ _ _ _ _  stat wit &m);auto. apply Sim1_run_ll. apply V_summitup_ll. apply V_challenge_ll. 
apply D_guess_ll.  conseq  D_guess_prop. auto.
   apply (sim1_rew_ph V). 
 apply V_summitup_ll. apply V_challenge_ll.  apply (rewindable_A_plus V).
apply rewindable_V_plus.
progress. 
rewrite (sim1_error V D _ _  _ _).  apply (rewindable_A_plus V).
apply rewindable_V_plus. 
apply V_summitup_ll.
apply V_challenge_ll. apply D_guess_ll. 
conseq D_guess_prop. auto. auto. auto.
progress.
rewrite (sim1_succ V D _ _ _ _ _ &m stat). apply (rewindable_A_plus V).
apply rewindable_V_plus. 
apply V_summitup_ll.
apply V_challenge_ll. apply D_guess_ll. conseq D_guess_prop. auto. smt(). auto.
qed.


end section.


end SchnorrZeroKnowledge.

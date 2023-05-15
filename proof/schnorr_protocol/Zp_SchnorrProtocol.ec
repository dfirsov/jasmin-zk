require import Int IntDiv.
require import Real.
require import Distr.
require import List.
require import StdOrder.
import Ring.IntID IntOrder.

require (*--*) Subtype.

require Abstract_SchnorrProtocol.
require ZModPStar.

require import Ring_ops_spec.
import Zp.

clone ZModPStar as ZPS with op p <- Zp.p,
                            theory Zp <= Zp.


import ZPS.

op g : ZPS.zmod.
op q : int.
axiom q_prime : prime q.
axiom g_unit : unit g.
axiom g_q_assumption: (ZModpField.exp g q) = Zp.one.

lemma lll' (z : zmod) : unit z => forall x, 0 <= x => Zps.(^) (Sub.insubd z)  x = Sub.insubd (ZModpField.exp z x). 
move => z_unit. apply intind. progress. smt. progress.  timeout 20. smt.
qed.

clone import Abstract_SchnorrProtocol as LSP with
  op g <- Sub.insubd g,
  op q <- q,
  theory CG <- ZPS.Zps
proof g_is_generator, q_prime.
realize g_is_generator.  rewrite lll'. apply g_unit. smt(q_prime).
rewrite g_q_assumption. auto. qed.
realize q_prime.  apply q_prime. qed.




type statement   = zmod.           (* statement *)
type witness     = int.          (* witness *)
type commitment  = zmod.            (* commitment *)
type response    = int.          (* response *)
type challenge   = int.          (* challenge *)
type secret      = int.

module type ZKProverG = {
  proc commitment() : commitment * secret
  proc response(w : witness, r : secret, c : challenge) : response
}.

module type ZKVerifierG = {
  proc challenge() : challenge
  proc verify(s : statement, z : commitment, c : challenge, t : response) :
    bool
}.

module SchnorrProver : ZKProverG = {
  proc commitment() : commitment * secret = {
    var r : secret;
    r <$ [0..q-1]; 
    return (ZModpField.exp g r, r);
  }
  proc response(w: witness, r:secret, c: challenge) : response = {
    return r + c * w;
  }
}.


module SchnorrVerifier : ZKVerifierG = {
  proc challenge() : challenge = {
    var c;
    c <$ [0..q-1];
    return c;
  }
  proc verify(s: statement, z: commitment, c: challenge, t: response) : bool = {
    return ((ZModpField.exp g t) = (s ^^ c) * z) /\ (ZModpField.exp s q) = Zp.one;
  }
}.


module CompletenessG(P : ZKProverG, V : ZKVerifierG) = {
  proc main(s:statement, w:witness) = {
    var z, c, r,t,v;
    (z,r) <@ P.commitment();
    c <@ V.challenge();
    t <@ P.response(w,r,c);
    v <@ V.verify(s,z,c,t);
    return v;
  }
}.



op completeness_relationG (s:statement) (w:witness) = (ZModpField.exp g w) = s.


lemma exp_lemma6 (z : zmod) : unit z => forall n,  unit (z ^^ n).
progress. apply ZModpRing.unitrX. auto.
qed.






lemma lll'' (z : zmod) : unit z => forall x, x < 0 => Zps.(^) (Sub.insubd z) x = Zps.inv (Zps.(^) (Sub.insubd z) (- x)).
smt().
qed.


lemma lll (z : zmod) : unit z => forall x, Zps.(^) (Sub.insubd z)  x = Sub.insubd (ZModpField.exp z x). 
move => zu.
move => x.
case (0 <= x).  apply lll'. auto.
move => xl.
rewrite lll''. auto. smt().
rewrite lll'. auto. smt().
smt(@ZModpField @Sub).       
qed.

lemma bbb : forall (a b : zmods), (Sub.val a = Sub.val b) <=> (a = b). smt. qed.

lemma completeness_relation_compatible : forall s w, completeness_relationG s w => completeness_relation (Sub.insubd s) (EG.inzmod w).
move => s w h. rewrite /completeness_relationG /completeness_relation /IsDL /=. (* move => eq. *)
rewrite /(^^).
rewrite EG.inzmodK.
rewrite - pow_mod. 
rewrite lll. apply g_unit. auto.
rewrite - bbb.
rewrite - h. auto.
qed.




lemma llll (x y : zmod) : unit x => unit y => (Zps.( * ) (Sub.insubd x)  (Sub.insubd y) )= Sub.insubd (x * y).
progress. smt. qed.

lemma exp_lemma4 : forall (x : zmod) (n : int), unit x => (ZModpField.exp x q) = one =>  (x ^^ n) = Sub.val ((Sub.insubd x) ^^ (EG.inzmod n)). 
proof. progress. rewrite /(^^). rewrite lll. auto.
rewrite  EG.inzmodK.
have ->: (ZModpField.exp x (n %% q)) = (ZModpField.exp x n). smt.
rewrite Sub.insubdK.
smt.
auto.
qed.


lemma exp_lemma5 : forall (z : zmod) (n : int), unit z => 0 <= n => (ZModpField.exp z q) = one  => Sub.insubd z ^^ (EG.inzmod n) = (Zps.(^) (Sub.insubd z) n).
progress. rewrite /(^^). 
rewrite lll. auto. 
rewrite - bbb.
rewrite Sub.insubdK. rewrite /P. smt.
have ->: (EG.asint ((EG.inzmod n))%EG) = n %% q. smt.
rewrite lll. auto.  
rewrite Sub.insubdK. smt.
rewrite  (exp_mod' z n q _). auto. auto.
qed.


   


lemma nosmt dokas : forall s w, s = ZModpField.exp g w => ZModpField.exp s q = one.
progress. 
have ->: (ZModpField.exp ((ZModpField.exp g w)) q) = (((ZModpField.exp g (w * q)))). 
 rewrite - ZModpField.exprM. auto.
have -> : w * q = q * w. smt().
have ->: (ZModpField.exp g (q * w)) = (ZModpField.exp ((ZModpField.exp g q)) w).
rewrite  ZModpField.exprM. auto.
rewrite  g_q_assumption. smt(@ZModpField).
qed.

(* in completeness not needed for any q, but only for THE q *)

lemma completenessG (s : statement) (w : witness) &m: completeness_relationG s w =>
   Pr[ CompletenessG(SchnorrProver, SchnorrVerifier).main(s,w)@&m : res] = 1%r.
proof. progress.
have statement_not_zero : unit s. rewrite - H. apply exp_lemma6. apply g_unit.
rewrite /completeness_relation /IsDL in H.
rewrite - (LSP.dl_completeness (Sub.insubd s) (EG.inzmod w) &m). 
  apply completeness_relation_compatible. auto.
byequiv (_: _ ==> _). proc.
inline*. wp. 
rnd EG.inzmod EG.asint. wp. rnd EG.inzmod EG.asint. wp. skip. progress. smt(@EG). smt(@DInterval @EG).
rewrite EG.inzmodK. 
 have : 0 <= r0L < q. smt(@DInterval @List). 
smt(@IntDiv).
smt(@EG).
smt(@DInterval @EG).
smt(@DInterval @EG).
have -> :((s{1} ^^ q) = one) =  ((Sub.insubd s{1}) ^^ (EG.inzmod q) = (Sub.insubd one)).
rewrite exp_lemma4. auto. rewrite (dokas s{1} w{1}). rewrite - H. auto. auto.
rewrite - (bbb ( ((Sub.insubd s{1})%Sub ^^ (EG.inzmod q))) (Sub.insubd one)). 
have -> : (Sub.val ((Sub.insubd one))%Sub) = one. 
rewrite Sub.insubdK. smt(@Zp). auto. auto. simplify. rewrite /verify_transcript. simplify.
have ->: ((g ^^ (r0L + c0L * w{1})) = (s{1} ^^ c0L) * (g ^^ r0L))  
  = ((Sub.insubd g)%Sub ^^ (EG.(+) (EG.inzmod r0L) (EG.( * ) (EG.inzmod c0L)  (EG.inzmod w{1})))%EG =
 (Sub.Lift.lift2 Zp.( * ) ((Sub.insubd s{1})%Sub ^^ (EG.inzmod c0L)%EG)
    ((Sub.insubd g)%Sub ^^ (EG.inzmod r0L)%EG))%Sub.Lift ).
rewrite /lift2. 
rewrite exp_lemma4. apply g_unit. apply g_q_assumption.
rewrite exp_lemma4. assumption. rewrite (dokas s{1} w{1}). rewrite - H. auto. auto.
rewrite exp_lemma4. apply g_unit. apply g_q_assumption.
simplify.
have ->: (EG.inzmod (r0L + c0L * w{1})) 
 = (EG.(+) (EG.inzmod r0L) (EG.( * ) (EG.inzmod c0L)  (EG.inzmod w{1}))). smt(@EG).
rewrite - bbb.
 pose x := (Sub.val ((Sub.insubd g)%Sub ^^ (EG.(+) (EG.inzmod r0L) (EG.( * ) (EG.inzmod c0L) (EG.inzmod w{1}))))).
rewrite Sub.insubdK. rewrite /P. smt.
rewrite - exp_lemma4. assumption. rewrite (dokas s{1} w{1}). rewrite - H. auto. auto. rewrite - exp_lemma4.  apply g_unit. apply g_q_assumption.
auto.
pose x := (Sub.insubd g)%Sub ^^ (EG.(+) (EG.inzmod r0L) (EG.( * ) (EG.inzmod c0L)  (EG.inzmod w{1})))%EG.
pose z := Sub.insubd s{1}.
pose o := Sub.insubd one.
rewrite /Zp.( * ).
pose y := (Sub.Lift.lift2 Ring_ops_spec.Zp.( * ) ((Sub.insubd s{1})%Sub ^^ (EG.inzmod c0L)%EG)
    ((Sub.insubd g)%Sub ^^ (EG.inzmod r0L)%EG)).
rewrite exp_lemma5. assumption. smt(@DInterval).
rewrite - H. 
  have ->: (ZModpField.exp ((ZModpField.exp g w{1})) q) = (((ZModpField.exp g (w{1} * q)))). 
   rewrite - ZModpField.exprM. auto.
  have -> : w{1} * q = q * w{1}. smt().
  have ->: (ZModpField.exp g (q{1} * w{1})) = (ZModpField.exp ((ZModpField.exp g q{1})) w{1}).
  rewrite  ZModpField.exprM. auto.
  rewrite g_q_assumption. smt(@ZModpField).
timeout 20. 
rewrite /(^^).
have ->: Zps.(^) z ((EG.asint ((EG.inzmod q)))) = Zps.(^) z q. 
rewrite  EG.inzmodK. 
  have ->: (q %% q) = 0. smt(@IntDiv).
  have ->: Zps.(^) z 0 = (Sub.insubd one). smt(@Zps).
  rewrite /z. rewrite lll. assumption. 
  rewrite (dokas s{1} w{1}). rewrite - H. auto. auto. auto.
auto. auto.
qed.






(* Extractability  *)
import Rew.

op sec_to_sbits : secret -> sbits.
op sec_from_sbits : sbits -> secret.
axiom sec_enc x : x = sec_from_sbits (sec_to_sbits x).
axiom sec_inj : injective sec_to_sbits.


(* Remove secret from commitment and response *)
module type ZKMaliciousProverG = {
  proc commitment() : commitment
  proc response(c : challenge) : response
}.


module type ZKRewindableMaliciousProverG = {
  proc commitment() : commitment
  proc response(c : challenge) : response
  proc getState() : sbits 
  proc setState(b : sbits) : unit 
}.

module SoundnessG(P : ZKMaliciousProverG, V : ZKVerifierG) = {
  proc run(s:statement) = {
    var z, c,t,v;
    z <@ P.commitment();
    c <@ V.challenge();
    t <@ P.response(c);
    v <@ V.verify(s,z,c,t);
    return v;
  }
}.

module type ExtractorG(P: ZKRewindableMaliciousProverG) = {
  proc extract(statement: statement): witness
}.

module SpecialSoundnessAdversaryG(P : ZKRewindableMaliciousProverG)  = {
  proc attack(statement:statement):(commitment * int * response) * (commitment * int * response) = {
    var i,c1,c2,r1,r2,pstate;
    i <@ P.commitment();
    c1 <$ [0..q-1];
    pstate <@ P.getState();
    r1 <@ P.response(c1);
    c2 <$ [0..q-1];
    P.setState(pstate);
    r2 <@ P.response(c2);
    return ((i,c1,r1), (i,c2,r2));
  }
}.


op special_soundness_extractG (t1 t2 : commitment * challenge * response): witness = 
 EG.asint (special_soundness_extract witness (Sub.insubd t1.`1, EG.inzmod t1.`2, EG.inzmod t1.`3) (Sub.insubd t2.`1, EG.inzmod t2.`2,EG.inzmod t2.`3)).

module (ExtractorG : ExtractorG)(P : ZKRewindableMaliciousProverG) = {  
  module SA = SpecialSoundnessAdversaryG(P)
  proc extract(p : statement) : witness = {
    var t1,t2;
    (t1,t2) <@ SA.attack(p);
    return special_soundness_extractG t1 t2;
 }
}.


section.

declare module P <: ZKRewindableMaliciousProverG{-HV}.
declare axiom P_response_ll : islossless P.response.
declare axiom P_commitment_ll : islossless P.commitment.

(* rewindability assumption *)
declare axiom rewindable_P_plus :
        (exists (f : glob P -> sbits),
         injective f /\
        (forall &m, Pr[ P.getState() @ &m : (glob P) = ((glob P){m})
                                          /\ res = f ((glob P){m} ) ] = 1%r) /\
        (forall &m b (x: glob P), b = f x =>
           Pr[P.setState(b) @ &m : glob P = x] = 1%r) /\ islossless P.setState).




local module P' = {
  proc commitment(s : dl_stat) : dl_com  = {
    var r;
    r <@ P.commitment();
    return (Sub.insubd r);
  }  
  proc response(challenge : dl_chal) : dl_resp  = {
    var r;
    r <@ P.response( EG.asint challenge);
    return (EG.inzmod r);
  }  
  proc getState = P.getState
  proc setState = P.setState
}.



lemma lles (a b : real) : 0%r <= a <= 1%r => 0%r <= b <= 1%r 
  => a  <= b  =>  a ^ 2 <= b ^ 2.
smt(@RealOrder).
qed.

lemma lles2 (a b x y : real) : 0%r <= a <= x => 0%r <= b <= y
  => a * b <= x * y.
smt(@Real @RealOrder).
qed.

lemma lles3 (a b : real) : 0%r < a => 0%r <= a * b => 0%r <= b.
progress.
smt(@Real @RealOrder).
qed.

lemma extractabilityG &m (s : zmod): 
  Pr[ExtractorG(P).extract(s) @ &m : LSP.soundness_relation (Sub.insubd s) (EG.inzmod res) ] >=
  (Pr[SoundnessG(P, SchnorrVerifier).run(s) @ &m : res] ^ 2
       - 1%r / (size EG.DZmodP.Support.enum)%r
           * Pr[SoundnessG(P, SchnorrVerifier).run(s) @ &m : res]).
proof. 
(* s = zero *)
case (s = zero). move => s_is_zero.
  have ->: Pr[SoundnessG(P, SchnorrVerifier).run(s) @ &m : res] = 0%r.
  pose ss := s.
  byphoare (_: arg = s ==> _). proc. hoare.
  inline*. wp.  call (_:true). wp. rnd. call(_:true). skip. progress. rewrite s_is_zero. 
  have ->: ZModpField.exp zero  q = zero. 
    rewrite (ZModpField.expr0z q). smt(q_prime).
  smt(@Zp). auto. auto. simplify.
  have ->: 0%r ^ 2 = 0%r. smt(@Real). 
  rewrite Pr[mu_ge0]. auto.
(* s <> zero *)
move => s_not_zero.
have soundness_less : Pr[SoundnessG(P, SchnorrVerifier).run(s) @ &m : res]
 <= Pr[Soundness(P', HV).run(Sub.insubd s) @ &m : res].
byequiv (_: _ ==> _).
proc. inline*. wp.  call(_:true). wp. 
rnd EG.inzmod EG.asint. wp. call (_:true). wp. skip. progress.
smt(@EG).  
smt(@DInterval @EG).
smt(@DInterval @EG).  
(* result_R = zero *)
case (result_R = Zp.zero). 
move => result_R_zero. smt.
(* result_R <> zero  *)
move => commitment_non_zero.
have f: ((g ^^ result_R0) = (s{1} ^^ c0L) * result_R)
             => ((Sub.insubd g)%Sub ^^ (EG.inzmod result_R0)%EG =
 (Sub.Lift.lift2 Ring_ops_spec.Zp.( * ) ((Sub.insubd s{1})%Sub ^^ (EG.inzmod c0L)%EG)
    ((Sub.insubd result_R)))%Sub.Lift ).
rewrite /lift2.
rewrite exp_lemma4. apply g_unit. apply g_q_assumption.
rewrite exp_lemma4. apply unitE. assumption. assumption.
simplify.
rewrite - bbb.
pose x := (Sub.val ((Sub.insubd g)%Sub ^^ (EG.inzmod result_R0))).
rewrite Sub.insubdK.
rewrite - exp_lemma4. apply unitE. assumption. assumption. 
rewrite /P.
  have ->: (Sub.val ((Sub.insubd result_R))%Sub) = result_R. 
    rewrite Sub.insubdK. apply unitE. assumption. auto.
    smt.
rewrite - exp_lemma4. apply unitE. assumption. assumption.
rewrite Sub.insubdK. smt(@Ring_ops_spec.Zp). auto.
apply f. auto.
rewrite - bbb.
      (* TODO *)
rewrite -  exp_lemma5. apply unitE. assumption. smt(@DInterval). assumption.
timeout 20. smt. 
auto.
auto.
have -> : Pr[ExtractorG(P).extract(s) @ &m : soundness_relation (Sub.insubd s)  (EG.inzmod res)] 
 = Pr[Extractor(P').extract(Sub.insubd s) @ &m : soundness_relation (Sub.insubd s) res].
byequiv (_: _ ==> _). proc.
inline*. wp. call (_:true). wp. 
call (_:true). wp. 
rnd EG.inzmod EG.asint. wp. call (_:true). wp.
call (_:true). rnd EG.inzmod EG.asint. wp.  call (_:true). wp.  skip. progress. 
smt. smt(@DInterval @EG). smt(@EG @DInterval). smt(@EG @DInterval).
have -: LSP.soundness_relation ((Sub.insubd p{1}))%Sub
      ((EG.inzmod
          (special_soundness_extractG (result_R, c1L, result_R1)
             (result_R, c2L, result_R2))))%EG.
auto. clear H9.
rewrite /soundness_relation /IsDL /special_soundness_extract. simplify.
rewrite /special_soundness_extractG. simplify. rewrite /special_soundness_extract.
simplify. smt.
have -: soundness_relation ((Sub.insubd p{1}))%Sub
      (special_soundness_extract ((Sub.insubd p{1}))%Sub
         ((Sub.insubd result_R)%Sub, (EG.inzmod c1L)%EG, (EG.inzmod result_R1)%EG)
         ((Sub.insubd result_R)%Sub, (EG.inzmod c2L)%EG, (EG.inzmod result_R2)%EG)). auto.
rewrite /soundness_relation /IsDL /special_soundness_extract. simplify.
rewrite /special_soundness_extractG. simplify. rewrite /special_soundness_extract.
simplify. smt.
auto. auto.
have  :   Pr[Soundness(P', HV).run((Sub.insubd s)%Sub) @ &m : res] ^ 2 -
  1%r / (size EG.DZmodP.Support.enum)%r *
  Pr[Soundness(P', HV).run((Sub.insubd s)%Sub) @ &m : res] <=
  Pr[Extractor(P').extract((Sub.insubd s)%Sub) @ &m :
     soundness_relation ((Sub.insubd s))%Sub res]. 
apply (dl_statistical_PoK P' _ _ _ &m (Sub.insubd s)).
proc. call P_response_ll. auto.
proc. call P_commitment_ll. auto.
apply rewindable_P_plus.
pose a:= Pr[Soundness(P', HV).run((Sub.insubd s)) @ &m : res].
pose b:= Pr[Extractor(P').extract((Sub.insubd s)%Sub) @ &m :
   soundness_relation ((Sub.insubd s))%Sub res].
pose c := (size EG.DZmodP.Support.enum)%r.
pose q := Pr[SoundnessG(P, SchnorrVerifier).run(s) @ &m : res].
progress.
case ((q ^ 2 - q / c) <= 0%r). smt.
move => pos. have impfact :  0%r < q * (q - 1%r / c). timeout 10. smt(@Real @RealOrder).
have : q <= a. auto. move => aq.
have ls1 : 0%r <= a <= 1%r. smt.
have ls2 : 0%r <= q <= 1%r. smt.
have : q ^ 2 - q / c  <=  a ^ 2 - a / c .
 have ->: q ^ 2 - q/c = q * (q  - 1%r/c). smt(@Real).
 have ->: a ^ 2 - a/c = a * (a  - 1%r/c). smt(@Real).
 have z: (q - 1%r / c) <= (a - 1%r / c). smt(@Real).
 apply lles2.  split. smt(@Real @RealOrder).
auto. 
split. 
apply (lles3 q). smt(@Real @RealOrder). smt(@Real @RealOrder).
auto.
smt(@Real @RealOrder).
qed.

end section.

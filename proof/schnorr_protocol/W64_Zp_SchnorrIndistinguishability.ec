require import AllCore Distr DInterval List Int IntDiv.
require import AuxLemmas.

from Jasmin require import JModel JBigNum.
require import Array32 Array64 Array128.
require import W64_SchnorrExtract.
require import W64_SchnorrProtocol.


require Constants.


require import ModularMultiplication_Concrete.
require import BarrettReduction_Concrete.

require import Ring_ops_spec Ring_ops_proof.
import W64xN R.                 
(* import Sub  *)

require Zp_SchnorrProtocol.


clone import Zp_SchnorrProtocol as ZPSP with op q <= Constants.q,
                                             op Zp.p <= Constants.p,
                                             op g <= Zp.inzmod Constants.g,
                                             type LSP.sbits <- sbits.
import ZPSP.Zp Zp.DZmodP Zp.Sub.



require MontgomeryLadder_Concrete.
clone import MontgomeryLadder_Concrete as MLC with theory Zp <= Zp.

axiom q_prime : prime q.
axiom p_prime : prime p.


axiom q_less_p       : q < p.
axiom q_val_prop1 x  : W64xN.valR x < q * q. 
axiom p_less_modulusR : p < W64xN.modulusR.


op Rip : int = nasty_id (4 ^ (dnlimbs * nlimbs) %/ q).
lemma Rip_def: Rip = 4 ^ (dnlimbs * nlimbs) %/ q.
rewrite /Rip. smt(nasty_id). qed.


lemma zp_eq z1 z2 : (val z1 = val z2) = (z1 = z2). smt(@Zp). qed.
lemma zp_mul (z1 z2 : zmod) : val (z1 * z2) = (val z1 * val z2) %% p. 
by smt(@Zp). qed.
lemma inzpKK: forall (z : int), val (inzmod z) = z %% p. smt(@Zp). qed.

  
module ASpecFp_Schnorr = {


 proc commit(h : zmod, w : R) : zmod * int = {
   var r;
   var a : zmod;    
   r <@ ASpecFp.rsample(q);
   a <@ ML_Spec.expm(g,r);
   return (a,  r);
  } 

  proc challenge() : int = {
   var r;
   r <@ ASpecFp.rsample(q);
   return r;
  }
}.

op completeness_relationJ (s: W64xN.R.t) (w:W64xN.R.t) = Constants.g ^ (W64xN.valR w) %% p = W64xN.valR s %% p.

lemma p_val_prop1 x : W64xN.valR x < p * p.  
by smt(q_less_p q_val_prop1 q_prime prime_p). 
qed.


lemma xxx:
  forall (a b : int), (inzmod a) = (inzmod b) <=> a %% p = b %% p.
smt(@Sub).
qed.


lemma w64_and (x y : W64.t) : (x = W64.one \/ x = W64.zero) 
 => (y = W64.one \/ y = W64.zero) => (x `&` y = W64.one) = (x = W64.one /\ y = W64.one). smt(@W64).
qed.


lemma w64_and_false (x y : W64.t) : (x = W64.one \/ x = W64.zero) 
 => (y = W64.one \/ y = W64.zero) => (x `&` y = W64.zero) = ((x = W64.one /\ y = W64.zero)  \/  (x = W64.zero /\ y = W64.one) \/ (x = W64.zero /\ y = W64.zero)). smt(@W64).
qed.

lemma exps_same (g : zmod) : ZModpField.exp g = ZModpRing.exp g.
rewrite /ZModpField.exp. rewrite /ZModpRing.exp. auto. qed.


lemma exps' (s : zmod) : forall n, 0 <= n => val (ZModpField.exp s n) = (val s ^ n) %% p.
apply intind. progress. smt(@ZModpField @Sub).
progress.
rewrite exprSr. auto.
rewrite ZModpField.exprSr. auto.
rewrite zp_mul.
rewrite H0.
smt(@IntDiv). 
qed.


lemma exps (x : zmod) : forall n, 0 <= n => (x ^ n) = (x ^^ n). 
apply intind. progress.
smt(@Zp @Ring).
progress.
have ->: (x ^ (i + 1)) = x * (x^ i). 
 rewrite /(^).
 have ->: asint x ^ (i + 1) = (asint x) * (asint x ^ i). smt.
 rewrite inzmodM. congr. rewrite asintK. auto.
have ->: (x ^^ (i + 1)) = x * (x ^^ i). smt.
rewrite H0.
auto.
qed.


lemma completness_compat s w : 
 completeness_relationJ s w
 =  completeness_relationG (inzmod (valR s)) (valR w).
(* move => s_not_zero. *)
rewrite /completeness_relationJ /completeness_relation /IsDL.
rewrite /completeness_relationG.
have ->: (ZModpField.exp (inzmod Constants.g) (valR w)) = ((inzmod Constants.g)  ^^ (valR w)). auto.
rewrite - exps. smt(@W64xN).
have ->: inzmod Constants.g ^ valR w = inzmod (Constants.g ^ valR w). smt.
rewrite xxx. auto.
qed.

(* lemma rels_compat s w : (valR s) %% p <> 0 => *)
(*  completeness_relationJ s w  *)
(*  =  LSP.completeness_relation  (ZPS.Sub.insubd (inzmod (valR s))) (LSP.EG.inzmod (valR w)). *)
(* move => s_not_zero. *)
(* rewrite /completeness_relationJ /completeness_relation /IsDL. *)
(* rewrite exp_lemma5. apply g_unit. smt(@W64xN). *)
(* rewrite g_q_assumption. auto. *)
(* rewrite  lll.  apply g_unit. *)
(* rewrite - bbb. *)
(* rewrite ZPS.Sub.insubdK. rewrite /P. smt(g_unit @ZModpField). *)
(* rewrite ZPS.Sub.insubdK. rewrite /P.  *)
(* apply unitE. rewrite /Zp.zero. smt(@Zp). *)
(* have ->: (ZModpField.exp (inzmod Constants.g) (valR w)) = ((inzmod Constants.g) ^^ (valR w)). rewrite /(^^). auto. *)
(* rewrite - exps. smt(@W64xN). *)
(* rewrite /(^). *)
(* rewrite inzmodK. *)
(* have ->: (Constants.g %% p) = Constants.g. rewrite /Constants.g. smt(@Zp). *)
(* rewrite xxx. *)
(* have ->: (Constants.g %% Constants.p) = Constants.g. rewrite /Constants.g. smt(@Zp). *)
(* auto. *)
(* qed. *)

(* TODO: move to constants *)
op yy : int = 1619143025881598520624761283475402020548391884071535717508227364160250029021913075600233405069001566834683913353926864105451868045119367799203330594939018027579182910491986631752134379672737328627758392039634104925436356398864177945255144950961436710218515919232515425511046597212472673535352725377222373577674557399263766126616709301502213900518108948863077641585338203695018313411734375313490314236425883902205676609966518701386913481608853106992344785426585987776048274548105346527876890352239772208848767741675883443476938540148618750188887210747096545526357760228916139597422735471808664106841641302833036768868.

op zz : int = 32317006071311007301090839450916075672074637894498330470309491614874605269258845429066617750438611497217172998255766216223761011478474532650974905473458381524348224983452534238842699055706528839316900073176359409123413739445397952234623184300460154670470987008412185029124584489601900670931121854398190604800292822877845957165654247519063010445688374293905515743037557007239230573090162415731314434935337651887720640264611889321352234483385341531370885728478742938129783934088697644527630028295616871380503535956364143710134154492766231832072494607343336005619107670188720508364918065676485338559326165037076233303652.

op ww : int = 1044388881413152506691752710716624382579964249047383780384233483283953907971557456848826811934997558340890106714439262837987573438185793607263236087851365277945956976543709998340361590134383718314428070011855946226376318839397712745672334684344586617496807908705803704071284048740118609114467977783598029006686938976881787785946905630190260940599579453432823469303026696443059025015972399867714215541693835559885291486318237914434496734087811872639496475100189041349008417061675093668333850551032972088269550769983616369411933015213796825837188091833656751221318492846368125550225998300412344784862595674492194617023806505913245610825731835380087608622102834270197698202313169017678006675195485079921636419370285375124784014907159135459982790513399611551794271106831134090584272884279791554849782954323534517065223269061394905987693002122963395687782878948440616007412945674919823050571642377154816321380631045902916136926708342856440730447899971901781465763473223850267253059899795996090799469201774624817718449867455659250178329070473119433165550807568221846571746373296884912819520317457002440926616910874148385078411929804522981857338977648103126085903001302413467189726673216491511131602920781738033436090243804708340403154190336.


lemma pq_euclid : euclidef ww Constants.p (zz, yy).
rewrite /euclidef. split. auto.
smt().
qed.


lemma bp_comp : Ri = Constants.bp. 
rewrite /Ri. rewrite nasty_id. simplify.
rewrite /edivz. simplify. simplify.
have ->: `|Constants.p| = Constants.p. 
auto.
rewrite /edivn. simplify. rewrite /euclidef. simplify.
have ->: Constants.p < 0 = false. auto. simplify.
have ->: (Constants.p = 0) = false. auto. simplify.
pose P := (fun (qr : int * int) =>
        ww =
        qr.`1 * Constants.p + qr.`2 /\ 0 <= qr.`2 && qr.`2 < `|Constants.p|).
have f1 : P (choiceb P (0,0)).
apply choicebP. exists (zz,yy). rewrite /P. simplify. split. rewrite /ww /zz /Constants.p /yy. simplify. auto.
smt(). 
elim f1. 
have z: choiceb
     (fun (qr : int * int) =>
        ww =
        qr.`1 * Constants.p + qr.`2 /\ 0 <= qr.`2 && qr.`2 < `|Constants.p|) (0,0) 
  = (choiceb P (0, 0)). auto.
progress. rewrite z.
rewrite /signz. 
have ->: (Constants.p < 0) = false. auto. simplify.
have ->: (Constants.p <> 0) = true. auto. 
have ->: (-1) ^ b2i false = 1. rewrite /b2i. simplify. auto.
have ->: 1 * b2i true  = 1. rewrite /b2i. simplify.  auto. simplify.
have ->: (let (q, r) = choiceb P (0, 0) in (q, r)).`1 = (choiceb P (0, 0)).`1.  smt().
have mem' : 
  forall (x1 y1 x2 y2 l : int),
    x1 \in range 0 l =>
    x2 \in range 0 l => x1 + l * y1 = x2 + l * y2 => y1 = y2 .
smt(mem_range_add_mul_eq).
have : (choiceb P (0, 0)).`1 = zz.
apply (mem' (choiceb P (0, 0)).`2 (choiceb P (0, 0)).`1  yy zz  Constants.p). 
smt(@List). smt(@List).
have ->: (choiceb P (0, 0)).`2 + Constants.p * (choiceb P (0, 0)).`1 = (choiceb P (0, 0)).`1 * Constants.p + (choiceb P (0, 0)).`2.
smt().
rewrite - H. simplify. rewrite /ww /yy /zz /Constants.p. simplify. done.  auto.
qed.


lemma verify_eq : 
  equiv [ SchnorrVerifier.verify ~ JVerifier.verify :
          Sub.val(s{1}) = valR statement{2}    %% p
       /\ Sub.val(z{1}) = valR commitment_0{2} %% p
       /\ c{1} %% q = (valR (challenge_0{2}))  %% q
       /\ t{1} %% q = (valR response_0{2})     %% q
       ==> (res{1} = (res{2} = W64.one)) /\ (res{2} = W64.zero \/ res{2} = W64.one) ].
proc. sp. simplify. wp.
ecall {2} (bn_eq_correct v3{2} v4{2}). simplify. 
ecall {2} (bn_set1_correct). simplify. 
ecall {2} (bn_expm_correct group_barrett{2} group_order{2} statement{2} exp_order{2}). simplify.      
ecall {2} (bn_eq_correct v1{2} v2{2}). simplify. 
ecall {2} (bn_expm_correct group_barrett{2} group_order{2} group_generator{2} response_0{2}). simplify. 
ecall {2} (bn_mulm_correct commitment_0{2} tmp{2} group_order{2}). simplify.
ecall {2} (bn_expm_correct group_barrett{2} group_order{2} statement{2} challenge_0{2}). simplify. 
ecall {2} (bnreduce_small_spec_ph response_0{2} exp_order{2}). simplify.
ecall {2} (bnreduce_small_spec_ph challenge_0{2} exp_order{2}). simplify.
ecall {2} (bnreduce_small_spec_ph commitment_0{2} group_order{2}). simplify.
ecall {2} (bnreduce_small_spec_ph statement{2} group_order{2}). simplify.
call{2} Constants.bn_set_g_correct.
call{2} Constants.bn_set_bp_correct.
call{2} Constants.bn_set_p_correct.
call{2} Constants.bn_set_bq_correct.
call{2} Constants.bn_set_q_correct.
simplify.
skip. progress.
rewrite ri_un. rewrite H6. rewrite /ri. smt().
rewrite H5. smt(prime_p).
smt(@W64xN).
smt(@W64xN).
rewrite H5. 
smt(p_val_prop1).
smt(prime_p).
smt(@W64xN).
smt(@W64xN).
rewrite H5. 
smt(p_val_prop1).
rewrite ri_un. rewrite H4. rewrite /ri. rewrite H3. smt().
smt(q_prime).
smt(@W64xN).
smt(@W64xN).
smt(q_val_prop1).
smt(q_prime).
smt(@W64xN).
smt(@W64xN).
smt(q_val_prop1).
smt().
rewrite /R. 
rewrite bp_comp.
rewrite - H6.  
rewrite R2.bnK. auto.
smt(@W64xN).
smt().
smt(@W64xN).
smt().
smt(@Zp).
  have sq_fact: ((ZModpField.exp s{1} q) = ZPS.Zp.one)
            = (result15 = W64.one). 
  rewrite H58. rewrite H56. rewrite H15. rewrite H5. rewrite H3. rewrite H57.
  have ->: (valR statement{2} %% Constants.p) = val s{1}. smt().
  have ->: (ZModpField.exp s{1} q) = s{1} ^^ q. 
    rewrite /(^^). smt(@ZModpField).
    rewrite - exps. smt(q_prime). rewrite /(^) /asint /ZPS.Zp.one xxx.  
    smt.
rewrite sq_fact.
have ->: (result12 `&` result15 = W64.one) 
  = (result12 = W64.one /\ result15 = W64.one). 
rewrite w64_and. smt(). smt(). auto.
rewrite  H52 - H48 H51 H39  H3 - H2 H7 H23 H42 H15 H5 - H - H0 H31 H3 - H1.
case (result15 = W64.one). progress. simplify.
rewrite - (zp_eq (g ^^ t{1}) (s{1} ^^ c{1} * z{1}) ). simplify.
 have ->: (val (g ^^ t{1}) = val (s{1} ^^ c{1} * z{1}))
  = (val (z{1} * s{1} ^^ c{1} ) = val (g ^^ t{1})). smt().
rewrite zp_mul.
congr.
congr.
congr.
congr.
rewrite /(^^).
have ->: (ZModpRing.exp s{1} c{1}) = (ZModpField.exp s{1} c{1}). 
rewrite exps_same. auto.
have  <- : (ZModpField.exp s{1} (c{1} %% q)) = (ZModpField.exp s{1} c{1}). 
rewrite (exp_mod s{1} c{1} q). rewrite sq_fact. auto. auto.
rewrite exps'. smt(@IntDiv).
auto. auto.
rewrite /(^).
have ->: val (ZModpField.exp g t{1})  = val (ZModpField.exp g (t{1} %% q)).
rewrite /(^^).
rewrite (exp_mod g t{1} q). rewrite g_q_assumption. auto.
auto.
rewrite  exps'. smt(@IntDiv). auto. rewrite /Constants.g /g. smt(@Zp).
progress.
rewrite (w64_and result12 result15). smt(). smt().
rewrite (w64_and_false result12 result15). 
smt(). smt().
smt().
qed.


require import UniformSampling_Concrete.

lemma commit_same1 : 
  equiv [ JProver.commitment ~ ASpecFp_Schnorr.commit 
          :   true
  ==> (val res{2}.`1) = (valR res{1}.`1)
    /\ res{2}.`2 = (valR res{1}.`2) ].
proc. 
symmetry. call expm_correct.
symmetry.
call usample_aspec. sp.
simplify.
call{1} Constants.bn_set_bp_correct.
call{1} Constants.bn_set_g_correct.
call{1} Constants.bn_set_p_correct.
call{1} Constants.bn_set_q_correct.
skip. move => &1 _ H r qe r2 vr rr iz rp vri.
split. rewrite qe. simplify. smt(q_prime).
move => h1. move => rL rR. move => rzrlrr. 
split. 
split.  smt. split. smt. split.  smt. split.  smt. rewrite /R. 
rewrite bp_comp.
rewrite - vri. smt(@W64x2N @R2).
move => qo. move => rl rrr ai. smt.
qed.


lemma commit_same : 
  equiv [ SchnorrProver.commitment ~ ASpecFp_Schnorr.commit 
          : true  ==> ={res} ].
proc. 
inline *. wp.  simplify. sp.
rnd.
skip. progress.  smt(@Distr).  
rewrite - zp_eq.
rewrite exps. smt(@DInterval).
rewrite /(^^) /(^).
auto.
qed.

lemma commitment_eq : 
  equiv [ SchnorrProver.commitment ~ JProver.commitment :
  true
  ==> (val res{1}.`1) = (valR res{2}.`1)
    /\ res{1}.`2 = (valR res{2}.`2) ].
transitivity ASpecFp_Schnorr.commit
  (true ==> ={res})
  (true
  ==> (val res{1}.`1) = (valR res{2}.`1)
    /\ res{1}.`2 = (valR res{2}.`2)). auto. auto.
apply commit_same.
symmetry. apply commit_same1.
qed.
     




lemma challenge_same : 
  equiv [ SchnorrVerifier.challenge ~ ASpecFp_Schnorr.challenge
          : true  ==> ={res} ].
proc. inline*. wp. rnd. wp. skip.
progress.
qed.

lemma challenge_eq : 
  equiv [ SchnorrVerifier.challenge ~ JVerifier.challenge :
  true ==> res{1} = (valR res{2}) ].
transitivity ASpecFp_Schnorr.challenge
  (true ==> ={res})
  (true
  ==> (res{1}) = (valR res{2})). auto. auto.
apply challenge_same.
proc. 
symmetry. call usample_aspec.
call{1} Constants.bn_set_q_correct. wp. skip. progress.
qed.


lemma response_eq : 
  equiv [ SchnorrProver.response ~ JProver.response :
        w{1}   %% q  = (valR (witness0{2}) )  %% q
    /\  r{1}   %% q  = (valR secret_power{2}) %% q
    /\  c{1}   %% q  = (valR challenge_0{2})  %% q
    ==> res{1} %% q  = (valR res{2}) ].
proc. sp. simplify.
ecall {2} (bn_addm2_ph secret_power{2} product{2} exp_order{2}). simplify. 
ecall {2} (bn_mulm_correct challenge_0{2} witness0{2} exp_order{2}). simplify.
ecall {2} (bnreduce_small_spec_ph witness0{2} exp_order{2}). simplify.
ecall {2} (bnreduce_small_spec_ph secret_power{2} exp_order{2}). simplify.
ecall {2} (bnreduce_small_spec_ph challenge_0{2} exp_order{2}). simplify.
call{2} Constants.bn_set_bq_correct. simplify.
call{2} Constants.bn_set_q_correct. simplify.
wp.
skip. 
progress. rewrite H3. rewrite ri_un. rewrite /ri. rewrite H2. smt().
smt. 
smt(@W64xN).
smt(@W64xN).
rewrite H2.   smt (q_val_prop1).
smt.
smt.
smt(@W64xN).
smt.
smt(@W64xN).
rewrite H2. smt (q_val_prop1).
smt(@W64xN).
rewrite H2. smt.
smt(@W64xN).
smt.
smt(@W64xN).
rewrite H2. smt.
smt(@W64xN).
rewrite H2. smt.
(* smt(@W64xN). *)
(* rewrite H2. smt (p_val_prop2 q_less_p). *)
rewrite - H38.
rewrite - H33. 
rewrite H2.
rewrite H27.
rewrite  H19 H2. rewrite - H0.
rewrite  H11 H2. rewrite - H1.
rewrite - H.
rewrite modzMml.
rewrite modzMmr. 
have -> : (r{1} + c{1} * w{1}) %% q
  = (r{1} %% q + (c{1} * w{1}) %% q ) %% q.
smt (modzDmr modzDml).
done.
qed.

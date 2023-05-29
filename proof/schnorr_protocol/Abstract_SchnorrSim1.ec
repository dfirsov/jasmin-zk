pragma Goals:printall.
require import AllCore DBool Bool List Distr AuxResults RealExp.
require import Abstract_SchnorrProtocol.

import CG EG.

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


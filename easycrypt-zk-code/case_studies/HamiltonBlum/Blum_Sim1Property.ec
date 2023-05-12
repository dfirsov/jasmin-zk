pragma Goals:printall.
require import AllCore DBool Bool List Distr Int AuxResults DJoin.
  
require import PrArg FSet StdRing StdOrder StdBigop.
(*---*) import RField RealOrder.
require Djoinmap.

require import Permutation Blum_Basics.

clone import ZeroKnowledge as ZK.
clone import OneShotSimulator as OSS.

import DJM.

module ZKP = {
  proc run(Ny : hc_stat, w : hc_wit, b : bool) = {
    var c,r,prm,fal,pi_gwco,pi_w;
    prm <$ perm_d K;
    fal <- permute_graph prm Ny;
    pi_gwco <@ DJM.main5(fal);
    c <- (unzip1 pi_gwco);
    pi_w <- permute_witness prm w;
    r <- if b then Left (prm, unzip2 pi_gwco) else Right (pi_w, unzip2 (prj_path pi_w pi_gwco));
    return (c, r);
  }
}.


(* one-shot simulator  *)
module Sim1(V : RewMaliciousVerifier)  = {
  proc sinit(p_a : hc_stat) : bool * (hc_com * hc_resp) = {
    var  g,bb,r;
    g <-  p_a;
    bb <$ {0,1};
    if (bb) {
       r <@ ZKP.run(p_a, witness, bb);
    }else{
       r <@ ZKP.run(compl_graph K, compl_graph_cyc K, bb);
    }
    return (bb, r);
  }

  proc run(pa : hc_stat)   = {
    var b',b,zryb,result,vstat;
    vstat <@ V.getState();
    (b',zryb) <@ sinit(pa);
    b <@ V.challenge(pa, zryb.`1);
    result <@ V.summitup(pa, zryb.`2);
    if (b <> b'){
      V.setState(vstat);
    }
    return (b = b', result);
  }
}.


section.
declare module V <: RewMaliciousVerifier {-HP, -ZK.Hyb.Count, -ZK.Hyb.HybOrcl}.

declare axiom V_summitup_ll : islossless V.summitup.
declare axiom V_challenge_ll : islossless V.challenge.
declare axiom P_response_ll : islossless HP.response.
declare axiom P_commitment_ll : islossless HP.commitment.


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


(* Sim1 rewinds itself in case of bad-event *)
lemma sim1_rew_ph : forall (x : (glob V) ),
    phoare[ Sim1(V).run :
             ((glob V)) = x
                 ==> ! res.`1 => ((glob V)) = x] = 1%r.
proof. progress.
exists* (glob V). elim* => V_v.
progress.
elim rewindable_V_plus.
move => fA [s1 [s2 [s3]]] [s4 [ s5 [s6 s7]]].
proc.
seq 1 : (V_v = (glob V) /\ vstat = fA V_v /\
  ((glob V)) =
  x).
call (_: true ==> true). auto. skip. auto.
call (s2 V_v).
skip. progress.
wp.
seq 3 : (vstat = fA V_v /\ x = (V_v)) 1%r.
call (_:true).  call (_:true). call (_:true). auto. wp.  auto.
simplify. call V_summitup_ll. call V_challenge_ll. sp.
conseq (_: true ==> true). progress.  
call (_:true). sp. 
seq 1 : (true). rnd. skip. auto. rnd.  skip. smt(@Distr).
if. call (_:true). wp. simplify. inline*. wp . rnd.
conseq (_: true ==> true). progress. 
smt (djoinmap_weight Com_lossless).
 wp.  rnd. skip. smt (perm_d_lossless).
skip. auto.
call (_:true).
wp. simplify. inline*. wp. rnd.
conseq (_: true ==> true). progress. 
smt (djoinmap_weight Com_lossless).
 wp.  rnd. skip. smt (perm_d_lossless).
 auto.  hoare. auto. auto. auto.
case (b = b').
rcondf 1. skip. auto. skip. auto.
rcondt 1. skip. auto. wp. call (s5 V_v). skip. auto. 
hoare. simplify.
call (_:true). call (_:true). conseq (_: _ ==> true). auto. 
auto.
auto.   hoare. simplify. 
call (s3 V_v). skip. progress. auto.
qed.

  

end section.


section.

op statProb : hc_stat.
op statWit : hc_wit.
declare axiom statGood : zk_relation statProb statWit.

declare module V <: RewMaliciousVerifier {-HP, -ZK.Hyb.Count, -ZK.Hyb.HybOrcl}.
declare module D <: ZKDistinguisher {-HP}.

declare axiom V_summitup_ll : islossless V.summitup.
declare axiom D_run_ll : islossless D.guess.
declare axiom V_summitup_ll2 : islossless V.summitup.
declare axiom V_challenge_ll2 : islossless V.challenge.
declare axiom D_guess_prop : equiv [ D.guess ~ D.guess : ={arg, glob V, glob ZK.Hyb.Count, glob ZK.Hyb.HybOrcl} 
  ==> ={res} ].

(* rewindability assumption  *)
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



  
local module Sim1_0(V : RewMaliciousVerifier, D : ZKDistinguisher) = {
  module ZKP_HP = ZKP
  proc sinit(p_a : hc_stat) : bool * (hc_com * hc_resp) = {
    var  g,bb,r;
    g <- p_a;
    bb <$ {0,1};

    if (bb) {
       r <@ ZKP_HP.run(p_a, witness, bb);
    }else{
       r <@ ZKP_HP.run((compl_graph K), (compl_graph_cyc K), bb);
    }
    return (bb, r);
  }

  proc simulate(pa : hc_stat, wa : hc_wit) : bool * bool  = {
    var b',b,zryb,result, rb;
    (b',zryb) <@ sinit(pa);
    b <@ V.challenge(pa, zryb.`1);
    result <@ V.summitup(pa, zryb.`2);
    rb <@ D.guess(pa, wa, result);
    return (b = b', rb);
  }
}.



local module Sim1_1(V : MaliciousVerifier) = {
  module ZKP_HP = ZKP
  proc sinit(p_a : hc_stat, w_a : hc_wit) = {
    var g,bb,r;
    g <- p_a;
    bb <$ {0,1};
    if (bb) {
       r <@ ZKP_HP.run(p_a, w_a, bb);
    }else{
        r <@ ZKP_HP.run(compl_graph K, w_a, bb);
    }
    return (bb, r);
  } 
  proc simulate(pa : hc_stat, wa : hc_wit) : bool * bool  = {
    var b',b,zryb,result, rb;
    (b',zryb) <@ sinit(pa,wa);
    b <@ V.challenge(pa, zryb.`1);
    result <@ V.summitup(pa,zryb.`2);
    rb <@ D.guess(pa, wa, result);
    return (b = b', rb);
  }
}.



local module ZKP' = {
  proc run(Ny : hc_stat, w : hc_wit, b : bool) = {
    var c,r,prm,fal,pi_w,ko,ok;
    prm <$ perm_d K;
    fal <- permute_graph prm Ny;
    (ok, ko) <@ DJM.main6(fal,prj_path (permute_witness prm w) fal, permute_witness prm w);
    pi_w <- permute_witness prm w;
    c <- (unzip1 (rep_path pi_w ok ko));
    r <- if b then Left (prm, unzip2 (rep_path pi_w ok ko)) else Right (pi_w, unzip2 ko);
    return (c, r);
  }
}.


local module Sim1_1'(V : MaliciousVerifier) = {
  proc sinit(p_a : hc_stat, w_a : hc_wit) = {
    var g,bb,r;
    g <- p_a;
    bb <$ {0,1};
    if (bb) {
       r <@ ZKP.run(p_a, w_a, bb);
    }else{
        r <@ ZKP'.run(compl_graph K, w_a, bb);
    }
    return (bb, r);
  } 
  proc simulate(pa : hc_stat, wa : hc_wit) : bool * bool  = {
    var b',b,zryb,result, rb;
    (b',zryb) <@ sinit(pa,wa);
    b <@ V.challenge(pa, zryb.`1);
    result <@ V.summitup(pa,zryb.`2);
    rb <@ D.guess(pa, wa, result);
    return (b = b', rb);
  }
}.


local module ZKP'' = {
  proc run(Ny : hc_stat, w : hc_wit, prm: permutation, cs : commitment list)  = {
    var c,ko,r,pi_w;
    ko <$ djoinmap Com (nseq K true);
    pi_w <- permute_witness prm w;
    c <- (rep_path pi_w cs (unzip1 ko));
    r <- if false then Left (prm, unzip2 ko) else Right (pi_w, unzip2 ko);
    return (c, r);
  }
}.



local module ZKP''' = {
  proc run(Ny : hc_stat, w : hc_wit, prm:permutation, b : bool) = {
    var c,r,fal,pi_gwco,pi_w;
    fal <- permute_graph prm Ny;
    pi_gwco <@ DJM.main5(fal);
    c <- (unzip1 pi_gwco);
    pi_w <- permute_witness prm w;
    r <- if b then Left (prm, unzip2 pi_gwco) else Right (pi_w, unzip2 (prj_path pi_w pi_gwco));
    return (c, r);
  }
}.



local module BlumUnhider2 : Unhider = {
  var prm : permutation
  proc choose() : bool list * bool list = {
    var fal1,fal2;
    prm <$ perm_d K;
    fal1 <- permute_graph prm (compl_graph K);
    fal2 <- permute_graph prm statProb;
    return (fal1,fal2);
  }
  
  proc guess(c : commitment list) : bool = {
    var bb,bb',r,result,dg;
    bb <$ {0,1};
    if (bb) {
       r <@ ZKP'''.run(statProb, statWit, prm,bb);
    }else{
        r <@ ZKP''.run(compl_graph K, statWit, prm, c);
    }    
    bb' <@ V.challenge(statProb, r.`1);
    result <@ V.summitup(statProb,r.`2);
    dg <@ D.guess(statProb, statWit, result);
    return (bb = bb') /\ dg;
  }
}.


local module M = {
  proc main6'(l : bool list, l' : bool list, w : int list) = {
    var xy;
    xy <@ DJM.main2(l,l');
    return  rep_path w xy.`1 xy.`2;
  }
}.

local lemma pr1 l l' w a &m : Pr[M.main6'(l,l',w) @ &m : res = a] = mu1 (dapply (fun xx' => rep_path w (fst xx') (snd xx')) ((djoinmap Com l) `*` (djoinmap Com l'))) a.
progress. byphoare (_: arg = (l,l',w) ==> _). proc.
inline*.  wp. sp. rnd. skip. progress.
rewrite dmap1E. simplify.
have ->: (fun (x : (commitment * opening) list * (commitment * opening) list) => rep_path w{hr} x.`1 x.`2 = a)
 = (pred1 a \o fun (xx' : (commitment * opening) list * (commitment * opening) list) => rep_path w{hr} xx'.`1 xx'.`2).
apply fun_ext. move => x. simplify. rewrite /(\o). rewrite /pred1.
auto. auto. auto. auto.
qed.


local lemma pr2 w l l' a &m : Pr[DJM.main5(rep_path w l' l) @ &m : res = a] = mu1 (djoinmap Com (rep_path w l' l)) a.
progress. byphoare (_: arg = (rep_path w l' l) ==> _). proc.
rnd. skip. progress. auto. auto.
qed.


local lemma kikk' w l l' : equiv [DJM.main5 ~ M.main6' : arg{1} = (rep_path w l' l) /\ arg{2} = (l,l',w) ==> res{1} = res{2} ].
bypr res{1} res{2}. auto.
progress. rewrite H. rewrite H0.  simplify. rewrite pr1. rewrite pr2. rewrite rep_path_distr.
auto.
qed.


local lemma kikk ww l l' : equiv [DJM.main5 ~ DJM.main6 : arg{1} = (rep_path ww l' l) /\ arg{2} = (l,l',ww) ==> res{1} = rep_path ww res.`1{2} res.`2{2} ].
symmetry.
transitivity M.main6'
 (={arg} /\ w{1} = ww ==> rep_path ww res.`1{1} res.`2{1} = res{2})
 (arg{2} = (rep_path ww l' l) /\ arg{1} = (l,l',ww) ==> ={res}).
smt().
smt().
proc.
call main12. skip. progress.
symmetry.
conseq (kikk' ww l l').
auto.
qed.


local lemma sim1_1' : equiv [Sim1_1(V).simulate ~ Sim1_1'(V).simulate : ={glob V, arg, glob ZK.Hyb.Count, glob ZK.Hyb.HybOrcl} ==> ={res}].
proc. 
inline Sim1_1(V).sinit.
inline Sim1_1'(V).sinit.
seq 5 5 : (={pa,wa,bb,r,glob V, glob ZK.Hyb.Count, glob ZK.Hyb.HybOrcl}).
seq 4 4 : (={pa,wa,p_a,w_a,bb,glob V, glob ZK.Hyb.Count, glob ZK.Hyb.HybOrcl}). 
rnd. wp. skip. progress.
if. progress. sim.
inline Sim1_1(V).ZKP_HP.run.
inline ZKP'.run. 
wp. 
seq 5 5 : (={Ny, w, bb,b0,prm, fal} /\ ={p_a, w_a, pa,wa,b0, glob V, glob Hyb.Count, glob Hyb.HybOrcl} /\ !b0{1} /\ fal{1} = permute_graph prm{1} Ny{1}). wp.  rnd. wp. skip. progress.
exists* fal{2}. exists* prm{2}. exists* w{2}. elim*. progress.
call (kikk (permute_witness prm_R w_R) fal_R (prj_path (permute_witness prm_R w_R) fal_R)).
skip. progress.
rewrite - prj_rep. auto.
rewrite  H. simplify. 
smt(rep_prj).
call D_guess_prop. 
call (_:true). call (_:true). wp. skip. progress.
qed.


local lemma sim1'_unhider : equiv [Sim1_1'(V).simulate ~ HidingGame(BlumUnhider2).main : ={glob V,  glob ZK.Hyb.Count, glob ZK.Hyb.HybOrcl} /\ arg{1} = (statProb, statWit) /\ arg{2} = true ==> (res.`1{1} /\ res.`2{1}) = res{2}].
proof. proc.
inline*. wp. call D_guess_prop. call(_:true). call (_:true). wp. sp. swap {2} 7 -6.
seq 1 1 : (={glob V, glob Hyb.HybOrcl, glob Hyb.Count,bb} /\ p_a{1} = pa{1} /\ w_a{1} = wa{1} /\ (pa{1},wa{1}) =(statProb,statWit) /\ b{2} = true).    
rnd. skip. progress.
case (bb{1} = true).
rcondt {1} 1. progress. 
rcondt {2} 7. progress. wp.  rnd. wp. wp. rnd.  skip. progress.  
sp. wp.  rnd. wp.  rnd{2}. wp. 
rnd. wp. skip. progress. smt(djoinmap_weight Com_lossless). smt(). 
rcondf {1} 1. progress. skip. progress. smt().
rcondf {2} 7. progress. wp.  rnd. wp. wp. rnd.  skip. progress. smt().
wp.  rnd. wp. rnd. wp. rnd. wp. skip. progress.
rewrite permute_compl_graph.
rewrite prj_path_compl_graph. rewrite /permute_witness. smt (statGood @List). auto.
have <-: djoinmap Com
      (prj_path (permute_witness prm0L statWit)
         (permute_graph prm0L (compl_graph K))) = djoinmap Com (nseq K true).
rewrite permute_compl_graph. rewrite prj_path_compl_graph. rewrite /permute_witness. smt (statGood @List). auto. auto.
smt(rep_path_map). smt(). smt().
qed.



local lemma sim_0_1 (g : hc_stat) (w: hc_wit):  K = size w => zk_relation g w =>
  equiv [ Sim1_0(V,D).simulate ~ Sim1_1(V).simulate : 
               g = arg{2}.`1 /\ w = arg{2}.`2 /\ ={arg} /\ ={glob V, glob ZK.Hyb.Count, glob ZK.Hyb.HybOrcl} ==> ={res} ].
proof. move => sas ishc. proc.
inline Sim1_0(V,D).sinit.
inline Sim1_1(V).sinit. 
sp.
seq 1 1 : (p_a{2} = pa{2} /\ (g,w) = (pa,wa){2} /\
  w_a{2} = wa{2} /\
  g = p_a{2} /\
  p_a{1} = pa{1} /\
  g = p_a{1} /\
  pa{1} = pa{2} /\ ={glob V,wa, glob ZK.Hyb.Count, glob ZK.Hyb.HybOrcl} /\ bb{1} = bb{2}).
rnd. skip. progress.  
if. auto. 
call D_guess_prop.
call (_:true).
wp. inline*. wp.  call (_:true).
 wp.  rnd.  wp. rnd. wp. skip. progress.
rewrite H. simplify. auto. 
seq 1 1 : (={r,bb, glob V,pa,wa, glob ZK.Hyb.Count, glob ZK.Hyb.HybOrcl} /\ !bb{1}). 
inline*.  
(* seq  13 13 : ( *)
(*    !b1{1} /\ b1{1} = b1{2} /\ ={pa,c,wa, HP.pi_w, HP.pi_gwco,bb, glob V, glob ZK.Hyb.Count, glob ZK.Hyb.HybOrcl} /\ !bb{1} ). *)
wp.  rnd. wp. 
rnd  
 (fun (f : permutation) => compose f (inv (mk_perm wa{2})))
  (fun (f : permutation) => compose f (mk_perm wa{2})) .
wp. skip. progress.  rewrite /compose.
simplify. 
have ->: (prmR \o mk_perm wa{2} \o inv (mk_perm wa{2}))
 = (prmR \o (mk_perm wa{2} \o inv (mk_perm wa{2}))). 
   apply fun_ext. move => x. rewrite /(\o). auto. 
rewrite   (inv_left (mk_perm wa{2}) K). 
apply perm_d_mk_perm. smt(). 
apply fun_ext. move => x. smt().
rewrite mu1_uni_ll. apply perm_d_uni. apply perm_d_lossless.
rewrite mu1_uni_ll. apply perm_d_uni. apply perm_d_lossless.
rewrite H1. simplify.
rewrite /compose. rewrite perm_d_comp_closed.  apply H1. smt(perm_d_mk_perm).
auto.
apply perm_d_comp_closed. auto.  apply perm_d_inv_closed. smt(perm_d_mk_perm).
rewrite /compose.
have ->: (prmL \o inv (mk_perm wa{2}) \o mk_perm wa{2})
 = (prmL \o (inv (mk_perm wa{2}) \o mk_perm wa{2})).
apply fun_ext. move => x. rewrite /(\o). auto.
rewrite   (inv_right (mk_perm wa{2}) K). 
apply perm_d_mk_perm. smt(). 
apply fun_ext. move => x.  rewrite /(\o). auto.
rewrite permute_compl_graph. rewrite permute_compl_graph. auto. 
rewrite permute_compl_graph. rewrite - (permute_compl_graph prmL). auto.
rewrite /permute_witness /compose. 
rewrite map_comp.
rewrite mk_perm_inv. 
elim ishc. progress. smt(). smt().
call D_guess_prop.
call (_:true). call (_:true). wp.  skip. progress.
qed.



local module Sim1_2(V : MaliciousVerifier) = {
  module ZKP_HP = ZKP
  proc sinit(p_a : hc_stat, w_a : hc_wit) = {
    var  g, bb, r;
    g <- p_a;

    bb <$ {0,1};
    if (bb) {
       r <@ ZKP_HP.run(p_a, w_a, bb);
    }else{
       r <@ ZKP_HP.run(p_a, w_a, bb);
    }
    return (bb, r);
  }

  proc simulate(pa : hc_stat, wa : hc_wit) : bool * bool  = {
    var b',b,zryb,result, rb;
    (b',zryb) <@ sinit(pa,wa);
    b <@ V.challenge(pa, zryb.`1);
    result <@ V.summitup(pa,zryb.`2);
    rb <@ D.guess(pa, wa, result);
    return (b = b', rb);
  }
}.


local module Sim1_2'(V : MaliciousVerifier) = {
  proc sinit(p_a : hc_stat, w_a : hc_wit) = {
    var g,bb,r;
    g <- p_a;
    bb <$ {0,1};
    if (bb) {
       r <@ ZKP.run(p_a, w_a, bb);
    }else{
        r <@ ZKP'.run(p_a, w_a, bb);
    }
    return (bb, r);
  } 
  proc simulate(pa : hc_stat, wa : hc_wit) : bool * bool  = {
    var b',b,zryb,result, rb;
    (b',zryb) <@ sinit(pa,wa);
    b <@ V.challenge(pa, zryb.`1);
    result <@ V.summitup(pa,zryb.`2);
    rb <@ D.guess(pa, wa, result);
    return (b = b', rb);
  }
}.


local lemma sim12_2' : equiv [Sim1_2(V).simulate ~ Sim1_2'(V).simulate : ={glob V, arg, glob ZK.Hyb.Count, glob ZK.Hyb.HybOrcl} ==> ={res}].
proc. 
inline Sim1_2(V).sinit.
inline Sim1_2'(V).sinit.
seq 5 5 : (={pa,wa,bb,r,glob V, glob ZK.Hyb.Count, glob ZK.Hyb.HybOrcl}).
seq 4 4 : (={pa,wa,p_a,w_a,bb,glob V, glob ZK.Hyb.Count, glob ZK.Hyb.HybOrcl}). 
rnd. wp. skip. progress.
if. progress. sim.
inline Sim1_1(V).ZKP_HP.run.
inline ZKP'.run. 
wp. 
seq 5 5 : (={Ny, w, bb,b0,prm, fal} /\ ={p_a, w_a, pa,wa,b0, glob V, glob Hyb.Count, glob Hyb.HybOrcl} /\ !b0{1} /\ fal{1} = permute_graph prm{1} Ny{1}). wp.  rnd. wp. skip. progress.
exists* fal{2}. exists* prm{2}. exists* w{2}. elim*. progress.
call (kikk (permute_witness prm_R w_R) fal_R (prj_path (permute_witness prm_R w_R) fal_R)).
skip. progress.
smt (prj_rep).
rewrite  H. simplify. smt (rep_prj).
call D_guess_prop. 
call (_:true). call (_:true). wp. skip. progress.
qed.


local lemma sim2'_unhider : equiv [Sim1_2'(V).simulate ~ HidingGame(BlumUnhider2).main : ={glob V,  glob ZK.Hyb.Count, glob ZK.Hyb.HybOrcl} /\ arg{1} = (statProb, statWit) /\ arg{2} = false ==> (res.`1{1} /\ res.`2{1}) = res{2}].
proof. proc.
inline*. wp. call D_guess_prop. call(_:true). call (_:true). wp. sp. swap {2} 7 -6.
seq 1 1 : (={glob V, glob Hyb.HybOrcl, glob Hyb.Count,bb} /\ p_a{1} = pa{1} /\ w_a{1} = wa{1} /\ (pa{1},wa{1}) =(statProb,statWit) /\ b{2} = false).
rnd. skip. progress.
case (bb{1} = true).
rcondt {1} 1. progress. 
rcondt {2} 7. progress. wp.  rnd. wp. wp. rnd.  skip. progress.  
sp. wp.  rnd. wp.  rnd{2}. wp. 
rnd.  wp. skip. progress. smt(djoinmap_weight Com_lossless). smt().  
rcondf {1} 1. progress. skip. progress. smt().
rcondf {2} 7. progress. wp.  rnd. wp. wp. rnd.  skip. progress.  smt().
wp.  rnd. wp. rnd. wp. rnd. wp. skip. progress.
smt(statGood witness_under_permutation).
have <-: djoinmap Com
      (prj_path (permute_witness prm0L statWit)
         (permute_graph prm0L statProb)) = djoinmap Com (nseq K true).
smt(statGood witness_under_permutation).
smt(rep_path_map). smt(rep_path_map). smt(). smt().
qed.



local lemma comm_scheme_hiding1 &m: 
   `|Pr[ Sim1_1(V).simulate(statProb,statWit) @ &m : res.`1 /\ res.`2 ]
      - Pr[ Sim1_2(V).simulate(statProb,statWit) @ &m : res.`1 /\ res.`2 ]| 
   <= eps.
have ->: Pr[Sim1_1(V).simulate(statProb, statWit) @ &m : res.`1 /\ res.`2]
 = Pr[Sim1_1'(V).simulate(statProb, statWit) @ &m : res.`1 /\ res.`2].
byequiv(_: ={glob V, arg, glob ZK.Hyb.Count, glob ZK.Hyb.HybOrcl} ==> _). conseq sim1_1'.
auto. auto. auto.
have ->: Pr[Sim1_1'(V).simulate(statProb, statWit) @ &m : res.`1 /\ res.`2]
 = Pr[HidingGame(BlumUnhider2).main(true) @ &m : res].
byequiv(_: ={glob V,  glob ZK.Hyb.Count, glob ZK.Hyb.HybOrcl} /\ arg{2} = true /\ arg{1} = (statProb, statWit) ==> _). conseq sim1'_unhider. progress. progress. auto. auto.
have ->: Pr[Sim1_2(V).simulate(statProb, statWit) @ &m : res.`1 /\ res.`2]
 = Pr[Sim1_2'(V).simulate(statProb, statWit) @ &m : res.`1 /\ res.`2].
byequiv(_: ={glob V, arg, glob ZK.Hyb.Count, glob ZK.Hyb.HybOrcl} ==> _). conseq sim12_2'.
auto. auto. auto.
have ->: Pr[Sim1_2'(V).simulate(statProb, statWit) @ &m : res.`1 /\ res.`2]
 = Pr[HidingGame(BlumUnhider2).main(false) @ &m : res].
byequiv(_: ={glob V,  glob ZK.Hyb.Count, glob ZK.Hyb.HybOrcl} /\ arg{2} = false /\ arg{1} = (statProb, statWit) ==> _). conseq sim2'_unhider. progress. progress. auto. auto.
apply (comm_scheme_hiding_eps &m BlumUnhider2).
qed.


local module BlumUnhider : Unhider = {
 proc choose () : bool list * bool list = {
    var prm,fal1,fal2;
    prm <$ perm_d K;
    fal1 <- permute_graph prm statProb;
    prm <$ perm_d K;
    fal2 <- permute_graph prm (compl_graph K);
    return (fal1,fal2);

 }
 proc guess(c : commitment list) : bool = {
   var b : bool;
   b <@ V.challenge(statProb, c);
   return b;
 }
}.

local lemma zz : equiv [ Sim1_0(V,D).simulate ~ HidingExperiment(BlumUnhider).main : arg{1} = (statProb, statWit) /\ ={glob V} ==> res.`1{1} = res{2} ].
progress.
proc. inline*. sp. wp. 
call {1} (_:true ==> true). apply D_run_ll.
call {1} (_:true ==> true). apply V_summitup_ll. simplify.
swap {2} 6 -5.
call (_:true).  wp.
seq 1 1 : (bb{1} = b{2} /\   p_a{1} = pa{1} /\
  g{1} = p_a{1} /\
  (pa{1} = statProb /\ wa{1} = statWit) /\
  ={glob V}).
rnd. skip. progress.
case (bb{1}). 
rcondt {1} 1. progress. sp. wp.
rnd.  wp.  rnd{2}.
wp. rnd.   wp.  skip. progress. apply perm_d_lossless. 
rewrite H. simplify. auto.
rewrite H. simplify. auto.
smt().
rcondf {1} 1. progress. sp. wp.
rnd.  wp.  rnd.
wp. rnd{2}.   wp.  skip. progress. apply perm_d_lossless.
rewrite H. simplify. auto. 
rewrite H. simplify. auto. 
smt().
qed.


local lemma comm_scheme_hiding2' &m :
  `|Pr[Sim1_0(V,D).simulate(statProb, statWit) @ &m : res.`1] -  1%r/2%r| <= eps2. 
have ->: Pr[Sim1_0(V,D).simulate(statProb, statWit) @ &m : res.`1] = Pr[HidingExperiment(BlumUnhider).main() @ &m : res].
byequiv. conseq zz. progress. smt(). smt(). auto. 
apply (comm_scheme_hiding_eps2 &m BlumUnhider).
qed.


local module Sim1_3(V : MaliciousVerifier) = {
  module ZKP_HP = ZKP
  proc sinit(p_a : hc_stat, w_a : hc_wit) = {
    var  g,bb,r;
    g <- p_a;
    bb <$ {0,1};
    r <@ ZKP_HP.run(p_a, w_a, bb);
    return (bb, r);
  }

  proc simulate(pa : hc_stat,  wa : hc_wit) : bool * bool  = {
    var b',b,zryb,result,rb;
    (b',zryb) <@ sinit(pa,wa);
    b <@ V.challenge(pa, zryb.`1);
    result <@ V.summitup(pa, zryb.`2);
    rb <@ D.guess(pa, wa, result);
    return (b = b', rb);
  }
}.


local lemma sim_2_3 (g : hc_stat)(w: hc_wit): zk_relation g w =>
  equiv [ Sim1_2(V).simulate ~ Sim1_3(V).simulate : 
               arg{1}.`1 = g /\ arg{1}.`2 = w /\ ={arg} /\ ={glob V, glob ZK.Hyb.Count, glob ZK.Hyb.HybOrcl} ==> ={res} ].
move => ishc.
proc.
inline Sim1_2(V).sinit.
inline Sim1_3(V).sinit.
sp.
seq 1 1 : (p_a{2} = pa{2} /\
  w_a{2} = wa{2} /\
  (g,w) = (pa{2},wa{2}) /\
  g = p_a{2} /\
  p_a{1} = pa{1} /\
  w_a{1} = wa{1} /\
  g = p_a{1} /\
   (pa{1}, wa{1}) = (pa{2}, wa{2}) /\ ={glob V, glob ZK.Hyb.Count, glob ZK.Hyb.HybOrcl} /\ bb{1} = bb{2}).
rnd. skip. progress. 
case (bb{1} = true).
rcondt {1} 1. progress.  
seq 4 4 : ((b{1} = b'{1}) = (b{2} = b'{2}) /\ ={pa,wa, result, glob V, glob ZK.Hyb.Count, glob ZK.Hyb.HybOrcl}). sim.
call D_guess_prop. skip. progress.
rcondf {1} 1. progress. skip. smt().
seq 1 1 : (p_a{2} = pa{2} /\
  w_a{2} = wa{2} /\
  g = p_a{2} /\
  p_a{1} = pa{1} /\
  w_a{1} = wa{1} /\
  g = p_a{1} /\
 (pa{1}, wa{1}) = (pa{2}, wa{2}) /\ ={glob V, glob ZK.Hyb.Count, glob ZK.Hyb.HybOrcl} /\ bb{1} = bb{2} /\ r{1} = r{2}).
symmetry.
inline*. wp.  rnd. wp.  rnd. wp.  skip. auto.
call D_guess_prop. call (_:true). call (_:true). wp. skip. progress.
qed.


local module Sim1_4(V : MaliciousVerifier) = {
  module ZKP_HP = ZKP
  proc simulate(pa : hc_stat, wa : hc_wit) : bool * bool  = {
    var b,result,r,g,bb,rb;
    g <- pa;
    bb <$ {0,1};
    r <@ ZKP_HP.run(pa, wa, bb);
    b <@ V.challenge(pa, r.`1);
    result <@ V.summitup(pa, r.`2);
    rb <@ D.guess(pa, wa, result);
    return (b = bb, rb);
  }
}.


local lemma sim_3_4:
  equiv [ Sim1_3(V).simulate ~ Sim1_4(V).simulate : 
               arg{1} = arg{2} /\ ={glob V, glob ZK.Hyb.Count, glob ZK.Hyb.HybOrcl} ==> ={res} ].
proc. 
seq 3 5 : (={glob V, glob ZK.Hyb.Count, glob ZK.Hyb.HybOrcl, pa,wa,result} /\ (b{1} = b'{1}) = (b{2} = bb{2})).
sim.
inline*. sp. wp. rnd. wp. rnd. wp.  rnd. skip. progress.
call D_guess_prop. skip. progress.
qed.


local module Sim1_5(V : MaliciousVerifier) = {
  proc simulate(pa : hc_stat,  wa : hc_wit) : bool * bool  = {
    var b,result,r1,r2,g,bb,rb;
    g <- pa;
    bb <$ {0,1};
    r1 <@ HP.commitment(pa,wa);
    r2 <@ HP.response(bb);
    b <@ V.challenge(pa, r1);
    result <@ V.summitup(pa,r2);
    rb <@ D.guess(pa, wa, result);
    return (b = bb, rb);
  }
}.


local lemma sim_4_5: 
  equiv [ Sim1_4(V).simulate ~ Sim1_5(V).simulate : 
               arg{1} = arg{2} /\ ={glob V, glob ZK.Hyb.Count, glob ZK.Hyb.HybOrcl} ==> ={res} ].
proc. 
call D_guess_prop. 
inline*. sp. wp. call (_:true). 
call (_:true).  wp. rnd. wp. rnd.  wp. rnd. skip.
progress.
qed.


local module Sim1_6(V : MaliciousVerifier) = {
  proc simulate(pa : hc_stat,  wa : hc_wit) : bool * bool  = {
    var b,result,r1,r2,g,bb,rb;
    g <- pa;
    r1 <@ HP.commitment(pa,wa);
    bb <$ {0,1};
    b <@ V.challenge(pa, r1);
    r2 <@ HP.response(bb);
    result <@ V.summitup(pa,r2);
    rb <@ D.guess(pa, wa, result);
    return (b = bb, rb);
  }
}.


local lemma sim_5_6: 
  equiv [ Sim1_5(V).simulate ~ Sim1_6(V).simulate : 
               arg{1} = arg{2} /\ ={glob V, glob ZK.Hyb.Count, glob ZK.Hyb.HybOrcl} ==> ={res} ].
proc. swap {1} 5 -1. call D_guess_prop.  swap {2} 3 -1. call (_:true). inline*. wp.  call (_:true). wp.
rnd.  wp.  rnd. wp.  rnd. wp. skip. progress.
qed.


local module Sim1_7(V : MaliciousVerifier) = {
  proc simulate(pa : hc_stat,  wa : hc_wit) : bool * bool  = {
    var b,result,r1,r2,g,bb,rb;
    g <- pa;
    r1 <@ HP.commitment(pa,wa);
    bb <$ {0,1};
    b <@ V.challenge(pa, r1);
    r2 <@ HP.response(b);
    result <@ V.summitup(pa,r2);
    rb <@ D.guess(pa, wa, result);
    return (b = bb, rb);
  }
}.


local lemma sim_6_7: 
  equiv [ Sim1_6(V).simulate ~ Sim1_7(V).simulate : 
               arg{1} = arg{2} /\ ={glob V, glob HP, glob ZK.Hyb.Count, glob ZK.Hyb.HybOrcl} ==> 
   res.`1{1} /\ res.`2{1} <=>  res.`1{2} /\ res.`2{2} ].
proc. sp. 
seq 3 3 : (={b,bb,r1,  wa, pa, glob V, glob HP, glob ZK.Hyb.Count, glob ZK.Hyb.HybOrcl}).
call (_:true). rnd. simplify.
inline*. wp.  rnd. wp.  rnd. wp.  skip. progress.
case (b{1} <> bb{1}).
call {1} (_:true ==> true). apply D_run_ll. 
call {2} (_:true ==> true). apply D_run_ll. 
call {1} (_:true ==> true). apply V_summitup_ll2. 
call {2} (_:true ==> true). apply V_summitup_ll2. 
call {1} (_:true ==> true). proc. wp. skip. auto.
call {2} (_:true ==> true). proc. wp. skip. auto.
skip.  smt().
call D_guess_prop.  inline*. call (_:true). wp.  skip. progress.
qed.


local module Sim1_8(V : MaliciousVerifier) = {
  proc simulate(pa : hc_stat,  wa : hc_wit) : bool * bool  = {
    var b,result,r1,r2,g,bb,rb;
    g <- pa;
    r1 <@ HP.commitment(pa,wa);
    b <@ V.challenge(pa,r1);
    r2 <@ HP.response(b);
    result <@ V.summitup(pa,r2);
    rb <@ D.guess(pa, wa, result);
    bb <$ {0,1};
    return (bb, rb);
  }
}.


local lemma sim_7_8: 
  equiv [ Sim1_7(V).simulate ~ Sim1_8(V).simulate : 
               arg{1} = arg{2} /\ ={glob V,  glob ZK.Hyb.Count, glob ZK.Hyb.HybOrcl} ==> ={res} ].
proc. swap {1} 3 4.
seq 6 6 : (={rb}). call D_guess_prop. call (_:true). inline*. wp. call (_:true). wp.  rnd. wp.
rnd. wp. skip. progress.
exists* b{1}. elim*. progress.
rnd (fun b => b ^^ !b_L).
skip. progress. smt(). smt().
smt().
qed.


local module Sim1_9(V : MaliciousVerifier) = {
  module ZKD = ZKD(HP,V,D)
  proc simulate(pa : hc_stat, wa : hc_wit) : bool * bool  = {
    var bb,rb;
    rb <@ ZKD.main(pa,wa);
    bb <$ {0,1};
    return (bb, rb);
  }
}.


local lemma sim_8_9: 
  equiv [ Sim1_8(V).simulate ~ Sim1_9(V).simulate : 
               arg{1} = arg{2} /\ ={glob V, glob HP,  glob ZK.Hyb.Count, glob ZK.Hyb.HybOrcl} ==> ={res} ].
proc. inline*. rnd. wp. call D_guess_prop. progress. call (_:true). wp.  call (_:true). wp.  rnd. wp. 
rnd.  wp. skip. progress.
qed.


local lemma sim_2_9 g w: zk_relation g w =>
  equiv [ Sim1_2(V).simulate ~ Sim1_9(V).simulate : 
              g = arg{1}.`1 /\ w = arg{1}.`2 /\ arg{1} = arg{2} /\ ={glob V, glob HP, glob ZK.Hyb.Count, glob ZK.Hyb.HybOrcl} ==> 
  res.`1{1} /\ res.`2{1} <=>  res.`1{2} /\ res.`2{2} ].
move => ishc.
transitivity Sim1_3(V).simulate 
(g = arg{1}.`1 /\ w = arg{1}.`2 /\ arg{1} = arg{2} /\ ={glob V, glob ZK.Hyb.Count, glob ZK.Hyb.HybOrcl, glob HP} ==> 
  res.`1{1} /\ res.`2{1} <=>  res.`1{2} /\ res.`2{2}) (arg{1} = arg{2} /\ ={glob V,  glob HP, glob ZK.Hyb.Count, glob ZK.Hyb.HybOrcl} ==> 
  res.`1{1} /\ res.`2{1} <=>  res.`1{2} /\ res.`2{2}). progress. smt(). smt().
conseq (sim_2_3 g w ishc). smt(). auto. 
transitivity Sim1_4(V).simulate 
(arg{1} = arg{2} /\ ={glob V, glob HP, glob ZK.Hyb.Count, glob ZK.Hyb.HybOrcl} ==> 
  res.`1{1} /\ res.`2{1} <=>  res.`1{2} /\ res.`2{2}) (arg{1} = arg{2} /\ ={glob V,  glob HP, glob ZK.Hyb.Count, glob ZK.Hyb.HybOrcl} ==> 
  res.`1{1} /\ res.`2{1} <=>  res.`1{2} /\ res.`2{2}). progress. smt(). smt().
conseq sim_3_4. auto. auto.
transitivity Sim1_5(V).simulate 
(arg{1} = arg{2} /\ ={glob V, glob HP, glob ZK.Hyb.Count, glob ZK.Hyb.HybOrcl} ==> 
  res.`1{1} /\ res.`2{1} <=>  res.`1{2} /\ res.`2{2}) (arg{1} = arg{2} /\ ={glob V, glob HP, glob ZK.Hyb.Count, glob ZK.Hyb.HybOrcl} ==> 
  res.`1{1} /\ res.`2{1} <=>  res.`1{2} /\ res.`2{2}). progress. smt(). smt().
conseq sim_4_5. auto. auto.
transitivity Sim1_6(V).simulate 
(arg{1} = arg{2} /\ ={glob V,  glob HP, glob ZK.Hyb.Count, glob ZK.Hyb.HybOrcl} ==> 
  res.`1{1} /\ res.`2{1} <=>  res.`1{2} /\ res.`2{2}) (arg{1} = arg{2} /\ ={glob V, glob HP, glob ZK.Hyb.Count, glob ZK.Hyb.HybOrcl} ==> 
  res.`1{1} /\ res.`2{1} <=>  res.`1{2} /\ res.`2{2}). progress. smt(). smt().
conseq sim_5_6. auto. auto.
transitivity Sim1_7(V).simulate 
(arg{1} = arg{2} /\ ={glob V, glob HP, glob ZK.Hyb.Count, glob ZK.Hyb.HybOrcl} ==> 
  res.`1{1} /\ res.`2{1} <=>  res.`1{2} /\ res.`2{2}) (arg{1} = arg{2} /\ ={glob V, glob HP, glob ZK.Hyb.Count, glob ZK.Hyb.HybOrcl} ==> 
  res.`1{1} /\ res.`2{1} <=>  res.`1{2} /\ res.`2{2}). progress. smt(). smt().
conseq sim_6_7. auto. 
transitivity Sim1_8(V).simulate 
(arg{1} = arg{2} /\ ={glob V, glob HP, glob ZK.Hyb.Count, glob ZK.Hyb.HybOrcl} ==> 
  res.`1{1} /\ res.`2{1} <=>  res.`1{2} /\ res.`2{2}) (arg{1} = arg{2} /\ ={glob V, glob HP, glob ZK.Hyb.Count, glob ZK.Hyb.HybOrcl} ==> 
  res.`1{1} /\ res.`2{1} <=>  res.`1{2} /\ res.`2{2}). progress. smt(). smt().
conseq sim_7_8. auto. auto.
conseq sim_8_9. auto. auto.
qed.


local lemma sim_9_10: 
  equiv [ Sim1_9(V).simulate ~ ZKD(HP,V,D).main : 
               arg{1} = arg{2} /\ ={glob V, glob HP, glob ZK.Hyb.Count, glob ZK.Hyb.HybOrcl} 
                  ==> res.`2{1} = res{2} ].
proc*.  
inline Sim1_9(V).simulate.
wp . rnd {1}.
simplify. sp.  
inline*. wp. call D_guess_prop. call (_:true). wp. call (_:true). wp.  rnd. wp. rnd. wp.  skip.
progress.
qed.


local lemma sim_9_pr1 &m pa wa: 
   Pr[ Sim1_9(V).simulate(pa,wa) @ &m : res.`2 ]
   =  Pr[ Sim1_9(V).simulate(pa,wa) @ &m : res.`2 /\ res.`1 ]
   + Pr[ Sim1_9(V).simulate(pa,wa) @ &m : res.`2 /\ !res.`1 ].
proof. rewrite Pr[mu_split res.`1]. auto. 
qed.


local lemma sim_9_pr2 &m pa wa: 
   Pr[ Sim1_9(V).simulate(pa,wa) @ &m : res.`2 /\ res.`1 ]
   = Pr[ Sim1_9(V).simulate(pa, wa) @ &m : res.`2 /\ !res.`1  ].
proof. byequiv (_: ={glob V, glob ZK.Hyb.Count, glob ZK.Hyb.HybOrcl, arg} ==> _).
proc. seq 1 1 : (={rb}). 
inline*. wp. call D_guess_prop. wp. call (_:true). wp. call (_:true). wp. rnd.
wp. rnd. wp.  skip. progress. 
rnd (fun x => !x). 
skip. progress. auto. auto.
qed.


local lemma sim_9_pr3 &m pa wa: 
   Pr[ Sim1_9(V).simulate(pa,wa) @ &m : res.`2 ]
   = 2%r * Pr[ Sim1_9(V).simulate(pa,wa) @ &m : res.`2 /\ res.`1  ].
smt (sim_9_pr1 sim_9_pr2).
qed.


local lemma sim1_main &m:  zk_relation statProb statWit =>
   `|Pr[ Sim1_0(V,D).simulate(statProb,statWit) @ &m : res.`1 /\ res.`2 ]
      / Pr[ Sim1_0(V,D).simulate(statProb,statWit) @ &m : res.`1 ]
         - Pr[ ZKD(HP,V,D).main(statProb,statWit) @ &m : res ]| 
  <= 2%r * eps + 20%r * eps2.
proof. move => ishc.
have ->: 
  Pr[ ZKD(HP,V,D).main(statProb,statWit) @ &m : res ]
  = Pr[ Sim1_9(V).simulate(statProb,statWit) @ &m : res.`2 ]. 
 byequiv (_: arg{1} = arg{2} /\ ={glob V, glob HP, glob ZK.Hyb.Count, glob ZK.Hyb.HybOrcl}  ==> _). 
 symmetry. conseq sim_9_10. progress;auto. auto. auto. auto.
have ->: 
   Pr[Sim1_0(V,D).simulate(statProb,statWit) @ &m : res.`1 /\ res.`2]
    = Pr[ Sim1_1(V).simulate(statProb,statWit) @ &m : res.`1 /\ res.`2 ].
   byequiv (_: ={glob V, glob ZK.Hyb.Count, glob ZK.Hyb.HybOrcl} /\ arg{2} = (statProb, statWit) /\ arg{1} = (statProb, statWit) ==> _). 
conseq (sim_0_1 statProb statWit _ _ ).   simplify. progress. smt(). auto. auto. auto.
have h: 
   Pr[Sim1_0(V,D).simulate(statProb,statWit) @ &m : res.`1]
    = Pr[ Sim1_1(V).simulate(statProb,statWit) @ &m : res.`1].
   byequiv (_: ={glob V, glob ZK.Hyb.Count, glob ZK.Hyb.HybOrcl} /\ arg{2} = (statProb, statWit) /\ arg{1} = (statProb, statWit) ==> _). conseq (sim_0_1 statProb statWit _ _). smt(). smt(). auto. auto. auto.
rewrite sim_9_pr3.
apply (ler_trans (2%r * 
    `|Pr[Sim1_1(V).simulate(statProb,statWit) @ &m : res.`1 /\ res.`2] -
        Pr[Sim1_9(V).simulate(statProb,statWit) @ &m : res.`2 /\ res.`1]| 
           + 20%r * eps2)).
apply main_fin.  split. rewrite Pr[mu_ge0]. auto. rewrite Pr[mu_le1]. auto.
rewrite Pr[mu_ge0]. auto. rewrite Pr[mu_le1]. auto.
rewrite Pr[mu_ge0]. auto. rewrite Pr[mu_le1]. auto.
smt (eps2_ge0). 
rewrite h. rewrite Pr[mu_sub]. auto. auto.
apply pr_e1. 
rewrite Pr[mu_ge0]. auto. rewrite Pr[mu_le1]. auto.
apply (comm_scheme_hiding2' &m).
apply pr_e2. 
rewrite Pr[mu_ge0]. auto. rewrite Pr[mu_le1]. auto.
apply comm_scheme_hiding2'.
have ->: Pr[Sim1_9(V).simulate(statProb, statWit) @ &m : res.`2 /\ res.`1] =
 Pr[Sim1_2(V).simulate(statProb,statWit) @ &m : res.`1 /\ res.`2].
byequiv (_: (statProb,statWit) = arg{1} /\ arg{1} = arg{2} 
 /\ ={glob V, glob HP, glob ZK.Hyb.Count, glob ZK.Hyb.HybOrcl} ==> _). 
symmetry. conseq (sim_2_9 statProb statWit ishc). smt(). smt(). auto. auto.
smt (comm_scheme_hiding1).
qed.    

                                      


local lemma sim110 p ww &m :    islossless D.guess =>
 Pr[Sim1(V).run(p) @ &m : res.`1] =
  Pr[ Sim1_0(V,D).simulate(p,ww) @ &m : res.`1 ].
move => dll.
byequiv (_: (p,ww) = arg{2} /\ arg{1} = arg{2}.`1
   /\ ={glob V} ==> res.`1{1} = res.`1{2}).
proc.  simplify.
seq 1 0 : ((p = pa{2} /\ ww = wa{2}) /\ ={pa, glob V}).
elim rewindable_V_plus.
move => fA [s1 [s2 [s3]]] [s4 [ s5 [s6 s7]]].
exists*  (glob V){1}. elim*. progress.
call {1} (s2 V_L). skip. progress.
seq 3 3 : ((b{1} = b'{1}) = (b{2} = b'{2})).
call (_:true). call (_:true).
inline*. wp. sp.
seq 1 1 : (  p_a{2} = pa{2} /\
  g{2} = p_a{2} /\
  p_a{1} = pa{1} /\
  g{1} = p_a{1} /\ (p = pa{2} /\ ww = wa{2}) /\ ={pa, glob V,bb}). rnd. skip. progress.
if. progress. sp. wp. rnd.  wp. rnd. wp. skip. progress.
wp. rnd. wp. rnd. wp. skip. progress.
if {1}. 
elim rewindable_V_plus.
move => fA [s1 [s2 [s3]]] [s4 [ s5 [s6 s7]]].
call {1} s7. call {2} dll. skip.  auto.
call {2} dll. skip. auto. auto. smt().
qed.


(* conditional indistinguishability  *)
lemma sim1_error &m :
   islossless D.guess =>
   islossless V.summitup =>
   zk_relation statProb statWit =>  
    `|Pr[RD(Sim1(V), D).run(statProb, statWit) @ &m : fst res.`2 /\ res.`1] /
         Pr[Sim1(V).run(statProb) @ &m : fst res] 
              - Pr[ ZKD(HP,V,D).main(statProb,statWit) @ &m : res ]| <= 2%r * eps + 20%r * eps2.
progress.
have ->: Pr[RD(Sim1(V), D).run(statProb, statWit) @ &m : fst res.`2 /\ res.`1]
 = Pr[ Sim1_0(V,D).simulate(statProb,statWit) @ &m : res.`1 /\ res.`2 ].
progress. byequiv (_: (statProb,statWit) = arg{1} /\ arg{1} = arg{2}
 /\ ={glob V,  glob ZK.Hyb.Count, glob ZK.Hyb.HybOrcl} ==> _).  proc. simplify.
seq 1 3 : (={glob ZK.Hyb.Count, glob ZK.Hyb.HybOrcl} /\ (statProb = a{1} ) /\
  (a{1} = pa{2} /\ w{1} = wa{2}) /\ r.`2{1} = result{2} /\ (r{1}.`1  <=> b{2} = b'{2}) /\ (b{2} = b'{2} => ={glob V})  ).
inline Sim1(V).run. wp. sp. simplify.
seq 4 3 :   (={Hyb.Count.c, Hyb.HybOrcl.l, Hyb.HybOrcl.l0} /\
  statProb = a{1} /\
  (a{1} = pa{2} /\ w{1} = wa{2}) /\
  ={result} /\
  (b0{1} = b'{1} <=> b{2} = b'{2}) /\ (b{2} = b'{2} => ={glob V})).  call (_:true). call (_:true).
seq 1 0 : (  pa{1} = a{1} /\
  (statProb = a{1} /\ statWit = w{1}) /\
  (a{1} = pa{2} /\ w{1} = wa{2}) /\
  ={glob V, Hyb.Count.c, Hyb.HybOrcl.l, Hyb.HybOrcl.l0}). 
elim rewindable_V_plus.
move => fA [s1 [s2 [s3]]] [s4 [ s5 [s6 s7]]].
exists*  (glob V){1}. elim*. progress.
call {1} (s2 V_L). skip. progress.
inline*. wp. sp.
seq 1 1 :     (p_a{2} = pa{2} /\
  g{2} = p_a{2} /\
  p_a{1} = pa{1} /\
  g{1} = p_a{1} /\
  pa{1} = a{1} /\
  (statProb = a{1} /\ statWit = w{1}) /\
  (a{1} = pa{2} /\ w{1} = wa{2}) /\
  ={glob V, Hyb.Count.c, Hyb.HybOrcl.l, Hyb.HybOrcl.l0,bb}). rnd.  skip. progress.
if. progress. wp.  rnd.  wp. rnd. wp. skip. progress.
wp. rnd. wp. rnd. wp. skip. progress.
case (b0{1} = b'{1}).
rcondf {1} 1. progress. skip. progress.
rcondt {1} 1. progress. call {1} (_:true ==> true). 
elim rewindable_V_plus.
move => fA [s1 [s2 [s3]]] [s4 [ s5 [s6 s7]]].
apply s7. skip. smt(). 
case (b{2} = b'{2}). 
call D_guess_prop. skip.  progress. 
call {1} H. call {2} H. skip. smt(). auto. auto.
rewrite (sim110 statProb statWit &m H).
apply (sim1_main  &m). assumption.
qed.

(* probability of a "success"-event  *)
lemma sim1_succ &m  : 
 1%r/2%r - eps2 <= Pr[Sim1(V).run(statProb) @ &m : res.`1].
progress.
have ->: Pr[Sim1(V).run(statProb) @ &m : res.`1] = 
 Pr[Sim1_0(V,D).simulate(statProb, statWit) @ &m : res.`1] .
rewrite (sim110 statProb statWit &m).
apply D_run_ll. auto.
have f : `|Pr[Sim1_0(V, D).simulate(statProb,  statWit) @ &m : res.`1] - 1%r / 2%r|
 <= eps2. 
apply comm_scheme_hiding2'. smt().
qed.

end section.



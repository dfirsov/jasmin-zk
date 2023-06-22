require import AllCore IntDiv CoreMap List Distr.
from Jasmin require import JModel.

require import Array32  Array256 WArray256.

require import W64_SchnorrExtract.

op f = (fun (a0 : WArray256.t) =>
             (init (fun (i : int) => get8 a0 i))%Array256).
op g = (fun aux => (Array32.init (fun i_0 => get64
                  (WArray256.init8 (fun i_0 => aux.[i_0])%Array256) i_0))).

op h = (fun (x : WArray256.t) =>
     (init
        (fun (i_0 : int) =>
           get64 ((init8 ("_.[_]" ((init (get8 x)))%Array256)))%WArray256 i_0))%Array32).

lemma h_eq : h = g \o f. auto. qed.

op d = dmap (dmap WArray256.darray f) g.

lemma fold_fin (f : int -> 'b) :
  map f (iota_ 0 8)
   = [f 0 ; f 1 ; f 2; f 3; f 4; f 5; f 6; f 7 ].  
 have -> : iota_ 0 8 = [0;1;2;3;4;5;6;7].
 have -> : 8 = ((((((((0 + 1) + 1) + 1) +1) + 1) +1) + 1) + 1). smt().
 do (rewrite iotaS;auto).
 simplify. apply iota0. auto.
 smt(@List).
qed.

lemma init_ext2:
  forall (f1 f2 : int -> W8.t),
       (init8 f1)%WArray256 = (init8 f2)%WArray256 =>
    (forall (x : int), 0 <= x && x < 256 => f1 x = f2 x).
smt(@WArray256).
qed.

lemma init_ext31:
  forall (f1 f2 : int -> W64.t),
       (Array32.init f1) = (Array32.init f2) =>
    (forall (x : int), 0 <= x && x < 32 => f1 x = f2 x).
smt(@Array32).
qed.

lemma init_ext32:
  forall (f1 f2 : int -> W64.t),
     (forall (x : int), 0 <= x && x < 32 => f1 x = f2 x) =>
       (Array32.init f1) = (Array32.init f2).
smt(@Array32).
qed.


lemma init_ext:
  forall (f1 f2 : int -> W64.t),
     (forall (x : int), 0 <= x && x < 32 => f1 x = f2 x) <=>
       (Array32.init f1) = (Array32.init f2).
smt(init_ext31 init_ext32).
qed.



lemma ext_pack8_1:
  forall (f1 f2 : int -> bool),
       (W64.init f1) = (W64.init f2) =>
    (forall (x : int), 0 <= x && x < 64 => f1 x = f2 x).
smt(@W64).
qed.


lemma ext_pack8_2:
  forall (f1 f2 : int -> bool),
    (forall (x : int), 0 <= x && x < 64 => f1 x = f2 x) 
 =>        (W64.init f1) = (W64.init f2) .
smt(@W64).
qed.


lemma ext_pack8:
  forall (f1 f2 : int -> bool),
    (forall (x : int), 0 <= x && x < 64 => f1 x = f2 x) 
      <=>        (W64.init f1) = (W64.init f2) .
smt(ext_pack8_1 ext_pack8_2).
qed.



lemma val_of_w (x: W8.t Array256.t, y: W8.t Array256.t) : 
  (init (fun (i_0 : int) => get64 (init8 ("_.[_]" x)) i_0))%Array32 =
  (init (fun (i_0 : int) => get64 (init8 ("_.[_]" y)) i_0))%Array32
 => forall (x0 v1 : int), 0 <= x0 < 256 => 0 <= v1 && v1 < 64 
       => x.[8 * (x0 %/ 8) + v1 %/ 8].[v1 %% 8] = y.[8 * (x0 %/ 8) + v1 %/ 8].[v1 %% 8].
pose f1 := (fun (i_0 : int) => get64 (init8 ("_.[_]" x)) i_0).
pose f2 := (fun (i_0 : int) => get64 (init8 ("_.[_]" y)) i_0).
rewrite - (init_ext f1 f2).
rewrite /f1. rewrite /f2.
progress.
pose v0 := (x0 %/8 ).
have  : get64 (init8 ("_.[_]" x)) v0 = get64 (init8 ("_.[_]" y)) v0. smt().
rewrite /get64_direct. rewrite /pack8_t. 
rewrite - ext_pack8. simplify.
move => q.
have  : ((init (fun (j : int) => (init8 ("_.[_]" x)).[8 * v0 + j])))%W8u8.Pack.[v1 %/ 8].[v1 %% 8] =
   ((init (fun (j : int) => (init8 ("_.[_]" y)).[8 * v0 + j])))%W8u8.Pack.[v1 %/ 8].[v1 %% 8].
apply q. smt().
rewrite init_of_list. simplify.
rewrite fold_fin. simplify.
rewrite init_of_list. simplify.
rewrite fold_fin. simplify.
rewrite get_of_list. smt().
rewrite get_of_list. smt().
have -> : [(init8 ("_.[_]" x)).[8 * v0]; (init8 ("_.[_]" x)).[8 * v0 + 1];
   (init8 ("_.[_]" x)).[8 * v0 + 2]; (init8 ("_.[_]" x)).[8 * v0 + 3];
   (init8 ("_.[_]" x)).[8 * v0 + 4]; (init8 ("_.[_]" x)).[8 * v0 + 5];
   (init8 ("_.[_]" x)).[8 * v0 + 6]; (init8 ("_.[_]" x)).[8 * v0 + 7]].[
v1 %/ 8]
 =
   (init8 ("_.[_]" x)).[8 * v0 + v1 %/ 8]. smt(@W8u8).
have -> : [(init8 ("_.[_]" y)).[8 * v0]; (init8 ("_.[_]" y)).[8 * v0 + 1];
   (init8 ("_.[_]" y)).[8 * v0 + 2]; (init8 ("_.[_]" y)).[8 * v0 + 3];
   (init8 ("_.[_]" y)).[8 * v0 + 4]; (init8 ("_.[_]" y)).[8 * v0 + 5];
   (init8 ("_.[_]" y)).[8 * v0 + 6]; (init8 ("_.[_]" y)).[8 * v0 + 7]].[
v1 %/ 8] =    (init8 ("_.[_]" y)).[8 * v0 + v1 %/ 8]. smt(@W8u8).
rewrite /init8.
rewrite initiE. smt().
rewrite initiE. smt().  rewrite /v0. rewrite /v1.
simplify.
auto.
qed.  

lemma h_inj : injective h.
rewrite h_eq.
apply inj_comp.
rewrite /g. simplify.
rewrite /injective.
move => x y.
move => q.
apply Array256.ext_eq. progress.
apply W8.ext_eq. progress.
have :     x.[8 * (x0 %/ 8) + (x0 %% 8 * 8 + x1) %/ 8].[(x0 %% 8 * 8 + x1) %% 8] =
  y.[8 * (x0 %/ 8) + (x0 %% 8 * 8 + x1) %/ 8].[(x0 %% 8 * 8 + x1) %% 8].
apply (val_of_w x y q x0 ((x0 %% 8) * 8 + x1) _ _).
smt(). smt().
have ->: 8 * (x0 %/ 8) + (x0 %% 8 * 8 + x1) %/ 8 = x0. smt(@IntDiv).
have -> : (x0 %% 8 * 8 + x1) %% 8 = x1. smt(@IntDiv).
auto.
rewrite /f.
simplify.
rewrite /injective. progress.
apply WArray256.ext_eq.
progress.
smt(@Array256).
qed.

(* types are finite and of the same cardinality *)
require import SurjFromInj.
require import ArrayFiniteness.
clone import SurjFromInj as GetSurj with type a <- t,
                                         type b <- W64.t Array32.t,
                                         op f <- h,
                                         op alist <- all_256words,
                                         op blist <- all_w64xN
proof*.

lemma h_surj : surjective h.    
apply f_surj. 
apply all_256words_uniq.
apply all_w64xN_uniq.
rewrite all_256words_size.
rewrite all_w64xN_size. by ring.
apply all_256words_full.
apply all_w64xN_full.
apply h_inj.
qed.



require import DList.

lemma darray_ll:
 is_lossless darray.
proof. rewrite /darray. apply dmap_ll; apply dlist_ll. smt(@W8). qed.

lemma supp_darray a:
 a \in darray <=> all (support W8.dword) (WArray256.to_list a).
proof.
rewrite /darray128 supp_dmap; split.
 move=> [x]; rewrite supp_dlist // => /> *.
 by rewrite WArray256.of_listK // /#.
move=> H; exists (to_list a); rewrite supp_dlist // H Array256.size_to_list /=.
qed.

lemma darray_uni:
   is_uniform (darray).
proof.
rewrite /darray256=> ?; apply dmap_uni_in_inj.
 move=> x y; rewrite !supp_dlist //; move => [? _] [? _] H.
  smt(@WArray256).
 apply dlist_uni. smt(@W8).
qed.

lemma darray_fu:
   is_full darray.
proof.
rewrite /darray => H; apply dmap_fu_in.
move=> x; exists (to_list x); rewrite to_listK supp_dlist //=.
rewrite allP.
progress. smt(@W8).
qed.


op jsmD = dmap WArray256.darray h.
lemma q : d = jsmD.
rewrite /d /d1 /f /g /(\o). simplify.
rewrite dmap_comp. simplify. auto.
qed.

lemma jsmdD_uni : is_uniform jsmD .
rewrite /jsmD.
apply dmap_uni_in_inj.
progress. smt (h_inj).
apply darray_uni.
qed.


lemma jsmdD_fu : is_full jsmD .
rewrite /jsmD.
apply dmap_fu.
smt (h_surj).
apply darray_fu.
qed.

lemma jsmdD_ll: is_lossless jsmD.
rewrite /jsmD.
apply dmap_ll.
apply darray_ll.
qed.


require import W64_SchnorrExtract.


require import BigNum_spec.

module SampleLoc = {
  proc jsmD() = {
    var r;
    r <$ jsmD;
    return r;
  }

  proc sampleInt() = {
    var r;
    r <$ D;
    return r;
  }

  proc sample(a:W8.t Array256.t) : W64.t Array32.t = {
     a <@ Syscall.randombytes_256 (a);
     return (Array32.init (fun i_0 => get64
               (WArray256.init8 (fun i_0 => a.[i_0])) i_0));
  }
}.



lemma lemma1 : 
  equiv [SampleLoc.sample ~ SampleLoc.jsmD : true ==> ={res}].
bypr res{1} res{2}.
auto.
progress.
have -> : Pr[SampleLoc.sample(arg{1}) @ &1 : res = a]
 = mu1 jsmD a.
byphoare. proc. inline*.
wp. rnd. wp. skip.  progress.
rewrite /jsmD.
rewrite h_eq.
have ->: (dmap darray (g \o f)) 
 =  dmap (dmap darray f) g.
smt(dmap_comp).
rewrite (dmapE (dmap darray f)). 
rewrite /pred1 /g /(\o). simplify. rewrite /f. simplify. auto. auto.
auto.
byphoare. proc. rnd. skip. auto. auto. auto.
qed.


require import Finite List.


lemma qqq (l : 'a list) (f : 'a -> 'b) : size l = size (map f l).
smt(@List).
qed.


lemma qq (l1 l2 : 'a list) : uniq l1 => uniq l2 
 => (forall x, x \in l1 <=>  x \in l2) => size l1 = size l2. smt(@List).
qed.


lemma ioo (x : 'b) (f : 'a -> 'b) (l : 'a list) : 
 x \in map f l <=> exists z, z \in l /\ x = f z.
smt(@List).
qed.

lemma jsmd_supp : size (to_seq (support jsmD)) = size (to_seq (support D)).
 have ->: size (to_seq (support jsmD)) = size (map W64xN.valR (to_seq (support jsmD))). 
rewrite size_map. auto.
 have ->: size (map W64xN.valR (to_seq (support jsmD))) = size (to_seq (support D)). 
apply qq.  
rewrite map_inj_in_uniq. progress. clear H H0. smt(@W64xN).
apply uniq_to_seq. smt(@Distr jsmdD_uni).
apply uniq_to_seq. smt(@Distr jsmdD_uni).
progress. 
have : exists z, z \in (to_seq (support jsmD)) /\ W64xN.valR z = x. smt(@List).
progress. 
have mf : 0 <= (W64xN.valR z) < W64xN.modulusR. smt(@W64xN). 
rewrite /D.
have mf2 : W64xN.valR z \in (range 0 W64xN.modulusR). smt(@List).
have mf3 : W64xN.valR z \in duniform (range 0 W64xN.modulusR). smt(@Distr).
smt(@Distr @Finite).
rewrite ioo.
exists (W64xN.R.bn_ofint x). split. 
have mf3 :   (W64xN.R.bn_ofint x)\in jsmD.
apply (jsmdD_fu (W64xN.R.bn_ofint x)). 
apply mem_to_seq.  smt(@Distr jsmdD_uni).
auto.    
rewrite W64xN.R.bn_ofintK.
have mf2 :  x \in D. smt(@Distr @Finite).
have mf3 : 0 <= x < W64xN.modulusR. smt(@Distr).
smt(@IntDiv).
auto.
qed.


lemma lemma2 : 
  equiv [SampleLoc.jsmD ~ SampleLoc.sampleInt : true ==> W64xN.valR res{1} = res{2} ].
proc. 
rnd W64xN.valR W64xN.R.bn_ofint.
skip. progress.
rewrite W64xN.R.bn_ofintK. 
have rval : 0 <= rR  < W64xN.modulusR. smt(@Distr @List).
smt(@Int).
have rval : 0 <= rR  < W64xN.modulusR. smt(@Distr @List).
have ->: mu1 D rR = 1%r / W64xN.modulusR%r.
rewrite /D. smt(@Distr @List).
rewrite mu1_uni. apply jsmdD_uni.
have -> : (W64xN.R.bn_ofint rR)%W64xN.R \in jsmD = true.
smt(jsmdD_fu).  
simplify.
have ->: weight jsmD = 1%r. 
smt(jsmdD_ll @Distr).
rewrite jsmd_supp.
smt(@Distr).
have rval : 0 <= W64xN.valR rL  < W64xN.modulusR. smt(@W64xN).
smt(@Distr).
smt(@W64xN).
qed.    


module WW = {
  proc rsample(byte_z : W64.t Array32.t) : int * W64.t Array32.t = {
    var aux : W8.t Array256.t;
    var i : int;
    var byte_p : W64.t Array32.t;
    var cf : bool;
    var byte_q : W64.t Array32.t;
    var _0 : bool;
    var _1 : bool;
    var _2 : bool;
    var _3 : bool;
    var _4 : W64.t;
    
    byte_p <- witness;
    byte_q <- witness;
    i <- 0;
    byte_p <@ M(Syscall).bn_set0(byte_p);
    (_0, cf, _1, _2, _3, _4) <- set0_64;
    while (!cf){
      byte_p <@ SampleLoc.sample((init
                              (fun (i_0 : int) =>
                                 get8
                                   (init64
                                      (fun (i_0_0 : int) => byte_p.[i_0_0])%Array32)
                                   i_0))%Array256);
      byte_q <@ M(Syscall).bn_copy(byte_p);
      (cf, byte_q) <@ M(Syscall).bn_subc(byte_q, byte_z);
      i <- i + 1;
    }   
    return (i, byte_p);
  }

  proc rsample0(byte_z : W64.t Array32.t) : int * W64.t Array32.t = {
    var aux : W8.t Array256.t;
    var i : int;
    var byte_p : W64.t Array32.t;
    var cf : bool;
    var byte_q : W64.t Array32.t;
    var _0 : bool;
    var _1 : bool;
    var _2 : bool;
    var _3 : bool;
    var _4 : W64.t;
    
    byte_p <- witness;
    byte_q <- witness;
    i <- 0;
    byte_p <@ M(Syscall).bn_set0(byte_p);
    (_0, cf, _1, _2, _3, _4) <- set0_64;
    while (!cf){
      byte_p <@ SampleLoc.jsmD();
      byte_q <@ M(Syscall).bn_copy(byte_p);
      (cf, byte_q) <@ M(Syscall).bn_subc(byte_q, byte_z);
      i <- i + 1;
    }   
    return (i, byte_p);
  }

  proc rsample2(a : int) : int * int = {
    var x : int;
    var b : bool;
    var i : int;
    var z : int;
    
    x <- 0;
    b <- true;
    i <- 0;
    while (b){
      x <@ SampleLoc.sampleInt();
      (b, z) <@ ASpecFp.subn(x, a);
      b <- !b;
      i <- i + 1;
    }
    
    return (i, x);
  }

}.

require import BigNum_proofs.
equiv rsample_cspec:
 M.bn_rsample ~ CSpecFp.rsample:
  W64xN.valR byte_z{1} = a{2}
  ==> W64xN.valR res{1}.`2 = res{2}.`2 /\ res{1}.`1 = res{2}.`1.
  transitivity WW.rsample
   (={arg} ==> ={res})
   (  W64xN.valR byte_z{1} = a{2}
  ==> W64xN.valR res{1}.`2 = res{2}.`2 /\ res{1}.`1 = res{2}.`1).
smt(). smt().
proc.  inline SampleLoc.sample. wp. sp. 
while (={i,cf,byte_p,byte_q,byte_z}). sim. wp. call (_:true).
sim. wp. skip. progress.
wp.  call (_:true). sim. skip. progress.
symmetry.
transitivity 
   WW.rsample2
   (={arg} ==> ={res})
   (ImplZZ arg{2} arg{1} ==> ImplZZ res{2}.`2 res{1}.`2 /\ res{2}.`1 = res{1}.`1).
smt(). smt().
proc. inline SampleLoc.sampleInt. sim.
symmetry.
transitivity 
   WW.rsample0
   (={arg} ==> ={res})
   (ImplZZ arg{1} arg{2} ==> ImplZZ res{1}.`2 res{2}.`2 /\ res{2}.`1 = res{1}.`1).
smt(). smt().
proc. 
while (={i,cf,byte_p,byte_q,byte_z}). sim. wp. 
call lemma1. skip. auto.
wp. call (_:true). sim. wp. skip. auto.
proc. wp.
  while (={i} /\ !cf{1} = b{2} /\ ImplZZ byte_p{1}  x{2} /\ W64xN.valR  byte_z{1} = a{2}). wp.
call  subc_spec. wp. ecall {1} (bn_copy_correct byte_p{1}).
wp. 
call lemma2. skip. progress. smt(). smt(). smt().
wp. 
call {1} (bn_set0_correct). wp. skip. progress.
qed.


require import UniformSampling_Abstract.

import RSP.
lemma bn_rsample_spec &m a y: 0 <= W64xN.valR y < W64xN.valR a
  => Pr[ M.bn_rsample(a)@&m: res.`2 = y ] 
     = Pr[ RSM.RS.sample(fun x => x < W64xN.valR a,0)@&m: res.`2 = W64xN.valR y ].
  have ->: Pr[ M.bn_rsample(a)@&m: res.`2 = y ] = Pr[CSpecFp.rsample(W64xN.valR a) @ &m : res.`2 = W64xN.valR y ].
  byequiv. conseq rsample_cspec. smt(). smt(@W64xN). auto. auto.
move => interval.
apply (rsample_pr2 (W64xN.valR a) &m (fun (x : int * int) => x.`2 = (W64xN.valR y))).
qed.

equiv rsample_aspec:
 M.bn_rsample ~ ASpecFp.rsample:
  W64xN.valR byte_z{1} = a{2} /\ 0 < a{2}
  ==> W64xN.valR res{1}.`2 = res{2}.
proof.
transitivity 
 CSpecFp.rsample
  (W64xN.valR byte_z{1} = a{2}
    ==> W64xN.valR res{1}.`2 = res{2}.`2 /\ res{1}.`1 = res{2}.`1)
  (={arg} /\ 0 < arg{1} < W64xN.modulusR  ==> res{1}.`2 = res{2}).
progress. 
exists (W64xN.valR arg{1}). split. smt(). split. smt().
split. 
auto.
move => _. smt(@W64xN).
progress.
apply rsample_cspec.
exists* arg{1}. elim*. move => P.
conseq (rsample_eq P  ). 
progress.
qed.


lemma bn_rsample_pmf &m a y: 0 <= W64xN.valR y < W64xN.valR a
  => Pr[ M.bn_rsample(a)@&m: res.`2 = y ] = 1%r/(W64xN.valR a)%r.
proof. move => interval.
  have ->: 1%r/(W64xN.valR a)%r = Pr[CSpecFp.rsample(W64xN.valR a) @ &m : res.`2 = W64xN.valR y ].
  rewrite - (rsample_uni &m (W64xN.valR y) (W64xN.valR a)).
  smt(@W64xN).   smt(@W64xN). smt(). auto.
byequiv. conseq rsample_cspec. smt(). 
progress. smt(@W64xN). smt(@W64xN).  auto. auto.
qed.

(* equiv usample_aspec: *)
(*  M.usample ~ ASpecFp.rsample: *)
(*   W64xN.valR byte_z{1} = a{2} /\ 0 < a{2} *)
(*   ==> W64xN.valR res{1} = res{2}. *)
(* proof. *)
(* transitivity  *)
(*  M.rsample *)
(*   (={arg} ==> res{1} = res{2}.`2) *)
(*   (W64xN.valR byte_z{1} = a{2} /\ 0 < a{2} *)
(*   ==> W64xN.valR res{1}.`2 = res{2}). *)
(* progress.  *)
(* smt(). progress. proc*. *)
(* inline M.usample. sp.  wp. call (_:true). sim. skip. progress. *)
(* apply rsample_aspec. *)
(* qed. *)

require import AllCore IntDiv CoreMap List Distr.
require import JModel.

require import Array32  Array256.
require import WArray256  .


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
smt.
smt.
qed.


lemma init_ext2:
  forall (f1 f2 : int -> W8.t),
       (init8 f1)%WArray256 = (init8 f2)%WArray256 =>
    (forall (x : int), 0 <= x && x < 256 => f1 x = f2 x).
smt.
qed.

lemma init_ext31:
  forall (f1 f2 : int -> W64.t),
       (Array32.init f1) = (Array32.init f2) =>
    (forall (x : int), 0 <= x && x < 32 => f1 x = f2 x).
smt.
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
smt.
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
   (init8 ("_.[_]" x)).[8 * v0 + v1 %/ 8]. smt.
have -> : [(init8 ("_.[_]" y)).[8 * v0]; (init8 ("_.[_]" y)).[8 * v0 + 1];
   (init8 ("_.[_]" y)).[8 * v0 + 2]; (init8 ("_.[_]" y)).[8 * v0 + 3];
   (init8 ("_.[_]" y)).[8 * v0 + 4]; (init8 ("_.[_]" y)).[8 * v0 + 5];
   (init8 ("_.[_]" y)).[8 * v0 + 6]; (init8 ("_.[_]" y)).[8 * v0 + 7]].[
v1 %/ 8] =    (init8 ("_.[_]" y)).[8 * v0 + v1 %/ 8]. smt.
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
have ->: 8 * (x0 %/ 8) + (x0 %% 8 * 8 + x1) %/ 8 = x0. smt.
have -> : (x0 %% 8 * 8 + x1) %% 8 = x1. smt.
auto.
rewrite /f.
simplify.
rewrite /injective. progress.
apply WArray256.ext_eq.
progress.
smt.
qed.

axiom h_surj : surjective h.    (* types are finite and of the same cardinality *)
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



module Syscall = {
  proc randombytes_256(a:W8.t Array256.t) : W8.t Array256.t = {
    a <$ dmap WArray256.darray
         (fun a => Array256.init (fun i => WArray256.get8 a i));
    return a;
  }
}.


require import Ring_ops_spec Ring_ops_proof.

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


lemma qqq (l : 'a list) (f : 'a -> 'b) : injective f => size l = size (map f l).
smt.
qed.


lemma qq (l1 l2 : 'a list) : uniq l1 => uniq l2 
 => (forall x, x \in l1 <=>  x \in l2) => size l1 = size l2. smt.
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
search uniq map.
rewrite map_inj_in_uniq. progress. clear H H0. smt.
smt.
smt.
progress. 
have : exists z, z \in (to_seq (support jsmD)) /\ W64xN.valR z = x. smt(@List).
progress. 
have mf : 0 <= (W64xN.valR z) < M. smt(@W64xN). 
rewrite /D.
have mf2 : W64xN.valR z \in (range 0 Ring_ops_spec.M). smt(@List).
have mf3 : W64xN.valR z \in duniform (range 0 Ring_ops_spec.M). smt(@Distr).
smt(@Distr @Finite).
rewrite ioo.
exists (W64xN.R.bn_ofint x). split. 
have mf3 :   (W64xN.R.bn_ofint x)\in jsmD.
apply (jsmdD_fu (W64xN.R.bn_ofint x)). 
smt.
rewrite W64xN.R.bn_ofintK.
have mf2 :  x \in D. smt.
have mf3 : 0 <= x < M. smt.
smt(@W64xN).
auto.
qed.


lemma lemma2 : 
  equiv [SampleLoc.jsmD ~ SampleLoc.sampleInt : true ==> W64xN.valR res{1} = res{2} ].
proc. 
rnd W64xN.valR W64xN.R.bn_ofint.
skip. progress.
rewrite W64xN.R.bn_ofintK. 
have rval : 0 <= rR  < M. smt(@Distr @List).
smt(@Int).
have rval : 0 <= rR  < M. smt(@Distr @List).
have ->: mu1 D rR = 1%r / M%r.
rewrite /D. smt(@Distr @List).
rewrite mu1_uni. apply jsmdD_uni.
have -> : (W64xN.R.bn_ofint rR)%W64xN.R \in jsmD = true.
smt(jsmdD_fu).  
simplify.
have ->: weight jsmD = 1%r. 
smt(jsmdD_ll @Distr).
rewrite jsmd_supp.
smt.
have rval : 0 <= W64xN.valR rL  < M. smt(@W64xN).
smt.
smt(@W64xN).
qed.    

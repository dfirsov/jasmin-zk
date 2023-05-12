pragma Goals:printall.
require import AllCore DBool Bool List Distr Int AuxResults DJoin.
require import Permutation Blum_Basics.


section.

local lemma prj_lemma (g : graph) (w : hc_wit) (perm : permutation) :
 completeness_relation g w => perm \in perm_d K 
  => prj_path w g = prj_path (permute_witness perm w) (permute_graph perm g).
progress.
have : completeness_relation (permute_graph perm g) (permute_witness perm w).
smt (witness_under_permutation).
elim. progress. elim H. progress.
rewrite - H4. rewrite  - H7. auto.
qed.


local lemma hc_complete_hoare pa wa : completeness_relation pa wa =>
   hoare[ Completeness(HP, HV).run : arg = (pa,wa) ==> res ].
move => ishc. proc. inline*. wp. rnd. 
wp. rnd. wp. rnd. wp. skip.
progress.
pose b1 := ch.
case (b1 = true). 
move => h. rewrite h. simplify.
  + have ->: (zip (unzip1 pi_gwco) (unzip2 pi_gwco)) = pi_gwco. rewrite zip_unzip. auto.
split.
have : all (fun (xy : bool * (commitment * opening) ) => xy.`2 \in (Com xy.`1)) 
    (zip  (permute_graph prm s{hr}) pi_gwco).
have f3 :   
  size (permute_graph prm s{hr}) = size pi_gwco /\
  all (fun (xy : bool * (commitment * opening)) => xy.`2 \in Com xy.`1)
    (zip (permute_graph prm s{hr}) pi_gwco).
apply (supp_djoinmap Com ((permute_graph prm s{hr}))  pi_gwco). auto.
elim f3. move => f31 f32.
auto.
move => q.
apply (sub_all (fun (xy : bool * (commitment * opening)) => xy.`2 \in Com xy.`1) Ver) .
simplify. apply Com_sound.  auto.
have f1 : size pi_gwco = size (permute_graph prm s{hr}).
smt(size_map permute_graph_size supp_djoin_size).
have f2 : size pi_gwco = size (unzip1 pi_gwco).
smt (size_map).
rewrite - f2. 
rewrite f1.
rewrite permute_graph_size.
split. smt(). split. smt(). split. smt(size_map permute_graph_size supp_djoin_size).
smt().
move => p.
have ->: b1 = false. smt().
simplify. clear p. progress.
elim ishc. progress. smt(size_map). smt(size_map permute_graph_size supp_djoin_size).
have : size pi_gwco = size (permute_graph prm s{hr}). smt(size_map permute_graph_size supp_djoin_size prj_path_size).
have ->: size (permute_graph prm s{hr}) = size s{hr}. smt (permute_graph_size). 
have ->: size s{hr} = K * K. elim ishc. smt().
move => q. 
have qqq : size (prj_path (permute_witness prm w{hr}) pi_gwco) = K.   
rewrite prj_path_size.  rewrite q. rewrite size_map. elim ishc. progress. smt(@StdOrder.IntOrder).
elim ishc. smt(size_map).
smt (size_map).
have ->: (prj_path (permute_witness prm w{hr}) (unzip1 pi_gwco))
  = (unzip1 (prj_path (permute_witness prm w{hr}) pi_gwco)).
rewrite prj_path_map. auto.
have ->: 
 (zip (unzip1 (prj_path (permute_witness prm w{hr}) pi_gwco))
        (unzip2 (prj_path (permute_witness prm w{hr}) pi_gwco)))
 = ((prj_path (permute_witness prm w{hr}) pi_gwco)). 
apply zip_unzip.
elim ishc. progress.
apply allP.
move => x1.
have ->: (nseq K true) = (prj_path (permute_witness prm w{hr}) (permute_graph prm s{hr})).
smt(witness_under_permutation).
progress.
apply Com_sound.
have : x1.`1 \in (nseq K true). 
 have md : (prj_path (permute_witness prm w{hr}) (permute_graph prm s{hr}))
   = (prj_path (w{hr}) (s{hr})).
smt (prj_lemma). 
smt (mem_zip_fst).
have : x1.`2 \in (prj_path (permute_witness prm w{hr}) pi_gwco).
   smt(mem_zip_snd).
 move => qq.
have : x1.`2 \in pi_gwco. apply (prj_path_in x1.`2 (permute_witness prm w{hr})). auto.
move => qqq.
  have :   size (permute_graph prm s{hr}) = size pi_gwco /\ all (fun xy => snd xy \in Com xy.`1) (zip (permute_graph prm s{hr}) pi_gwco).
   apply (supp_djoinmap Com (permute_graph prm s{hr}) pi_gwco ). apply H0.
   elim. progress.
  have : forall x, x \in (zip (permute_graph prm s{hr}) pi_gwco) => x.`2 \in Com x.`1.
apply allP. apply H8.
progress. apply H10. 
have H6' : 
 x1 \in prj_path (permute_witness prm w{hr}) (zip (permute_graph prm s{hr}) pi_gwco).
rewrite - prj_path_zip. auto.
rewrite  (prj_path_in x1 (permute_witness prm w{hr})). apply H6'.
smt(perm_eq_permute perm_eq_trans).
smt().
qed.


local lemma hc_complete statement witness &m : completeness_relation statement witness =>
  Pr[Completeness(HP, HV).run(statement, witness) @ &m : true] = 1%r.
move => inlang. byphoare (_: arg = (statement, witness) ==> _);auto. 
proc. inline*. wp. rnd.  simplify. wp. 
rnd.  wp. 
conseq (_: _ ==> true). progress. simplify. smt (@Distr). 
apply djoinmap_weight. apply Com_lossless.
rnd. wp.  skip. progress. apply perm_d_lossless.
qed.


local lemma hc_complete_failure statement witness &m : 
 completeness_relation statement witness =>
   Pr[Completeness(HP, HV).run(statement, witness) @ &m : !res] = 0%r.
progress. byphoare (_: arg = (statement,witness) ==> _);auto.
hoare. simplify. conseq (hc_complete_hoare statement witness H).
qed.


lemma hc_completeness: forall (statement : hc_stat) (witness : hc_wit) &m,
        completeness_relation statement witness =>
     Pr[Completeness(HP, HV).run(statement, witness) 
            @ &m : res] = 1%r.
progress. 
rewrite - (hc_complete statement witness &m H).
have f : 0%r = 
 Pr[Completeness(HP, HV).run(statement, witness) @ &m : true]
  - Pr[Completeness(HP, HV).run(statement, witness) @ &m : res].
rewrite Pr[mu_split res].  
rewrite hc_complete_failure;auto. 
smt().
qed.


(* iterated completeness for Blum protocol  *)
lemma hc_completeness_iter: forall (statement:hc_stat) (witness:hc_wit) &m n,
        1 <= n =>
       completeness_relation statement witness =>
      Pr[CompletenessAmp(HP,HV).run(statement, witness,n) @ &m : res] = 1%r.
progress.
apply (PerfectCompleteness.completeness_seq HP HV).
progress.
apply hc_completeness. auto. auto. auto.
qed.


end section.


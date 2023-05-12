pragma Goals:printall.
require import AllCore DBool Bool List Distr Int AuxResults DJoin.
require import  Permutation Blum_Basics.


section.

local lemma is_hc_perm_2  (g : graph) (w : hc_wit) :
  !soundness_relation g w /\
     K = size w /\ 
     K * K = size g /\ 
     perm_eq w (range 0 K)
  => false \in prj_path w g  .
progress.
  have : nseq (size w) true <> prj_path w g. smt().
progress.
have f : size (prj_path w g) = size w. rewrite prj_path_size. smt(). auto.
apply (aux_lem (prj_path w g)  (size w)).
auto. auto.
qed.

    
local lemma phase2  (g : graph) (w : hc_wit) :
  !soundness_relation g w /\
     K = size w /\ 
     K * K = size g /\ 
     perm_eq w (range 0 K) =>
   false \in (prj_path w g).
smt (is_hc_perm_2).
qed.


local lemma quasi_fin ['a] (l' : bool list) n (l X : 'a list) ver : 
     false \in l'
  => all ver (zip (nseq n true) X)
  => all ver (zip l' l)
  => size l' = n
  => size l  = n
  => size X  = n
  => ver (true,  nth witness X (index false l')) /\
     ver (false, nth witness l (index false l')).
progress.
have f : (forall (i : int), 0 <= i && i < size (zip (nseq (size l') true) X) =>
            ver (nth witness (zip (nseq (size l') true) X) i)).
smt (all_nthP).
have : ver (nth witness (zip (nseq (size l') true) X) (index false l')). apply f. split.
smt(index_ge0). progress. 
rewrite size2_zip.
rewrite size_nseq. smt(). smt(index_mem).
have ->:  (nth witness <:bool * 'a>  (zip (nseq (size l') true) X) (index false l')) = ((nth (witness <: bool * 'a>).`1 (nseq (size l') true) (index false l')), (nth (witness <: bool * 'a>).`2 X (index false l'))).  
rewrite - nth_zip. rewrite size_nseq. rewrite H3. smt(@List).
smt (nth_zip).
have ->: nth witness<:bool * 'a>.`1 (nseq (size l') true) (index false l') = true.
rewrite nth_nseq_if. rewrite index_ge0. simplify.  rewrite index_mem. rewrite H. simplify. auto.
rewrite (nth_change_dfl witness witness<: bool * 'a>.`2). rewrite index_ge0. simplify.
smt(index_mem). auto.
have f : (forall (i : int), 0 <= i && i < size (zip l' l) =>
            ver (nth witness (zip l' l) i)).
smt (all_nthP).
have : ver (nth witness (zip l' l) (index false l')).
apply f. split.
smt(index_ge0). progress. 
rewrite size2_zip. smt(). smt(index_mem).
have ->: (nth witness <:bool * 'a> (zip l' l) (index false l'))
  = ((nth witness<:bool * 'a>.`1 l' (index false l')), (nth witness<:bool * 'a>.`2 l (index false l'))). 
rewrite - nth_zip. smt(). smt (nth_zip).
have ->: nth witness<:bool * 'a>.`1 l' (index false l') = false. 
smt(@List).
rewrite (nth_change_dfl witness witness<: bool * 'a>.`2). rewrite index_ge0. simplify.
smt(index_mem). auto.
qed.




lemma fin_bind_real   (w : hc_wit) (g : graph)  c o1 (p : permutation) X: 
   !soundness_relation g (permute_witness (inv p) w) =>  
   p \in perm_d K =>
   hc_verify (g) c true  (Left (p,o1)) =>
   hc_verify (g) c false (Right (w,X)) 
  => Ver (true,  nth witness ( (zip (prj_path w c)
                             X)) (index false ( (prj_path  w  (permute_graph p g))))) /\
     Ver (false, nth witness ( (zip (prj_path  w c)
                             (prj_path w o1))) (index false ( (prj_path w (permute_graph p g))))).
proof.  
move => p0 pin p1 p2 .
apply (quasi_fin (prj_path w (permute_graph p g)) K) .
apply (is_hc_perm_2 ).
progress. 
case (soundness_relation (permute_graph p g) w).
move => q. 
apply p0. 
have -> : g = permute_graph (inv p) (permute_graph p g). rewrite permute_graph_inv. auto.  smt (permute_graph_size). auto.
rewrite /soundness_relation.
rewrite - (witness_under_permutation  (permute_graph p g) (inv p) w ). smt (perm_d_inv_closed).  auto. auto.
elim p2. progress. rewrite H. auto.
rewrite permute_graph_size.
elim p1. progress.  rewrite H1. auto. 
elim p2. progress.
elim p2. progress. 
elim p1. progress. 
rewrite prj_path_zip. rewrite prj_path_zip.
apply allP. progress.
have f : x \in (zip (permute_graph p g) (zip c o1)). smt(prj_path_in).
apply (allP Ver ( zip (permute_graph p g) (zip c o1))). auto. auto.
have f1 : K <= size (permute_graph p g). elim p1.
progress. smt (permute_graph_size).
have f2 : K = size w. elim p2. progress. rewrite H. auto.
smt (prj_path_size).
have f1 : size (prj_path w c) = K. elim p1.  elim p2. progress.
rewrite prj_path_size. rewrite H0. rewrite H. smt(). auto.
have f2 : size (prj_path w o1) = K. elim p1.  elim p2. progress.
smt (prj_path_size).
rewrite prj_path_zip. 
rewrite prj_path_size. 
elim p2. progress.
rewrite H. elim p1. progress.
have ->: size (zip c o1) = K * K. 
rewrite size1_zip. rewrite H0. rewrite H8. auto. rewrite H6. auto.
smt().
elim p2. progress.
elim p2. progress.
rewrite size1_zip.
rewrite prj_path_size. rewrite H. rewrite H0. smt().
rewrite H1. rewrite H. auto.
rewrite prj_path_size.
rewrite H. rewrite H0. smt(). apply H.
qed.
end section.



op my_extract (p : hc_stat) (c : hc_com)   (r1 r2 : hc_resp) : int list  =
 with r1 = Left  x, r2 = Right z => let n = K in let g = p  in let p = x.`1 in let o1 = x.`2 in 
                                    let w = z.`1 in let X = z.`2 in 
                                     permute_witness (inv p) w
 with r1 = Right z, r2 = Left  x => let n = K in let g = p  in let p = x.`1 in let o1 = x.`2 in 
                                    let w = z.`1 in let X = z.`2 in 
                                     permute_witness (inv p) w
 with r1 = Left  x, r2 = Left  z => witness
 with r1 = Right x, r2 = Right z => witness.

 
op special_soundness_extract (p : hc_stat) (r1 r2 : transcript) : int list = 
 my_extract p r1.`1  r1.`3 r2.`3.

clone export SpecialSoundness  with  
  op special_soundness_extract <- special_soundness_extract.


op hc_verify1 (p : hc_stat) (c : hc_com)   (r1 r2 : hc_resp) : (bool * (commitment * opening)) * (bool * (commitment * opening))  =
 with r1 = Left  x, r2 = Right z => let n = K in let g = p  in let p = x.`1 in let o1 = x.`2 in 
                                    let w = z.`1 in let X = z.`2 in 
   ((true,  nth witness ((zip (prj_path w c)
                             X)) (index false ( (prj_path (w) (permute_graph p g))))), 
                                 (false, nth witness ( (zip (prj_path w c)
                             (prj_path w o1))) (index false ( (prj_path (w) (permute_graph p g))))))
 with r1 = Right z, r2 = Left  x => let n = K in let g = p  in let p = x.`1 in let o1 = x.`2 in 
                                    let w = z.`1 in let X = z.`2 in 
                            ((true,  nth witness ( (zip (prj_path w c)
                             X)) (index false ( (prj_path ( w) (permute_graph p g))))), 
                                 (false, nth witness ( (zip (prj_path w c)
                             (prj_path w o1))) (index false ( (prj_path ( w) (permute_graph p g))))))
 with r1 = Left  x, r2 = Left  z => ((witness, witness), (witness, witness))
 with r1 = Right x, r2 = Right z => ((witness, witness), (witness, witness)).

 
 
module SpecialSoundnessAdvReduction (A : SpecialSoundnessAdversary)  = {
  proc run(statement : hc_stat) : bool = {
      var r1,r2,g,p1,p2;
      (r1, r2) <@ A.attack(statement);
      g    <- statement;
      (p1, p2) <- hc_verify1 (g) r1.`1  r1.`3 r2.`3 ;
      return (Ver p1 /\ Ver p2) /\ p1.`1 <> p2.`1 /\ p1.`2.`1 = p2.`2.`1;
  }
}.


lemma hc_computational_special_soundness:
      forall (s : hc_stat) &m
        (SpecialSoundnessAdversary <: SpecialSoundnessAdversary),
        let attack_prob =
          Pr[SpecialSoundnessAdversary.attack(s) @ &m :
             valid_transcript_pair s res.`1 res.`2 /\
             ! soundness_relation
                 s (special_soundness_extract s res.`1 res.`2)] in
        let red_prob =
          Pr[SpecialSoundnessAdvReduction(SpecialSoundnessAdversary).run
             (s) @ &m : res] in
        attack_prob <= red_prob.
proof.  simplify.
progress.
byequiv;auto.
proc*.
inline*. wp.
call (_:true). wp. simplify.
skip.  move => &1  &2 h1. 
split. smt().  
move => h2. move => result_L result_R L1 l2 l3.  elim.
have ->:  statement{2} = s. smt().
clear h1 h2.  elim l3.
move => e1 e2. rewrite e1.  clear e2 e1 l2 L1 result_L.
elim.
case (result_R.`1.`2).
rewrite /special_soundness_extract.
elim result_R.`1.`3.
elim result_R.`2.`3. progress. 
smt(). smt(). smt(). smt().
move => x p1 p2 p3 p4.
simplify. move => p5.
have : K <= size (prj_path x.`1 p1.`2). 
elim p4. move => _. elim.
progress. 
have ->: size (prj_path x.`1 p1.`2) = K.
rewrite prj_path_size. smt(). smt(). auto.
auto.
have : K <=  size x.`2.  smt().
move => q g. 
elim p4. move => zz1 . elim.
have ->: result_R.`2.`2 = false. smt().
 move => zz2 zz3.
elim zz2.  move => _. elim zz3.
move => _ qq ll. 
rewrite (fin_bind_real  x.`1 s). auto. smt().
smt(). smt(). simplify.
have ->: (nth witness <: commitment * opening> (zip (prj_path x.`1 result_R.`1.`1) x.`2)
   (index false (prj_path x.`1 (permute_graph p1.`1 s))))
 = (nth (fst witness <: commitment * opening>, snd witness <: commitment * opening>) (zip (prj_path x.`1 result_R.`1.`1) x.`2)
   (index false (prj_path x.`1 (permute_graph p1.`1 s)))). smt().
rewrite nth_zip. 
rewrite prj_path_size. smt(). smt().
simplify.
have ->: (nth witness <: commitment * opening>  (zip (prj_path x.`1 result_R.`1.`1) (prj_path x.`1 p1.`2))
   (index false (prj_path x.`1 (permute_graph p1.`1 s))))
 = (nth (fst witness <: commitment * opening>, snd witness <: commitment * opening>) (zip (prj_path x.`1 result_R.`1.`1) (prj_path x.`1 p1.`2))
   (index false (prj_path x.`1 (permute_graph p1.`1 s)))). smt().
rewrite nth_zip. 
rewrite prj_path_size. smt(). 
rewrite prj_path_size. smt(). auto.
simplify. auto.
progress. simplify.
rewrite /special_soundness_extract.
elim result_R.`1.`3.
progress.
elim result_R.`2.`3.
move => x p1 p2 p3 p4. 
simplify .
move => z.
rewrite (fin_bind_real  p1.`1 s ).  auto. 
smt(). smt(). smt(). simplify. 
have ->: (nth witness <: commitment * opening> (zip (prj_path p1.`1 result_R.`1.`1) p1.`2)
   (index false (prj_path p1.`1 (permute_graph x.`1 s))))
 = (nth (fst witness <:commitment * opening>, snd witness <:commitment * opening>) (zip (prj_path p1.`1 result_R.`1.`1) p1.`2)
   (index false (prj_path p1.`1 (permute_graph x.`1 s)))). smt().
rewrite nth_zip. 
elim p4. move => q. elim. move => q1 q2. elim q1.
progress. 
rewrite prj_path_size. rewrite H H0.  smt(K_pos). smt().
 simplify.
have ->: (nth witness <: commitment * opening> (zip (prj_path p1.`1 result_R.`1.`1) (prj_path p1.`1 x.`2))
   (index false (prj_path p1.`1 (permute_graph x.`1 s)))) 
 = (nth (fst witness <: commitment * opening>, snd witness <: commitment * opening>)  (zip (prj_path p1.`1 result_R.`1.`1) (prj_path p1.`1 x.`2))
   (index false (prj_path p1.`1 (permute_graph x.`1 s)))). smt().
rewrite nth_zip. 
elim p4. move => q. elim. move => q1 q2. elim q2. elim q1. progress. smt(prj_path_size). simplify. auto.
smt().
qed.



theory SSB.
section.
declare module S <: SpecialSoundnessAdversary.

op ss : hc_stat.

module SpecialSoundnessBinder(A : SpecialSoundnessAdversary) : Binder = {
  proc bind() = {
      var r1,r2,g,p1,p2;
      (r1, r2) <@ A.attack(ss);
      g    <- ss;
      (p1, p2) <- hc_verify1 g r1.`1  r1.`3 r2.`3 ;
      return (p1.`2.`1, p1.`1, p1.`2.`2, p2.`1, p2.`2.`2);
  }
}.


local lemma qq &m : 
 Pr[SpecialSoundnessAdvReduction(S).run
             (ss) @ &m : res] <= Pr[BindingExperiment(SpecialSoundnessBinder(S)).main() @ &m : res]  .
byequiv;auto. 
proc. inline*. wp.  call (_:true). skip. progress. 
smt().
smt().
qed.



lemma hc_computational_special_soundness_binding &m :
          Pr[S.attack(ss) @ &m :
             valid_transcript_pair ss res.`1 res.`2 /\
             ! soundness_relation
                 ss
                  (special_soundness_extract ss res.`1 res.`2)] 
  <= Pr[BindingExperiment(SpecialSoundnessBinder(S)).main() @ &m : res].
have f :           Pr[S.attack(ss) @ &m :
             valid_transcript_pair ss res.`1 res.`2 /\
             ! soundness_relation
                 ss
                  (special_soundness_extract ss res.`1 res.`2)] 
 <= Pr[SpecialSoundnessAdvReduction(S).run(ss) @ &m : res].
apply (hc_computational_special_soundness ss  &m S).
smt (qq).
qed.

end section.

end SSB.

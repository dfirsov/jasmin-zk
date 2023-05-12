require import AllCore Distr.

type in_t, out_t.

module type JasminModuleWrapper = {
 proc main(x : in_t) : out_t
}.



section.                        

declare module P <: JasminModuleWrapper.

op p_fun : in_t -> out_t * (glob P).


declare axiom p_lossless : forall &m x, Pr[P.main(x) @ &m : true] = 1%r.
declare axiom p_deterministic &m x :
  Pr[ P.main(x)@&m : (res, glob P) = p_fun x  ] = 1%r.

declare axiom p_ct_equiv:
 equiv [P.main ~ P.main : ={glob P} ==> ={glob P}].

local lemma p_ct &m x1 x2 g:
  Pr[ P.main(x1)@&m : (glob P) = g ]
 = Pr[ P.main(x2)@&m : (glob P) = g ].
byequiv. conseq p_ct_equiv;auto. auto. auto.
qed.

local lemma g_all_same x1 x2 : snd (p_fun x1) = snd (p_fun x2).
proof. 
case ((p_fun x1).`2 = (p_fun x2).`2). auto.
have h1 : forall &m,  Pr[ P.main(x1)@&m : (glob P) = (p_fun x1).`2 ]
 = Pr[ P.main(x2)@&m : (glob P) = (p_fun x1).`2 ].
progress. apply p_ct. 
have h2 : forall &m, Pr[P.main(x2) @ &m : (glob P) = (p_fun x1).`2] = 1%r. move => &m. rewrite - h1. 
  rewrite - (p_deterministic &m x1). smt.
have h3 : forall &m, Pr[P.main(x2) @ &m : (glob P) = (p_fun x2).`2] = 1%r. move => &m.   rewrite - (p_deterministic &m x2). smt.
move => h.
have h4 : forall &m, Pr[P.main(x2) @ &m : (glob P) = (p_fun x1).`2 \/ (glob P) = (p_fun x2).`2] = 2%r. move => &m.
rewrite Pr[mu_disjoint]. progress. smt(). rewrite h2. rewrite h3. simplify. auto.
have : exists &m, Pr[P.main(x2) @ &m :
         (glob P) = (p_fun x1).`2 \/ (glob P) = (p_fun x2).`2] =
      Pr[P.main(x2) @ &m :
         (glob P) = (p_fun x1).`2 \/ (glob P) = (p_fun x2).`2]. smt.
elim. move => &m _.  
have h5 : Pr[P.main(x2) @ &m :
         (glob P) = (p_fun x1).`2 \/ (glob P) = (p_fun x2).`2] <= 1%r. smt(@Distr). smt().
qed.

 
op g_fun' (g : glob P) : in_t option = choiceb 
 (fun i =>  i <> None /\ snd (p_fun (oget i)) = g) 
  None.

op g_fun (g : glob P) : real = if g_fun' g = None then 0%r else 1%r.

lemma lf_implies_ct &m x r g:
  Pr[ P.main(x)@&m : res = r ] > 0%r =>
  Pr[ P.main(x)@&m : (res, glob P) = (r,g) ]
   / Pr[ P.main(x)@&m : res = r ]
   = g_fun g.
proof. progress.
have claim1 : Pr[P.main(x) @ &m : res = r]
 = 1%r.
+ rewrite - (p_deterministic &m x).
  case (fst (p_fun x) = r).
  move => q. rewrite - q.
  have : Pr[P.main(x) @ &m : res = (p_fun x).`1]
     >= Pr[P.main(x) @ &m : (res, (glob P)) = p_fun x].
  rewrite Pr[mu_sub]. smt(). auto.
  rewrite (p_deterministic &m x). progress. smt(@Distr).
progress.
  have claim2 : Pr[P.main(x) @ &m : (res, (glob P)) <> p_fun x] = 0%r.
  rewrite Pr[mu_not]. rewrite p_lossless.
  rewrite p_deterministic. simplify. auto.
  have claim3 : Pr[P.main(x) @ &m : res = r] <= 0%r.
    rewrite - claim2.  rewrite Pr[mu_sub]. smt(). auto.
  have claim4 : Pr[P.main(x) @ &m : res = r] = 0%r. smt.
smt().
rewrite claim1. simplify.
 case (snd (p_fun x) = g).
move => h.
have claim2 : (r,g) = p_fun x.
  rewrite - h.
  have : r = fst (p_fun x).
  case (r = (p_fun x).`1). auto.
  move => hh.
    have q : Pr[P.main(x) @ &m : res = (p_fun x).`1] = 1%r.
    rewrite - (p_deterministic &m x). timeout 15. smt.
    have : Pr[P.main(x) @ &m : res = r \/ res = (p_fun x).`1] = 2%r. rewrite Pr[mu_disjoint]. smt().  rewrite q claim1. auto. smt.
  smt().
rewrite /g_fun. rewrite /g_fun'.
have : g_fun' g <> None.
rewrite /g_fun'.
pose P := (fun (i : in_t option) => i <> None /\ (p_fun (oget i)).`2 = g).
have cl : exists x0, P x0.
exists (Some x). rewrite /P. split. smt().
simplify. apply h. smt.
move => hh.
have : choiceb (fun (i : in_t option) => i <> None /\ (p_fun (oget i)).`2 = g)
     None <>
   None. smt.
have -> : (if choiceb (fun (i : in_t option) => i <> None /\ (p_fun (oget i)).`2 = g)
     None =
   None then 0%r
else 1%r) = 1%r. smt().
move => _.
+ rewrite - (p_deterministic &m x).
rewrite Pr[mu_eq]. smt(). auto.
move => h.
have -> : Pr[P.main(x) @ &m : res = r /\ (glob P) = g] = 0%r.
  have q : Pr[P.main(x) @ &m : (res, glob P) = (p_fun x)]  = 1%r.
rewrite p_deterministic. auto.
 have q2 : Pr[P.main(x) @ &m : (res, glob P) <> (p_fun x)]  = 0%r. rewrite Pr[mu_not]. rewrite p_lossless. rewrite q. auto.
 have q3  : Pr[P.main(x) @ &m : res = r /\ (glob P) = g]
  <= Pr[P.main(x) @ &m : (res, glob P) <> (p_fun x)].
  rewrite Pr[mu_sub]. smt(). auto. smt.
have : g_fun' g = None.
rewrite /g_fun'.
rewrite choiceb_dfl.
progress.
case (x0 = None). simplify. auto.
simplify. smt (g_all_same). auto. rewrite /g_fun.
move => hh. rewrite hh. simplify. auto.
qed.

(* end section. *) (* EasyCrypt bug?: cannot close the section (I think this is due to the (glob P) which appear in the ops; Workaround state as one huge lemma. *)

require import AllCore Distr DInterval List IntDiv.

module SampleByte = {
  proc sampleInt() = {
    var x;
    x <$ [0..255];
    return x;
  }

  proc run() = {
    var x : int;
    x <@ sampleInt();
    x <- x %% 2;
    return x;
  }
}.


lemma sample_prob0 : phoare[SampleByte.run : true ==> res = 0 ] = (inv 2%r).
proc. inline*.
wp. rnd. skip. progress.
rewrite duniformE.
have ->: (undup (range 0 256)) = (range 0 256).
smt(@List).
have ->: (size (range 0 256)) = 256. smt(@List).
have ->: (count (fun (x : int) => x %% 2 = 0) (range 0 256)) = 128.
do (rewrite range_ltn /=; first by trivial). 
by rewrite /b2i;rewrite range_geq;simplify;done.
auto.
qed.

lemma sample_prob1 : phoare[SampleByte.run : true ==> res <> 0  ] = (inv 2%r).
proc. inline*.
wp. rnd. skip. progress.
rewrite duniformE.
have ->: (undup (range 0 256)) = (range 0 256).
smt(@List).
have ->: (size (range 0 256)) = 256. smt(@List).
have ->: (count (fun (x : int) => x %% 2 <> 0) (range 0 256)) = 128.
do (rewrite range_ltn /=; first by trivial). 
by rewrite /b2i;rewrite range_geq;simplify;done.
auto.
qed.



theory RandomChoice.

type t.

module BinSampleSpec = {

  proc main(a b : t) = {
    var s : int;
    var r : t;
    s <@ SampleByte.run();
    r <- if (s = 0) then a else b;
    return r;
  }

  proc spec(a b : t) = {
    var r : t;
    r <$ duniform [a; b];
    return r;
  }
}.

section.

local lemma fst_choice_pr a b : a <> b => phoare[BinSampleSpec.main : arg = (a,b) ==> res = a ] = (inv 2%r).
proof. progress.
proc. wp.
call sample_prob0.
skip. progress.
smt().
qed.

local lemma snd_choice_pr a b : a <> b => phoare[BinSampleSpec.main : arg = (a,b) ==> res = b ] = (inv 2%r).
proof. progress.
proc. wp.
call sample_prob1.
skip. progress. smt().
smt().
qed.


local lemma sat_spec_not_eq aa bb : aa <> bb
 => equiv[ BinSampleSpec.main ~ BinSampleSpec.spec : arg{1} = (aa,bb) /\ ={arg} ==> ={res} ].
progress.
bypr res{1} res{2}. smt().
progress.
case (a = aa).
progress.
have ->: Pr[BinSampleSpec.main(a{1}, b{1}) @ &1 : res = aa] = (inv 2%r).
byphoare (_: arg = (aa,bb) ==> _).
apply fst_choice_pr. smt(). smt(). auto.
byphoare (_: arg = (aa,bb) ==> _).
proc. rnd. skip. progress.
rewrite duniformE.
have ->: (undup [a{hr}; b{hr}]) = [a{hr}; b{hr}]. smt(@List).
simplify. rewrite /b2i. simplify.
have ->: (b{hr} = a{hr}) = false. smt().
simplify.
auto. smt(). auto.
case (a = bb).
progress.
have ->: Pr[BinSampleSpec.main(a{1}, b{1}) @ &1 : res = bb] = (inv 2%r).
byphoare (_: arg = (aa,bb) ==> _).
apply snd_choice_pr. smt(). smt(). auto.
byphoare (_: arg = (aa,bb) ==> _).
proc. rnd. skip. progress.
rewrite duniformE.
have ->: (undup [a{hr}; b{hr}]) = [a{hr}; b{hr}]. smt(@List).
simplify. rewrite /b2i. simplify.
have ->: (a{hr} = b{hr}) = false. smt().
simplify.
auto. smt(). auto.
progress.
rewrite H0. simplify.
have -> : Pr[BinSampleSpec.main(aa, bb) @ &1 : res = a] = 0%r.
byphoare (_: arg = (aa, bb) ==> _). proc. hoare. inline*.
wp. rnd. skip. progress.  smt(). auto. auto.
rewrite - H1 H0. simplify.
byphoare (_: arg = (aa, bb) ==> _).
proc. rnd. skip. progress.
rewrite duniformE.
rewrite undup_id. smt(@List).
simplify.
smt(). auto. auto.
qed.


lemma sat_spec aa bb : 
  equiv[ BinSampleSpec.main ~ BinSampleSpec.spec : arg{1} = (aa,bb) /\ ={arg} ==> ={res} ]. 
case (aa = bb).
progress.
proc.
wp.  rnd{2}.
inline*. wp. rnd {1}. skip. progress.
smt(@Distr).
smt(@Distr).
smt(@Distr).
progress. apply sat_spec_not_eq. auto.
qed.

end section.

end RandomChoice.

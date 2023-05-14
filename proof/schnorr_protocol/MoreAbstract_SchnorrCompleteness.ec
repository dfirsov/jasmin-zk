pragma Goals:printall.
require import AllCore DBool Bool List Distr.
require import Int IntDiv Real Distr StdOrder List.

require import MoreAbstract_SchnorrBasics.
import CG EG.

section.

local lemma dl_complete_h (p : dl_stat) (w : dl_wit) : 
  completeness_relation p w =>
   hoare [ Completeness(HP,HV).run : arg = (p,w) ==> res ].
progress.
proc. inline*.  wp. 
rnd. wp.  rnd.  wp. 
skip. progress.
rewrite /verify_transcript. simplify.
rewrite /dl_verify. simplify.   rewrite /(^^).
pose ch := x2.
have ->: asint (r0 + ch * w{hr}) = (asint r0 + asint (ch * w{hr})) %% q. smt.
have <-: g ^ ((asint r0 + asint (ch * w{hr})))
 = g ^ ((asint r0 + asint (ch * w{hr})) %% q). smt (pow_mod).
have ->: g ^ (asint r0 + asint (ch * w{hr}))
 = g ^ asint r0 * g ^  asint (ch * w{hr}).
smt(@CG).
have ->: asint (ch * w{hr}) = (asint ch * asint w{hr}) %% q. smt.
have ->: g ^ (asint ch * asint w{hr} %% q) = g ^ (asint ch * asint w{hr}). smt (pow_mod).
have -> : (asint ch * asint w{hr}) = (asint w{hr} * asint ch). smt().
have ->: g ^ (asint w{hr} * asint ch) = g ^ asint w{hr} ^ asint ch. smt.
have ->: g ^ asint w{hr} = s{hr}. smt().
smt(@CG).
smt(@CG g_is_generator).
qed. 

(* one-round completeness  *)
lemma dl_completeness: forall (statement : dl_stat) (witness : dl_wit) &m,
  completeness_relation statement witness =>
     Pr[Completeness(HP, HV).run(statement, witness) 
            @ &m : res] = 1%r.
move => ya wa &m  isdl .
 byphoare (_: arg = (ya, wa) ==> _);auto.
proc*.
seq 1 : true 1%r 1%r 1%r 0%r r.
call (dl_complete_h ya wa). auto.
conseq (_: true ==> true). inline*. sp.
wp.  progress. rnd. simplify.
conseq (_: true ==> true). progress. apply duniform_ll. smt(challenge_set_size).
wp.  rnd. skip. simplify.
smt(@Distr q_prime). skip. auto. skip. auto. auto.
qed.


(* iterated completeness *)
lemma dl_completeness_iter: forall (statement:dl_stat) (witness:dl_wit) &m n,
        1 <= n =>
       completeness_relation statement witness =>
      Pr[CompletenessAmp(HP,HV).run(statement, witness,n) @ &m : res] = 1%r.
progress.
apply (PerfectCompleteness.completeness_seq HP HV).
progress.
apply dl_completeness. auto. auto. auto.
qed.

  
end section.

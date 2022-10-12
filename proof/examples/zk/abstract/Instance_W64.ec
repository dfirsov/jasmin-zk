

require import AllCore IntDiv CoreMap List.

require import JModel.
require import BitEncoding.
import BS2Int.

op P : int.
axiom P_small : 0 <= P < W64.max_uint.
axiom P_prime : prime P.

require import Fp_small.

require Abstract_exp_proof_8.
clone import Abstract_exp_proof_8 as ExpW64 with type R  <- W64.t,
                                                 op Rsize <- 64,
                                                 op Rbits <- W64.w2bits,
                                                 op bitsR <- W64.bits2w,
                                                 op P <- P
proof*.

realize Rsize_max. smt(). qed.
realize Rsize_pos. smt(). qed.
realize valr_pos. smt (@W64). qed.
realize iii.  smt (@W64). qed.
realize valr_ofint.  
progress. 
progress. rewrite /valR. rewrite /of_int. 
have ->: (w2bits ((bits2w (int2bs 64 x)))%W64) 
 = (int2bs 64 x). smt.
admit.
qed.
realize P_prime. apply P_prime. qed.
realize ofint_valr. progress. smt. qed.
realize rbits_bitsr. smt. qed.
realize bitsr_rbits. smt. qed.

(* not ours *)
realize Zp.Sub.insubN. admitted.
realize Zp.Sub.insubT.  admitted.
realize Zp.Sub.valP. admitted.
realize Zp.Sub.valK. admitted.
realize Zp.Sub.insubW. admitted.

require import Fp_small_proof.



print W64.
lemma pre_fin_real : 
 equiv[ Spec.expm ~ M7(M).expm :
            valR m{2} = P /\
            ImplFp x{2} a{1} /\ b{1} = valR n{2} /\ valR x{2} < P ==>
            ImplFp res{2} res{1}].
apply (exp_pre_fin M).
symmetry.
transitivity ASpecFp.swapw 
  (={arg} ==> ={res})
  (arg{2}.`1 = arg{1}.`1 /\ arg{2}.`2 = arg{1}.`2 /\   arg{2}.`3 = as_word arg{1}.`3
    ==> ={res}).
progress. smt(). smt().
proc. skip. progress.
symmetry.
proc.  wp. skip.
progress.
rewrite /set0_64. simplify.
case (toswap{2}). progress.
rewrite /as_word. simplify.
smt (@W64).
rewrite /as_word. simplify.
smt (@W64).
progress.
rewrite /as_word. simplify.
smt (@W64).  
rewrite /as_word. simplify.
smt (@W64).  

symmetry.
transitivity ASpecFp.ith_bit 
  (={arg} ==> ={res})
  (arg{1}.`1 = arg{2}.`1 /\  arg{1}.`2 = W64.to_uint arg{2}.`2 
    /\ 0 <= ctr{1} < 64 ==> ={res} /\ (res{2} = W64.one \/ res{2} = W64.zero)).
progress. smt(). smt().
proc. skip. progress. rewrite /ith_bitR. rewrite /ith_bitword64.
rewrite /ith_bit. rewrite /as_w64. 
rewrite /as_word.
have -> : nth witness (w2bits k{2}) ctr{2}  = k{2}.[ctr{2}].

auto.





admit. 


admit.

auto.
qed.


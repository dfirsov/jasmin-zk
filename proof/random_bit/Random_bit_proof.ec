
require import AllCore IntDiv CoreMap List Distr DList.
from Jasmin require import JModel.

require import Array32.
require BinUniSample_spec.
require import Array1 WArray1.
require import Finite ArrayFiniteness.

require import BigNum_proofs.
require import W64_SchnorrExtract.

require import BinUniSample_spec.


clone import RandomChoice as W8RandomChocie with type t <- W8.t 
proof*.

section.

local op h = (fun (a : WArray1.t) => Array1.init (fun i => WArray1.get8 a i)).

local lemma init_ext:
  forall (f1 f2 : int -> W8.t),
       (Array1.init f1) = (Array1.init f2) =>
    (forall (x : int), 0 <= x && x < 1 => f1 x = f2 x).
smt(@Array1).
qed.


local lemma h_inj : injective h.
rewrite /injective.
rewrite /h. 
move => x y  q.
have :  get8 x 0 =  get8 y 0.
apply  (init_ext _ _ q 0 _). smt().
rewrite /get8. smt(@WArray1).
qed.


local lemma h_surj : surjective h.    
rewrite /surjective.
progress. 
exists (WArray1.init (fun i => x.[i])).
rewrite /h.
apply Array1.ext_eq.
progress. have ->: x0 = 0. smt().
smt(@Array1 @WArray1).
qed.



local lemma darray_ll:
 is_lossless darray.
proof. rewrite /darray. apply dmap_ll; apply dlist_ll. smt(@W8). qed.


local lemma supp_darray a:
 a \in darray <=> all (support W8.dword) (WArray1.to_list a).
proof.
rewrite /darray128 supp_dmap; split.
 move=> [x]; rewrite supp_dlist // => /> *.
 by rewrite WArray1.of_listK // /#.
move=> H; exists (to_list a); rewrite supp_dlist // H Array256.size_to_list /=.
qed.


local lemma darray_uni:
   is_uniform (darray).
proof.
rewrite /darray1=> ?; apply dmap_uni_in_inj.
 move=> x y; rewrite !supp_dlist //; move => [? _] [? _] H.
  smt(@WArray1).
 apply dlist_uni. smt(@W8).
qed.


local lemma darray_fu:
   is_full darray.
proof.
rewrite /darray => H; apply dmap_fu_in.
move=> x; exists (to_list x); rewrite to_listK supp_dlist //=.
rewrite allP.
progress. smt(@W8).
qed.

local op byte_distr = dmap WArray1.darray h.

local lemma byte_distr_uni : is_uniform byte_distr .
rewrite /jsmD.
apply dmap_uni_in_inj.
progress. smt (h_inj).
apply darray_uni.
qed.


local lemma byte_distr_ll: is_lossless byte_distr.
rewrite /jsmD.
apply dmap_ll.
apply darray_ll.
qed.

local lemma byte_distr_fu : is_full byte_distr .
rewrite /jsmD.
apply dmap_fu.
smt (h_surj).
apply darray_fu.
qed.




local module SampleModule = {
  proc byte_distr() = {
    var r;
    r <$ byte_distr;
    return r;
  }

  proc bit_distr() = {
    var b;
    b <@ byte_distr();
    b.[0] <- (b.[0] `&` (W8.of_int 1));
    return b.[0];
  }

}.



local lemma zzz : size (to_seq (support byte_distr)) =  256.
have : size all_256words1 = size (to_seq (support byte_distr)).
apply uniq_size_uniq.
apply uniq_to_seq.
smt(@Distr byte_distr_uni).
progress. apply all_256words1_full.
have : x \in byte_distr.
apply byte_distr_fu.
smt.
apply all_256words1_uniq.
progress. rewrite - H.
rewrite all_256words1_size. smt().
qed.

local op toi (x : W8.t Array1.t) : int = W8.to_uint x.[0].
local op fri (x : int) : W8.t Array1.t   = (Array1.init (fun i => (W8.of_int x))).
local lemma lemma2 : 
  equiv [SampleModule.byte_distr ~ SampleByte.sampleInt : true ==> (toi res{1} = res{2})  ].
proc.
rnd  toi fri.
skip. progress.
rewrite /toi /fri. 
smt.
rewrite duniform1E_uniq. smt(@List).
have ->: xR \in range 0 (255 + 1). smt(@List @Distr).
simplify. 
have ->: size (range 0 256) = 256. smt(@List).
rewrite mu1_uni. apply byte_distr_uni.
rewrite byte_distr_fu. simplify.
rewrite byte_distr_ll. 
rewrite zzz. auto.
have : 0 <= toi rL < 256. rewrite /toi. 
have ->: 256 = W8.modulus. ring.
apply W8.to_uint_cmp.
smt(@Distr).
rewrite /fri /toi.
apply Array1.ext_eq.
progress.
have ->: x = 0. smt().
simplify. auto.
qed.

local lemma lemma3 : 
  equiv [SampleModule.bit_distr ~ SampleByte.run : true ==> (W8.to_uint res{1} = res{2}) /\ (res{1} = W8.zero \/ res{1} = W8.one) ].
proc.
wp. call lemma2. skip. progress.
rewrite /toi. 
have ->: W8.one = (W8.of_int (2 ^ 1 - 1)). simplify. auto.
rewrite (W8.and_mod 1 result_L.[0] _ ). auto. simplify. smt(@IntDiv).
have ->: W8.one = W8.of_int (2 ^ 1 - 1). smt(@W8).
rewrite (W8.and_mod 1 result_L.[0] _). auto. simplify.
smt(@W8).
qed.


lemma random_bit_lemma4 : 
  equiv [M(Syscall).random_bit ~ SampleByte.run : true ==>  (W8.to_uint res{1} = res{2}) /\ (res{1} = W8.zero \/ res{1} = W8.one) ].
transitivity SampleModule.bit_distr
 (true ==> res{1} = res{2})
 (true ==> W8.to_uint res{1} = res{2} /\ (res{1} = W8.zero \/ res{1} = W8.one)).
auto. auto.
proc. wp.
inline*.
wp. rnd. wp.
skip. progress.
conseq lemma3.
qed.


local lemma lemma5 : 
  equiv [M(Syscall).random_bit ~ BinSampleSpec.main : arg{2} = (W8.zero, W8.one) ==> res{1} = res{2} ].
proof.
proc*. inline BinSampleSpec.main. wp.
call random_bit_lemma4. wp. skip. progress.
elim H. progress. progress.
qed.


(* this lemma establishes that random_bit is equivalent to the distribution "duniform [W8.zero; W8.one]"  *)
lemma random_bit_eq :
  equiv [M(Syscall).random_bit ~ BinSampleSpec.spec : arg{2} = (W8.zero, W8.one) ==> res{1} = res{2} ].
symmetry.
transitivity BinSampleSpec.main
  (={arg} ==> ={res})
  (arg{1} = (W8.zero, W8.one)  ==> ={res}).
progress. smt(). auto.
symmetry.
proc*. ecall (sat_spec a{1} b{1}). skip. auto.
symmetry.
conseq lemma5.
auto. 
qed.



end section.

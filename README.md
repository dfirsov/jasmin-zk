## Contents

### `src/`
* `schnorr_protocol.jazz` implementation of Schnorr protocol in Jasmin.
* `constants.py` Python script which given primes `p` and `q` generates parameters for Jasmin `constants.jazz` and proofs in EasyCrypt `proof/schnorr_protocol/Constants.ec`.
* `bn_generic.jazz` Jasmin's Big Numb library.
* `dbn_generic.jazz` Same as `bn_generic.jazz`, but for words of `2*nlimbs` size.
* `bn_generic_extra.jazz` extension of Jasmin BigNum library.
   - `bn_addm` modular addition;
   - `bn_breduce` Barrett's modular reduction;
   - `bn_mulm` modular multiplication;
   - `bn_expm` Montgomery ladder based modular  exponentiation;
   - `bn_rsample` rejection sampling algorithm for uniform distributions.
* `schnorr_protocol.h` C-interface of external calls for the Schnorr protocol entry points.

### `src/example`
* `example.c` C-wrapper which links the Schnorr protocol procedures (which were previously compiled by Jasmin) and handles dispatching of messages.
* `syscalls/` implementation of System calls for linking with Jasmin programs.


### `proof/`
* `BigNum_proofs.ec` proof of correctness for (simple) Jasmin procedures on Big Numbers.
* `BigNum_spec.ec` parameters and (abstract + semi-abstract) specification of operations on Big Numbers.
* `AuxLemmas.ec` auxiliary lemmas.
* `montgomery_ladder/`:
   - `MontgomeryLadder_Abstract.eca` correctness of abstract Montgomery ladder parameterized by a monoid.
   - `MontgomeryLadder_Concrete.eca` instance of Montgomery ladder for Jasmin's `bn_expm` function.
   - `MontomeryLadder_Concrete_CT.ec` proof that `bn_expm` is constant-time.  
* `modular_multiplication/`
   - `BarrettRedInt.ec` derivation of correctness of Barrett reduction for reals and then integers.
   - `BarrettReduction_Abstract.ec` equivalence proof of abstract and (semi-abstract) specifications of Barrett reduction algorithms.
   - `BarrettReduction_Concrete.ec`  correctness proof of Jasmin's `bn_breduce` implementation of Barrett reduction.
   - `BarretReduction_Concrete_CT.ec` constant-time proof for `bn_breduce`.
   - `ModularMultiplication_Concrete.ec` correctness for implementation of modular multiplication `bn_mulm`.
   - `ModularMultiplication_Concrete_CT.ec` proof that `bn_mulm` is constant-time.   
* `rejection_sampling/`
  - `RejectionSamplingModule.eca` abstract rejection sampling algorithm in EasyCrypt.
  - `RejectionSamplingProperties.eca` main properties of of abstract EasyCrypt's rejection sampling algorithm.  
  - `UniformSampling_Concrete.ec` proof that Jasmin's function `bn_rsample` implements rejection sampling is correctly.
  - `UniformSampling_Concrete_LF.ec` proof that `bn_rsample` is leakage-free (probabilistic non-interference).
* `jasmin_extracts/` folder which contains EasyCrypt code automatically extracted by Jasmin compiler.
* `eclib/` Jasmin's standard library for EasyCrypt.
* `definition_analysis/` analysis of constant-time and leakage-freeness definitions.
* `finite_types/`
   - `FinLists.ec` proofs that Jasmin's array datatypes (i.e., `ArrayX`, `WArrayY`) are finite.
   - `SurjFromInj.ec` proof that every injective function on the finite sets of the same cardinality is also surjective.
* `schnorr_protocol/`
  - `Abstract_SchnorrProtocol.ec` formalization of Schnorr protocol at the "high-level" of abstraction (elements are group elements, exponents are fintie field elements).
  - `Zp_SchnorrProtocol.eca` formalization of Schnorr protocol at the "middle-level" of abstraction (elements are finite field elements, exponents are integers).
  - `W64_SchnorrProtocol.ec` basic definitions associated with "low-level" (Jasmin extract) implementation of Schnorr protocol.
  - `W64_Zp_SchnorrCorrespondance.eca` proofs of equivalences between Schnorr procedures at "middle-level" and "low-level".
  - `W64_SchnorrProeprties.eca` final derivation of properties for Schnorr at the "low-level".
  - `Constants.ec` automatically generated file by `src/constants.py` file which contains Schnorr protocol parameters `p` (group order),`q` (exponent order), `bp` (Barrett factor for `p`), `bq` (Barrett factor for `q`), and `g` (generator of subgroup of prime order `q`). Also contains automatically generated proofs that Jasmin functions `bn_set_p`, `bn_set_q`, etc. correctly encode the respective values.
  - `ConstantsValidation.ec` proofs (based on tacticals) that parameters in `Constants.ec` are valid (e.g., `g` is a generator of order subgoup of `q`, `bp` is a Barrett parameter for `p`, etc.).
  - `W64_SchnorrInstance.ec` instance of the Schnorr protocol defined for parameters from `Constants.ec`.
  - `side_channel_properties/` proofs that Jasmin implementation of `verify` and `response` are constant time; `commitment` and `challenge` are leakage-free.
  - `ZModPStar.eca` abstract definition of Zp*.

* `leakage_functions/Ops_LeakageFunctions.ec` explicit proofs that main operations on the big nums are "constant-time" in a sense that there exist functions which compute leakages from public inputs.

* `easycrypt-zk-code/` contains formalization of zero-knowledge proofs by  (Firsov, Unruh, CSF 2023).

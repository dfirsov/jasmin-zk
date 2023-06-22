## Makefile
* `make opam_pin` installs EasyCrypt and Jasmin (versions specified in `Makefile`).
* `make update_downloads` fetches dependendencies from Github repositories (versions specified in the `Makefile`).
   - BigNum library of Jasmin;
   - Zero-Knowledge library of EasyCrypt;
   - Jasmin's `eclib` for EasyCrypt.
* `make check_all` runs the EasyCrypt proof-checker on the entire development (requires CVC4, Alt-Ergo, and Z3 SMT solvers).
* `make compile_and_run` compiles and runs Schnorr protocol (Jasmin protocol implementation in `src/schnorr_protocol.jazz`; linked together by C-wrapper `src/example/example.c`).


## Contents

### `src/`
* `schnorr_protocol.jazz` implementation of Schnorr protocol in Jasmin.
* `constants.py` Python script which given primes `p` and `q` generates parameters for Jasmin `constants.jazz` and proofs in EasyCrypt `proof/schnorr_protocol/Constants.ec`.
* `bn_generic.jazz` basic operations on big-nums.
* `dbn_generic.jazz` Same as `bn_generic.jazz`, but for words of `2*nlimbs` size.
* `bn_generic_extra.jazz` more advanced ops on big-nums
   - `bn_addm` modular addition;
   - `bn_breduce` Barrett's modular reduction;
   - `bn_mulm` modular multiplication;
   - `bn_expm` Montgomery ladder based modular  exponentiation;
   - `bn_rsample` rejection sampling algorithm for uniform distributions.
   - `random_bit` implements `{0,1}` distribution.
* `schnorr_protocol.h` C-interface of external calls for the Schnorr protocol entry points.
* `constants.py` Python script which takes primes `p` and `q` and produces Jasmin encoding in  `src/constants.jazz` and their validation in `proof/Constants.ec`.


### `src/example/`
* `example.c` C-wrapper which links the Schnorr protocol procedures and handles dispatching of messages.
* `syscalls/` (random and pseudo-random) implementation of Jasmin's `#randombytes` system-call.


### `proof/`
* `auxiliary_lemmas/`
   - `AuxLemmas.ec` auxiliary lemmas.
   - `SurjFromInj.ec` derives surjectivity from injectivity of functions of finite set of same cardinality.
   - `ArrayFiniteness.ec` derives finiteness of `ArrayN` and `WArrayN`  types.
* `big_num_ops/`:
   - `BigNum_proofs.ec` proof of correctness for (simple) Jasmin procedures on big-nums.
   - `BigNum_spec.ec` parameters and (abstract + semi-abstract) specification of operations on big-nums.
   - `BigNum_instances.ec` instantiation of big-nums for a particular nlimbs.
   - `W64xN_Finite.ec` proofs that `W64xN.R.t` type is finite.
   - `leakage_freeness/` proofs of CT of operations on big-nums.
* `montgomery_ladder/`:
   - `MontgomeryLadder_Abstract.eca` correctness of abstract Montgomery ladder parameterized by a monoid.
   - `MontgomeryLadder_Concrete.eca` instance of Montgomery ladder for Jasmin's `bn_expm` function.
   - `leakage_freeness/` proofs of CT of `bn_expm`.
* `modular_multiplication/`
   - `BarrettRedInt.ec` derivation of correctness of Barrett reduction for reals and then integers.
   - `BarrettReduction_Abstract.ec` equivalence proof of abstract and (semi-abstract) specifications of Barrett reduction algorithms.
   - `BarrettReduction_Concrete.ec`  correctness proof of Jasmin's `bn_breduce` implementation of Barrett reduction.
   - `ModularMultiplication_Concrete.ec` correctness for implementation of modular multiplication `bn_mulm`.
   - `leakage_freeness/` proofs of CT of `bn_breduce` and `bn_mulm`.
* `rejection_sampling/`
  - `RejectionSamplingModule.eca` abstract rejection sampling algorithm in EasyCrypt.
  - `RejectionSamplingProperties.eca` main properties of abstract EasyCrypt's rejection sampling algorithm.  
  - `UniformSampling_Concrete.ec` proof that Jasmin's function `bn_rsample` implements rejection sampling is correctly.
  - `leakage_freeness/` proofs of LF of `bn_rsample`.
* `jasmin_extracts/` folder which contains EasyCrypt code automatically extracted by Jasmin compiler.
* `eclib/` Jasmin's library for EasyCrypt.
* `definition_analysis/` analysis of constant-time and leakage-freeness definitions (see the paper).
* `schnorr_protocol/`
  - `Abstract_SchnorrProtocol.ec` formalization of Schnorr protocol at the "high-level" of abstraction (elements are group elements, exponents are fintie field elements).
  - `Zp_SchnorrProtocol.eca` formalization of Schnorr protocol at the "middle-level" of abstraction (elements are finite field elements, exponents are integers).
  - `Zp_Abstract_SchnorrCorrespondance.eca` proofs of equivalences between Schnorr procedures at "high-level" and "middle-level".
  - `Zp_SchnorrCompleteness.eca` completeness for "middle-level" Schnorr.
  - `Zp_SchnorrExtractability.eca` extractability for "middle-level" Schnorr.
  - `Zp_SchnorrZK.eca` zero-knowledge for "middle-level" Schnorr.
  - `W64_SchnorrProtocol.ec` basic definitions associated with "low-level" (Jasmin extract) implementation of Schnorr protocol.
  - `W64_Zp_SchnorrCorrespondance.eca` proofs of equivalences between Schnorr procedures at "middle-level" and "low-level".
  - `W64_SchnorrCompleteness.eca` completeness for "low-level" Schnorr.
  - `W64_SchnorrExtractability.eca` extractability for "low-level" Schnorr.
  - `W64_SchnorrZK.eca` zero-knowledge for "low-level" Schnorr.
  - `W64_SchnorrInstance.ec` instantiation of Schnorr protocol and all its properties for particular choice of constants from `Constants.ec`.
  - `Constants.ec` automatically generated file by `src/constants.py` file which contains Schnorr protocol parameters `p` (group order),`q` (exponent order), `bp` (Barrett factor for `p`), `bq` (Barrett factor for `q`), and `g` (generator of subgroup of prime order `q`). Also contains automatically generated proofs that Jasmin functions `bn_set_p`, `bn_set_q`, etc. correctly encode the respective values.
  - `ConstantsValidation.ec` proofs (based on tacticals) that parameters in `Constants.ec` are valid (e.g., `g` is a generator of subgoup of order `q`, `bp` is a Barrett parameter for `p`, etc.).
  - `W64_SchnorrInstance.ec` instance of the Schnorr protocol cloned with parameters from `Constants.ec`.
  - `leakage_freeness/` proofs that Jasmin implementation of `verify`, `challenge` and `response` are constant time;  `challenge` is leakage-free.
  - `ZModPStar.eca` abstract definition of Zp* through `Subtype` theory.

* `easycrypt-zk-code/` contains formalization of zero-knowledge proofs from "D. Firsov, D. Unruh. [Zero-Knowledge in EasyCrypt](https://eprint.iacr.org/2022/926)".

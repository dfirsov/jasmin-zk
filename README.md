## Contents

### `src/`

* `schnorr_protocol.jazz`: Implementation of Schnorr protocol in Jasmin.
* `constants.py`: Python script which given prime `p` and `q` generates parameters for Jasmin (`constants.jazz`) and EasyCrypt (`proof/schnorr_protocol/Constants.ec`)
* `bn_generic_extra.jazz` features:
   - `bn_addm` modular addition 
   - `bn_breduce` Barrett's modular reduction;
   - `bn_mulm` modular multiplication (uses `bn_breduce`);
   - `bn_expm` Montgomery ladder based modular  exponentiation (uses `bn_mulm`).
   - `bn_rsample` rejection sampling algorithm for uniform distributions.
* `bn_generic.jazz`: Jasmin's Big Numb library.
* `dbn_generic.jazz`: same as `bn_generic.jazz`, but for words of 2*nlimbs size.
* `schnorr_protocol.h` specifies the interfaces of the Schnorr protocol entry points.

### `src/example`

* `example.c` - the C wrapper which links the Schnorr protocol procedures (which were previously compiled by Jasmin) and handles a dispatching of messages.
* `syscalls/` - the folder which contains implementation of System calls for linking with Jasmin programs.


### `proof/`
* `BigNum_proofs.ec` proof of correctness for (simple) Jasmin procedures on Big Numbers.
* `BigNum_spec.ec` parameters and specification of operations on Big Numbers.
* `AuxLemmas.ec` auxiliary lemmas.
* `montgomery_ladder/`:
   - `MontgomeryLadder_Abstract.eca` formalization of correctness of Montgomery ladder parameterized by a monoid.
   - `MontgomeryLadder_Concrete.eca` instance and proof of correctness for Jasmin's `bn_expm` function.
   - `MontomeryLadder_Concrete_CT.ec` proof of constant-time.  
* `modular_multiplication/`
   - `BarrettRedInt.ec` derivation of correctness of Barrett reduction for integers.
   - `BarrettReduction_Abstract.ec` proof of equivalence of abstract and concrete specifications of Barrett reduction.
   - `BarrettReduction_Concrete.ec` proof of correctness of Jasmin's `bn_breduce` implementation of Barrett reduction.
   - `BarretReduction_Concrete_CT.ec` proof that `bn_breduce` is constant-time.
   - `ModularMultiplication_Concrete.ec` proof of concrete Jasmin implementation of modular multiplication (`bn_mulm` function).
   - `ModularMultiplication_Concrete_CT.ec` proof that `bn_mulm` is constant-time.   
* `rejection_sampling/`
  - `UniformSampling_Concrete.ec` proof that Jasmin's implementation of rejection sampling is correct (procedure `bn_rsample`).
  - `UniformSampling_Concrete_LF.ec` proof that `bn_rsample` is leakage-free.
  - `RejectionSamplingModule.eca` module which implements rejection sampling in EasyCrypt.
  - `RejectionSamplingProperties.eca` main properties of of abstract EasyCrypt's rejection sampling algorithm.  
* `jasmin_extracts/`: folder which contains EasyCrypt code automatically extracted by Jasmin compiler.
* `eclib/`: Jasmin's standard library for EasyCrypt.
* `definition_analysis/`: analysis constant-time and leakage-freeness definitions.
* `finite_types/`:
   - `FinLists.ec` - proofs that Jasmin's array datatypes (i.e., `ArrayX`, `WArrayY` are finite).
   - `SurjFromInj.ec` - proof that every injective function on the finite sets of the same cardinality is also surjective.
* `schnorr_protocol/`:
  - `Abstract_SchnorrProtocol.ec` formalization of Schnorr protocol at the "high-level" of abstractions (elements are group elements, exponents are fintie field elements).
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

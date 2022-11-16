## Contents

### `src/`

* `bn_generic.jazz`: part of the `libjbn` library (with minor additions).
* `ring_ops.jazz` features:
   - `bn_breduce` Barrett reduction;
   - `mulm` field multiplication (uses `bn_breduce`);
   - `expm` Montgomery ladder based field exponentiation (uses `mulm`).
   

### `proof/`
* `eclib/` parts of Jasmin stdlib (+ autogenerated Array* WArray*).
* `montgomery_ladder/` abstract and axiomatized formalization of correctness of montgomery ladder algorithm.
* `BarrettRedInt.ec` Analysis (correctness + width) of Barrett reduction.
* `Ring_ops_extract.ec` EasCrypt extract from `ring_ops.jazz` for functional correctness proofs.
* `Ring_ops_proof.ec` proofs of functional correctness of `bn_breduce`, `mulm`, and `expm` (and other misc stuff).
* `Ring_ops_extract_ct.ec` constant-time extraction of `ring_ops.jazz`.
* `Ring_ops_proof_ct.ec` constant-time proof based on `Ring_ops_extract_ct.ec`.
* `Ring_ops_spec.ec` abstract specification (in finite fields) of properties of `mulm`, `expm`, and `bn_breduce`.


### `test/`
* `ring_ops.c` C program for testing (must be linked with `ring_ops.s` which is produced by Jasmin) during the compilation.
* `gmp_test.c` GMP based modular exponentiation for perfomance comparison.


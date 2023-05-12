# Overview

Our generic development is contained in EasyCrypt theories. Below we present how these theories are structured and the main results (lemmas) which they feature:

- StatisticalCompleteness  (file: GenericSoundness.eca)
  - `lemma completeness_seq` 
    *(iterated completeness from one run statistical completeness)*
- PerfectCompleteness (file: GenericSoundness.eca)
   - `lemma completeness_seq`
     *(iterated completeness from one run perfect completeness)* 
- StatisticalSoundness (file: GenericSoundness.eca)
   - `lemma soundness_seq` 
    *(iterated soundness from one run statistical soundness)*

- Extractability (file: GenericExtractability.eca)
  - `lemma statistical_soundness_generic`
    *(statistical soundness from extractability)* 
- SpecialSoundness (file: GenericSpecialSoundness.eca)
  - Computational
    - `lemma computational_extractability`
       *(computational extractability from computational special soundness)*
    - `lemma computational_soundness`
        *(computational soundness from computational special soundness)*
     - `lemma computational_soundness_II`
       *(computational soundness from computational special soundness with different security boudns)*
  - Perfect
    - `lemma statistical_extractability`
       *(computational extractability from perfect  special soundness)*
    - `lemma statistical_soundness`
       *(computational soundness from perfect  special soundness)*
- ZeroKnowledge  (file: GenericZeroKnowledge.eca)
  - SequentialComposition
    - `lemma zk_seq`
     *(iterated zero-knowledge from statistical one run zero-knowledge)*
  - OneShotSimulator
    - Computational
      - `lemma computational_zk`
      *(computational zero-knowledge from computational properties of one-shot simulator)*
    - Statistical
    *(statistical zero-knowledge from statistical properties of one-shot simulator)*
      - `lemma statistical_zk`


# Implementing a protocol
In the following we give instructions on how to instantiate our development for sigma protocols. Also consider investigating our case studies in `case_studies/` folder.  Especially Fiat-Shamir is well-peppered with comments and has concise and clear instantiation.

## Step 1: Clone sigma protocol 

    require GenericSigmaProtocol.
    
    clone include GenericSigmaProtocol with 
      type statement           <- your_statement,
      type commitment          <- your_commitment,   
      type witness             <- your_witness,
      type response            <- your_response,
      type challenge           <- your_challenge,
      op challenge_set         <= your_challenge_set,
      op verify_transcript     <- your_verify_transcript,
      op soundness_relation    <- your_soundness_relation,
      op completeness_relation <- your_completeness_relation,
      op zk_relation           <- your_zk_relation
    proof*.
    (* realize the proof obligatgions *)

After cloning you can use the results from theories described in Overview above.

Also you already "instantiated" the honest verifier `HV: HonestVerifier`. You can see its contents by writing: `print HV.`

## Step 2: (Iterated) Completeness

- Implement a module for honest prover:

      module HP : HonestProver = {
      ...
      }.

- Prove one round completeness (usually perfect or statistical) for honest prover `HP`. 
- Combine one round completeness with `competeness_seq` (from `StatisticalCompleteness` or  `PerfectCompleteness`) to automatically conclude iterated completeness.

## Step 3: Special Soundness

Prove perfect or computational special soundness. 

## Step 4: Extractability

Depending on whether you proved perfect or computational special soundness in the previous step combine it with  `SpecialSoundness.Perfect.statistical_extractability` or `SpecialSoundness.Computational.computational_extractability` to automatically conclude extractability for your sigma protocol.

## Step 5: (Iterated) Soundness

- If previously you proved special soundness then combine it with `SpecialSoundness.Perfect.statistical_soundness` or `SpecialSoundness.Computational.computational_soundness` to automatically conclude one run soundness.
- If previously you derived extractabiltiy, but not from special soundness then combine `Extractability.statistical_soundness_generic`  with your extractrabiltiy statement to derive soundness (consult the paper for details).
- After you derived one run statistical soundness then combine it with `soundness_seq` to conclude iterated soundness.

## Step 6: (Iterated) Zero-Knowledge
- Implement "one-shot" simulator 
 
      module Sim1(V : RewMaliciousVerifier) : Simulator1 = {
      ...
      }.
- Use `ZeroKnowledge.OneShotSimulator.Computational.computational_zk` or `ZeroKnowledge.OneShotSimulator.Statistical.statistical_zk` to conclude one run zero-knowledge for `Sim1`. To do that you will additionally need to prove properties about `Sim1`. 
- If in the previous step you concluded statistical zero-knowledge use  `ZeroKnowledge.SequentialComposition.zk_seq` to conclude iterated zero-knowledge automatically.

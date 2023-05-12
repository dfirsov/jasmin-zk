# Fiat-Shamir protocol 

The language of Fiat-Shamir protocol consists of quadratic residues. An element $s \in \mathbb{Z}/n\mathbb{Z}$ is a quadratic residue if there exists $w$ so that $s=w^2$ and $s$ is invertible. Here the multipication must be understood as a ring multiplication. In Fiat-Shamir protocol the prover tries to convince a verifier that a statement is quadratic residue and it knows the witness.

## Protocol description
Let us give an informal protocol description. The protocol starts by the prover generating a random invertible ring element $r$ and sending its square $a = r^2$ to the verifier.  The verifier receives the commitment $a$ and replies with a random bit $b$ as a challenge.  The prover replies with $z = w^br$. Finally, the verifier accepts if $z^2 = s^ba$ and $a$ is invertible.

## Main results
- *[FS_Basics.ec](FS_Basics.ec)*
	- `module HP` - honest prover.
	- `op verify_transcript` -  verification function of honest verifier.
- *[FS_Completeness.ec](FS_Completeness.ec)* 
	- `lemma qr_completeness` - direct proof of one-round completeness.
	- `lemma qr_completeness_iter` - automatic conclusion of iterated completeness from one-round completeness.
- *[FS_SpecialSoundness.ec](FS_SpecialSoundness.ec)* - direct proof of perfect special soundness.
	- `op special_soundness_extract` - function for perfect witness extraction from two valid transcripts
- *[FS_Extractability.ec](FS_Extractability.ec)* 
	- `lemma qr_statistical_PoK` - automatic conclusion of extractability from special soundness. 
- *[FS_Soundness.ec](FS_Soundness.ec)*
	- `lemma qr_soundness` - automatic conclusion of one-round soundness from extractability.
	- `lemma qr_soundness_iter` - automatic conclusion of iterated soundness from one-round soundness 
- *[FS_Sim1Property.ec](FS_Sim1Property.ec)*
	- `module Sim1` - one-time simulator
	- `lemma sim1_rew_ph` - Sim1 rewinds itself in case of bad-event
	- `lemma sim1_succ` - probability of success-event
	- `lemma sim1_error` -  conditional indistinguishability
- *[FS_ZeroKnowledge.ec](FS_ZeroKnowledge.ec)* 
	- `lemma qr_statistical_zk` - automatic one-round zero-knowledge from Sim1 properties
	- `lemma qr_statistical_zk_iter` - automatic iterated zero-knowledge from one-round zero-knowledge 

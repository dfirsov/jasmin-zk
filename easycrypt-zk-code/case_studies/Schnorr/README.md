# Schnorr protocol 
The protocol is defined for a cyclic group $G_q$ of order $q$ with generator $g$. The language of the Schnorr protocol consists of all group elements.  In the Schnorr protocol the prover tries to convince a verifier that it knows a discrete logarithm of the statement. In other words, if $s \in G_q$ is a statement then then a corresponding witness is an element $w$ so that $s = g^w$. The group $G_q$ and the generator $g$ are public parameters.

The prover interacts with the verifier as follows:
- The prover chooses a $y \in \mathbb{Z}_q$ uniformly at random and sends $z := g^y$ as the commitment.
- The verifier replies with a challenge $c \in \mathbb{Z}_q$ chosen uniformly at random.
-  The prover responds with $t=y+cw$.
- The verifier accepts if $g^t = zs^c$.

**Completeness.** The Schnorr protocol has perfect completeness. For our EasyCrypt implementation the completeness proof is derived almost entirely automatically by using the built-in support for SMT solvers.

**Soundness.** It is important to note that in Schnorr protocol all statements (i.e., elements of the group) are in the language
(i.e., have witnesses). Therefore the protocol is trivially sound with soundness-error 0. Since soundness is thus a meaningless property for this protocol, we do not prove it. But note that it is meaningful to say that the protocol proves that the prover *knows* a witness. We show this below (proof of knowledge).

**Zero-Knowledge.**  Another interesting aspect of the Schnorr protocol is that we cannot show the malicious-verifier
zero-knowledge property because there is no efficient simulator. (At least no construction is known. We are not aware of a formal impossibility result.) Indeed, the challenge of the verifier is an element of the group sampled uniformly at random. This means that the size of the set of challenges (|challenge_set|) equals to the order of the group (i.e., exponentially big).  Hence, if we build a simulator based on the idea of guessing the challenge of a malicious verifier then the probability of a successful simulation will be negligible.

The Schnorr protocol does, however, satisfy the honest-verifier zero-knowledge (HVZK) property.  This property has been formalized previously and is not related to rewinding, so we did not include a proof in our case study.

**Special Soundness.** The Schnorr protocol has perfect special soundness. Recall that in the case of perfect special soundness, we are given two transcripts $t_1 = (c_1,ch_1,r_1)$ and $t_2 = (c_1,ch_2,r_2)$ which have the same commitments ($c_1 = c_2$) and different challenges ($ch_1 \neq ch_2$). In addition we know that both transcripts pass the verification which tells us that $r_1 = y + c_1w$ and $r_2 = y + c_2w$. Hence, witness can be extracted by computing $(r_1 - r_2)(c_1 - c_2)^{-1}$. In our formalization we used this idea to implement the extraction function and the special soundness is derived almost entirely automatically by the built-in SMT solvers.

**Proof of Knowledge.**  From special soundness we conclude the proof of knowledge property automatically by using the previously derived lemma |statistical_extractability|. We get the following lower bound on the success probability of the extractor:

    Pr[r <- Extractor(P).extract(s)@&m: s = g^r]
      >= (Pr[r <- Soundness(P,HV).run(s)@&m: r]^2
       - 1/(size challenge_set)
           *Pr[r <- Soundness(P,HV).run(s)@&m: r])

It is important to note that since |challenge_set = Z_p| is big then |1/(size challenge_set)| is small and therefore the success probability of an extractor is close to the square of the success probability of malicious prover in the soundness game.

The Schnorr protocol illustrates that the size of the challenge set affects zero-knowledge and proof of knowledge differently. The small challenge set is good for zero-knowledge property since the simulator has more odds of guessing the verifier's challenge; on the other hand, the small challenge set makes extractor less efficient (and vice versa for the big challenge set).

## Main results
- *[Schnorr_Basics.ec](Schnorr_Basics.ec)*
	- `module HP` - honest prover.
	- `op verify_transcript` -  verification function of honest verifier.
- *[Schnorr_Completeness.ec](Schnorr_Completeness.ec)* 
	- `lemma dl_completeness` - direct proof of one-round completeness.
	- `lemma dl_completeness_iter` - automatic conclusion of iterated completeness from one-round completeness.
- *[Schnorr_SpecialSoundness.ec](Schnorr_SpecialSoundness.ec)* - direct proof of perfect special soundness.
	- `op special_soundness_extract` - perfect witness extraction from two valid transcripts.
- *[Schnorr_Extractability.ec](Schnorr_Extractability.ec)* 
	- `lemma dl_statistical_PoK` - automatic conclusion of extractability from special soundness. 


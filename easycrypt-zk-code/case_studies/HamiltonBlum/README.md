# Blum protocol

A graph $G$ is said to be Hamiltonian if there exists a cycle that passes through each vertex of $G$ exactly once. This cycle is called a Hamiltonian cycle. Finding a Hamiltonian cycle in a graph is an NP-complete problem. Blum described a zero-knowledge protocol whose language consists of Hamiltonian graphs. More specifically, the statements are graphs and witnesses are Hamiltonian cycles.

In the following we describe the Blum protocol. Let the graph $G$ have $n$ vertices and be represented by the  adjacency matrix with $n$ rows and $n$ columns. We write $G(i,j)$ to refer to the entry at the $i$-th row and $j$-th column. The entries of adjacency matrix are booleans so that $G(i,j) = 1$ iff there is an edge from vertex $i$ to vertex $j$.  We also assume \textit{(Commit, Verify)} is a commitment scheme.  In the Blum protocol the prover $P$ wishes to prove to the verifier $V$ that $G$ is Hamiltonian as follows:


- The prover samples a random permutation $\phi$ over $n$   vertices. Then it uses $\phi$ to construct $\phi(G)$ which is a   permuted version of the adjacency matrix of~$G$. Next, $P$ commits   to each edge in the permuted adjacency matrix.  Let  $C_\phi(i,j)$ denote a commitment resulting from   running the \textit{Commit} algorithm on the $\phi(G)(i,j)$, so $C_\phi$ is a matrix of commitments.   The opening keys of these commitments are  stored in a matrix   $D_\phi$. Additionally, $P$ commits to the permutation $\phi$ that   was used to permute the adjacency matrix; denote this commitment by   $p_\phi$ and its respective opening key by $q_\phi$. Finally, the prover proceeds by sending $p_\phi$ and  $C_\phi$ to the verifier.
- The verifer replies with a challenge bit $b \in \{0,1\}$ sampled uniformly at random.
- The prover receives the bit $b$. If $b = 0$ then prover sends   the permutation $\phi$ and opening keys $D_\phi$ and $q_\phi$ to the   verifier.  That is, it opens commitments to the permuted graph and to the permutation. Otherwise, if $b = 1$ then prover uses the permutation   $\phi$ on $w$ which translates it to the Hamiltonian cycle in   $\phi(G)$. Finally, the prover sends $\phi(w)$ and the opening keys   from $D_\phi$ for only those entries whose edges appear in~$\phi(w)$.
- If the challenge bit was zero (i.e., $b=0$) then verifier   receives a permutation $\phi$, opening keys $D_\phi$ and $q_\phi$.   It uses the commitment verification algorithm \emph{Verify} to check   that $q_\phi$ is a correct opening for $\phi$ and that $D_\phi$ is a correct opening for $\phi(G)$. However, if $b = 1$, then verifier receives a cycle $\phi(w)$ and   openings for its edges. It checks that the received cycle is Hamiltonian and   that the openings corresponding to the edges of $\phi(G)$ are all 1. (That is, that $\phi(G)$ is indeed   a subgraph of the committed graph.)



**Commitment Scheme.** The security properties of the Blum protocol depend on the hiding and binding properties of the underlying commitment scheme. More specifically, special soundness, extractability, and soundness depend on the binding property, and zero-knowledge depends on the hiding property of the commitment scheme.  In our formalization we assumed that the commitment scheme is statistically hiding and computationally binding.\footnote{We choose this direction because in the context of this paper, computational soundness is more interesting that computational ZK: Analyzing computational soundness showcases the use of rewinding in the computational setting (i.e., in a setting involving reductions).} As a result we proved that our variant of Blum protocol has computational special soundness, extractability, and soundness.  At the same time zero-knowledge is statistical.

**Completeness.** The completeness of the Blum protocol relies on the correct operation of the commitment scheme. In our formalization we assumed that the commitment scheme always produces functional commitment-opening pairs. In this case the Blum protocol has perfect completeness.

**Special Soundness.** The special soundness of the Blum protocol depends on the binding property of the used commitment scheme. Let $t_1 = (c_1,ch_1,r_1)$ and $t_2 = (c_2,ch_2,r_2)$ be two valid transcripts (i.e., $c_1 = c_2$ and $ch_1 \neq ch_2$). Then w.l.o.g., assume that $ch_1 = 0$ and $ch_2 = 1$.  In this case, $c_1 = (C_\phi,q_\phi)$, where $C_\phi$ contains commitments on edges for a permuted graph, and $q_\phi$ is a commitment on the permutation.  Also, $r_1 = (\phi,D_\phi,q_\phi)$, where $\phi$ is a permutation, $D_\phi$ contains valid opening keys to commitments in $C_\phi$ and $q_\phi$ is a valid opening to $p_\phi$. At the same time, $r_2 = (w',d)$ where $w'$ is a Hamiltonian cycle in the permuted graph and $d$ contains openings of the $w'$-edges in $C_\phi$.  At this point, we  known that the keys in $d$ successfully open commitments in $C_\phi$ and that $w'$ is a cycle.  We also know that keys in $D_\phi$ open commitments in $C_\phi$ with respect to $\phi(G)$. Hence, either $\phi^{-1}(w')$ is a Hamiltonian cycle in $G$ or there exists a commitment in $C$ which corresponds to an edge in $w'$ which opens to two different values by the respective keys from $d$ and $D$.

Based on this idea we  implemented a function |special_soundness_extract| which returns $\phi^{-1}(w')$ as a Hamiltonian cycle for $G$. Also, we define a |BlumBinder| module which finds two opening keys for different values and the same commitment in case when $\phi^{-1}(w')$ is not a Hamiltonian cycle for $G$.

To sum up, the probability of unsuccesfull witness extraction from two valid transcripts is bounded from above by the probability of a successfull attack on the binding of a commitment scheme:

    lemma blum_spec_soundness: forall &m,
     Pr[Extractor(P).extract(s)@&m:
          valid_transcript_pair s r.1 r.2 /\
           !soundness_relation s
            (special_soundness_extract s r.1 r.2) ]
         <= Pr[r <- BindingExperiment(
               BlumBinder(Extractor(P))).main()@&m: r].


In our formalization, the \textbf{proof of knowledge} and \textbf{soundness} of Blum protocol are automatically derived by our generic lemmas from |blum_spec_soundness|.



**Zero-Knowledge.** In our formalization we derived zero-knowledge from a "one-shot'' simulator. Similarly to the Fiat-Shamir protocol, in the Blum protocol we define a "one-shot'' simulator which starts by trying to guess the challenge of the verifier. Next, assuming that the guess is correct, the simulator prepares a commitment to which it is going to be able to provide a response which will verify correctly.  More specifically, if the ``one-shot'' simulator guesses that the verifier sends a $0$-challenge, then the simulator produces a commitment which consists of $C_\phi$ and $p_\phi$ computed exactly as described in the protocol.  However, if the simulator guesses that the challenge is $1$, then it sends $C'_\phi$ and $p_\phi$ to the verifier where $C'_\phi$ is a commitment matrix produced for the complete graph with $n$ vertices. If the guess was correct and the verifier challenge is $1$, the simulator can reply with opening keys which correspond to edges in Hamiltonian cycle $\phi(h_n)$, where $h_n$ is a trivial Hamiltonian cycle in the complete graph $H_n$.

The proof of the properties for the described ``one-shot'' simulator are not trivial.  In our formalization, we give a sequence of cryptographic games which establish that if malicious verifier acts differently in the simulation and the real interaction with the honest prover then this verifier can be reduced to an  attacker which breaks the hiding property
of the commitment scheme.

## Main results
- *[Blum_Basics.ec](Blum_Basics.ec)*
	- `module HP` - honest prover.
	- `op verify_transcript` -  verification function of honest verifier.
- *[Blum_Completeness.ec](Blum_Completeness.ec)* 
	- `lemma hc_completeness` - direct proof of one-round completeness.
	- `lemma hc_completeness_iter` - automatic conclusion of iterated completeness from one-round completeness.
- *[Blum_SpecialSoundness.ec](Blum_SpecialSoundness.ec)* - direct proof of perfect special soundness.
	- `op special_soundness_extract` - function for witness extraction from two valid transcripts.
	- `module SpecialSoundnessAdvReduction` - adversary who breaks binding of a commitment scheme if function `special_soundness_extract` fails to return a valid witness.
	- `lemma hc_computational_special_soundness_binding` - proof that `SpecialSoundnessAdvReduction` succeeds in breaking binding if witness extraction fails.  
- *[Blum_Extractability.ec](Blum_Extractability.ec)*
	- `lemma hc_computational_PoK` - automatic conclusion of computational extractability from special soundness.
- *[Blum_Soundness.ec](Blum_Soundness.ec)*
	- `lemma hc_computational_soundness` - automatic conclusion of computational soundness from extractability.
- *[Blum_Sim1Property.ec](Blum_Sim1Property.ec)*
	- `module Sim1` - one-time simulator
	- `lemma sim1_rew_ph` - Sim1 rewinds itself in case of bad-event
	- `lemma sim1_succ` - probability of success-event
	- `lemma sim1_error` -  conditional indistinguishability
- *[Blum_ZeroKnowledge.ec](Blum_ZeroKnowledge.ec)* 
	- `lemma hc_statistical_zk` - automatic one-round zero-knowledge from Sim1 properties
	- `lemma hc_statistical_zk_iter` - automatic iterated zero-knowledge from one-round zero-knowledge 

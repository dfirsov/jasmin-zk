# Rewinding and Reflection Library

This folder contains results associated with rewindability of
adversaries and reflection of probabilistic programs as distributions.
Learn more in the respective [publication](https://eprint.iacr.org/2021/1078). 

Contents
--------

* Reflection.ec - probabilistic reflection.

  lemmas from Sec. 3.1: reflection, reflection_simple 

* FiniteApproximation.ec - finite Pr-approximation for distributions and programs.

  lemmas from Sec. 3.2: fin_pr_approx_distr_conv, fin_pr_approx_prog_conv

* Averaging.ec - averaging technique.

  lemmas from Sec. 3.2: averaging

* JensensInf.ec - Jensen's inequality for distributions with infinite support.

  lemmas from Sec. 3.2: Jensen_inf

* SquareConvex.ec - square function is convex.

* ReflectionComp.ec - reflection of composition.

  lemmas from Sec. 3.3: refl_comp_simple, refl_comp

* RewBasics.ec - basic definition of rewindable adversaries.

  defs from Sec. 4: RewProp

* RewMultRule.ec - multiplication rule for rewindable adversaries

  lemmas from Sec. 4.2: rew_mult_law, rew_clean, rew_mult_simple

* RewWithInit.ec - inequality for rewinding with initialization.

# Zero-Knowledge in EasyCrypt

This repository contains the EasyCrypt code associated with the paper "D. Firsov, D. Unruh. [Zero-Knowledge in EasyCrypt](https://eprint.iacr.org/2022/926)".

## Contents
- *[generic/](generic)*  - generic formalization of properties and derivations associated with sigma protocols.
- *[case_studies/FiatShamir/](case_studies/FiatShamir/)* - instance of Fiat-Shamir protocol.
- *[case_studies/Schnorr/](case_studies/Schnorr/)* - instance of Schnorr protocol.
- *[case_studies/HamiltonBlum/](case_studies/HamiltonBlum/)* - instance of Blum protocol. 
- *[misc/](misc/)* - miscellaneous useful results.
- *[checkall](checkall)* - script for running the EasyCrypt proof-checker on the entire development.
- *[rewinding/](rewinding/)* - rewinding and probabilistic reflection library.
- *[MANUAL.md](MANUAL.md)* - brief description of structure of the generic development.

## Setup
* For this project we used the first stable release of EasyCrypt (1.0) theorem prover ([GIT tag r2022.04](https://github.com/EasyCrypt/easycrypt/releases/tag/r2022.04), hash 577c882) 
* EasyCrypt was configured with support from the following SMT solvers: Why3@1.4.1, Z3@4.8.7, CVC4@1.6, Alt-Ergo@2.4.2.
* To check the development run:

      $> cd DEVELOPMENT_FOLDER
      $> bash checkall

* If you want to typecheck this code in Emacs then you must update your load path. Make sure your `~/.emacs` file contains the following load paths:

      '(easycrypt-load-path
       (quote
        ( "DEVELOPMENT_PATH/rewinding" 
          "DEVELOPMENT_PATH/misc"
          "DEVELOPMENT_PATH/generic")))


* **The development of EasyCrypt and its standard library is very active. As a result, to load this development we strongly suggest to use the indicated versions of the EasyCrypt, its standard library, and SMT solvers. As there were some breaking changes the current development is guaranteed not to load with older versions of EasyCrypt.**






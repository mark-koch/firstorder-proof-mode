# A first-order logic proof mode in Coq

*Update: We presented this work at the [2021 Coq Workshop](https://coq-workshop.gitlab.io/2021/). Here is the [extended abstract](https://coq-workshop.gitlab.io/2021/abstracts/Coq2021-02-01-fol-toolbox.pdf) and the [latest version](https://github.com/dominik-kirst/coq-library-undecidability/tree/fol-library/theories/FOL/Proofmode) for Coq 8.13.*

See the [documentation](https://raw.githubusercontent.com/mark-koch/firstorder-proof-mode/main/documentation/proof-mode.pdf) for a users guide and a description of how the proof mode works.

## Requirements
- [Coq](https://github.com/coq/coq/) 8.12.0 (`coq.8.12.0`)
- [Equations](https://mattam82.github.io/Coq-Equations/) 1.2.3 (`coq-equations.1.2.3+8.12`)

## How to build
Simply run `make`.

## Demo
Have a look at the demo files `DemaPA.v` and `DemoZF.v` where the proof mode is applied to Peano arithmetic and Zermelo-Fraenkel set theory.

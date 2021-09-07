<!---
This file was generated from `meta.yml`, please do not edit manually.
Follow the instructions on https://github.com/coq-community/templates to regenerate.
--->
# Matrix Canonical Forms

[![Docker CI][docker-action-shield]][docker-action-link]
[![Contributing][contributing-shield]][contributing-link]
[![Code of Conduct][conduct-shield]][conduct-link]
[![Zulip][zulip-shield]][zulip-link]

[docker-action-shield]: https://github.com/coq-community/matrix_canonical_forms/workflows/Docker%20CI/badge.svg?branch=master
[docker-action-link]: https://github.com/coq-community/matrix_canonical_forms/actions?query=workflow:"Docker%20CI"

[contributing-shield]: https://img.shields.io/badge/contributions-welcome-%23f7931e.svg
[contributing-link]: https://github.com/coq-community/manifesto/blob/master/CONTRIBUTING.md

[conduct-shield]: https://img.shields.io/badge/%E2%9D%A4-code%20of%20conduct-%23f15a24.svg
[conduct-link]: https://github.com/coq-community/manifesto/blob/master/CODE_OF_CONDUCT.md

[zulip-shield]: https://img.shields.io/badge/chat-on%20zulip-%23c1272d.svg
[zulip-link]: https://coq.zulipchat.com/#narrow/stream/237663-coq-community-devs.20.26.20users



This library builds on Mathematical Components and CoqEAL to provide formal
proofs in Coq about matrices: the existence of Smith normal forms, Jordan
normal forms, etc., converging towards a proof of the Perron-Frobenius theorem.

## Meta

- Author(s):
  - Guillaume Cano (initial)
- Coq-community maintainer(s):
  - Yves Bertot ([**@ybertot**](https://github.com/ybertot))
- License: [MIT License](LICENSE)
- Compatible Coq versions: 8.10 or later
- Additional dependencies:
  - [MathComp ssreflect](https://math-comp.github.io) 1.12
  - [MathComp fingroup](https://math-comp.github.io) 1.12
  - [MathComp algebra](https://math-comp.github.io) 1.12
  - [MathComp real-closed](https://math-comp.github.io) 1.1.2 or later
  - [CoqEAL](https://github.com/coq-community/coqeal) 1.0.5 or later
- Coq namespace: `matrix_canonical_forms`
- Related publication(s):
  - [https://tel.archives-ouvertes.fr/tel-00986283/](Interaction entre algèbre linéaire et analyse en formalisation des mathématiques) 

## Building and installation instructions

The easiest way to install the latest released version of Matrix Canonical Forms
is via [OPAM](https://opam.ocaml.org/doc/Install.html):

```shell
opam repo add coq-released https://coq.inria.fr/opam/released
opam install coq-matrix-canonical-forms
```

To instead build and install manually, do:

``` shell
git clone https://github.com/coq-community/matrix_canonical_forms.git
cd matrix_canonical_forms
make   # or make -j <number-of-cores-on-your-machine> 
make install
```


## Documentation

For more information about the project, see the
[website](https://www-sop.inria.fr/marelle/Guillaume.Cano/).

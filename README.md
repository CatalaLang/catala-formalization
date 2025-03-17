# Artifact for "Scaling Up Mechanized Proof Automation for Small-step Semantics"

This is the companion artifact to the paper "Scaling Up Mechanized Proof
Automation for Small-step Semantics".

This artifact contains the Rocq code described in the paper.


## Detailed File Description

The file `CLAIMS.md` links statements made in the paper with this artifact.

The file `sequences.v` is adapted from previous work by François Pottier, which
was based on work by Xavier Leroy, with a few additions by the authors of this
artifact.

| File Name                                     | Spec     | Proof     | Comments     | Description |
|-----------------------------------------------|----------|-----------|--------------|-------------|
| `theories/common.v`                           | 52       | 82        | 3            | Contains common definitions and utilities used across multiple modules. |
| `theories/tactics.v`                          | 378      | 28        | 100          | Contains custom tactics for automated proof strategies in Rcoq. |
| `theories/sequences.v`                        | 274      | 246       | 26           | Defines operations and properties of sequences of reduction (`star`, `plus` and related lemmas). |
| `theories/miniml/miniml.v`                    | 502      | 676       | 77           | Defines syntax and proofs for mini-ML. |
| `theories/miniml/miniml_ifthenelse.v`         | 775      | 1542      | 234          | Defines syntax and proofs for mini-ML + `if-then-else`. |
| `theories/catala/syntax.v`                    | 521      | 250       | 11           | Defines the syntax of the fragment of $\lambda^\delta$ we are dealing with. |
| `theories/catala/small_step.v`                | 315      | 122       | 11           | Describes the traditional small-step semantics of the language. |
| `theories/catala/continuations.v`             | 442      | 181       | 32           | Describes the continuation-based small-step semantics of the language. |
| `theories/catala/typing.v`                    | 399      | 86        | 34           | Provides the typing rules and their verification for the language. |
| `theories/catala/simulation_cred_to_sred.v`   | 200      | 204       | 14           | Provides a simulation proof from continuation steps to small steps semantic. |
| `theories/catala/simulation_sred_to_cred.v`   | 572      | 556       | 62           | Provides a simulation proof from small steps to continuation steps semantic. |
| `theories/catala/trans.v`                     | 205      | 181       | 26           | Handles the transformation that removes default terms from $\lambda^\delta$ intermediate languages. |
| **Total**                                     | **4635** | **4154**  | **630**      |  |

This table was computed using the `coqwc` utility

## Hardware Dependencies    

Minimal dependencies are required. The entire proof builds under 2 minute on a
recent laptop.


## Building and Installation

To start developing, you first need to install `opam` using your package manager. According to [https://opam.ocaml.org/doc/Install.html], you can run the following commands:

    bash -c "sh <(curl -fsSL https://raw.githubusercontent.com/ocaml/opam/master/shell/install.sh)"
    opam init

Then, you can execute the following commands to install the artifact dependencies (including Rocq):

    opam switch create rocq-catala 4.14.0
    eval $(opam env --switch=rocq-catala --set-switch)
    opam repo add coq-released https://coq.inria.fr/opam/released
    opam repository add rocq-released --all-switches
    opam install . --deps-only


## Step-by-Step Instructions

Once you have installed the dependencies, you can use Dune to build the `Rcoq` development:

    dune build

Then, start your favorite interactive proof interface for `Rcoq`.

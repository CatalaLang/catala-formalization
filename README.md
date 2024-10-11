# Artifact for "Scaling Up Mechanized Proof Automation for Small-step Semantics"

This is the companion artifact to the paper "Scaling Up Mechanized Proof Automation for Small-step Semantics".

This artifact contains the Rocq code described in the paper.


## Detailed File Description

The file `CLAIMS.md` links statements made in the paper with this artifact.

The file `sequences.v` is adapted from previous work by François Pottier, which was based on work by Xavier Leroy, with a few additions by the authors of this artifact.

| File Name                          | Spec     | Proof     | Comments     | Description |
|------------------------------------|----------|-----------|--------------|-------------|
| `common.v`                         | 48       | 70        | 3            | Contains common definitions and utilities used across multiple modules. |
| `tactics.v`                        | 224      | 3         | 69           | Contains custom tactics for automated proof strategies in Rcoq. |
| `sequences.v`                      | 242      | 220       | 25           | Defines operations and properties of sequences of reduction (`star`, `plus` and related lemmas). |
| `miniml/miniml.v`                  | 650      | 763       | 70           | Defines syntax and proofs for mini-ML. |
| `miniml/miniml_ifthenelse.v`       | 393      | 137       | 40           | Defines syntax and proofs for mini-ML + `if-then-else`. |
| `catala/syntax.v`                  | 521      | 250       | 9            | Defines the syntax of the fragment of $\lambda^\delta$ we are dealing with. |
| `catala/small_step.v`              | 315      | 122       | 11           | Describes the traditional small-step semantics of the language. |
| `catala/continuations.v`           | 452      | 181       | 35           | Describes the continuation-based small-step semantics of the language. |
| `catala/typing.v`                  | 394      | 90        | 35           | Provides the typing rules and their verification for the language. |
| `catala/simulation_cred_to_sred.v` | 213      | 219       | 15           | Provides a simulation proof from continuation steps to small steps semantic. |
| `catala/simulation_sred_to_cred.v` | 606      | 609       | 45           | Provides a simulation proof from small steps to continuation steps semantic. |
| `catala/trans.v`                   | 203      | 182       | 26           | Handles the transformation that removes default terms from $\lambda^\delta$ intermediate languages. |
| **Total**                          | **4261** | **2846**  | **383**      |  |

This table was computed using the `coqwc` utility

## Hardware Dependencies    

Minimal dependencies are required. The entire proof builds in 1 minute on a recent laptop.


## Building and Installation

To start developing, you first need to install `opam` using your package manager. According to [https://opam.ocaml.org/doc/Install.html], you can run the following commands:

    bash -c "sh <(curl -fsSL https://raw.githubusercontent.com/ocaml/opam/master/shell/install.sh)"
    opam init

Then, you can execute the following commands to install the artifact dependencies (including Rocq):

    opam switch create rocq-catala 4.14.0
    opam repo add coq-released https://coq.inria.fr/opam/released
    eval $(opam env --switch=rocq-catala --set-switch)
    opam repository add rocq-released --all-switches
    opam install . --deps-only


## Step-by-Step Instructions

Once you have installed the dependencies, you can use Dune to build the `Rcoq` development:

    dune build

Then, start your favorite interactive proof interface for `Rcoq`.

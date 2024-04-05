# Artifact for "Should You Use Continuation Semantics for Your λ-calculus? Application to Catala’s Verified Compilation"

This is the companion artifact to the paper "Should You Use Continuation Semantics for Your λ-calculus? Application to Catala’s Verified Compilation".

This artifact contains only the Rocq code described in the paper. We plan to include the transformation implementation in the official Catala compiler upon submission to the OOPSLA Artifacts track.


## Detailed File Description

The file `CLAIMS.md` links statements made in the paper with this artifact.

The file `sequences.v` is adapted from previous work by François Pottier, which was based on work by Xavier Leroy, with a few additions by the authors of this artifact.

| File Name                    | Spec | Proof | Comments | Description |
|------------------------------|------|-------|----------|-------------|
| common.v                     | 47   | 65    | 3        | Contains common definitions and utilities used across multiple modules. |
| sequences.v                  | 242  | 220   | 25       | Defines operations and properties of sequences of reduction (`star`). |
| tactics.v                    | 224  | 3     | 70       | Contains custom tactics for automated proof strategies in Rcoq. |
| syntax.v                     | 531  | 251   | 10       | Defines the syntax of the fragment of $\lambda^\delta$ we are dealing with. |
| small_step.v                 | 315  | 122   | 11       | Describes the small-step operational semantics of the language. |
| continuations.v              | 452  | 189   | 86       | Describes the continuation steps semantics of the language. |
| typing.v                     | 394  | 91    | 39       | Provides the typing rules and their verification for the language. |
| simulation_cred_to_sred.v    | 213  | 219   | 14       | Provides a simulation proof from continuation steps to small steps semantic. |
| simulation_sred_to_cred.v    | 606  | 609   | 41       | Provides a simulation proof from small steps to continuation steps semantic. |
| trans.v                      | 205  | 182   | 26       | Handles the transformation that removes default terms from $\lambda^\delta$ intermediate languages. |
| **Total**                    | **3677** | **2503**  | **372**      |  |

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

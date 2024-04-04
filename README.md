## File detailed description.

The file `sequences.v` is adapted from previous work by François Pottier itself taken on previous work by Xavier Leroy with additions by the authors of this artifact. 

| File Name                   | Spec | Proof | Comments | Description |
|-----------------------------|------|-------|----------|-------------|
| common.v                    | 68   | 117   | 3        | Contains common definitions and utilities used across multiple modules. |
| sequences.v                 | 238  | 223   | 19       | Defines operations and properties of sequences of reduction (`star`). |
| tactics.v                   | 226  | 3     | 69       | Contains custom tactics for automated proof strategies in Rcoq. |
| syntax.v                    | 610  | 303   | 13       | Defines the syntax of the fragment of $\lambda^\delta$ we are dealing with. |
| small_step.v                | 330  | 145   | 12       | Describes the small-step operational semantics of the language. |
| continuations.v             | 434  | 170   | 82       | Describes the continuation steps semantics of the language. |
| typing.v                    | 500  | 107   | 72       | Provides the typing rules and their verification for the language. |
| simulation_cred_to_sred.v   | 216  | 250   | 16       | Provides a simulation proof from continuation steps to small steps semantic. |
| simulation_sred_to_cred.v   | 827  | 814   | 54       | Provides a simulation proof from small steps to continuation steps semantic. |
| trans.v                     | 194  | 162   | 17       | Handles the transformation between the dcalc to lcalc intermediate languages. |
| total                       | 3897 | 2624  | 539      |  |


## Building and installation


To start developing, you first need to install opam. Then you can run the following commands:

    opam switch create rcoq-catala 4.14.0
    opam repo add coq-released https://coq.inria.fr/opam/released
    eval $(opam env --switch=rcoq-catala --set-switch)
    opam repository add rcoq-released --all-switches
    opam install . --deps-only

Once it is done, you can use dune to build the Rcoq development

    dune build

And start your favorite interactive proof interface for Rcoq.


## Limitations and disclaimer

**REMOVED FOR ANONYMITY**.

In this file, we describe the various claims of the paper.

The entire development is axiom-free except for two aspects: autosubst relies on Functional Extensionality, and the submodule `correctness` in the `theories/catala/typing.v` file contains a hypothesis, `measure`, which decreases when terms are executed. We assume such a measure exists since simply typed lambda calculus terminates, but we do not prove it. This assumption is only used in these specific lemmas.

## Section 2

The syntax, semantics, and proof of the $\lambda$-calculus augmented with `if-then-else` are in the `miniml/miniml_ifthenelse.v` file.

* The syntax is defined using the `term` and `value` inductives. We use de Bruijn indices.

## Section 2.1
* The inductive rules for the traditional small-step semantics are defined in the `sred` inductive.
* The reduction rules for the contextual reductions are not defined in our development.

## Section 2.2
* The syntax for the continuation-based small-step semantics is defined in the `cont`, `result`, and `state` inductives. Environments are represented using lists of values.
* The reduction rules are defined in the `cred` inductive.
* The example reduction at the end of Section 2 is presented in `example_of_reduction`.

## Section 3.1

* Theorem 1 appears in multiple files. In the small-scale development, it is in the file `miniml/miniml.v` as the `simulation_sred_cred` theorem (without `if-then-else`). In the Catala development, it is in the file `catala/simulation_sred_to_cred.v` as the lemma `simulation_sred_cred`.
* The contextual reduction lemma (Lemma 1) is named `cred_append_stack` and is found in both `miniml/miniml.v` and `catala/continuations.v`.

## Section 3.2

* The proof of determinism is present in both `miniml/miniml.v` and `miniml/miniml_ifthenelse.v` to compare both versions. The lemma is named `cred_determinism` for the continuation-based small-step reduction and `sred_determinism` for the traditional small-step reduction. Similar theorems are present for `catala` in the `catala/continuations.v` and `catala/small_step.v` files. Note that the proof in the continuation case is identical to that for MiniML!
* The typing rules for MiniML are defined in `miniml/miniml.v` and `miniml/miniml_ifthenelse.v`. The inductive names are `type` for the type syntax, `jt_term`, `jt_value`, `jt_result`, `jt_cont`, `jt_conts`, and `jt_state`.
* For recursive inversion, we use the `inv_jt` tactic, which itself relies on the `smart_inversion` Ltac2 tactic defined in the `tactics.v` file.
* The progress theorem is `progress_cont` and `progress_trad` for continuation-based and traditional semantics. In both theorems, you can check that the proofs correspond to the prose in the paper.

## Section 4

* The syntax of types is in the `catala/typing.v` file as the `type` inductive.
* The syntax of values, terms, and defaults is in the `syntax` file as the `term` and `value` inductives.

## Section 4.1
* The selected rules of Figure 2 are present in the `sred` inductive, defined in the `catala/small_step.v` file.
* The translation in Figure 3 is defined in the `catala/trans.v` file.
* The proof of Theorem 1 for Catala is the proof of the `simulation_sred_cred_base` theorem in the `theories/simulation_sred_to_cred.v` file. We omit the lifting back to `simulation_sred_cred` in the paper as well as the equivalence relation that express that two terms are quivalent if we inline the values present in the closure. The induction on the continuation is marked with `(* INDUCTION ON KAPPA *)`. The induction step starts at `(* INDUCTION STEP *)`. The induction on the small-step reduction is marked with `(* INDUCTION SRED *)`. The hypothesis saturation steps are marked with `(* HYPOTHESIS SATURATION STEP 1 *)` and `(* HYPOTHESIS SATURATION STEP 2 *)`. The Ltac interpreter is done at `(* INTERPRETER *)`. The final simulation proof is marked with `(* FINISH *)`.
* The `(* INTERPRETER *)` marker provides more advanced examples of an interpreter (compatible with `plus`, `star`, and normal reduction). A more basic example is available in the `miniml/miniml_ifthenelse.v` file as the `example_of_reduction` example.
* The "smart-inversion" tactic is defined for specific inductives, such as in the `catala/typing.v` file with the `sinv_inv` and `sinv_jt` tactics. These tactics use the `smart_inversion` Ltac2 tactic defined in the `tactics.v` file.

## Section 4.2

* The simulation from traditional to continuation-based small-step semantics is in the file `catala/simulation_sred_to_cred.v`.
* The simulation from continuation-based to traditional small-step semantics is in the file `catala/simulation_cred_to_sred.v`.

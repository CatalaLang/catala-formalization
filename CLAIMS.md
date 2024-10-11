In this file, we describe the different claims of the paper.

The whole development is axiom-free except for two things: autosubst relies on Functional Extensionality, and the submodule `correctness` of the `theories/catala/typing.v` file contains a hypothesis `measure` that decreases when executing terms. We suppose such a measure exists as simply typed lambda calculus terminates but do not prove it. We don't use this fact anywhere but in those lemmas or in our paper.


## Section 2

The syntax, semantics, and proof of the $\lambda$-calculus augemented with `if-then-else` is in the `miniml/miniml_ifthenelse.v` file.

* The syntax is defined using `term` and `value` inductives. We use de Bruijn indices.

## Section 2.1
* The inductives rules for the traditionnal small-step semantics is defined in the `sred` inductive.
* The reduction rules for the contextual reductions are not defined in our developement.

## Section 2.2
* The syntax for the continuation-based small-step semantics is defined in the `cont`, `result` and `state` inductives. Environement are represented using list of values.
* The reduction rules are defined in the `cred` inductive.
* The sampled reduction at the end of section two is presented in `example_of_reduction`.

## Section 3.1

* Theorem 1 is present in multiple files. In the small-scale developement in the file `miniml/miniml.v` as the `simulation_sred_cred` theorem (without `if-then-else`). And in the Catala developement in the file `catala/simulation_sred_to_cred.v` as the lemma `simulation_sred_cred`.
* The contextual reduction lemma (lemma 1) is named `cred_append_stack` and is present in both `miniml/miniml.v` and `catala/continuations.v`.

## Section 3.2

* The proof of determinism is present in `miniml/miniml.v` and `miniml/miniml_ifthenelse.v` to compare both versions. The name of the lemma is `cred_determinism` for the continuation-based small-step reduction determinism and `sred_determinism` for the traditional small-step reduction. Similar theorems are present for `catala` in the `catala/continuations.v` and `catala/smallstep.v` files. Note that the proof in the continuation case is the same as for miniml!
* Typing rules for miniml are defined in the `miniml/miniml.v` and  `miniml/miniml_ifthenelse.v`. the inductive names are `type` for the type syntax, `jt_term`, `jt_value`, `jt_result`, `jt_cont`, `jt_conts`, and `jt_state`.
* For the recursive inversion we use the `inv_jt` tactic that itself relies on the `smart_inversion` ltac2 tactic defined in the `tactics.v` file.
* The progress theorem is `progress_cont` and `progress_trad` for continuation-based and traditional semantics. In both theorem, you can check that the proof correspond to the prose in the paper.

## Section 4

* The syntax of types is in the `catala/typing.v` file as the `type` inductive.
* The syntax of value, terms and defaults in in the `syntax` file as the `term` and `value` inductives.

## Section 4.1
* The selected rules of figure 2 are present in the `sred` inductive defined in the `catala/small_step.v` file.
* The translation in figure 3 are is defined in the `catala/trans.v` file.
* The proof of theorem 1 for catala is the proof of the `simulation_sred_cred_base` theorem in the `theories/simulation_sred_to_cred.v` file. We omit in the paper the lifting back to `simulation_sred_cred`. The induction on the continuation is at the marker `(* INDUCTION ON KAPPA *)`. The induction step starts at the marker `(* INDUCTION STEP *)`. The induction on the small-step reduction is done at the marker `(* INDUCTION SRED *)`. The hypothesis saturation is done at the markers `(* HYPOTHESIS SATURATION STEP 1 *)` and `(* HYPOTHESIS SATURATION STEP 2 *)`. The Ltac interpreter is done at the marker `(* INTERPRETOR *)`. The final simulation proof is done at the marker `(* FINISH *)`.
* The `(* INTERPRETOR *)` marker provide more advanced examples of interpreter (compatible with `plus`, `star`, and normal reduction). But more basic example is available for example in the `miniml/miniml_ifthenelse.v` file as the `example_of_reduction` example.
* The "smart-inversion" tactic is defined for specific inductives such as in the `catala/typing.v` file as the `sinv_inv` and `sinv_jt` tactics. These tactics uses the `smart_inversion` ltac2 tactic defined in the `tactics.v` file.

## Section 4.2

* The traditional to continuation-based small step semantic simulation is in the file `catala/simulation_sred_to_cred.v`
* The continuation-based to traditional small step semantic simulation is in the file `catala/simulation_cred_to_sred.v`

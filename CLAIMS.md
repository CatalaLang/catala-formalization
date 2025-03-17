In this file, we describe the various claims of the paper.

The entire development is axiom-free except for two aspects: autosubst relies on Functional Extensionality, and the submodule `correctness` in the `theories/catala/typing.v` file contains a hypothesis, `measure`, which decreases when terms are executed. We assume such a measure exists since simply typed lambda calculus terminates, but we do not prove it. This assumption is only used in these specific lemmas.

The file `miniml/miniml_ifthenelse.v` contains multiple "admit", corresponding to cases that are not completed. This is because the theorem is wrong. However, other cases of the proof have been used in the other version of the proof. The theorems themself are not admitted, but Aborted.

## Section 2

The syntax, semantics, and proof of the $\lambda$-calculus augmented with `if-then-else` are in the `miniml/miniml_ifthenelse.v` file.

* The syntax is defined using the `term` and `value` inductives. We use de Bruijn indices.

* A difference from the paper is that in the files `miniml/miniml_ifthenelse.v` and `catala/syntax.v`, values also includes closures `Closure t sigma`. This is technical debt from our developement but does not change the claims of our papers, as the `miniml/miniml.v` is up to date with the syntax described in the paper.

## Section 2.1
* The inductive rules for the traditional small-step semantics are defined in the `sred` inductive. Similarly to the syntax, files `miniml/miniml_ifthenelse.v` and `catala/syntax.v` still have an explicit rule `sred_lam` that transfrom a lambda into a closure.
* The reduction rules for the contextual reductions are not defined in our development.

## Section 2.2
* The syntax for the continuation-based small-step semantics is defined in the `cont`, `result`, and `state` inductives. Environments are represented using lists of values.
* The reduction rules are defined in the `cred` of the file `miniml/miniml_ifthenelse.v`.

## Section 3.1.1

* The example of inversion with cred is the example `inversion_with_cred` of the file `miniml/miniml_ifthenelse.v`.
* The example of inversion with sred is the example `inversion_with_sred` of the file `miniml/miniml_ifthenelse.v`.
* Forcing syntactic separation between values and terms is done in our developement. However, as stated above, the `miniml/miniml_ifthenelse.v` and `catala/syntax.v` uses closures, while `miniml/miniml.v` directly use `Lam`. In the first two cases, we observe that making this syntactic distinction simplify the proof. But in the third case, this adds boilerplate code, because autosubst does not seems to handle mutual induction correctly. This adds ~200 lines of spec and proof.
* The empirical check of the uniqueness of the inversion is (partially) done by checking the determinism proof. The determinism proof is in the `miniml/miniml_ifthenelse.v` file under the name `cred_deterministic` `sred_deterministic`. For the first one, we observe one case, while in the second we observe 13 cases.

## Section 3.1.2

* The examples of constructor on sred are the examples `constructor_sred_ok` and
`constructor_sred_fail` of the file `miniml/miniml_ifthenelse.v`.
* The examples of constuctor on cred are the examples `constructor_cred_explicit` and
`constructor_cred_explicit_no_evar`of the file `miniml/miniml_ifthenelse.v`.

# Section 3.1.3
* The non-recursiveness of the `cred` invariant can be checked by doing `Check cred_ind` in the file `miniml/miniml_ifthenelse.v`.

* Theorem 1 appear in multiple files with differnt versions of the simulation diagram. In the paper, we used the "plus" variant of the simulation diagram. In the Catala development, it is in the file `catala/simulation_sred_to_cred.v` as the lemma `simulation_sred_cred` uses the plus variant. It is in the file `miniml/miniml.v`, theorem 1 is defined as the `simulation_sred_cred` theorem and uses the star version of the theorem. Because of the complexity of the meta-interpreter implementation when using plus instead of star, we prefered to show the star version in `miniml/miniml.v`.

* The contextual reduction lemma (Lemma 1) is named `cred_append_stack` and is found in the `miniml/miniml.v`, `miniml/miniml_ifthenelse.v` and `catala/continuations.v` files.

## Section 3.2.2
* The proof of determinism is present in both `miniml/miniml.v` and `miniml/miniml_ifthenelse.v` to compare both versions. The lemma is named `cred_determinism` for the continuation-based small-step reduction and `sred_determinism` for the traditional small-step reduction. Similar theorems are present for `catala` in the `catala/continuations.v` and `catala/small_step.v` files. Note that the proof in the continuation case is identical to that for MiniML!

## Section 3.2.3
* The typing rules for MiniML are defined in `miniml/miniml.v` and `miniml/miniml_ifthenelse.v`. The inductive names are `type` for the type syntax, `jt_term`, `jt_value`, `jt_result`, `jt_cont`, `jt_conts`, and `jt_state`.
* For recursive inversion, we use the `invert_jt` tactic, which itself relies on the `smart_inversion` Ltac2 tactic defined in the `tactics.v` file.
* The progress theorem is `progress_cont` and `progress_trad` for continuation-based and traditional semantics. In both theorems, you can check that the proofs correspond to the prose in the paper.

## Section 3.2.4

The proofs of the correctness of the peep-hole optimization are all in the `miniml/miniml_ifthenelse.v` file (from rougly line 1000 to the end). We kept failing proof for comparison purposes. The different correctness lemmas are named according to the following table.

| **Semantic** | **Proof Strategy**    | **First Diagram: 1-step simulation** | **Second Diagram: n-steps simulation** |
|--------------|-----------------------|--------------------------------------|----------------------------------------|
| **sred**     | Induction on sred     | correctness_sred_ind_red_1step       | correctness_sred_ind_red_nstep         |
|              | Induction on inv      | -                                    | correctness_sred_ind_inv_nstep         |
| **cred**     | Induction on cred     | correctness_cred_ind_red_1step       | correctness_cred_ind_red_nstep         |
|              | Induction on inv      | correctness_cred_ind_inv_1step       | correctness_cred_ind_inv_nstep         |
|              | WF induction on stack | correctness_cred_ind_wf_1step        | correctness_cred_ind_wf_nstep          |

* Lemma 3 is named `refined_progress`.

## Section 4

* The syntax of types is in the `catala/typing.v` file as the `type` inductive.
* The syntax of values, terms, and defaults is in the `catala/syntax.v` file as the `term` and `value` inductives.

## Section 4.1
* The reduction rules for -> are defined in the `sred` inductive, defined in the `catala/small_step.v` file. As previously mentionned, the `sred` inductive includes a rule `sred_lam` not described in the paper that does not change the claims of our work.
* The novel compilation pass is defined in the `catala/trans.v` file, along with its correctness theorem.
* The proof of Theorem 1 for Catala is the proof of the `simulation_sred_cred_base` theorem in the `theories/simulation_sred_to_cred.v` file. We omit the lifting back to `simulation_sred_cred` in the paper as well as the equivalence relation that express that two terms are quivalent if we inline the values present in the closure. The induction on the continuation is marked with `(* INDUCTION ON KAPPA *)`. The induction step starts at `(* INDUCTION STEP *)`. The induction on the small-step reduction is marked with `(* INDUCTION SRED *)`. The hypothesis saturation steps are marked with `(* HYPOTHESIS SATURATION STEP 1 *)` and `(* HYPOTHESIS SATURATION STEP 2 *)`. The Ltac interpreter is done at `(* INTERPRETER *)`. The final simulation proof is marked with `(* FINISH *)`.
* The `(* INTERPRETER *)` marker provides more advanced examples of an interpreter (compatible with `plus`, `star`, and normal reduction). A more basic example is available in the `miniml/miniml_ifthenelse.v` file as the `example_of_reduction` example.
* The "smart-inversion" tactic is defined for specific inductives, such as in the `catala/typing.v` file with the `sinv_inv` and `sinv_jt` tactics. These tactics use the `smart_inversion` Ltac2 tactic defined in the `tactics.v` file.

## Section 4.2

* The simulation from traditional to continuation-based small-step semantics is in the file `catala/simulation_sred_to_cred.v`.
* The simulation from continuation-based to traditional small-step semantics is in the file `catala/simulation_cred_to_sred.v`.

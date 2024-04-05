In this file, we describe the different claims of the paper.

The whole development is axiom-free except for two things: autosubst relies on Functional Extensionality, and the submodule `correctness` of the `theories/typing.v` file contains a hypothesis `measure` that decreases when executing terms. We suppose such a measure exists as simply typed lambda calculus terminates but do not prove it. We don't use this fact anywhere but in those lemmas or in our paper.

## Section 3.1

* The syntax of the $\lambda^\delta$ language is defined in the `term` and `value` inductives of the `theories/syntax` file.
* The typing of the $\lambda^\delta$ language is defined in `theories/typing.v`. The inductive `type` describes the syntax of types in figure 1, while `jt_term` describes the typing rules in figure 2. The preservation and progress mentioned are only proved using the continuation-based semantics in the `preservation` and the `progress` theorems. More inductives `jt_cont`, `jt_conts`, `jt_result`, and `jt_state` are needed to lift the typing judgment to states. The lifting operation is similar to what is described in section 4.1 for the translation and is not detailed in the paper.
* Well-formedness is defined as mutual inductive statements `inv_base` for $\text{well-formed}_true$ and `no_immediate_default` for $\text{well-formed}_false$.

## Section 3.2

* Small-step semantics is defined in the `theories/small-steps.v` file. The reduction rule is defined in the `sred` inductive. The new rules are `sred_lam`, `sred_beta`, `sred_default_E_one_empty`, and `sred_default_E_zero_empty`.
* Continuation-based semantics is defined in the `theories/continuation.v` file. The syntax is defined in the `is_hole`, `cont`, `result`, and `state` definitions. The reduction in figure 4 itself is defined as an inductive `cred`. Recall that we use De Bruijn indices in the development.
* Term rebuilding is done separately in both `theories/simulation_cred_to_sred.v` and `theories/simulation_sred_to_cred.v` files as the functions called `apply_state`, `apply_conts`, `apply_cont`, and for the default term, `apply_CDefault`.
* The reduction sequence 1-8 is the example `example1` of the `theories/continuations.v` file. The reduction sequence 9-19 is the example `example2` of the `theories/continuation.v` file.
* The `Hole`/`NoHole` markers are defined in `is_hole`. The invariant indicating no `hole` can appear inside the continuation except at the top when in continuation mode is defined in the `inv_conts_no_hole` and `inv_state` invariants.

## Section 3.3

* Lemma 3.1 is the theorem `star_cred_append_stack` of `theories/continuations.v`. Its converse is in lemma `cred_stack_sub` of the same file.
* Inductives with `List.Forall` include the `jt_term` of `theories/typing.v`, `inv_state` of `theories/continuation.v`, and `sim_term` of `theories/syntax.v`. We do not prove the induction principle for the first two but show one for the last: theorems `sim_term_value_ind'` and `sim_value_term_ind'` of `theories/syntax.v`.
* Equivalence theorems are in `theories/simulation_cred_to_sred.v` and `theories/simulation_sred_to_cred.v`: theorem 3.3 is `simulation_cred_sred` and theorem 3.2 is `simulation_sred_cred`. We do not include the counterexamples in the development.

## Section 4.1

* The translation $[[t]]$ of figure 5 is defined in the `theories/trans.v`. The translation of terms is defined as `trans`. The translation of types is defined as `trans_ty`. The lifting of `trans` to states in figure 7 is done in the same file as `trans_conts`, `trans_return`, and `trans_state`.
* Theorem 4.1 is the `correction_small_steps` theorem of `theories/trans.v`.
* Theorem 4.2 is the `correction_continuation_steps` theorem of `theories/trans.v`.

## Section 4.2

* Lemmas 4.3 and 4.4 are `trans_te_renaming` and `trans_te_substitution` in the `theories/trans.v` file.

Counting the lines of code was done by removing comments and empty lines inside code.

In 4.2.3, we count the number of lines of code of:
* for the small-step specification, the `sred` inductive in the `small_step.v` file.
* for the continuation-based specification, the `cred`, `state`, `cont`, `result`, and `is_hole` inductives in the `theories/continuations.v` file.

To extract dependencies of lemmas, we use the DPD Rcoq library that dumps the dependencies between all lemmas in the Rcoq development (`export/export.v` file). We then conduct an analysis of the result in the `doc/dpd-reader.ipynb` file. This Python program is only available for completeness, is not mentioned in the paper, and is not part of the artifact.

## Section 5.1

* During the proof of `simulation_sred_cred_base`, we can see the number of proof goals reaches 2760 cases at the `(* HYPOTHESIS SATURATION STEP 1 *)` marker. It then reduces to 344 at the `(* HYPOTHESIS SATURATION STEP 2 *)` marker, and then to 255 at the `(* INTERPRETOR *)` marker (not included in the paper).
* The `star_step_prop` is in the `theories/sequences.v` file. Similar lemmas include for forward simulation diagrams: `star_refl_prop`, `star_step_prop`, `star_trans_prop`, `plus_star_trans_prop`, `star_plus_trans_prop`, `plus_step_prop`. They are used in both `simulation_cred_sred_base` and `simulation_sred_cred_base`. We indicate a marker `(* PROOF AUTOMATION *)` where we use them.
* The "smart inversion" is implemented for typing judgments and invariants in the `sinv_jt` and `sinv_inv` tactics in the `theories/typing.v` file. The helper tactic `smart_inversion` is found in the `theories/tactics.v` file.
* Our terms `term` in `theories/syntax.v` make use of mutually recursive inductive types, list containers, and require simplification (with autosubst).

## Section 5.2

* The lines of code to compare the equivalence between `sred` and `cred` were obtained using `coqwc`.
* The proof of theorem 3.2 is the proof of the `simulation_sred_cred_base` theorem in the `theories/simulation_sred_to_cred.v` file. We omit in the paper the lifting back to `simulation_sred_cred`. The induction on the continuation is at the marker `(* INDUCTION ON KAPPA *)`. The induction step starts at the marker `(* INDUCTION STEP *)`. The induction on the small-step reduction is done at the marker `(* INDUCTION SRED *)`. The hypothesis saturation is done at the markers `(* HYPOTHESIS SATURATION STEP 1 *)` and `(* HYPOTHESIS SATURATION STEP 2 *)`. The Ltac interpreter is done at the marker `(* INTERPRETOR *)`. The final simulation proof is done at the marker `(* FINISH *)`.

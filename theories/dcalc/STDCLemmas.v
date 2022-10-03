Require Import MyTactics.
Require Import DCSyntax.
Require Import DCValues.
Require Import DCReduction.
Require Import STDCDefinition.

Require Import LibTactics.

Require Import MyList.

(*|
---------------------------
Renamings of term variables
---------------------------
|*)

(*|

The typing judgement is preserved by a renaming `xi` that maps
term variables to term variables. Note that `xi` need not be
injective.

|*)

Lemma jt_te_renaming:
  forall Gamma t U,
  jt Gamma t U ->
  forall Gamma' xi,
  Gamma = xi >>> Gamma' ->
  jt Gamma' t.[ren xi] U.
Proof.
(*
  (* A detailed proof, where every case is dealt with explicitly: *)
  induction 1; intros; subst.
  (* JTVar *)
  { asimpl. econstructor. eauto. }
  (* JTLam *)
  { asimpl. econstructor. eapply IHjt. autosubst. }
  (* JTApp *)
  { asimpl. econstructor. eauto. eauto. }
Restart.*)
  (* A shorter script, where all cases are dealt with uniformly: *)
  induction 1 using jt_ind'; intros; subst; asimpl;
  econstructor; eauto with autosubst.
  - induction H; econstructor.
    * inverts H0.
      now eapply H6.
    * inverts H0.
      eapply IHForall.
      eauto.
Qed.

(*|

As a corollary, `jt` is preserved by the renaming `(+1)`.

|*)

Lemma jt_te_renaming_0:
  forall Gamma t T U,
  jt Gamma t U ->
  jt (T .: Gamma) (lift 1 t) U.
Proof.
  intros. eapply jt_te_renaming. eauto. autosubst.
Qed.

(*|
-----------------------------------------
Substitutions of terms for term variables
-----------------------------------------
|*)

(*|

The typing judgement is extended to substitutions of terms for term
variables.

With respect to a type environment `Gamma`, a substitution `sigma` has
type `Delta` if and only if, for every variable `x`, the term `sigma
x` has type `Delta x`.

This auxiliary judgement encourages us to think of terms of *total*
substitutions, where *every* variable is replaced by a term. This
concept turns out to be easier to understand and manipulate,
especially during proofs by induction. Of course one always later
consider the special case of a substitution that seems to affect just
one variable, say variable 0. (In reality, such a substitution affects
all variables, as the variables other than 0 are renumbered.)

|*)

Definition js Gamma sigma Delta :=
  forall x : var,
  jt Gamma (sigma x) (Delta x).

(*|

The following are basic lemmas about `js`.

The identity substitution has type `Gamma` in environment `Gamma`.

|*)

Lemma js_ids:
  forall Gamma,
  js Gamma ids Gamma.
Proof.
  unfold js. eauto with jt.
Qed.

(*|

The typing judgement `js` behaves like an infinite list of typing judgements
`jt`. So, one can prepend one more `jt` judgement in front of it.

|*)

Lemma js_cons:
  forall Gamma t sigma T Delta,
  jt Gamma t T ->
  js Gamma sigma Delta ->
  js Gamma (t .: sigma) (T .: Delta).
Proof.
  intros. intros [|x]; asimpl; eauto.
Qed.

(*|

The typing judgement `js` is preserved by the introduction of a new term
variable. That is, a typing judgement `js` can be pushed under a
lambda-abstraction.

|*)

Lemma js_up:
  forall Gamma sigma Delta T,
  js Gamma sigma Delta ->
  js (T .: Gamma) (up sigma) (T .: Delta).
Proof.
  intros. eapply js_cons.
  { eauto with jt. }
  { intro x. asimpl. eauto using jt_te_renaming_0. }
Qed.

(*|

The typing judgement is preserved by a well-typed substitution `sigma`
of (all) term variables to terms.

|*)


Require Import MyList.

Lemma jt_te_substitution:
  forall Delta t U,
  jt Delta t U ->
  forall Gamma sigma,
  js Gamma sigma Delta ->
  jt Gamma t.[sigma] U.
Proof.
  (* A short script, where all cases are dealt with in the same way: *)
  induction 1 using jt_ind'; intros; subst; asimpl; eauto using js_up with jt.
  * econstructor; eauto.
    induction H0; inverts H.
    - econstructor.
    - subst; asimpl; eauto.
Qed.

(*|

As a corollary, the typing judgement is preserved by a well-typed
substitution of one term for one variable, namely variable 0.

This property is exploited in the proof of subject reduction, in the
case of beta-reduction.

|*)

Lemma jt_te_substitution_0:
  forall Gamma t1 t2 T U,
  jt (T .: Gamma) t1 U ->
  jt Gamma t2 T ->
  jt Gamma t1.[t2/] U.
Proof.
(*
  (* One can do the proof step by step as follows: *)
  intros. eapply jt_te_substitution.
  { eauto. }
  { eapply js_cons.
    { eauto. }
    { eapply js_ids. } }
  (* Of course one can also let Coq find the proof by itself: *)
  Restart.*) eauto using jt_te_substitution, js_ids, js_cons.
Qed.

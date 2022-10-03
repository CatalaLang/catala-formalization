Require Import MyTactics.
Require Import DCSyntax.
Require Import DCValues.
Require Import DCReduction.
Require Import STDCDefinition.
Require Import STDCLemmas.

Require Import LibTactics.
Require Import DCValuesRes.
Require Import DCErrors.
Require Import MySequences.
(*|

This is a failed attempt to prove the lemma `jt_te_substitution_0` in
a direct way, without introducing the auxiliary judgement `js`. See
STLCLemmas for a valid proof.

|*)

Goal (* jt_te_substitution_0 *)
  forall Delta t1 U,
  jt Delta t1 U ->
  forall Gamma t2 T,
  Delta = T .: Gamma ->
  jt Gamma t2 T ->
  jt Gamma t1.[t2/] U.
Proof.
  (* Let us attempt to naively prove this statement by induction. *)
Abort.

(*|

The subject reduction theorem, also known as type preservation:
the typing judgement is preserved by one step of reduction.

This is proved here for `cbv`, but could be proved for other notions
of reduction, such as `cbn`, or strong reduction.

|*)

Lemma jt_preservation:
  forall Gamma t T,
  jt Gamma t T ->
  forall t',
  cbv t t' ->
  jt Gamma t' T.
Proof.
  induction 1 using jt_ind'; intros; subst; invert_cbv; try eauto with jt.
  { pick_jt (Lam t) invert. eauto using jt_te_substitution_0. }
  { eapply List.Forall_elt in H; eauto. }
  { econstructor; try eassumption.
    eapply List.Forall_app; split; try econstructor;
    eapply List.Forall_app in H as [Hts1 Hts2];
    inverts Hts2; try eauto.
    eapply List.Forall_elt in H0.
    eauto.
  }
Qed.

(*|

An inversion lemma: if a closed value admits a function type `TyFun T1 T2`,
then it must be a lambda-abstraction.

|*)

Lemma invert_jt_TyFun:
  forall Gamma t T1 T2,
  jt Gamma t (TyFun T1 T2) ->
  closed t ->
  is_value t ->
  (exists t', t = Lam t') \/ is_error t.
Proof.
  induction t; intros; inverts H; subst; try eauto; tryfalse.
  * false; eauto with closed.
Qed.

Lemma invert_jt_TyBool:
  forall Gamma t,
  jt Gamma t TyBool ->
  closed t ->
  is_value_res t ->
  (exists b, t = Const b) \/ is_error t.
Proof.
  induction t; intros; inverts H; try eauto; tryfalse.
Qed.

(*|

The progress theorem: a closed, well-typed term
must either be able to make one step of reduction
or be a value.

|*)

Lemma jt_progress:
  forall Gamma t T,
  jt Gamma t T ->
  closed t ->
  (exists t', cbv t t')
  \/ is_value_res t.
Ltac use_ih ih :=
  destruct ih; [ eauto with closed | unpack; eauto with red |  ].
Proof.
  induction 1 using jt_ind'; intros; subst;
  (* all the cases where it is a value *)
  try solve [right; eauto with is_value_res];
  (* all the other cases *)
  left.
  { false; eauto with closed. }
  { use_ih IHjt1.
    use_ih IHjt2; forward invert_jt_TyFun; try eauto with closed;
    destruct H4 as [[t'' Ht''] | Herr]; subst; try obvious.
    { admit. (* need reduction of error inside context for cbv *) }
  }
  {
    induction ts.
    * use_ih IHjt1.
      forward invert_jt_TyBool.
      { eauto with closed. }
      { destruct H5; unpack; subst.
        * case b; obvious.
        * admit. (* need reduction of error inside context for cbv *) }
    * rename a into ti.
      inverts H0; inverts H.
      use_ih H6.
      use_ih IHjt1.
      admit.
      admit.
      admit.
  }
Abort.

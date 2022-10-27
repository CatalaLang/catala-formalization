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
  is_value_res t ->
  (exists t', t = Lam t') \/ is_error t.
Proof.
  induction t; intros; inverts H; subst; try eauto; tryfalse.
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

Tactic Notation "check" "[" uconstr_list(hs) "|-" uconstr(g) "]" :=
  match goal with
  | [ |- g ] => idtac
  | _ => fail
  end.

Ltac look t := induction t; simpl in *; tryfalse; eauto.


Lemma Forall_modus_ponms {A} {P Q: A -> Prop} {l: list A}:
  List.Forall (fun x => P x -> Q x) l ->
  List.Forall (fun x => P x) l ->
  List.Forall (fun x => Q x) l.
Proof.
  intros.
  induction H;
  inverts_Forall;
  econstructor;
  eauto.
Qed.


Lemma Forall_takewhile' {A} (P Q: A -> Prop) ts:
  (List.Forall (fun x => P x \/ Q x) ts) ->
  exists ts1 ts2, ts = ts1 ++ ts2 /\ List.Forall P ts1 /\ List.Forall (fun x => P x \/ Q x) ts2 /\ (ts2 = nil \/ exists ti ts22, ts2 = ti :: ts22 /\ Q ti ).
Proof.
  intros.
  induction H.
  * eexists nil, nil.
    simpl.
    repeat split; eauto.
  * case H.
    - (* P x, we apply induction hypothesis. *)
      intros; unpack.
      exists (x ::ts1), ts2.
      simpl; subst.
      repeat split; eauto.
    - (* Q x, we cut here. *)
      intros; unpack.
      eexists nil, (x :: l).
      simpl; subst.
      repeat split; simpl; eauto.
Qed.

Lemma Forall_takewhile {A} {P Q: A -> Prop} {ts}:
  (List.Forall (fun x => P x \/ Q x) ts) ->
  (List.Forall P ts) \/ exists ts1 ti ts2, ts1 ++ ti :: ts2 = ts /\ List.Forall P ts1 /\ List.Forall (fun x => P x \/ Q x) ts2 /\ Q ti.
Proof.
  intros.
  destruct (@Forall_takewhile' A P Q ts H); unzip; subst.
  - autorewrite with list; left; eauto.
  - right.
    rename x into ts1, x1 into ti, x2 into ts2.
    exists ts1 ti ts2; inverts_Forall; repeat split; eauto.
Qed.

Lemma Forall_or_comm {A} {P Q: A -> Prop} {ts}:
  List.Forall (fun x => P x \/ Q x) ts ->
  List.Forall (fun x => Q x \/ P x) ts
.
Proof.
  induction 1; econstructor; unzip; eauto.
Qed.

Lemma is_empty_dec x:
  {x = Empty} + {x <> Empty}.
Proof.
  look x; try solve [right; intro; congruence| left; eauto].
Qed.


Lemma count_nempty {ts} :
  List.Forall is_value_res ts ->
  (exists ts1 ti ts2 tj ts3, 
    ts = ts1 ++ ti :: ts2 ++ tj :: ts3 
    /\ ti <> Empty
    /\ tj <> Empty
  ) \/
  (exists ts1 ti ts2,
    ts = ts1 ++ ti :: ts2
    /\ ti <> Empty
    /\ List.Forall (eq Empty) ts1
    /\ List.Forall (eq Empty) ts2
  ) \/ List.Forall (eq Empty) ts.
Proof.
  induction 1.
  * right; right; eauto.
  * unzip.
    - left. exists (x :: x0) x1 x2 x3 x4; eauto.
    - destruct (is_empty_dec x).
      + right; left.
        exists (x :: x0) x1 x2; eauto.
      + left. exists (@nil term) x x0 x1 x2; eauto.
    - destruct (is_empty_dec x).
      + right; right; eauto.
      + right; left.
        exists (@nil term) x l; eauto.
Qed.


Lemma jt_progress:
  forall Gamma t T,
  jt Gamma t T ->
  closed t ->
  (exists t', cbv t t')
  \/ is_value_res t.
Ltac use_ih ih :=
  destruct ih; [ eauto with closed | unpack; eauto with red |  ].
Proof.
  induction 1 using jt_ind';
  try solve [intros; subst; right; eauto with is_value_res]
  (* all the other cases *).
  { left; false; eauto with closed. }
  { left; use_ih IHjt1.
    1:{ (* either t2 is an error or it is not. *)
        destruct (is_error_dec t1); eauto with red.
        - look t1; invert_cbv.
        - destruct (is_error_dec t2); eauto with red.
          look t2.
          + eexists; eapply RedAppREmpty; eauto;
            look t1.
          + eexists; eapply RedAppRConflict; eauto.
      }
    use_ih IHjt2.
    1:{
      destruct (is_error_dec t2); eauto with red.
      - look t2; invert_cbv.
      - destruct (is_error_dec t1); eauto with red.
        + look t1.
          * eexists. eapply RedAppLEmpty. eauto.
            look t2.
          * eexists; eapply RedAppLConflict; eauto.
        + eexists; eapply RedAppVR; simpl; eauto with is_value.
    }

    (* Because `t1` is a closed value and has a function type,
      it must be a lambda-abstraction. *)
    forward invert_jt_TyFun. { eauto with closed. }

    destruct H4.
    - destruct (is_error_dec t2).
      { look t2; eexists;
        try eapply RedAppREmpty;
        try eapply RedAppRConflict; simpl; eauto; look t1.
        { unpack; tryfalse. }
      }
      {
        unpack; subst.
        obvious.
      }
    - destruct (is_error_dec t2).
      { look t1; look t2; eexists;
        try eapply RedAppRConflict;
        try eapply RedAppLConflict;
        try eapply RedAppLEmpty; eauto.
      }
      {
        look t1; look t2; eexists;
        try eapply RedAppRConflict;
        try eapply RedAppLConflict;
        try eapply RedAppLEmpty;
        try eapply RedAppREmpty; eauto.
      }
  }
  {
    left.
    assert (Htsclosed: List.Forall closed ts).
    { eauto with closed. }

    remember (Forall_modus_ponms H0 Htsclosed) as Hts; simpl in Hts.


    destruct (Forall_takewhile (Forall_or_comm Hts)) as [Hts' | Hts'].
    2: {
      unzip; eexists; eapply RedDefaultE; simpl; eauto.
    }
    clear Hts HeqHts; rename Hts' into Hts.

    destruct (count_nempty Hts) as [Hconflict|[Hvalue|Hempty]]; unzip.
    { exists Conflict. eapply RedDefaultEConflict with _ x0 _ x2 _; simpl; eauto. }
    { exists x0; eapply RedDefaultEValue; inverts_Forall; simpl; eauto. }
    
    use_ih IHjt1.
    destruct (invert_jt_TyBool _ _ H1); eauto with closed.
    - unzip; induction x; eexists; [eapply RedDefaultJTrue|eapply RedDefaultJFalse]; eauto.

    - look tj; eexists; try eapply RedDefaultJConflict; try eapply RedDefaultJEmpty; simpl; eauto.
  }
Qed.



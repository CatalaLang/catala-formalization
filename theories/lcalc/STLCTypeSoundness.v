Require Import MyTactics.
Require Import LCSyntax.
Require Import LCValues.
Require Import LCReduction.
Require Import STLCDefinition.
Require Import STLCLemmas.

(*|

This is a failed attempt to prove the lemma `jt_te_substitution_0` in
a direct way, without introducing the auxiliary judgement `js`. See
STLCLemmas for a valid proof.

|*)

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
  (* By induction on the type derivation,
     then by cases on `cbv t t'`. *)
  induction 1; intros; subst; invert_cbv; try eauto with jt.
  (* Case: JApp/RedBetaV. *)
  { pick_jt (ELam t) invert.
    eauto using jt_te_substitution_0. }
  { pick_jt (EVariantSome vc) invert.
    eauto using jt_te_substitution_0.
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
  exists t', t = ELam t'.
Proof.
  (* By cases. The type system is so simple that an induction is not
     even required here. An induction would be required if the type
     system had non-syntax-directed rules, such as a subtyping rule, or
     type abstraction and type instantiation rules, as in System F. *)
  inversion 1; intros; subst.
  (* Case: JVar. A variable is not closed. Contradiction. *)
  { false. eauto with closed. }
  (* Case: JLam. Immediate. *)
  { obvious. }
  (* Case: JApp. An application is not a value. Contradiction. *)
  { false. }
  (* Case: Ite. An Ite is not a value. Contradiction. *)
  { false. }
Qed.

Lemma invert_jt_TyOption:
  forall Gamma t T,
  jt Gamma t (TyOption T) ->
  is_value t ->
  closed t ->
  (
    t = EVariantNone \/
    exists t',
      is_value t'
      /\ closed t'
      /\ jt Gamma t' T
      /\ t = EVariantSome t'
  ).
Proof.
  inversion 1; intros; subst.
  { false. eauto with closed. }
  { false. }
  { obvious. }
  { right. exists t0; repeat split; eauto with closed. }
  { false. }
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
  (exists t', cbv t t') \/ is_value t.
Ltac use_ih ih :=
  destruct ih; [ eauto with closed | unpack; eauto with red |  ].
Proof.
  (* By induction on the type derivation. *)
  induction 1; intros; subst.
  (* Case: JVar. *)
  { (* A variable does not reduce, so we must find a contradiction among
       our hypotheses. Here, the hypothesis that `t` is closed provides
       such a contradiction. (We could also exploit the fact that,
       according to our definition of `is_value`, a variable is a value,
       but it is preferable not to do so if we can avoid it.) *)
    false. eauto with closed. }
  (* Case: JLam. *)
  { (* A lambda-abstraction is a value. *)
    compute; eauto. }
  (* Case: JApp. *)
  { (* Apply the induction hypothesis to `t1`. If `t1` reduces, then
       obviously `App t1 t2` reduces as well, so we are finished. There
       remains to consider the case where `t1` is a value. *)
    use_ih IHjt1.
    (* Reason in the same way about `t2`. *)
    use_ih IHjt2.
    (* We wish to prove that `App t1 t2` is a beta-redex. *)
    left.
    (* Because `t1` is a closed value and has a function type,
       it must be a lambda-abstraction. *)
    forward invert_jt_TyFun. { eauto with closed. }
    (* Therefore, we have a beta-redex. *)
    subst; eexists; eapply RedBetaV; eauto. }

  { (* A Constant is a value. *)
    right; now compute. }
  { use_ih IHjt.
    edestruct (invert_jt_TyOption).
    - eapply JtSome; eassumption.
    - eauto.
    - eauto.
    - discriminate.
    - right. unpack; injections; subst.
      eauto.
  }
  { 
    left.
    use_ih IHjt1.
    forward invert_jt_TyOption. { eauto with closed. }
    destruct H4; unpack; eauto with red.
  }
Qed.

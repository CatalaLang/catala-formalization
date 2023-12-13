Require Import syntax.

Require Import small_step tactics.


Notation monad_bind t1 t2 := (Match_ t1 ENone t2).


Fixpoint monad_handle_one (ts: list term) : term :=
  match ts with
  | nil => ESome (Var 0)
  | cons thead ttail =>
    Match_ (lift 1 thead)
      (monad_handle_one ttail)
      (Conflict)
  end.

Fixpoint monad_handle_zero ts tj tc: term :=
  match ts with
  | nil => If tj tc ENone
  | cons thead ttail =>
    Match_ thead
      (monad_handle_zero ttail tj tc)
      (monad_handle_one ttail)
  end.

Definition monad_handle ts tj tc: term :=
  monad_handle_zero ts tj tc
.

Lemma subst_monad_handle_one :
  forall ts sigma,
  (monad_handle_one ts).[up sigma] = monad_handle_one ts..[sigma].
Proof.
  induction ts; repeat (asimpl; intros; f_equal; eauto).
Qed.

Lemma subst_monad_handle_zero :
  forall ts tj tc sigma,
  (monad_handle_zero ts tj tc).[sigma] = monad_handle_zero ts..[sigma] tj.[sigma] tc.[sigma].
Proof.
  induction ts; repeat (asimpl; intros; f_equal; eauto).
  eapply subst_monad_handle_one.
Qed.

Lemma subst_monad_handle:
  forall ts tj tc sigma,
  (monad_handle ts tj tc).[sigma] = monad_handle ts..[sigma] tj.[sigma] tc.[sigma].
Proof.
  eapply subst_monad_handle_zero.
Qed.


Hypothesis magic: forall {T}, T.

Fixpoint trans (t: term) : term :=
  match t with
  | Var x => Var x
  | FreeVar x => FreeVar x
  | App t1 t2 => App (trans t1) (trans t2)
  | Lam t => Lam (trans t)

  | ErrorOnEmpty t => Match_ (trans t) Conflict (Var 0)
  | DefaultPure t => ESome (trans t)
  | Default ts tj tc =>
    monad_handle (List.map trans ts) (trans tj) (trans tc)
  | Empty => ENone
  | Conflict => Conflict

  | Value v => Value (trans_value v)
  | Binop op t1 t2 => Binop op (trans t1) (trans t2)

  | Match_ u t1 t2 =>
    Match_ (trans u) (trans t1) (trans t2)
  | ENone => ENone
  | ESome t => ESome (trans t)

  | If t ta tb =>
    If (trans t) (trans ta) (trans tb)
  end

with trans_value v :=
  match v with
  | Bool b => Bool b
  | Int i => Int i
  | Closure t sigma => Closure (trans t) (List.map trans_value sigma)
  | VNone => VNone
  | VUnit => VUnit
  | VSome v => VSome (trans_value v)
  | VPure v => VPure (trans_value v)
  end
.

Lemma trans_te_renaming:
  forall t u,
  trans t = u ->
  forall xi,
  trans t.[ren xi] = u.[ren xi].
Proof.
  induction t; repeat (asimpl; intros; subst; f_equal; eauto).
  * admit.
  * admit.
  * rewrite subst_monad_handle;
    repeat (asimpl; intros; subst; f_equal; eauto).
    admit "true with the correct induction hypothesis".
Admitted.


Lemma trans_te_renaming_0:
  forall t u,
  trans t = u ->
  trans (lift 1 t) = (lift 1 u).
Proof.
  intros.
  eapply trans_te_renaming; eauto.
Qed.


Theorem trans_te_substitution:
  forall t u,
  trans t = u ->
  forall sigma1 sigma2,
  List.Forall2 (fun v1 v2 => trans_value v1 = v2) sigma1 sigma2 ->
  trans t.[subst_of_env sigma1] = u.[subst_of_env sigma2].
Proof.
  induction t; try solve [repeat (asimpl; intros; subst; f_equal; eauto)].
  { admit "should be trivial". }
  { admit "should be trivial using trans_te_renaming_0.". }
  { admit. }
  { admit. }
  { asimpl; intros; subst.
    rewrite subst_monad_handle; repeat (f_equal; eauto).
    admit "correct with the correct induction hypothesis.".
  }
  { intros; subst; asimpl; f_equal; eauto.
    admit "should be trivial using trans_te_renaming_0". }
  Fail next goal.
Admitted.

Require Import typing.

(* Theorem correction_typing:
  forall Gamma t T,
  jt_term Gamma t T ->
  exists Gamma' T',
  jt_term Gamma' (trans t) T'.
Admitted. *)

Import Learn.

Theorem correction_continuations:
  forall s1 s2,
  (exists GGamma Gamma T, jt_term GGamma Gamma s1 T) ->
  sred s1 s2 ->
  exists target,
    star sred
      (trans s1) target /\
    star sred
      (trans s2) target.
Proof.
  intros s1 s2.
  intros (GGamma & Gamma & T & Hty) Hsred.
  generalize dependent GGamma.
  generalize dependent Gamma.
  generalize dependent T.
  induction Hsred; intros.
  all: repeat multimatch goal with
  | _ => inv_jt
  | [h1: forall _ _ _, jt_term _ _ ?u _ -> _, h2: jt_term _ _ ?u _ |- _] =>
    learn (h1 _ _ _ h2);
    clear h1
  | [h: exists var, _ |- _] =>
    let var := fresh var in
    destruct h as (var & ?)
  | [h: _ /\ _ |- _] =>
    destruct h
  end.
  (* When the right hand side is the result of the left hand side. *)
  all: try solve [eexists; split; [eapply star_one; simpl; econstructor|eapply star_refl]].
  7: { eexists; split; [|eapply star_refl]; simpl; eapply star_one. }
  { admit. }
  {  }
  6: {
    eexists; split; eapply star_sred_binop_right; eauto.
  }
  all: admit.
Admitted.

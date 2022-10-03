Require Import MyTactics.
Require Import DCSyntax.

(* The syntactic subcategory of errors is decidable. *)

Definition if_error {A} (t : term) (a1 a2 : A) : A :=
  match t with
  | Empty | Conflict => a1
  | _ => a2
  end.

Definition is_error (t : term) :=
  if_error t True False.

Global Hint Extern 1 (is_error _) => (simpl; tauto) : is_error obvious.

(* A term either is or is not a error. *)

Lemma error_or_nonerror:
  forall t,
  is_error t \/ ~ is_error t.
Proof.
  destruct t; simpl; eauto.
Qed.

(* Simplification rules for [if_error]. *)

Lemma if_error_error:
  forall A v (a1 a2 : A),
  is_error v ->
  if_error v a1 a2 = a1.
Proof.
  destruct v; simpl; tauto.
Qed.

Lemma if_error_nonerror:
  forall A t (a1 a2 : A),
  ~ is_error t ->
  if_error t a1 a2 = a2.
Proof.
  destruct t; simpl; tauto.
Qed.

(* The syntactic subcategory of errors is preserved by renamings. *)

Lemma is_error_renaming:
  forall v xi,
  is_error v ->
  is_error v.[ren xi].
Proof.
  destruct v; simpl; eauto.
Qed.

Lemma is_nonerror_renaming:
  forall v xi,
  ~ is_error v ->
  ~ is_error v.[ren xi].
Proof.
  destruct v; simpl; eauto.
Qed.

Global Hint Resolve is_error_renaming is_nonerror_renaming : is_error obvious.

Ltac is_error :=
  eauto with is_error.

(* The tactic [not_a_error] can be used to prove that the current case
   is impossible, because we have a hypothesis of the form [~ is_error v],
   where [v] clearly is a error. *)

Ltac not_a_error :=
  solve [ false; is_error ].

Ltac if_error :=
  repeat first [ rewrite if_error_error by is_error |
                 rewrite if_error_nonerror by is_error ].

(* The tactic [error_or_nonerror t] creates two cases: either [t] is a error,
   or it isn't. *)

Ltac error_or_nonerror t :=
  destruct (error_or_nonerror t);
  if_error.

(* The tactic [error_or_app_or_let] creates three cases: either [t] is a error,
   or it is an application, or it is a [let] construct. *)

Ltac error_or_app_or_let t :=
  error_or_nonerror t; [|
    destruct t as [ ? | ? | t1 t2 | t1 t2 ]; [ not_a_error | not_a_error | |]
      (* In principle, we should not fix the names [t1] and [t2] here,
         as it might cause name clashes. *)
  ].

(* The predicate [is_error_subst sigma] holds if every term in the
   codomain of the substitution [sigma] is a error. *)

Definition is_error_subst (sigma : var -> term) :=
  forall x, is_error (sigma x).

Lemma is_error_subst_cons:
  forall v sigma,
  is_error v ->
  is_error_subst sigma ->
  is_error_subst (v .: sigma).
Proof.
  intros. intros [|x]; is_error.
Qed.

Lemma is_error_subst_renaming:
  forall sigma i,
  is_error_subst sigma ->
  is_error_subst (sigma >> ren (+i)).
Proof.
  intros. intro x. asimpl. is_error.
Qed.

Global Hint Resolve  is_error_subst_renaming
  : is_error obvious.

Lemma errors_are_preserved_by_error_substitutions:
  forall v sigma,
  is_error v ->
  is_error_subst sigma ->
  is_error v.[sigma].
Proof.
  destruct v; simpl; intros; eauto with is_error.
Qed.

Global Hint Resolve
  is_error_subst_cons
  errors_are_preserved_by_error_substitutions
: is_error obvious.

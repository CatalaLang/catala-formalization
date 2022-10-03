Require Import MyTactics.
Require Import DCSyntax.

(* The syntactic subcategory of values is decidable. *)

Definition if_value {A} (t : term) (a1 a2 : A) : A :=
  match t with
  | Var _ | Lam _ | Empty | Conflict | Const _ => a1
  | _ => a2
  end.

Definition is_value (t : term) :=
  if_value t True False.

Global Hint Extern 1 (is_value _) => (simpl; tauto) : is_value obvious.

(* A term either is or is not a value. *)

Lemma value_or_nonvalue:
  forall t,
  is_value t \/ ~ is_value t.
Proof.
  destruct t; simpl; eauto.
Qed.

(* Simplification rules for [if_value]. *)

Lemma if_value_value:
  forall A v (a1 a2 : A),
  is_value v ->
  if_value v a1 a2 = a1.
Proof.
  destruct v; simpl; tauto.
Qed.

Lemma if_value_nonvalue:
  forall A t (a1 a2 : A),
  ~ is_value t ->
  if_value t a1 a2 = a2.
Proof.
  destruct t; simpl; tauto.
Qed.

(* The syntactic subcategory of values is preserved by renamings. *)

Lemma is_value_renaming:
  forall v xi,
  is_value v ->
  is_value v.[ren xi].
Proof.
  destruct v; simpl; eauto.
Qed.

Lemma is_nonvalue_renaming:
  forall v xi,
  ~ is_value v ->
  ~ is_value v.[ren xi].
Proof.
  destruct v; simpl; eauto.
Qed.

Global Hint Resolve is_value_renaming is_nonvalue_renaming : is_value obvious.

Ltac is_value :=
  eauto with is_value.

(* The tactic [not_a_value] can be used to prove that the current case
   is impossible, because we have a hypothesis of the form [~ is_value v],
   where [v] clearly is a value. *)

Ltac not_a_value :=
  solve [ false; is_value ].

Ltac if_value :=
  repeat first [ rewrite if_value_value by is_value |
                 rewrite if_value_nonvalue by is_value ].

(* The tactic [value_or_nonvalue t] creates two cases: either [t] is a value,
   or it isn't. *)

Ltac value_or_nonvalue t :=
  destruct (value_or_nonvalue t);
  if_value.

(* The tactic [value_or_app_or_let] creates three cases: either [t] is a value,
   or it is an application, or it is a [let] construct. *)

Ltac value_or_app_or_let t :=
  value_or_nonvalue t; [|
    destruct t as [ ? | ? | t1 t2 | t1 t2 ]; [ not_a_value | not_a_value | |]
      (* In principle, we should not fix the names [t1] and [t2] here,
         as it might cause name clashes. *)
  ].

(* The predicate [is_value_subst sigma] holds if every term in the
   codomain of the substitution [sigma] is a value. *)

Definition is_value_subst (sigma : var -> term) :=
  forall x, is_value (sigma x).

Lemma is_value_subst_ids:
  is_value_subst ids.
Proof.
  intros x. is_value.
Qed.

Lemma is_value_subst_cons:
  forall v sigma,
  is_value v ->
  is_value_subst sigma ->
  is_value_subst (v .: sigma).
Proof.
  intros. intros [|x]; is_value.
Qed.

Definition is_value_subst_up:
  forall sigma,
  is_value_subst sigma ->
  is_value_subst (up sigma).
Proof.
  intros sigma h. intros [|x]; asimpl.
  { simpl. eauto. }
  { is_value. }
Qed.

Definition is_value_subst_upn:
  forall sigma i,
  is_value_subst sigma ->
  is_value_subst (upn i sigma).
Proof.
  induction i; intros; asimpl.
  { eauto. }
  { rewrite <- fold_up_upn. eauto using is_value_subst_up. }
Qed.

Lemma is_value_subst_renaming:
  forall sigma i,
  is_value_subst sigma ->
  is_value_subst (sigma >> ren (+i)).
Proof.
  intros. intro x. asimpl. is_value.
Qed.

Global Hint Resolve is_value_subst_up is_value_subst_upn is_value_subst_renaming
  : is_value obvious.

Lemma values_are_preserved_by_value_substitutions:
  forall v sigma,
  is_value v ->
  is_value_subst sigma ->
  is_value v.[sigma].
Proof.
  destruct v; simpl; intros; eauto with is_value.
Qed.

Lemma nonvalues_are_preserved_by_substitutions:
  forall t sigma,
  ~ is_value t ->
  ~ is_value t.[sigma].
Proof.
  destruct t; simpl; tauto.
Qed.

Global Hint Resolve
  is_value_subst_ids
  is_value_subst_cons
  values_are_preserved_by_value_substitutions
  nonvalues_are_preserved_by_substitutions
: is_value obvious.

Lemma is_ren_is_value_subst:
  forall sigma,
  is_ren sigma ->
  is_value_subst sigma.
Proof.
  intros ? [ xi ? ]. subst. eauto with is_value.
Qed.

Global Hint Resolve is_ren_is_value_subst : is_value obvious.

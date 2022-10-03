Require Import MyTactics.
Require Import DCSyntax.
Require Import DCValues.

(* The syntactic subcategory of values is decidable. *)

Definition if_value_res {A} (t : term) (a1 a2 : A) : A :=
  match t with
  | Lam _ | Empty | Conflict | Const _ => a1
  | _ => a2
  end.

Definition is_value_res (t : term) :=
  if_value_res t True False.

Lemma is_value_res_subset_is_value:
  forall t,
  is_value_res t -> is_value t.
Proof.
  unfold is_value_res, is_value, if_value_res, if_value.
  intros; induction t; eauto.
Qed.

Global Hint Resolve is_value_res_subset_is_value : is_value obvious.

Global Hint Extern 1 (is_value_res _) => (simpl; tauto) : is_value_res obvious.

(* A term either is or is not a value. *)

Lemma value_or_nonvalue:
  forall t,
  is_value_res t \/ ~ is_value_res t.
Proof.
  destruct t; simpl; eauto.
Qed.

(* Simplification rules for [if_value_res]. *)

Lemma if_value_res_value:
  forall A v (a1 a2 : A),
  is_value_res v ->
  if_value_res v a1 a2 = a1.
Proof.
  destruct v; simpl; tauto.
Qed.

Lemma if_value_res_nonvalue:
  forall A t (a1 a2 : A),
  ~ is_value_res t ->
  if_value_res t a1 a2 = a2.
Proof.
  destruct t; simpl; tauto.
Qed.

(* The syntactic subcategory of values is preserved by renamings. *)

Lemma is_value_res_renaming:
  forall v xi,
  is_value_res v ->
  is_value_res v.[ren xi].
Proof.
  destruct v; simpl; eauto.
Qed.

Lemma is_value_res_subst_stable:
  forall v sigma,
  is_value_res v ->
  is_value_res v.[sigma].
Proof.
  destruct v; simpl; eauto; intros; false; eauto.
Qed.

Lemma is_value_res_subst_list_stable:
  forall l sigma,
  List.Forall is_value_res l ->
  List.Forall is_value_res l..[sigma].
Proof.
  induction l; intros; asimpl; inverts_Forall; econstructor; eauto using is_value_res_subst_stable.
Qed.

Lemma is_nonvalue_renaming:
  forall v xi,
  ~ is_value_res v ->
  ~ is_value_res v.[ren xi].
Proof.
  destruct v; simpl; eauto.
Qed.

Global Hint Resolve is_value_res_renaming is_nonvalue_renaming : is_value_res obvious.

Ltac is_value_res :=
  eauto with is_value_res.

(* The tactic [not_a_value] can be used to prove that the current case
   is impossible, because we have a hypothesis of the form [~ is_value_res v],
   where [v] clearly is a value. *)

Ltac not_a_value :=
  solve [ false; is_value_res ].

Ltac if_value_res :=
  repeat first [ rewrite if_value_res_value by is_value_res |
                 rewrite if_value_res_nonvalue by is_value_res ].

(* The tactic [value_or_nonvalue t] creates two cases: either [t] is a value,
   or it isn't. *)

Ltac value_or_nonvalue t :=
  destruct (value_or_nonvalue t);
  if_value_res.

(* The tactic [value_or_app_or_let] creates three cases: either [t] is a value,
   or it is an application, or it is a [let] construct. *)

Ltac value_or_app_or_let t :=
  value_or_nonvalue t; [|
    destruct t as [ ? | ? | t1 t2 | t1 t2 ]; [ not_a_value | not_a_value | |]
      (* In principle, we should not fix the names [t1] and [t2] here,
         as it might cause name clashes. *)
  ].

(* The predicate [is_value_res_subst sigma] holds if every term in the
   codomain of the substitution [sigma] is a value. *)

Definition is_value_res_subst (sigma : var -> term) :=
  forall x, is_value_res (sigma x).

Definition is_not_value_res_subst (sigma : var -> term) :=
  forall x, ~ is_value_res (sigma x).

Lemma is_value_res_subst_is_value_subst sigma :
  is_value_res_subst sigma -> is_value_subst sigma.
Proof.
  unfold is_value_res_subst, is_value_subst.
  is_value.
Qed.

Global Hint Resolve is_value_res_subst_is_value_subst : is_value obvious.

Lemma is_value_res_subst_cons:
  forall v sigma,
  is_value_res v ->
  is_value_res_subst sigma ->
  is_value_res_subst (v .: sigma).
Proof.
  intros. intros [|x]; is_value_res.
Qed.

Lemma is_value_res_subst_renaming:
  forall sigma i,
  is_value_res_subst sigma ->
  is_value_res_subst (sigma >> ren (+i)).
Proof.
  intros. intro x. asimpl. is_value_res.
Qed.

Global Hint Resolve is_value_res_subst_renaming
  : is_value_res obvious.

Lemma values_are_preserved_by_value_substitutions:
  forall v sigma,
  is_value_res v ->
  is_value_res_subst sigma ->
  is_value_res v.[sigma].
Proof.
  destruct v; simpl; intros; eauto with is_value_res.
Qed.

Lemma nonvalues_are_preserved_by_substitutions:
  forall t sigma,
  is_not_value_res_subst sigma ->
  ~ is_value_res t ->
  ~ is_value_res t.[sigma].
Proof.
  destruct t; simpl; try tauto.
  - unfold is_not_value_res_subst.
    eauto.
Qed.

Global Hint Resolve
  is_value_res_subst_cons
  values_are_preserved_by_value_substitutions
  nonvalues_are_preserved_by_substitutions
: is_value_res obvious.

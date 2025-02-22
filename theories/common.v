Require Import Lists.List.
Require Import Lia.
Require Import tactics.
Import List.ListNotations.


(** Definition of [lastn n l]: gives the last [n] elements of a list [l]. *)
Definition lastn {A} n (l: list A) := List.skipn ((List.length l) - n) l.

Theorem lastn_def_firstn {A} n (l: list A):
  lastn n l = rev (firstn n (rev l)).
Proof.
  rewrite firstn_rev.
  rewrite rev_involutive.
  eauto.
Qed.

(* Some properties about [lastn]. *)
Lemma length_lastn {A} n:
  forall l: list A, List.length (lastn n l) = min n (List.length l).
Proof.
  unfold lastn.
  setoid_rewrite List.length_skipn; lia.
Qed.

Lemma lastn_cons {A} n:
  forall a (l: list A), List.length l >= n -> lastn n (a::l) = lastn n l.
Proof.
  unfold lastn.
  intros.
  simpl List.length.
  replace (S (List.length l) - n) with (S (List.length l - n)); eauto.
  lia.
Qed.

Lemma list_diagonal {A} (x: A) l :
  x :: l <> l.
Proof.
  induction l; intro; inj; contradiction.
Qed.


Lemma lastn1_append {A}:
  forall (l: list A) k,
    lastn 1 (l ++ [k]) = [k].
Proof.
  intros.
  rewrite lastn_def_firstn.
  rewrite rev_unit; simpl.
  eauto.
Qed.

Lemma lastn1_one {A}:
  forall k: A,
    lastn 1 [k] = [k].
Proof.
  intros.
  rewrite lastn_def_firstn.
  simpl.
  eauto.
Qed.

Lemma lastn1_nil {A}:
  lastn 1 ([]: list A) = [].
Proof.
  intros.
  rewrite lastn_def_firstn.
  simpl.
  eauto.
Qed.

Lemma nth_error_nil {A} x:
  List.nth_error (nil: list A) x = None.
Proof.
  induction x; simpl; eauto.
Qed.

(* Such that [l = lastn n l ++ firstn n l] *)
Definition droplastn {A} n (l: list A) := List.firstn ((List.length l) - n) l.

Theorem droplastn_def_firstn {A} n (l: list A) : droplastn n l = List.firstn ((List.length l) - n) l.
Proof. eauto. Qed.

Lemma droplastn_cons {A} a n (l: list A) :
  n <= List.length l -> droplastn n (a :: l) = a :: droplastn n l.
Proof.
  intros H.
  rewrite droplastn_def_firstn.
  simpl List.length.
  replace (S (List.length l) - n) with (S (List.length l - n)) by lia.
  simpl firstn.
  rewrite <- droplastn_def_firstn.
  eauto.
Qed.


Lemma lastn1_length1 {A}:
  forall k (kappa: list A),
    lastn 1 kappa = cons k nil ->
    1 <= Datatypes.length kappa.
Proof.
  intros k kappa Hk.
  replace 1 with (List.length (lastn 1 kappa)).
  { rewrite length_lastn. eapply PeanoNat.Nat.le_min_r. }
  rewrite Hk; eauto.
Qed.

Theorem Forall2_nth_error_Some_left {A B} F l1 l2:
  Forall2 F l1 l2 ->
  forall k (x: A),
    nth_error l1 k = Some x ->
    exists (y: B), nth_error l2 k = Some y.
Proof.
  induction 1, k; simpl; intros; inj; eauto.
Qed.

Theorem Forall2_nth_error_Some_right {A B} F l1 l2:
  Forall2 F l1 l2 ->
  forall k (y: A),
    nth_error l2 k = Some y ->
    exists (x: B), nth_error l1 k = Some x.
Proof.
  induction 1, k; simpl; intros; inj; eauto.
Qed.


Theorem Forall2_nth_error_Some {A B} F l1 l2:
  Forall2 F l1 l2 ->
  forall k (x: A) (y: B),
    nth_error l1 k = Some x ->
    nth_error l2 k = Some y ->
    F x y.
Proof.
  induction 1, k; simpl; intros; inj; eauto.
Qed.

Lemma nth_error_Some' {A: Type} {l: list A} {n v} : nth_error l n = Some v -> n < List.length l.
Proof.
  intros.
  rewrite <- nth_error_Some in *.
  repeat intro; tryfalse.
Qed.

Lemma nth_error_alt_def {A: Type} {l: list A} {n}:
    if (n <? Datatypes.length l)%nat
    then exists v, nth_error l n = Some v
    else nth_error l n = None.
Proof.
  induction (Nat.ltb_spec n (Datatypes.length l)).
  { learn (proj2 (List.nth_error_Some l n) H).
    induction (nth_error l n).
    { exists a; eauto. }
    { tryfalse. }
  }
  { learn (proj2 (List.nth_error_None l n) H).
    eauto.
  }
Qed.


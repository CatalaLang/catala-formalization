Require Import List.
Require Import MyTactics.
Require Export ListFacts.

(* A few random additions to the [List] module, which is woefully incomplete. *)

(* -------------------------------------------------------------------------- *)

Lemma rev_cons_app:
  forall {A} (x : A) xs ys,
  rev (x :: xs) ++ ys = rev xs ++ x :: ys.
Proof.
  intros. simpl. rewrite <- app_assoc. reflexivity.
Qed.

(* -------------------------------------------------------------------------- *)

Lemma length_nil:
  forall A,
  length (@nil A) = 0.
Proof.
  reflexivity.
Qed.

Lemma length_cons:
  forall A (x : A) xs,
  length (x :: xs) = 1 + length xs.
Proof.
  reflexivity.
Qed.

Hint Rewrite length_nil length_cons app_length map_length : length.

Ltac length :=
  autorewrite with length in *;
  try lia.

(* -------------------------------------------------------------------------- *)

(* We have [app_nth1] and [app_nth2], but the following lemma, which can be
   viewed as a special case of [app_nth2], is missing. *)

Lemma app_nth:
  forall {A} (xs ys : list A) x n,
  n = length xs ->
  nth n (xs ++ ys) x = nth 0 ys x.
Proof.
  intros.
  rewrite app_nth2 by lia.
  replace (n - length xs) with 0 by lia.
  reflexivity.
Qed.

(* -------------------------------------------------------------------------- *)

(* [rev_nats n] is the semi-open interval (n, 0], counted down. *)

(* It could also be defined as [rev (seq 0 n)], but a direct definition
   is easier to work with, as it is immediately amenable to proofs by
   induction. *)

Fixpoint rev_nats (n : nat) : list nat :=
  match n with
  | 0 =>
      nil
  | S n =>
      n :: rev_nats n
  end.

(* [nats n] is the semi-open interval [0, n), counted up. *)

Definition nats (n : nat) : list nat :=
  seq 0 n.

(* These sequences have length [n]. *)

Lemma length_rev_nats:
  forall n,
  length (rev_nats n) = n.
Proof.
  induction n; intros; simpl; [| rewrite IHn ]; eauto.
Qed.

Lemma length_nats:
  forall n,
  length (nats n) = n.
Proof.
  unfold nats. intros. eauto using seq_length.
Qed.

(* -------------------------------------------------------------------------- *)

(* A few basic lemmas about [Forall]. *)

Lemma Forall_map:
  forall A B (f : A -> B) (P : B -> Prop) xs,
  Forall (fun x => P (f x)) xs ->
  Forall P (map f xs).
Proof.
  induction 1; intros; subst; simpl; econstructor; eauto.
Qed.

Lemma Forall_app:
  forall A (P : A -> Prop) xs ys,
  Forall P xs ->
  Forall P ys ->
  Forall P (xs ++ ys).
Proof.
  induction 1; intros; subst; simpl; eauto.
Qed.

Lemma Forall_rev:
  forall A (P : A -> Prop) xs,
  Forall P xs ->
  Forall P (rev xs).
Proof.
  induction 1; intros; subst; simpl; eauto using Forall_app.
Qed.

Lemma Forall_seq:
  forall (P : nat -> Prop) len start,
  (forall i, start <= i < start + len -> P i) ->
  Forall P (seq start len).
Proof.
  induction len; intros; simpl; econstructor; eauto with lia.
Qed.

Lemma Forall_filter:
  forall (P: nat -> bool) l,
  Forall (fun x => P x = true) (filter P l).
Proof.
  intros.
  induction l; simpl.
  * econstructor.
  * remember (P a) as b.
    induction b; [econstructor|]; auto.
Qed.

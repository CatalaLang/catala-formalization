Require Import Lists.List.
Require Import Lia.


(** Definition of [lastn n l]: gives the last [n] elements of a list [l]. *)
Definition lastn {A} n (l: list A) := List.skipn ((List.length l) - n) l.

Theorem lastn_def_lastn {A} n (l: list A):
  lastn n l = List.skipn ((List.length l) - n) l.
Proof.
  eauto.
Qed.

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
  setoid_rewrite List.skipn_length; lia.
Qed.

Lemma lastn_cons {A} n:
  forall a (l: list A), length l >= n -> lastn n (a::l) = lastn n l.
Proof.
  unfold lastn.
  intros.
  simpl length.
  replace (S (length l) - n) with (S (length l - n)); eauto.
  lia.
Qed.

Lemma lastn_length {A}:
  forall (a: A) l, lastn (length l) (a :: l) = l.
Proof.
  intros.
  rewrite lastn_def_lastn.
  replace (length (a :: l) - length l) with 1 by (simpl length; lia).
  simpl; eauto.
Qed.

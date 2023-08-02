Require Import Lists.List.
Require Import Lia.
Require Import tactics.


(** Definition of [lastn n l]: gives the last [n] elements of a list [l]. *)
Definition lastn {A} n (l: list A) := List.skipn ((List.length l) - n) l.

Theorem lastn_def_skip {A} n (l: list A):
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

Lemma lastn_cons' {A} n:
  forall a (l: list A), n > length l -> lastn n (a::l) = a :: lastn n l.
Proof.
  intros a l H.
  repeat rewrite lastn_def_firstn.
  repeat rewrite firstn_all2.
  repeat rewrite rev_involutive; eauto.
  all: rewrite rev_length; simpl; lia.
Qed.

Lemma lastn_length {A}:
  forall (l: list A), lastn (length l) l = l.
Proof.
  intros.
  rewrite lastn_def_skip.
  replace (length l - length l) with 0 by lia.
  simpl; eauto.
Qed.

Lemma lastn_length_cons {A}:
  forall (a: A) l, lastn (length l) (a :: l) = l.
Proof.
  intros.
  rewrite lastn_def_skip.
  replace (length (a :: l) - length l) with 1 by (simpl length; lia).
  simpl; eauto.
Qed.

Lemma fuck_stdlib {A} (x: A) l :
  x :: l <> l.
Proof.
  induction l; intro; inj; contradiction.
Qed.

Lemma lastn_cons_length {A}:
  forall (a: A) n l, 
  lastn n l = lastn n (a :: l) -> n <= length l.
Proof.
  intros a n l.
  destruct (Compare_dec.le_gt_dec n (length l)); eauto.
  { intros.
    exfalso.
    rewrite lastn_cons' in H; try lia.
    eapply fuck_stdlib; eauto.
  }
Qed.

Lemma lastn_cons_cons_length {A}:
  forall (a b: A) n l, 
  a <> b ->
  lastn n (b :: l) = lastn n (a :: l) -> n <= length l.
Proof.
  intros a b n l.
  destruct (Compare_dec.le_gt_dec n (length l)); eauto.
  { intros.
    exfalso.
    do 2 rewrite lastn_cons' in H0; try lia.
    injections; eauto.
  }
Qed.



(* Such that [l = lastn n l ++ firstn n l] *)
Definition droplastn {A} n (l: list A) := List.firstn ((List.length l) - n) l.

Theorem droplastn_def_firstn {A} n (l: list A) : droplastn n l = List.firstn ((List.length l) - n) l.
Proof. eauto. Qed.

Theorem droplastn_def_skipn {A} n (l: list A) :
  droplastn n l = rev (skipn n (rev l)).
Proof.
  rewrite skipn_rev; rewrite rev_involutive.
  eauto.
Qed.

Lemma droplastn_cons {A} a n (l: list A) :
  n <= length l -> droplastn n (a :: l) = a :: droplastn n l.
Proof.
  intros H.
  rewrite droplastn_def_firstn.
  simpl length.
  replace (S (length l) - n) with (S (length l - n)) by lia.
  simpl firstn.
  rewrite <- droplastn_def_firstn.
  eauto.
Qed.


Theorem append_droplastn_lastn {A} n (l: list A):
  l = droplastn n l ++ lastn n l
.
Proof.
  unfold lastn, droplastn.
  rewrite firstn_skipn.
  eauto.
Qed.


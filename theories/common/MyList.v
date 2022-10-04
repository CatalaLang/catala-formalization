Require Import List.
Require Import MyTactics.

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

Global Hint Rewrite length_nil length_cons app_length map_length : length.

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

(*
This lemma state that if we have two different ways to express a list t = as1 ++ a :: as2 = bs1 ++ b :: bs2, then there is three possibilities: 
* a is before b, hence there is a l such that bs1 = as1 ++ a :: l, and as2 = l ++ b :: bs2
* a is after b, hence there is a l such that as1 = bs1 ++ b :: l, and bs2 = l ++ a :: as2
* a is exactly at b, hence a = b /\ as1 = bs1 /\ as2 = bs2
*)




Lemma app_inj2: forall A (l1 l2 l2': list A), 
  l1 ++ l2 = l1 ++ l2' -> l2 = l2'.
Proof.
  induction l1; simpl; intros; injections; eauto.
Qed.

Lemma rev_same: forall A (l1 l2: list A),
  rev l1 = rev l2 -> l1 = l2.
Proof.
  intros.
  rewrite <- rev_involutive at 1.
  rewrite <- rev_involutive.
  f_equal; eauto.
Qed.


Lemma app_inj1: forall A (l1 l1' l2: list A), 
  l1 ++ l2 = l1' ++ l2 -> l1 = l1'.
Proof.
  intros.
  (* same as before, but with reversed lists *)
  forwards: app_inj2 (rev l2) (rev l1) (rev l1').
  { repeat rewrite <- rev_app_distr. now rewrite H. }
  now eapply rev_same.
Qed. 

Lemma split_list:
  forall (A: Type) (a b : A) (as1 as2 bs1 bs2: list A),
  as1 ++ a :: as2 = bs1 ++ b :: bs2 ->
  {l | bs1 = as1 ++ a :: l /\ as2 = l ++ b :: bs2 } +
  {l | as1 = bs1 ++ b :: l /\ bs2 = l ++ a :: as2 } +
  {a = b /\ as1 = bs1 /\ as2 = bs2}
.
Proof.
  intros.
  (* remember (as1 ++ a :: as2) as t. *)
  remember (length as1) as i.
  remember (length bs1) as j.
  forwards [[Hij|Hij]|Hij]: lt_eq_lt_dec i j.
  * (* first case: a is before b *)
    left; left.
    remember (firstn ((j-1) - i) as2) as l.
    assert (Hbs1: bs1 = as1 ++ a :: l).
    {
      rewrite Heql.
      rewrite <- firstn_cons.
      replace (S (j-1-i)) with (j - i) by lia.
      rewrite <- firstn_all2 with A j as1 by lia.
      rewrite Heqi.
      rewrite <- firstn_app.
      rewrite H.
      rewrite firstn_app.
      rewrite <- Heqj.
      replace (j - j) with 0 by lia.
      rewrite -> firstn_O, app_nil_r, Heqj, firstn_all.
      reflexivity.
    }
    exists l; split.
    - apply Hbs1.
    - (* bs1 ++ b :: bs2 = as1 ++ a :: l ++ b :: bs2 *)
      (* as1 ++ a :: as2 = as1 ++ a :: l ++ b :: bs2 *)
      assert (Hfinal: bs1 ++ b :: bs2 = as1 ++ a :: l ++ b :: bs2).
      { rewrite Hbs1.
        repeat rewrite <- app_assoc, <- app_comm_cons.
        f_equal. }
      rewrite <- H in Hfinal.
      forward app_inj2.
      now injections.
  * right. (* we only need to show that as1 = bs1. The rest will follow from H. *)
    assert (H1: as1 = bs1).
    { 
      (* this simply follows from the fact that as1 and bs1 are of the same length *)
      remember (firstn i (as1 ++ a :: as2)) as l.
      apply eq_trans with l.
      { rewrite Heql, Heqi.
        rewrite firstn_app.
        replace (_ - _) with 0 by lia.
        now rewrite firstn_O, firstn_all, app_nil_r.
      }
      {
        rewrite Heql, Hij, Heqj, H.
        rewrite firstn_app.
        replace (_ - _) with 0 by lia.
        now rewrite firstn_O, firstn_all, app_nil_r.
      }
    }
    rewrite H1 in H; forwards: app_inj2 H; injections.
    eauto.  
  * left; right. (* same as the first case. *)
    admit.
Admitted.

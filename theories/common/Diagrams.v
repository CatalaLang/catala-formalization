(** relation composition *)

Require Import Relations.
Require Import MyRelations.
Require Import MySequences.
Require Import MyTactics.
Require Import LibTactics.
Section Composition.

(* 
Context {A B : Type}.
Variable C1: Type.
Variable step1: C1 -> C1 -> Prop.
Variable C2: Type.
Variable step2: C2 -> C2 -> Prop.
Variable inv: C1 -> C2 -> Prop.
*)

Definition determinist {X} (R: X -> X -> Prop) :=
    forall x y1 y2, R x y1 -> R x y2 -> y1 = y2.


Definition simulation2
    {C1 C2: Type}
    (step1: relation C1)
    (step2: relation C2)
    (inv: C1 -> C2) :=
    forall c1 c1', step1 c1 c1' ->
    exists target,
        (star step2 (inv c1) target)
        /\ (star step2 (inv c1') target).


Definition simulation1
    {C1 C2: Type}
    (step1: relation C1)
    (step2: relation C2)
    (inv: C1 -> C2) :=
    forall c1 c1', step1 c1 c1' ->
        (plus step2 (inv c1) (inv c1') ).

Lemma star_determnist {C1} (step: relation C1):
    determinist step ->
    forall c1 c2 , 
      star step c1 c2 -> forall c2', star step c1 c2' ->
    (star step c2 c2' \/ star step c2' c2).
Proof.
  intro Hdet.
  unfold determinist in *.
  induction 1.
  { eauto. }
  { intros. induction H1.
    - eauto with sequences.
    - replace b0 with b in *. 2:{ eapply Hdet; eauto. }
      destruct (IHstar c0); eauto with sequences.
  }
Qed.

Lemma star_determnist_easy_to_use {C1} (step: relation C1):
    determinist step ->
    forall c1 c2 , 
      star step c1 c2 ->
      forall c2', star step c1 c2' ->
        exists target,
        (star step c2 target /\ star step c2' target).
Proof.
  introv Hdet H12 H12'.
  destruct (star_determnist _ Hdet _ _ H12  _ H12').
  - exists c2'; eauto with sequences.
  - exists c2; eauto with sequences.
Qed.



Lemma simulation2_horizontal_concat {C1 C2: Type}:
    forall step1 step2 (inv: C1 -> C2),
    simulation2 step1 step2 inv ->
    determinist step2 ->
    forall c1 c2 c3, step1 c1 c2 -> step1 c2 c3 ->
        exists target, (star step2 (inv c1) target)
        /\ (star step2 (inv c3) target).
Proof.
    unfold simulation2.
    introv Hsim Hdet.
    intros c1 c2 c3 H12 H23.
    destruct (Hsim c1 c2 H12) as [target1 [H11 Htarget1]].
    destruct (Hsim c2 c3 H23) as [target2 [Htarget2 H32]].

    edestruct (star_determnist_easy_to_use _ Hdet _ _ Htarget1 _ Htarget2)
    as [target [Ht1 Ht2]].
    exists target; eauto with sequences.
Qed.

Lemma simulation2_star {C1 C2: Type}:
    forall step1 step2 (trans: C1 -> C2),
    simulation2 step1 step2 trans ->
    determinist step2 ->
    simulation2 (star step1) step2 trans.

Proof.
    introv Hsim Hdet.
    induction 1; eauto with sequences.
    destruct (Hsim a b H) as [target1 [H11 Htarget1]].
    destruct IHstar as [target2 [Htarget2 H32]].

    edestruct (star_determnist_easy_to_use _ Hdet _ _ Htarget1 _ Htarget2)
    as [target [Ht1 Ht2]].
    exists target; eauto with sequences.
Qed.

Require Import Coq.Program.Basics.

Lemma simulation1_star {C1 C2: Type}:
    forall step1 step2 (trans: C1 -> C2),
    simulation1 step1 step2 trans ->
    forall c1 c1', star step1 c1 c1' ->
    star step2 (trans c1) (trans c1').
Proof.
    introv Hsim.
    induction 1; intros; eauto with sequences.
Qed.

Lemma simulation2_vertical_concat {C1 C2 C3: Type}:
    forall step1 step2 step3 (trans1: C1 -> C2) (trans2: C2 -> C3),
        simulation1 step2 step3 trans2 ->
        simulation2 step1 step2 trans1 ->

        simulation2 step1 step3 (compose trans2 trans1)
        .
Proof.
    introv Hsim1 Hsim2.
    unfold simulation2 in *.
    introv Hstep1.
    destruct (Hsim2 _ _ Hstep1) as [target2 [Hc1target Hc1target']].
    {
        exists (trans2 target2).
        unfold compose.
        split; eapply simulation1_star; eauto.
    }
Qed.

Lemma simulation2_vertical_concat2 (C1 C2 C3: Type):
    forall step1 step2 step3 (trans1: C1 -> C2) (trans2: C2 -> C3),
        determinist step2 ->
        determinist step3 ->
        simulation2 step1 step2 trans1 ->
        simulation2 step2 step3 trans2 ->
        simulation2 step1 step3 (compose trans2 trans1).
Proof.
    introv Hdet2 Hdet3 Hsim1 Hsim2.
    introv Hstep11'.
    destruct (Hsim1 _ _ Hstep11') as [target2 [Htarget2 Htarget2']].

    destruct (simulation2_star _ _ _ Hsim2 Hdet3 _ _ Htarget2) as [t1 [Ht1 Ht1']].
    destruct (simulation2_star _ _ _ Hsim2 Hdet3 _ _ Htarget2') as [t2 [Ht2 Ht2']].
    unfold compose.

    edestruct (star_determnist_easy_to_use _ Hdet3 _ _ Ht1' _ Ht2')
    as [target [Htarget Htarget']].
    exists target; eauto with sequences.
Qed.
    


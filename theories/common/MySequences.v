(** A library of relation operators defining sequences of transitions
    and useful properties about them. Originally by Xavier Leroy, with
    some improvements and additions by François Pottier. *)

Require Import Classical.
Require Import Relation_Operators.
Require Import Operators_Properties.


Set Implicit Arguments.

Section SEQUENCES.

Variable A: Type.

Implicit Types R S : A -> A -> Prop.
Implicit Types P   : A -> Prop.

(** Zero, one or several transitions: reflexive, transitive closure of [R]. *)

Inductive star R : A -> A -> Prop :=
| star_refl:
    forall a,
    star R a a
| star_step:
    forall a b c,
    R a b -> star R b c -> star R a c.



    Lemma star_is_clos_trans_1n:
    forall R a b,
    star R a b <-> clos_refl_trans_1n A R a b.
  Proof.
    split; induction 1; econstructor; eauto.
  Qed.
  
  Theorem star_ind_clos_refl_trans
    : forall (R : A -> A -> Prop) (P : A -> A -> Prop),
      (forall x y : A, R x y -> P x y) ->
      (forall x : A, P x x) ->
      (forall x y z : A,
      star R x y ->
      P x y -> star R y z -> P y z -> P x z) ->
      forall x a : A, star R x a -> P x a.
  Proof.
    setoid_rewrite star_is_clos_trans_1n.
    setoid_rewrite <-clos_rt_rt1n_iff.
    intros ? ? ? ? ? ? ?.
    induction 1; eauto.
  Qed.
  
  Theorem star_ind_1n
    : forall (R : A -> A -> Prop) (P : A -> A -> Prop),
      (forall x : A, P x x) ->
      (forall x y z : A,
      R x y -> star R y z -> P y z -> P x z) ->
      forall x a : A, star R x a -> P x a.
  Proof.
    setoid_rewrite star_is_clos_trans_1n.
    intros ? ? ? ? ? ?.
    induction 1; eauto.
  Qed.
  
  Theorem star_ind_n1
    : forall (R : A -> A -> Prop) (x : A) (P : A -> Prop),
      P x ->
      (forall y z : A, R y z -> star R x y -> P y -> P z) ->
      forall a : A, star R x a -> P a
  .
  Proof.
    setoid_rewrite star_is_clos_trans_1n.
    setoid_rewrite <-clos_rt_rt1n_iff.
    setoid_rewrite clos_rt_rtn1_iff.
    intros ? ? ? ? ? ?.
    induction 1; eauto.
  Qed.
  
  
  Theorem star_step_1n:
    forall R x y z,  R x y -> star R y z -> star R x z.
  Proof.
    eapply star_step.
  Qed.
  
  Theorem star_step_n1:
    forall R x y z,  R y z -> star R x y -> star R x z.
  Proof.
    intros ? ? ? ? ?.
    induction 1; econstructor; eauto; econstructor. 
  Qed.
Hint Constructors star : star.

Lemma star_refl_eq:
  forall R a b, a = b -> star R a b.
Proof.
  intros. subst. eauto with star.
Qed.

Lemma star_one:
  forall R a b, R a b -> star R a b.
Proof.
  eauto with star.
Qed.

Lemma star_trans:
  forall R a b, star R a b ->
  forall c, star R b c -> star R a c.
Proof.
  induction 1; eauto with star.
Qed.

Lemma star_covariant:
  forall R S,
  (forall a b, R a b -> S a b) ->
  (forall a b, star R a b -> star S a b).
Proof.
  induction 2; eauto with star.
Qed.

(* If [R] preserves some property [P], then [star R] preserves [P]. *)

Lemma star_implication:
  forall P R,
  (forall a1 a2, R a1 a2 -> P a1 -> P a2) ->
  (forall a1 a2, star R a1 a2 -> P a1 -> P a2).
Proof.
  induction 2; eauto.
Qed.

(* The same implication holds in the reverse direction (right to left). *)

Lemma star_implication_reversed:
  forall P R,
  (forall a1 a2, R a1 a2 -> P a2 -> P a1) ->
  (forall a1 a2, star R a1 a2 -> P a2 -> P a1).
Proof.
  induction 2; eauto.
Qed.

(** One or several transitions: transitive closure of [R]. *)

Inductive plus R: A -> A -> Prop :=
| plus_left:
    forall a b c,
    R a b -> star R b c -> plus R a c.

Hint Constructors plus : plus.

Lemma plus_one:
  forall R a b, R a b -> plus R a b.
Proof.
  eauto with star plus.
Qed.

Lemma plus_star:
  forall R a b, plus R a b -> star R a b.
Proof.
  inversion 1; eauto with star.
Qed.

Lemma plus_covariant:
  forall R S,
  (forall a b, R a b -> S a b) ->
  (forall a b, plus R a b -> plus S a b).
Proof.
  induction 2; eauto using star_covariant with plus.
Qed.

(* A direct induction principle for [plus]: when [plus R a b] holds,
   either there is just one step, or there is one, followed with more. *)

Lemma plus_ind_direct:
  forall R P : A -> A -> Prop,
  (forall a b, R a b -> P a b) ->
  (forall a b c, R a b -> plus R b c -> P b c -> P a c) ->
  forall a b, plus R a b -> P a b.
Proof.
  intros ? ? Hone Hmore a c Hplus. destruct Hplus as [ ? b ? hR hRStar ].
  generalize b c hRStar a hR.
  clear b c hRStar a hR.
  induction 1; eauto with plus.
Qed.

Lemma plus_star_trans:
  forall R a b c, plus R a b -> star R b c -> plus R a c.
Proof.
  inversion 1; eauto using star_trans with plus.
Qed.

Lemma star_plus_trans:
  forall R a b c, star R a b -> plus R b c -> plus R a c.
Proof.
  inversion 1; inversion 1; eauto using star_trans with star plus.
Qed.

Lemma plus_trans:
  forall R a b c, plus R a b -> plus R b c -> plus R a c.
Proof.
  eauto using plus_star_trans, plus_star.
Qed.

Lemma plus_right:
  forall R a b c, star R a b -> R b c -> plus R a c.
Proof.
  eauto using star_plus_trans with star plus.
Qed.

(** Absence of transitions. *)

Definition irred R a :=
  forall b, ~ R a b.

Definition halts R a :=
  exists b, star R a b /\ irred R b.

(** Infinitely many transitions. *)

CoInductive infseq (R: A -> A -> Prop)  : A -> Prop :=
| infseq_step:
    forall a b,
    R a b -> infseq R b -> infseq R a.
  
Definition infseq' (R: A -> A -> Prop) (a: A) : Prop :=
  exists X: A -> Prop,
  X a /\ (forall a1, X a1 -> exists a2, R a1 a2 /\ X a2).

Lemma infseq_inv' (R: A -> A -> Prop):
  forall (a: A), infseq' R a -> exists b, R a b /\ infseq' R b.
Proof.
  intros a (X & Xa & XP). destruct (XP a Xa) as (b & Rab & Xb). 
  exists b; split; auto. exists X; auto.
Qed.

Require Import MyTactics.

Lemma infseq_inv (R: A -> A -> Prop):
  forall (a: A), infseq R a -> exists b, R a b /\ infseq R b.
Proof.
  intros a H.
  destruct H.
  exists b; eauto.
Qed.


Lemma infseq_equiv_infseq':
  forall R a, infseq R a <-> infseq' R a.
Proof.
  split; intros.
  * admit. 
  * admit.
Admitted.


(** Properties of [irred]. *)

Lemma irred_irred:
  forall R t1 u1,
  irred R t1 ->
  (forall u2, R u1 u2 -> exists t2, R t1 t2) ->
  irred R u1.
Proof.
  unfold irred. intros ? ? ? Hirred Himpl u2 Hu2.
  destruct (Himpl _ Hu2) as [ t2 Ht2 ].
  eapply Hirred. eauto.
Qed.

Lemma irreducible_terms_do_not_reduce:
  forall R a b, irred R a -> R a b -> False.
Proof.
  unfold irred, not. eauto.
Qed.

(** Coinduction principles to show the existence of infinite sequences. *)

Lemma infseq_coinduction_principle:
  forall R P,
  (forall a, P a -> exists b, R a b /\ P b) ->
  forall a, P a -> infseq R a.
Proof.
  intros ? ? Hstep. cofix COINDHYP; intros a hPa.
  destruct (Hstep a hPa) as (?&?&?).
  econstructor; eauto.
Qed.

Lemma infseq_coinduction_principle_2:
  forall R P a,
  P a ->
  (forall a, P a -> exists b, plus R a b /\ P b) ->
  infseq R a.
Proof.
  intros ? ? ? ? Hinv.
  apply infseq_coinduction_principle with
    (P := fun a => exists b, star R a b /\ P b).
  (* Proof that the invariant is preserved. *)
  { clear dependent a.
    intros a (b&hStar&hPb).
    inversion hStar; subst.
    { destruct (Hinv b hPb) as [c [hPlus ?]].
      inversion hPlus; subst. eauto. }
    { eauto. }
  }
  (* Proof that the invariant initially holds. *)
  { eauto with star. }
Qed.

Lemma infseq_coinduction_principle_3 :
  forall R, 
  forall (X: A -> Prop),
  (forall a, X a -> exists b, plus R a b /\ X b) ->
  forall a, X a -> infseq' R a.
Proof.
  intros R X H a0 Xa0. 
  exists (fun a => exists b, star R a b /\ X b); split.
- exists a0; auto using star_refl.
- intros a1 (a2 & S12 & X2). inversion S12; subst.
  + destruct (H a2 X2) as (a3 & P23 & X3). inversion P23; subst.
    exists b; split; auto. exists a3; auto.
  + exists b; split; auto. exists a2; auto.
Qed.

Lemma infseq_plus:
  forall R a,
  infseq (plus R) a ->
  infseq R a.
Proof.
  intros. eapply infseq_coinduction_principle_2
    with (P := fun a => infseq (plus R) a).
  { eauto. }
  clear dependent a. intros a hInfSeq.
  destruct hInfSeq. eauto.
Qed.

(** An example of use of [infseq_coinduction_principle]. *)

Lemma infseq_alternate_characterization:
  forall R a,
  (forall b, star R a b -> exists c, R b c) ->
  infseq R a.
Proof.
  intros R. apply infseq_coinduction_principle.
  intros a Hinv. destruct (Hinv a); eauto with star.
Qed.

Lemma infseq_covariant:
  forall R S,
  (forall a b, R a b -> S a b) ->
  forall a, infseq R a -> infseq S a.
Proof.
  intros. eapply infseq_coinduction_principle
  with (P := fun a => infseq R a); [| eauto ].
  clear dependent a. intros a hInfSeq.
  destruct hInfSeq. eauto.
Qed.

(** A sequence either is infinite or stops on an irreducible term.
    This property needs excluded middle from classical logic. *)

Lemma infseq_or_finseq:
  forall R a,
  infseq R a \/ halts R a.
Proof.
  intros.
  destruct (classic (forall b, star R a b -> exists c, R b c)).
  { left. eauto using infseq_alternate_characterization. }
  { right.
    destruct (not_all_ex_not _ _ H) as [b Hb].
    destruct (imply_to_and _ _ Hb).
    unfold halts, irred, not. eauto. }
Qed.

(** Additional properties for deterministic transition relations. *)

Section DETERMINISM.

Variable R : A -> A -> Prop.

Hypothesis R_determ: forall a b c, R a b -> R a c -> b = c.

Ltac R_determ :=
  match goal with h1: R ?a ?b1, h2: R ?a ?b2 |- _ =>
    assert (b1 = b2); [ eauto | subst ]
  end.

(** Uniqueness of transition sequences. *)

Lemma star_star_inv:
  forall a b, star R a b -> forall c, star R a c -> star R b c \/ star R c b.
Proof.
  induction 1; inversion 1; intros; subst; try R_determ; eauto with star.
Qed.

Lemma finseq_unique:
  forall a b b',
  star R a b -> irred R b ->
  star R a b' -> irred R b' ->
  b = b'.
Proof.
  unfold irred, not.
  intros ? ? ? Hab Hirred Hab' Hirred'.
  destruct (star_star_inv Hab Hab') as [ Hbb' | Hbb' ];
  inversion Hbb'; subst;
  solve [ eauto | elimtype False; eauto ].
Qed.

Lemma infseq_star_inv:
  forall a b, star R a b -> infseq R a -> infseq R b.
Proof.
  induction 1; inversion 1; intros; try R_determ; eauto.
Qed.

Lemma infseq_finseq_excl:
  forall a b,
  star R a b -> irred R b -> infseq R a -> False.
Proof.
  unfold irred, not. intros.
  assert (h: infseq R b). { eauto using infseq_star_inv. }
  inversion h. eauto.
Qed.

Lemma infseq_halts_excl:
  forall a,
  halts R a -> infseq R a -> False.
Proof.
  intros ? (?&?&?). eauto using infseq_finseq_excl.
Qed.

End DETERMINISM.

End SEQUENCES.

Global Hint Resolve star_refl star_step star_one star_trans plus_left plus_one
             plus_star plus_star_trans star_plus_trans plus_right: sequences.

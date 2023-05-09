Require Import MyTactics.
Require Import LCSyntax.

(* This technical lemma states that the renaming [lift 1] is injective. *)

Lemma lift_inj_EVar:
  forall t x,
  lift 1 t = EVar (S x) <-> t = EVar x.
Proof.
  split; intros.
  { eauto using lift_inj. }
  { subst. eauto. }
Qed.

(* -------------------------------------------------------------------------- *)

(* The predicate [fv] is characterized by the following lemmas. *)

Lemma fv_EVar_eq:
  forall k x,
  fv k (EVar x) <-> x < k.
Proof.
  unfold fv. asimpl. induction k; intros.
  (* Base case. *)
  { asimpl. split; intros; false.
    { unfold ids, Ids_term in *. injections.
      (* In Coq 8.12, this goal is solved by [lia], but not in Coq 8.10. *)
      eapply Nat.neq_succ_diag_l. eauto. }
    { lia. }
  }
  (* Step. *)
  { destruct x; asimpl.
    { split; intros. { lia. } { reflexivity. } }
    rewrite lift_inj_EVar. rewrite IHk. lia. }
Qed.

Lemma fv_ELam_eq:
  forall k t,
  fv k (ELam t) <-> fv (S k) t.
Proof.
  unfold fv. intros. asimpl. split; intros.
  { injections. eauto. }
  { unpack. congruence. }
Qed.

Lemma fv_EApp_eq:
  forall k t1 t2,
  fv k (EApp t1 t2) <-> fv k t1 /\ fv k t2.
Proof.
  unfold fv. intros. asimpl. split; intros.
  { injections. eauto. }
  { unpack. congruence. }
Qed.

Lemma fv_EMatch_eq:
  forall k tc t1 t2,
  fv k (EMatch tc t1 t2) <-> fv k tc /\ fv k t1 /\ fv (S k) t2.
Proof.
  unfold fv. intros. asimpl. split; intros.
  { injections. eauto. }
  { unpack. congruence. }
Qed.

Lemma fv_EVariantNone_eq:
  forall k,
  fv k EVariantNone.
Proof.
  unfold fv. intros. now asimpl.
Qed.

Lemma fv_EVariantSome_eq:
  forall k t,
  fv k (EVariantSome t) <-> fv k t.
Proof.
  unfold fv. intros. asimpl. split; intros.
  { injections. eauto. }
  { congruence. }
Qed.

#[export]
Hint Rewrite
  fv_EVar_eq
  fv_ELam_eq
  fv_EApp_eq
  fv_EVariantSome_eq
  fv_EVariantNone_eq
  fv_EMatch_eq: fv.

(* -------------------------------------------------------------------------- *)

(* The following lemmas allow decomposing a closedness hypothesis.
   Because [closed] is not an inductive notion, there is no lemma
   for [ELam]. *)

Lemma closed_EVar:
  forall x,
  closed (EVar x) ->
  False.
Proof.
  unfold closed; intros; fv. lia.
Qed.

Lemma closed_EAppL:
  forall t1 t2,
  closed (EApp t1 t2) ->
  closed t1.
Proof.
  unfold closed; intros; fv. tauto.
Qed.

Lemma closed_EAppR:
  forall t1 t2,
  closed (EApp t1 t2) ->
  closed t2.
Proof.
  unfold closed; intros; fv. tauto.
Qed.

Lemma closed_EMatchC:
  forall tc t1 t2,
  closed (EMatch tc t1 t2) -> closed tc.
Proof.
  unfold closed; intros; fv. tauto.
Qed.

Lemma closed_EMatchL:
  forall tc t1 t2,
  closed (EMatch tc t1 t2) -> closed t1.
Proof.
  unfold closed; intros; fv. tauto.
Qed.

Lemma closed_EVariantSome:
  forall t,
  closed (EVariantSome t) -> closed t.
Proof.
  unfold closed; intros; fv; tauto.
Qed.

Lemma closed_EVariantNone:
  closed EVariantNone.
Proof.
  unfold closed; intros; eapply fv_EVariantNone_eq.
Qed.

Global Hint Resolve
  closed_EVar
  closed_EAppL
  closed_EAppR
  closed_EMatchC
  closed_EMatchL
  closed_EVariantSome
  closed_EVariantNone
: closed.

(* -------------------------------------------------------------------------- *)

(* If the free variables of the term [t] are below [k], then [t] is unaffected
   by a substitution of the form [upn k sigma]. *)

Lemma fv_unaffected:
  forall t k sigma,
  fv k t ->
  t.[upn k sigma] = t.
Proof.
  induction t; intros; fv; unpack; asimpl;
  try solve [ eauto using upn_k_sigma_x with typeclass_instances
            | f_equal; eauto ].
Qed.
  
(* If the term [t] is closed, then [t] is unaffected by any substitution. *)

Lemma closed_unaffected:
  forall t sigma,
  closed t ->
  t.[sigma] = t.
Proof.
  intros. eapply fv_unaffected with (k := 0). eauto.
Qed.

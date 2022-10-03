Require Import MyTactics.
Require Import LCSyntax.

(* This technical lemma states that the renaming [lift 1] is injective. *)

Lemma lift_inj_Var:
  forall t x,
  lift 1 t = Var (S x) <-> t = Var x.
Proof.
  split; intros.
  { eauto using lift_inj. }
  { subst. eauto. }
Qed.

(* -------------------------------------------------------------------------- *)

(* The predicate [fv] is characterized by the following lemmas. *)

Lemma fv_Var_eq:
  forall k x,
  fv k (Var x) <-> x < k.
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
    rewrite lift_inj_Var. rewrite IHk. lia. }
Qed.

Lemma fv_Lam_eq:
  forall k t,
  fv k (Lam t) <-> fv (S k) t.
Proof.
  unfold fv. intros. asimpl. split; intros.
  { injections. eauto. }
  { unpack. congruence. }
Qed.

Lemma fv_App_eq:
  forall k t1 t2,
  fv k (App t1 t2) <-> fv k t1 /\ fv k t2.
Proof.
  unfold fv. intros. asimpl. split; intros.
  { injections. eauto. }
  { unpack. congruence. }
Qed.

Lemma fv_Let_eq:
  forall k t1 t2,
  fv k (Let t1 t2) <-> fv k t1 /\ fv (S k) t2.
Proof.
  unfold fv. intros. asimpl. split; intros.
  { injections. eauto. }
  { unpack. congruence. }
Qed.

Lemma fv_Match_eq:
  forall k tc t1 t2,
  fv k (Match tc t1 t2) <-> fv k tc /\ fv k t1 /\ fv (S k) t2.
Proof.
  unfold fv. intros. asimpl. split; intros.
  { injections. eauto. }
  { unpack. congruence. }
Qed.

Lemma fv_VariantNone_eq:
  forall k,
  fv k VariantNone.
Proof.
  unfold fv. intros. now asimpl.
Qed.

Lemma fv_VariantSome_eq:
  forall k t,
  fv k (VariantSome t) <-> fv k t.
Proof.
  unfold fv. intros. asimpl. split; intros.
  { injections. eauto. }
  { congruence. }
Qed.


Hint Rewrite
  fv_Var_eq
  fv_Lam_eq
  fv_App_eq
  fv_Let_eq
  fv_VariantSome_eq
  fv_VariantNone_eq
  fv_Match_eq: fv.

(* -------------------------------------------------------------------------- *)

(* The following lemmas allow decomposing a closedness hypothesis.
   Because [closed] is not an inductive notion, there is no lemma
   for [Lam] and for the right-hand side of [Let]. *)

Lemma closed_Var:
  forall x,
  closed (Var x) ->
  False.
Proof.
  unfold closed; intros; fv. lia.
Qed.

Lemma closed_AppL:
  forall t1 t2,
  closed (App t1 t2) ->
  closed t1.
Proof.
  unfold closed; intros; fv. tauto.
Qed.

Lemma closed_AppR:
  forall t1 t2,
  closed (App t1 t2) ->
  closed t2.
Proof.
  unfold closed; intros; fv. tauto.
Qed.

Lemma closed_LetL:
  forall t1 t2,
  closed (Let t1 t2) ->
  closed t1.
Proof.
  unfold closed; intros; fv. tauto.
Qed.

Lemma closed_MatchC:
  forall tc t1 t2,
  closed (Match tc t1 t2) -> closed tc.
Proof.
  unfold closed; intros; fv. tauto.
Qed.

Lemma closed_MatchL:
  forall tc t1 t2,
  closed (Match tc t1 t2) -> closed t1.
Proof.
  unfold closed; intros; fv. tauto.
Qed.

Lemma closed_VariantSome:
  forall t,
  closed (VariantSome t) -> closed t.
Proof.
  unfold closed; intros; fv; tauto.
Qed.

Lemma closed_VariantNone:
  closed VariantNone.
Proof.
  unfold closed; intros; eapply fv_VariantNone_eq.
Qed.

Global Hint Resolve
  closed_Var
  closed_AppL
  closed_AppR
  closed_LetL
  closed_MatchC
  closed_MatchL
  closed_VariantSome
  closed_VariantNone
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

Require Import LCSyntax.
Require Import STLCDefinition.
Require Import STLCTypeSoundness.
Require Import LCReduction.
Require Import MySequences.
Require Import MyTactics.

Fail Inductive R : ty -> term -> Prop :=
| Rvar : forall x t,
  (forall Gamma, jt Gamma t (TyVar x)) ->
  halts cbv t ->
  R (TyVar x) t
| Rapp : forall t T1 T2,
  halts cbv t ->
  (forall Gamma, jt Gamma t (TyFun T1 T2)) ->
  (forall s, R T1 s -> R T2 (App t s)) ->
  R (TyFun T1 T2) t
.


Fixpoint R (T: ty) (t: term) : Prop :=
  (forall Gamma, jt Gamma t T) /\ closed t /\ halts cbv t /\
  match T with
  | TyVar _ => True
  | TyFun T1 T2 =>
    (forall s, R T1 s -> R T2 (App t s))
  | TyOption T => True
  end
.


Lemma R_unfold:
  forall T t, R T t = (
  (forall Gamma, jt Gamma t T) /\ closed t /\ halts cbv t /\
  match T with
  | TyVar _ => True
  | TyFun T1 T2 =>
    (forall s, R T1 s -> R T2 (App t s))
  | TyOption T => True
  end)
.
Proof.
  intros; case T; simpl; try reflexivity.
Qed.
  

Lemma R_halts: forall T t, R T t -> halts cbv t.
Proof.
  induction T; intros; unfold R in *; unpack; eauto.
Qed.

Lemma R_typable: forall T t, R T t -> forall Gamma, jt Gamma t T.
Proof.
  induction T; intros; unfold R in *; unpack; eauto.
Qed.

Lemma cbv_preserves_halt:
  forall t t', cbv t t' -> halts cbv t -> halts cbv t'.
Proof.
  unfold halts.
  intros; unpack.
  induction H0.
  * unfold irred in *.
    false; eapply H1; eauto.
  * forwards: cbv_deterministic H H0; subst.
    eauto.
Qed.

Lemma cbv_preserves_closed:
  forall t t', cbv t t' -> closed t -> closed t'.
Proof.
  intros.
  induction H;
    try solve [ false; eauto 3 with obvious ];
    try solve [ unfold closed in *; fv; repeat split; unpack; eauto ].
  * unfold closed in *; fv.
    admit.
  * unfold closed in *; fv.
    admit.
  * unfold closed in *; fv.
    admit.
Admitted.




Lemma cbv_preserves_R:
  forall T t t', cbv t t' -> R T t -> R T t'.
Proof.
  induction T; intros; unfold R in *.
  * unpack; repeat split; intros;
    eauto using
      jt_preservation,
      cbv_preserves_closed,
      cbv_preserves_halt.
  * fold R in *; unpack; repeat split; intros;
    eauto using
      jt_preservation,
      cbv_preserves_closed,
      cbv_preserves_halt.
    - eapply IHT2.
      { eapply RedAppL; simpl; eauto. }
      eauto.
  * admit.
Admitted.

Lemma cbvstar_preserves_R:
  forall T t t', star cbv t t' -> R T t -> R T t'.
Proof.
  intros.
  induction H; eauto using cbv_preserves_R.
Qed.

Lemma halt_inv:
  forall t t', cbv t t' -> halts cbv t' -> halts cbv t.
Proof.
  unfold halts; intros; unpack.
  eexists; split; eauto. eauto with sequences.
Qed.

Lemma empty_typed_is_closed:
  forall t T, (forall Gamma, jt Gamma t T) -> closed t.
Proof.
  admit.
Admitted.





Lemma cbv_preserves_R_inv:
  forall T t t', (forall Gamma, jt Gamma t T) -> cbv t t' -> R T t' -> R T t.
Proof.
  induction T; intros; unfold R in *.
  * unpack; repeat split; intros;
    eauto using
      jt_preservation,
      cbv_preserves_closed,
      cbv_preserves_halt,
      empty_typed_is_closed,
      halt_inv.
  * fold R in *; unpack; repeat split; intros;
    eauto using
      jt_preservation,
      cbv_preserves_closed,
      cbv_preserves_halt,
      empty_typed_is_closed,
      halt_inv.
    - eapply IHT2.
      unfold R in H5; induction T1; unpack; fold R in *.
      { admit. } { admit. } { admit. }
      { eapply RedAppL; simpl; eauto. }
      eauto.
  * admit.
Admitted.

Print Acc.
Inductive Acc (A : Type) (R : A -> A -> Prop) (x : A) : Prop :=
  Acc_intro: (forall y: A, R y x -> Acc A R y) -> Acc A R x.

(* RPO *)


Lemma strong: forall Gamma T t, jt Gamma t T -> R T t.
Proof.
  intros.
  induction T.
  * admit.
  * admit.
  * admit.
Admitted.
(*
  * econstructor.
    induction H; subst; tryfalse.
    - econstructor.
      exists (Var x0); split; eauto with sequences.
      unfold irred; repeat intro. invert_cbv.
    - exists (Lam t); split; eauto with sequences.
      unfold irred; repeat intro. invert_cbv.
*)
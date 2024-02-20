Require Export Autosubst.Autosubst.
Require Export AutosubstExtra.
Require Import String.
Require Import Coq.ZArith.ZArith.

Require Import tactics.

Inductive op :=
  | Add
  | Eq
.

Inductive term :=
  (* Lambda calculus part of the language*)
  | Var (x: var)
  | App (t1 t2: term)
  | Lam (t: {bind term})

  (* Default fragment of the language. *)
  | ErrorOnEmpty (arg: term)
  | DefaultPure (arg: term)
  | Default (ts: list term) (tj tc: term)
  | Empty
  | Conflict

  (* value computating fragment of the language*)
  | Value (v: value)
  | FreeVar (x: string) (* external variables *)
  | Binop (op: op) (t1 t2: term)

  | Match_ (u t1: term) (t2: {bind term})
  | ENone
  | ESome (t: term)
  | Fold (f: term) (ts: list term) (t: term)

  | If (t ta tb: term)

with value :=
  | Bool (b: bool)
  | Int (i: Z)
  | Closure (t: {bind term}) (sigma: list value)
  | VNone
  | VUnit
  | VSome (v: value)
  | VPure (v: value)
.


Require Import Autosubst_FreeVars.
#[export] Instance Ids_term : Ids term. derive. Defined.
#[export] Instance Idslemmas_term : IdsLemmas term.
  econstructor.
  unfold ids, Ids_term.
  intros; inj; eauto.
Defined.
#[export] Instance Rename_term : Rename term. derive. Defined.
#[export] Instance Subst_term : Subst term. derive. Defined.
#[export] Instance SubstLemmas_term : SubstLemmas term. derive. Qed.

Lemma ids_inj:
  forall x y, ids x = ids y -> x = y.
intros; inj; eauto.
Qed.



(* -------------------------------------------------------------------------- *)
(** autosubst and lists*)

Lemma subst_app:
  forall ts1 ts2 sigma,
  ((ts1 ++ ts2)..[sigma] = ts1..[sigma] ++ ts2..[sigma])%list.
Proof.
  induction ts1; intros; asimpl; eauto.
  * now rewrite IHts1.
Qed.

Lemma subst_cons:
  forall ti ts sigma,
  ((ti::ts)..[sigma] = (ti.[sigma] :: ts..[sigma]))%list.
Proof.
  autosubst.
Qed.


Global Hint Resolve
  subst_app
  subst_cons: autosubst.

Global Hint Rewrite subst_app subst_cons: autosubst.



Definition get_op op i1 i2 :=
  match op, i1, i2 with
  | Add, Int i1, Int i2 => Some (Int (Z.add i1 i2))
  | Eq, Int i1, Int i2 => Some (Bool (Z.eqb i1 i2))
  | _, _, _ => None
  end.

Definition value_eqb (v1 v2 : value) : bool :=
  match v1, v2 with
  | Bool b1, Bool b2 => Bool.eqb b1 b2
  | Int i1, Int i2 => Z.eqb i1 i2
  | _, _ => false
  end.

Require Import Autosubst_FreeVars.

Lemma lift_inj_EVar:
  forall t x,
  lift 1 t = Var (S x) <-> t = Var x.
Proof.
  split; intros.
  { eauto using lift_inj. }
  { subst. eauto. }
Qed.

Lemma fv_Var_eq:
  forall k x,
  fv k (Var x) <-> x < k.
Proof.
  unfold fv. asimpl. induction k; intros.
  (* Base case. *)
  { asimpl. split; intros; exfalso.
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

Lemma fv_Binop_eq:
  forall k op t1 t2,
  fv k (Binop op t1 t2) <-> fv k t1 /\ fv k t2.
Proof.
  unfold fv. intros. asimpl. split; intros.
  { injections. eauto. }
  { unpack. congruence. }
Qed.

Lemma fv_Match_eq:
  forall k tc t1 t2,
  fv k (Match_ tc t1 t2) <-> fv k tc /\ fv k t1 /\ fv (S k) t2.
Proof.
  unfold fv. intros. asimpl. split; intros.
  { injections. eauto. }
  { unpack. congruence. }
Qed.


Lemma fv_If_eq:
  forall k t ta tb,
  fv k (If t ta tb) <-> fv k t /\ fv k ta /\ fv k tb.
Proof.
  unfold fv. intros. asimpl. split; intros.
  { injections. eauto. }
  { unpack. congruence. }
Qed.

Lemma fv_VariantNone_eq:
  forall k,
  fv k ENone.
Proof.
  unfold fv. intros. now asimpl.
Qed.

Lemma fv_VariantSome_eq:
  forall k t,
  fv k (ESome t) <-> fv k t.
Proof.
  unfold fv. intros. asimpl. split; intros.
  { injections. eauto. }
  { congruence. }
Qed.

Lemma fv_ErrorOnEmpty_eq:
  forall k t,
  fv k (ErrorOnEmpty t) <-> fv k t.
Proof.
  unfold fv. intros. asimpl. split; intros.
  { injections. eauto. }
  { congruence. }
Qed.

Lemma fv_DefaultPure_eq:
  forall k t,
  fv k (DefaultPure t) <-> fv k t.
Proof.
  unfold fv. intros. asimpl. split; intros.
  { injections. eauto. }
  { congruence. }
Qed.

Lemma thing: forall ts sigma,
  ts..[sigma] = ts <-> List.Forall (fun ti : term => ti.[sigma] = ti) ts.
Proof.
  induction ts.
  * split; intros; eauto.
  * split; intros; msimpl in *.
    - injections.
      econstructor; eauto.
      { apply IHts. eauto. }
    - inversion H.
      f_equal; [eauto | now eapply IHts].
Qed.

Lemma fv_Default_eq:
  forall k ts tj tc,
  fv k (Default ts tj tc) <->
    (List.Forall (fun ti => fv k ti) ts) /\ fv k tj /\ fv k tc.
Proof.
  unfold fv. intros. asimpl. split; intros.
  { injections. repeat split; eauto.
    { apply thing; assumption. }
  }
  { unpack. rewrite H0; rewrite H1.
    remember (thing ts (upn k (ren (+1)))).
    destruct i.
    remember (e H).
    rewrite e0.
    reflexivity. }
Qed.

Lemma fv_Fold_eq:
  forall k f ts acc,
  fv k (Fold f ts acc)  <-> fv k f /\ (List.Forall (fv k) ts) /\ fv k acc.
Proof.
  unfold fv. intros. asimpl. split; intros.
  { injections. repeat split; eauto.
    { eapply thing; assumption. }
  }
  { unpack. rewrite H, H1; repeat f_equal.
    pose proof (thing ts) as Hrw.
    rewrite Hrw.
    eauto.
  }
Qed.


Lemma fv_Value_eq:
  forall k v,
  fv k (Value v) <-> True.
Proof.
  unfold fv. intros. asimpl. split; eauto.
Qed.

#[export]
Hint Rewrite
  fv_Var_eq
  fv_Lam_eq
  fv_App_eq
  fv_VariantSome_eq
  fv_VariantNone_eq
  fv_Match_eq
  fv_Binop_eq
  fv_Default_eq
  fv_ErrorOnEmpty_eq
  fv_DefaultPure_eq
  fv_Value_eq
  fv_Fold_eq
  : fv.

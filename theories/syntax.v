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

Import List.ListNotations.
Require Import Autosubst_FreeVars.
Open Scope list.
  
Definition subst_of_env sigma :=
  fun n =>
  match List.nth_error sigma n with
  | None => ids (n - List.length sigma)
  | Some t => Value t
  end
.

Notation "'soe' sigma n" := (
match List.nth_error sigma n with
| None => ids (n - List.length sigma)
| Some t => Value t
end)
(at level 69, sigma at level 1, n at level 1).

Theorem soe_nil:
  subst_of_env [] = ids.
Proof.
  eapply FunctionalExtensionality.functional_extensionality.
  induction x; eauto.
Qed.

Lemma soe_cons v sigma:
  subst_of_env (v :: sigma) = (Value v) .: subst_of_env sigma.
Proof.
  eapply FunctionalExtensionality.functional_extensionality.
  induction x; asimpl; eauto.
Qed.

Theorem subst_env_regular:
  forall sigma: list value,
  regular (subst_of_env sigma).
Proof.
  intros.
  exists (List.length sigma), 0.
  eapply FunctionalExtensionality.functional_extensionality.
  unfold subst_of_env; intros; asimpl.
  destruct (List.nth_error_None sigma (List.length sigma + x)) as [_ H].
  rewrite H.
  f_equal.
  all: lia.
Qed.

Lemma subst_env_0: forall t v, t.[subst_of_env [v]] = t.[Value v/].
Proof.
  intros.
  repeat progress (
    try rewrite soe_nil;
    try rewrite soe_cons;
    try reflexivity).
Qed.

Lemma subst_env_fv_sub:
  forall sigma t k,
    fv k t ->
    fv (k-List.length sigma) (t.[subst_of_env sigma]).
Proof.
  induction sigma.
  * rewrite soe_nil.
    intros; asimpl.
    replace (k - 0) with k.
    all: eauto; lia.
  * rewrite soe_cons.
    intros.
    asimpl.
    replace t.[Value a .: subst_of_env sigma] with (t.[Value a/].[subst_of_env sigma]) by autosubst.
    replace (k - S (List.length sigma)) with (pred k - (List.length sigma)) by lia.
    eapply IHsigma.
    { induction k; asimpl; eauto.
      { replace 0 with (0 - 1) by lia.
        eapply fv_closed_kregular_subst; eauto.
        { induction x; asimpl; unfold closed; fv; lia. }
      }
      { replace k with (S k - 1) by lia.
        eapply fv_closed_kregular_subst; eauto.
        { induction x; asimpl; unfold closed; fv; lia. }
      }
    }
Qed.

Lemma subst_env_fv_closed:
  forall sigma t,
    fv (List.length sigma) t ->
    closed (t.[subst_of_env sigma]).
Proof.
  unfold closed.
  intros.
  replace 0 with (List.length sigma - List.length sigma) by lia.
  eapply subst_env_fv_sub.
  eauto.
Qed.

(* Strong induction princple for terms and values *)

Theorem term_value_ind
  : forall (P : term -> Prop) (P0 : value -> Prop),
      (forall x : var, P (Var x)) ->
      (forall t1 : term, P t1 -> forall t2 : term, P t2 -> P (App t1 t2)) ->
      (forall t : {bind term}, P t -> P (Lam t)) ->
      (forall arg : term, P arg -> P (ErrorOnEmpty arg)) ->
      (forall arg : term, P arg -> P (DefaultPure arg)) ->
      (forall (ts : list term), List.Forall P ts -> forall (tj : term),
       P tj -> forall tc : term, P tc -> P (Default ts tj tc)) ->
      P Empty ->
      P Conflict ->
      (forall v : value, P0 v -> P (Value v)) ->
      (forall x : string, P (FreeVar x)) ->
      (forall (op : op) (t1 : term),
       P t1 -> forall t2 : term, P t2 -> P (Binop op t1 t2)) ->
      (forall u : term,
       P u ->
       forall t1 : term,
       P t1 -> forall t2 : {bind term}, P t2 -> P (Match_ u t1 t2)) ->
      P ENone ->
      (forall t : term, P t -> P (ESome t)) ->
      (forall f : term,
       P f -> forall (ts : list term), List.Forall P ts -> forall (t : term), P t -> P (Fold f ts t)) ->
      (forall t : term,
       P t ->
       forall ta : term, P ta -> forall tb : term, P tb -> P (If t ta tb)) ->
      (forall b : bool, P0 (Bool b)) ->
      (forall i : Z, P0 (Int i)) ->
      (forall t : {bind term},
       P t -> forall sigma : list value, List.Forall P0 sigma -> P0 (Closure t sigma)) ->
      P0 VNone ->
      P0 VUnit ->
      (forall v : value, P0 v -> P0 (VSome v)) ->
      (forall v : value, P0 v -> P0 (VPure v)) ->
      (forall t : term, P t) /\ (forall v : value, P0 v).
Admitted.


Inductive sim_term : term -> term -> Prop :=
  | sim_term_var : forall x y, x = y -> sim_term (Var x) (Var y)
  | sim_term_app : forall t1 t2 u1 u2,
      sim_term t1 u1 ->
      sim_term t2 u2 ->
      sim_term (App t1 t2) (App u1 u2)
  | sim_term_lam : forall t1 u1,
      sim_term t1 u1 ->
      sim_term (Lam t1) (Lam u1)
  | sim_term_value : forall v1 w1,
      sim_value v1 w1 ->
      sim_term (Value v1) (Value w1)
  | sim_term_erroronempty : forall t1 t2,
      sim_term t1 t2 ->
      sim_term (ErrorOnEmpty t1) (ErrorOnEmpty t2)
  | sim_term_defaultpure : forall t1 t2,
      sim_term t1 t2 ->
      sim_term (DefaultPure t1) (DefaultPure t2)
  | sim_term_default : forall ts1 ts2 tj1 tj2 tc1 tc2,
      List.Forall2 sim_term ts1 ts2 ->
      sim_term tj1 tj2 ->
      sim_term tc1 tc2 ->
      sim_term (Default ts1 tj1 tc1) (Default ts2 tj2 tc2)
  | sim_term_empty : sim_term Empty Empty
  | sim_term_conflict : sim_term Conflict Conflict
  | sim_term_freevar : forall x y, x = y -> sim_term (FreeVar x) (FreeVar y)
  | sim_term_binop : forall op1 op2 t1 t2 u1 u2,
      op1 = op2 ->
      sim_term t1 u1 ->
      sim_term t2 u2 ->
      sim_term (Binop op1 t1 t2) (Binop op2 u1 u2)
  | sim_term_match : forall u1 u2 t1 t2 t3 t4,
      sim_term u1 u2 ->
      sim_term t1 t2 ->
      sim_term t3 t4 ->
      sim_term (Match_ u1 t1 t3) (Match_ u2 t2 t4)
  | sim_term_enone : sim_term ENone ENone
  | sim_term_esome : forall t1 t2,
      sim_term t1 t2 ->
      sim_term (ESome t1) (ESome t2)
  | sim_term_fold : forall f1 f2 ts1 ts2 t1 t2,
      sim_term f1 f2 ->
      List.Forall2 sim_term ts1 ts2 ->
      sim_term t1 t2 ->
      sim_term (Fold f1 ts1 t1) (Fold f2 ts2 t2)
  | sim_term_if : forall t1 t2 ta1 ta2 tb1 tb2,
      sim_term t1 t2 ->
      sim_term ta1 ta2 ->
      sim_term tb1 tb2 ->
      sim_term (If t1 ta1 tb1) (If t2 ta2 tb2)

with sim_value : value -> value -> Prop :=
  | sim_value_bool : forall b1 b2,
      b1 = b2 ->
      sim_value (Bool b1) (Bool b2)
  | sim_value_int : forall i1 i2,
      i1 = i2 ->
      sim_value (Int i1) (Int i2)
  | sim_value_closure : forall t1 t2 sigma1 sigma2,
      sim_term t1.[up (subst_of_env sigma1)] t2.[up (subst_of_env sigma2)] ->
      sim_value (Closure t1 sigma1) (Closure t2 sigma2)
  | sim_value_vnone : sim_value VNone VNone
  | sim_value_vunit : sim_value VUnit VUnit
  | sim_value_vsome : forall v1 v2,
      sim_value v1 v2 ->
      sim_value (VSome v1) (VSome v2)
  | sim_value_vpure : forall v1 v2,
      sim_value v1 v2 ->
      sim_value (VPure v1) (VPure v2).

Require Import Coq.Classes.SetoidClass.

Lemma sim_term_ren:
  forall t1 t2,
    sim_term t1 t2 ->
    forall xi,
      sim_term t1.[ren xi] t2.[ren xi].
Proof.
  induction 1; intros; subst; asimpl.
  all: try econstructor; eauto.
  { induction H; simpl; econstructor; eauto. admit "need stronger induction priple". }
  { induction H0; simpl; econstructor; eauto. admit "need stronger induction priple". }
Admitted.

Lemma sim_term_subst:
  forall t1 t2,
    sim_term t1 t2 ->
    forall sigma1 sigma2,
      (forall x, sim_term (sigma1 x) (sigma2 x)) ->
      sim_term t1.[sigma1] t2.[sigma2].
Proof.
  induction 1; intros; subst; asimpl.
  all: try econstructor; eauto.
  { eapply IHsim_term.
    induction x; asimpl.
    { econstructor; eauto. }
    { eapply sim_term_ren; eauto. }
  }
  { induction H; asimpl; econstructor; eauto. admit "need stronger induction priple". }
  { eapply IHsim_term3.
    induction x; asimpl.
    { econstructor; eauto. }
    { eapply sim_term_ren; eauto. }
  }
  { induction H0; asimpl; econstructor; eauto. admit "need stronger induction priple". }
Admitted.


Lemma sim_term_refl: Reflexive sim_term /\ Reflexive sim_value.
Proof.
  eapply term_value_ind; intros.
  all: try (econstructor; eauto).
  { induction H; econstructor; eauto. }
  { induction H0; econstructor; eauto. }
  {
    eapply sim_term_subst.
    { eauto. }
    { intro x; case x; asimpl.
      { econstructor; eauto. }
      { intros; eapply sim_term_ren.
        revert n.
        induction sigma.
        { rewrite soe_nil; econstructor; eauto. }
        { inversion H0; subst; intros. case n; asimpl.
          { econstructor; eauto. }
          { intros. rewrite soe_cons.
            eapply IHsigma; eauto.
          }
        }
      }
    }
  }
Qed.


Instance Reflexive_sim_term : Reflexive sim_term. eapply sim_term_refl. Qed. 
Instance Symmetric_sim_term : Symmetric sim_term. Admitted.
Instance Transtive_sim_term : Transitive sim_term. Admitted.


Instance Reflexive_sim_value : Reflexive sim_value. eapply sim_term_refl. Qed. 
Instance Symmetric_sim_value : Symmetric sim_value. Admitted.
Instance Transtive_sim_value : Transitive sim_value. Admitted.

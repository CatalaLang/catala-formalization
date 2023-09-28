Require Import syntax sequences.
Import List.ListNotations.
Require Import Autosubst_FreeVars.
Open Scope list.

Require Import tactics.

Definition is_value v :=
    match v with
    | Value _ => True
    | _ => False
    end.

Definition subst_of_env sigma :=
  fun n =>
  match List.nth_error sigma n with
  | None => ids (n - List.length sigma)
  | Some t => Value t
  end
.

Theorem subst_env_nil:
  subst_of_env [] = ids.
Proof.
  eapply FunctionalExtensionality.functional_extensionality.
  induction x; eauto.
Qed.

Lemma subst_env_cons v sigma:
  subst_of_env (v :: sigma) = (Value v) .: subst_of_env sigma.
Proof.
  eapply FunctionalExtensionality.functional_extensionality.
  induction x; asimpl; eauto.
Qed.

Theorem subst_env_regular:
  forall sigma,
  regular (subst_of_env sigma).
Proof.
  intros.
  exists (length sigma), 0.
  eapply FunctionalExtensionality.functional_extensionality.
  unfold subst_of_env; intros; asimpl.
  destruct (List.nth_error_None sigma (length sigma + x)) as [_ H].
  rewrite H.
  f_equal.
  all: lia.
Qed.

Lemma subst_env_0: forall t v, t.[subst_of_env [v]] = t.[Value v/].
Proof.
  intros.
  repeat progress (
    try rewrite subst_env_nil;
    try rewrite subst_env_cons;
    try reflexivity).
Qed.

Lemma subst_env_fv_sub:
  forall sigma t k,
    fv k t ->
    fv (k-List.length sigma) (t.[subst_of_env sigma]).
Proof.
  induction sigma.
  * rewrite subst_env_nil.
    intros; asimpl.
    replace (k - 0) with k.
    all: eauto; lia.
  * rewrite subst_env_cons.
    intros.
    asimpl.
    replace t.[Value a .: subst_of_env sigma] with (t.[Value a/].[subst_of_env sigma]) by autosubst.
    replace (k - S (length sigma)) with (pred k - (length sigma)) by lia.
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
  replace 0 with (length sigma - length sigma) by lia.
  eapply subst_env_fv_sub.
  eauto.
Qed.

Inductive sred: term -> term -> Prop :=
  | sred_beta:
    forall t v sigma',
      sred
        (App (Value (Closure t sigma')) (Value v))
        (t.[subst_of_env (v :: sigma')])
  | sred_lam:
    forall t,
      sred
        (Lam t)
        (Value (Closure t []))
  | sred_app_left:
    forall t1 t2 u,
      sred (t1) (t2) ->
      sred
        (App t1 u)
        (App t2 u)

   | sred_app_right:
    forall t u1 u2 sigma,
      sred (u1) (u2) ->
      sred
        (App (Value (Closure t sigma)) u1)
        (App (Value (Closure t sigma)) u2)
  | sred_binop_left:
    forall op t1 t2 u,
      sred (t1) (t2) ->
      sred
        (Binop op t1 u)
        (Binop op t2 u)
  | sred_binop_right:
    forall op v u1 u2,
      sred (u1) (u2) ->
      sred
        (Binop op (Value v) u1)
        (Binop op (Value v) u2)
  | sred_binop_finish:
    forall op v v1 v2,
    Some v = get_op op v1 v2 ->
    sred
      (Binop op (Value v1) (Value v2))
      (Value v)

  (** Conflict & Empty handling *)
  | sred_app_right_conflict:
    forall u,
      sred (App Conflict u) Conflict
  | sred_app_right_empty:
    forall u,
      sred (App Empty u) Empty
  | sred_app_left_conflict:
      forall t sigma,
        sred
          (App (Value (Closure t sigma)) Conflict)
          Conflict
  | sred_app_left_empty:
    forall t sigma,
      sred
        (App (Value (Closure t sigma)) Empty)
        (Empty)

  | sred_defaultConflict:
    forall ts ts1 vi ts2 vj ts3 tjust tcons,
      List.Forall (eq Empty) ts1 ->
      List.Forall (eq Empty) ts2 ->
      ts = (ts1 ++ (Value vi) :: ts2 ++ (Value vj) :: ts3)%list ->
      sred (Default ts tjust tcons) Conflict
  | sred_DefaultEValue:
    forall ts1 vi ts2 tjust tcons,
      List.Forall (eq Empty) ts1 ->
      List.Forall (eq Empty) ts2 ->
      sred (Default (ts1++(Value vi)::ts2) tjust tcons) (Value vi)
  | sred_DefaultEConflict:
    forall ts1 ts2 tjust tcons,
      List.Forall (eq Empty) ts1 ->
      sred (Default (ts1++Conflict::ts2) tjust tcons) Conflict
 | sred_DefaultE_empty:
    forall ts1 ti ti' ts2 tj tc,
      sred ti ti' ->
      (List.Forall (eq Empty) ts1) ->
      sred (Default (ts1++ti::ts2) tj tc) (Default (ts1++ti'::ts2) tj tc)
  | sred_DefaultE_one:
    forall ts1 vi ts2 tj tj' ts3 tjust tcons,
      sred tj tj' ->
      (List.Forall (eq Empty) ts1) ->
      (List.Forall (eq Empty) ts2) ->
      sred
        (Default (ts1++(Value vi)::ts2++tj::ts3) tjust tcons)
        (Default (ts1++(Value vi)::ts2++tj'::ts3) tjust tcons)
  | sred_DefaultJ:
    forall ts tj1 tj2 tc,
      List.Forall (eq Empty) ts ->
      sred tj1 tj2 ->
      sred (Default ts tj1 tc) (Default ts tj2 tc)
  | sred_DefaultJTrue:
    forall ts tc,
      List.Forall (eq Empty) ts ->
      sred (Default ts (Value (Bool true)) tc) tc
  | sred_DefaultJFalse:
    forall ts tc,
      List.Forall (eq Empty) ts ->
      sred (Default ts (Value (Bool false)) tc) Empty
  | sred_DefaultJEmpty:
    forall ts tc,
      List.Forall (eq Empty) ts ->
      sred (Default ts Empty tc) Empty
  | sred_DefaultJConflict:
    forall ts tc,
      List.Forall (eq Empty) ts ->
      sred (Default ts Conflict tc) Conflict
  | sred_match_cond:
    forall u1 u2 t1 t2,
      sred u1 u2 ->
      sred (Match_ u1 t1 t2) (Match_ u2 t1 t2)
  | sred_match_None:
    forall t1 t2,
      sred (Match_ (Value (VNone)) t1 t2) t1
  | sred_match_Some:
    forall v t1 t2,
      sred (Match_ (Value (VSome v)) t1 t2) t2.[Value v/]
  | sred_None:
    sred ENone (Value VNone)
  | sred_Some_context:
    forall t1 t2,
      sred t1 t2 ->
      sred (ESome t1) (ESome t2)
  | sred_Some:
    forall v,
      sred (ESome (Value v)) (Value (VSome v))
.

Lemma remove_head_empty {ts1 ts1' ti ti' ts2 ts2'}:
  List.Forall (eq Empty) ts1 ->
  List.Forall (eq Empty) ts1' ->
  ti <> Empty ->
  ti' <> Empty ->
  ts1 ++ ti :: ts2 = ts1' ++ ti' :: ts2' ->
  ts1 = ts1' /\ ti = ti' /\ ts2 = ts2'
.
Proof.
  intros Hts1 Hts1'.
  revert Hts1 ts1' Hts1' ts2 ts2' ti ti'.
  induction 1; inversion 1; simpl.
  { intros; injections; eauto.  }
  { intros; injections; congruence. }
  { intros; injections; congruence. }
  { intros; injections.
    destruct (IHHts1 _ H1 _ _ _ _ H3 H4 H5); unpack; subst.
    eauto.
   }
Qed.

Lemma sred_nonempty_conflict_value {ti ti'}:
  sred ti ti' ->
  ti <> Empty /\ ti <> Conflict /\ forall v, ti <> Value v.
Proof.
  intros Hsred; repeat split; repeat intro; subst; inversion Hsred.
Qed.

Lemma value_notempty vi:
  Value vi <> Empty.
Proof.
  repeat intro; inj.
Qed.

Lemma conflict_notempty:
  Conflict <> Empty.
Proof.
  repeat intro; inj.
Qed.

Import Learn.

Theorem sred_deterministc:
  forall t t1,
    sred t t1 ->
    forall t2,
      sred t t2 ->
      t1 = t2.
Proof.
  induction 1; inversion 1; simpl in *; subst; unpack; tryfalse; eauto; repeat f_equal.
  all: repeat match goal with
  (* handling of non-terminating terms, putting them into a nice and easy form. *)
  | [h: sred Conflict _ |- _] => inversion h
  | [h: sred Empty _ |- _] => inversion h
  | [h: sred (Value _) _ |- _] => inversion h
  | [h: sred ?t1 ?t2 |- _] =>
    learn (sred_nonempty_conflict_value h)
  | [_: context ti [Value ?vi] |- _ ] =>
    learn (value_notempty vi)
  | [_: context ti [Conflict] |- _ ] =>
    learn conflict_notempty

  (* apply induction hypothesis when possible. *)
  | [
    h1: sred ?t ?t1,
    h2: sred ?t ?t2,
    IHsred: forall t3, sred ?t _ -> _
    |- _ ] =>
    eapply IHsred; eauto

  (* Main helper lemma: we can only take a look to the first non-empty term *)
  | [
    hts1: List.Forall (eq Empty) ?ts1,
    hts1': List.Forall (eq Empty) ?ts1',
    hti: ?ti <> Empty,
    hti': ?ti' <> Empty,
    h: ?ts1 ++ ?ti :: _ = ?ts1' ++ ?ti' :: _ |- _
  ] =>
    learn (remove_head_empty hts1 hts1' hti hti' h); unpack; subst

  (* Simplify, substitute etc to continue the search by saturation*)
  | _ => unpack; injections; subst; tryfalse; eauto
  end.


  (* After saturation, there is only one case left. *)
  { rewrite <- H in H5; injections; eauto. }
Qed.

Notation "'sred' t1 t2" :=
  (sred t1 t2) (
  at level 50,
  t1 at level 3,
  t2 at level 3,
  only printing,
  format "'sred'  '[hv' t1  '/' t2 ']'"
).
Notation "'star' 'sred' t1 t2" :=
  (star sred t1 t2) (
  at level 50,
  t1 at level 3,
  t2 at level 3,
  only printing,
  format "'star'  'sred'  '[hv' t1  '/' t2 ']'"
).
Notation "'plus' 'sred' t1 t2" :=
  (plus sred t1 t2) (
  at level 50,
  t1 at level 3,
  t2 at level 3,
  only printing,
  format "'plus'  'sred'  '[hv' t1  '/' t2 ']'"
).

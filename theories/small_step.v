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

  | sred_binop_right_conflict:
    forall op u,
      sred (Binop op Conflict u) Conflict
  | sred_binop_right_empty:
    forall op u,
      sred (Binop op Empty u) Empty
  | sred_binop_left_conflict:
      forall op v,
        sred
          (Binop op (Value v) Conflict)
          Conflict
  | sred_binop_left_empty:
    forall op v,
      sred
        (Binop op (Value v) Empty)
        (Empty)

  | sred_default_Conflict:
    forall ts vi vj tjust tcons,
      sred (Default ((Value vi)::(Value vj)::ts) tjust tcons) Conflict
  | sred_default_E_value:
    forall vi ts tjust tcons,
      ts = [] ->
      sred (Default ((Value vi)::ts) tjust tcons) (Value vi)
  | sred_default_E_zero_conflict:
    forall ts2 tjust tcons,
      sred (Default (Conflict::ts2) tjust tcons) Conflict
  | sred_default_E_one_conflict:
    forall vi ts2 tjust tcons,
      sred (Default ((Value vi)::Conflict::ts2) tjust tcons) Conflict
  | sred_default_E_zero:
    forall ti ti' ts2 tj tc,
      ti' <> Empty ->
      sred ti ti' ->
      sred (Default (ti::ts2) tj tc) (Default (ti'::ts2) tj tc)
  | sred_default_E_one:
    forall vi tj tj' ts3 tjust tcons,
      tj' <> Empty ->
      sred tj tj' ->
      sred
        (Default ((Value vi)::tj::ts3) tjust tcons)
        (Default ((Value vi)::tj'::ts3) tjust tcons)

  (* todo : add a comment to explain why version of the semantics and not the sred t Empty -> sred (Default (t::ts) tj tc) (Default ts tj tc). *)
  | sred_default_E_zero_empty:
    forall ti ts2 tj tc,
      sred ti Empty ->
      sred (Default (ti::ts2) tj tc) (Default ts2 tj tc)
  | sred_default_E_one_empty:
    forall vi tj ts3 tjust tcons,
      sred tj Empty ->
      sred
        (Default ((Value vi)::tj::ts3) tjust tcons)
        (Default ((Value vi)::ts3) tjust tcons)
  | sred_default_J:
    forall tj1 tj2 tc,
      sred tj1 tj2 ->
      forall ts,
      ts = [] ->
      sred (Default ts tj1 tc) (Default ts tj2 tc)
  | sred_default_JTrue:
    forall tc,
    forall ts,
    ts = [] ->
      sred (Default ts (Value (Bool true)) tc) tc
  | sred_default_JFalse:
    forall tc,
    forall ts,
    ts = [] ->
      sred (Default ts (Value (Bool false)) tc) Empty
  | sred_default_JEmpty:
    forall tc,
    forall ts,
    ts = [] ->
      sred (Default ts Empty tc) Empty
  | sred_default_JConflict:
    forall tc,
    forall ts,
    ts = [] ->
      sred (Default ts Conflict tc) Conflict
  | sred_match_cond:
    forall u1 u2 t1 t2,
      sred u1 u2 ->
      sred (Match_ u1 t1 t2) (Match_ u2 t1 t2)
  | sred_match_None:
    forall t1 t2,
      sred (Match_ (Value (VNone)) t1 t2) t1
  | sred_match_conflict:
    forall t1 t2,
      sred
        (Match_ Conflict t1 t2)
        Conflict
  | sred_match_empty:
    forall t1 t2,
    sred
      (Match_ Empty t1 t2)
      Empty
  | sred_match_Some:
    forall v t1 t2,
      sred (Match_ (Value (VSome v)) t1 t2) t2.[Value v/]
  | sred_None:
    sred ENone (Value VNone)
  | sred_Some_conflict:
    sred (ESome Conflict) Conflict
  | sred_Some_empty:
    sred (ESome Empty) Empty
  | sred_Some_context:
    forall t1 t2,
      sred t1 t2 ->
      sred (ESome t1) (ESome t2)
  | sred_Some:
    forall v,
      sred (ESome (Value v)) (Value (VSome v))
.


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

(* -------------------------------------------------------------------------- *)

(* Lifting context rules to star. *)


Lemma star_sred_app_left:
    forall t1 t2 u,
      star sred (t1) (t2) ->
      star sred
        (App t1 u)
        (App t2 u).
Proof.
  induction 1; [eapply star_refl|]; eapply star_step; [econstructor; eauto| eauto].
Qed.

Lemma star_sred_app_right:
  forall t u1 u2 sigma,
    star sred (u1) (u2) ->
    star sred
      (App (Value (Closure t sigma)) u1)
      (App (Value (Closure t sigma)) u2).
Proof.
  induction 1.
  { eapply star_refl. }
  { eapply star_step; [|eapply IHstar].
    econstructor; eauto.
  }
Qed.

Lemma star_sred_binop_left:
    forall op t1 t2 u,
      star sred (t1) (t2) ->
      star sred
        (Binop op t1 u)
        (Binop op t2 u).
Proof.
  induction 1; [eapply star_refl|]; eapply star_step; [econstructor; eauto| eauto].
Qed.

Lemma star_sred_binop_right:
    forall op v u1 u2,
      star sred (u1) (u2) ->
      star sred
        (Binop op (Value v) u1)
        (Binop op (Value v) u2).
Proof.
  induction 1.
  { eapply star_refl. }
  { eapply star_step; [|eapply IHstar].
    econstructor; eauto.
  }
Qed.

Lemma star_sred_default_E_zero:
    forall ti ti' ts2 tj tc,
      star sred ti ti' ->
      ti' <> Empty ->
      star sred (Default (ti::ts2) tj tc) (Default (ti'::ts2) tj tc).
Proof.
  induction 1; intros; [eapply star_refl|]; eapply star_step; [econstructor; eauto| eauto].
  admit.
  admit.
Admitted.

Lemma star_sred_default_E_one:
    forall vi tj tj' ts3 tjust tcons,
      star sred tj tj' ->
      star sred
        (Default ((Value vi)::tj::ts3) tjust tcons)
        (Default ((Value vi)::tj'::ts3) tjust tcons).
Proof.
  induction 1.
  { eapply star_refl. }
  { eapply star_step; [|eapply IHstar].
    econstructor; eauto.
    admit.
  }
Admitted.

Lemma star_sred_default_J:
    forall tj1 tj2 tc,
      star sred tj1 tj2 ->
      forall ts,
      ts = [] ->
      star sred (Default ts tj1 tc) (Default ts tj2 tc).
Proof.
  induction 1; intros; [eapply star_refl|]; eapply star_step; [econstructor; eauto| eauto].
Qed.

Lemma star_sred_match_cond:
    forall u1 u2 t1 t2,
      star sred u1 u2 ->
      star sred (Match_ u1 t1 t2) (Match_ u2 t1 t2).
Proof.
  induction 1; [eapply star_refl|]; eapply star_step; [econstructor; eauto| eauto].
Qed.

Lemma star_sred_Some_context:
    forall t1 t2,
      star sred t1 t2 ->
      star sred (ESome t1) (ESome t2).
Proof.
  induction 1; [eapply star_refl|]; eapply star_step; [econstructor; eauto| eauto].
Qed.

Lemma star_sred_empty_empty:
  forall t2,
    star sred Empty t2 -> t2 = Empty.
Proof.
  intros.
  induction H using star_ind_n1; subst; eauto.
  inversion H.
Qed.

Hint Resolve
  star_sred_app_left
  star_sred_app_right
  star_sred_binop_left
  star_sred_binop_right
  star_sred_default_E_zero
  star_sred_default_E_one
  star_sred_default_J
  star_sred_match_cond
  star_sred_Some_context

  star_sred_empty_empty
: sred.

Hint Resolve
  star_refl
: sred.

Hint Constructors sred : sred.


(* -------------------------------------------------------------------------- *)

(* Determinsm lemma *)

Theorem sred_deterministc:
  forall t t1,
    sred t t1 ->
    forall t2,
      sred t t2 ->
      t1 = t2.
Abort.

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
    IHsred: forall t3, sred ?t t3 -> _
    |- _ ] =>
    learn (IHsred _ h1)

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

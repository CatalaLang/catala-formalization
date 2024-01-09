Require Import syntax continuations small_step sequences tactics.
Require Import Coq.ZArith.ZArith.
Import List.ListNotations.



(* -------------------------------------------------------------------------- *)

(* Translating a state into a term *)

Lemma EmptyOrNotEmpty:
  forall t, (t = Empty) \/ (t <> Empty).
Proof.
  induction t; try solve [right; repeat intro; congruence|left; eauto].
Qed.


Definition apply_CDefault b o ts tj tc t sigma : term :=
  match b, t, o with
  | Hole, Empty, Some v =>
      Default ((Value (VPure v)).[subst_of_env sigma]::ts..[subst_of_env sigma]) tj.[subst_of_env sigma] tc.[subst_of_env sigma]
  | Hole, Empty, None =>
      Default (ts..[subst_of_env sigma]) tj.[subst_of_env sigma] tc.[subst_of_env sigma]
  | _, _, Some v =>
      Default ((Value (VPure v)).[subst_of_env sigma]::t::ts..[subst_of_env sigma]) tj.[subst_of_env sigma] tc.[subst_of_env sigma]
  | _, _,None =>
      Default (t::(ts)..[subst_of_env sigma]) tj.[subst_of_env sigma] tc.[subst_of_env sigma]
  end.

Lemma apply_CDefault_hole_some_empty:
  forall v ts tj tc t sigma,
    t = Empty ->
    apply_CDefault Hole (Some v) ts tj tc t sigma =
      Default ((Value (VPure v)).[subst_of_env sigma]::ts..[subst_of_env sigma]) tj.[subst_of_env sigma] tc.[subst_of_env sigma].
Proof.
  intros; induction t; subst; unfold apply_CDefault; eauto; tryfalse.
Qed.

Lemma apply_CDefault_hole_none_empty:
  forall ts tj tc t sigma,
    t = Empty ->
    apply_CDefault Hole None ts tj tc t sigma =
      Default (ts..[subst_of_env sigma]) tj.[subst_of_env sigma] tc.[subst_of_env sigma].
Proof.
  intros; induction t; subst; unfold apply_CDefault; eauto; tryfalse.
Qed.

Lemma apply_CDefault_hole_some_nempty:
  forall v ts tj tc t sigma,
    t <> Empty ->
    apply_CDefault Hole (Some v) ts tj tc t sigma =
      Default ((Value (VPure v)).[subst_of_env sigma]::t::ts..[subst_of_env sigma]) tj.[subst_of_env sigma] tc.[subst_of_env sigma].
Proof.
  intros; induction t; subst; unfold apply_CDefault; eauto; tryfalse.
Qed.

Lemma apply_CDefault_hole_none_nempty:
  forall ts tj tc t sigma,
    t <> Empty ->
    apply_CDefault Hole None ts tj tc t sigma =
      Default (t::(ts)..[subst_of_env sigma]) tj.[subst_of_env sigma] tc.[subst_of_env sigma].
Proof.
  intros; induction t; subst; unfold apply_CDefault; eauto; tryfalse.
Qed.

Lemma apply_CDefault_nohole_some:
  forall v ts tj tc t sigma,
    apply_CDefault NoHole (Some v) ts tj tc t sigma =
      Default ((Value v).[subst_of_env sigma]::t::ts..[subst_of_env sigma]) tj.[subst_of_env sigma] tc.[subst_of_env sigma].
Proof.
  intros; induction t; subst; unfold apply_CDefault; eauto; tryfalse.
Qed.

Lemma apply_CDefault_nohole_none:
  forall ts tj tc t sigma,
  apply_CDefault NoHole None ts tj tc t sigma =
    Default (t::(ts)..[subst_of_env sigma]) tj.[subst_of_env sigma] tc.[subst_of_env sigma].
Proof.
  intros; induction t; subst; unfold apply_CDefault; eauto; tryfalse.
Qed.


Ltac simpl_apply_CDefault := match goal with
| [h1: ?t=Empty, h2: context [apply_CDefault Hole (Some _) _ _ _ ?t _] |- _] =>
  rewrite apply_CDefault_hole_some_empty in h2
| [h1: ?t=Empty, h2: context [apply_CDefault Hole (Some _) _ _ _ ?t _] |- _] =>
  rewrite apply_CDefault_hole_none_empty in h2
| [h1: ?t<>Empty, h2: context [apply_CDefault Hole (Some _) _ _ _ ?t _] |- _] =>
  rewrite apply_CDefault_hole_some_nempty in h2
| [h1: ?t<>Empty, h2: context [apply_CDefault Hole (Some _) _ _ _ ?t _] |- _] =>
  rewrite apply_CDefault_hole_none_nempty in h2
| [h: context [apply_CDefault NoHole (Some _) _ _ _ ?t _] |- _] =>
  rewrite apply_CDefault_nohole_some in h
| [h: context [apply_CDefault NoHole None _ _ _ ?t _] |- _] =>
  rewrite apply_CDefault_nohole_none in h
end.




Opaque apply_CDefault.

(* This permits to simplify apply defaults using the EmptyOrNotEmpty lemma in an automatic fashon *)


Definition apply_cont
  (param1: term * list value)
  (k: cont)
  : term * list value :=
  let '(t, sigma) := param1 in
  match k with
  | CAppR t2 =>
    (App t t2.[subst_of_env sigma], sigma)
  | CBinopL op v1 =>
    (Binop op (Value v1) t, sigma)
  | CBinopR op t2 =>
    (Binop op t t2.[subst_of_env sigma], sigma)
  | CClosure t_cl sigma_cl =>
    (App (Value (Closure t_cl sigma_cl)) t, sigma)
  | CReturn sigma' => (t, sigma')
  | CDefault b o ts tj tc =>
    (apply_CDefault b o ts tj tc t sigma, sigma)
  | CDefaultBase tc =>
    (Default nil t tc.[subst_of_env sigma], sigma)
  | CMatch t1 t2 =>
    (Match_ t t1.[subst_of_env sigma] t2.[up (subst_of_env sigma)], sigma)
  | CSome =>
    (ESome t, sigma)

  | CIf t1 t2=>
    (If t t1.[subst_of_env sigma] t2.[subst_of_env sigma], sigma)
  | CErrorOnEmpty =>
    (ErrorOnEmpty t, sigma)
  | CDefaultPure =>
    (DefaultPure t, sigma)
  end.

Definition apply_conts
  (kappa: list cont)
  : term * list value -> term * list value :=
  List.fold_left apply_cont kappa.

Definition apply_return (r: result) :=
  match r with
  | RValue v => Value v
  | REmpty => Empty
  | RConflict => Conflict
  end.

Definition apply_state_aux (s: state): term * list value :=
  match s with
  | mode_eval t stack env =>
    (apply_conts stack (t.[subst_of_env env], env))
  | mode_cont stack env r =>
    (apply_conts stack ((apply_return r), env))
  end.

(* We use an notation to be apple to simplify this definition. *)
Notation "'apply_state' s" := (fst (apply_state_aux s)) (at level 50, only parsing).

Inductive apply_conts' : list cont -> term -> list value -> term -> list value -> Prop := .

Inductive apply_state_aux' : state -> term -> list value -> Prop :=
  | apply_mode_eval:
    forall stack t env t' env',
      apply_conts' stack t.[subst_of_env env] env t' env' ->
      apply_state_aux' (mode_eval t stack env) t' env'
  (* | apply_mode_cont:
    forall stack t env t' env',
      apply_conts' stack t.[subst_of_env env]x² env t' env' ->
      apply_state_aux' (mode_eval t stack env) t' env' *)
.

(* -------------------------------------------------------------------------- *)

(* Require Import typing.

Lemma apply_state_typing:
  forall Delta Gamma s1 T,
    jt_state Delta Gamma s1 T ->
    jt_term Delta Gamma (apply_state s1) T.
Proof.
Abort. *)

Lemma NEmpty_subst_of_env_NEmpty {t} sigma:
  t <> Empty -> t.[subst_of_env sigma] <> Empty.
Proof.
  induction t; simpl; repeat intro; try congruence.
  unfold subst_of_env in *.
  induction (List.nth_error sigma x).
  all: unfold ids, Ids_term in *; try congruence.
Qed.


Lemma Empty_eq_Empty : Empty = Empty.
Proof.
  reflexivity.
Qed.

Import Learn.

Ltac dsimpl :=
  repeat match goal with
  (* (* | [h: ?t = Empty |- context [apply_CDefault (Some _) _ _ _ ?t _]] =>
    rewrite (apply_CDefault_SE h)
  | [h: ?t = Empty |- context [apply_CDefault None _ _ _ ?t _]] =>
    rewrite (apply_CDefault_NE h) *)
  | [h: ?t <> Empty |- context [apply_CDefault (Some _) _ _ _ ?t _]] =>
    rewrite (apply_CDefault_ST h)
  | [h: ?t <> Empty |- context [apply_CDefault None _ _ _ ?t _]] =>
    rewrite (apply_CDefault_NT h)
  (* | [h1: ?t = Empty, h2: context [apply_CDefault (Some _) _ _ _ ?t _] |- _] =>
    rewrite (apply_CDefault_SE h1) in h2
  | [h1: ?t = Empty, h2: context [apply_CDefault None _ _ _ ?t _] |- _] =>
    rewrite (apply_CDefault_NE h1) in h2 *)
  | [h1: ?t <> Empty, h2: context [apply_CDefault (Some _) _ _ _ ?t _] |- _] =>
    rewrite (apply_CDefault_ST h1) in h2
  | [h1: ?t <> Empty, h2: context [apply_CDefault None _ _ _ ?t _] |- _] =>
    rewrite (apply_CDefault_NT h1) in h2 *)

  | [h: ?t <> Empty |- context [?t.[subst_of_env ?sigma]]] =>
    learn (NEmpty_subst_of_env_NEmpty sigma h)
  | [h: _ /\ _ |- _] =>
    destruct h
  | [h: exists _, _ |- _] =>
    destruct h

  | _ => learn (Empty_eq_Empty) (* so the first two cases trigger*)
  | _ => progress subst
  | _ => progress asimpl
  end.


Inductive eq_value: value -> value -> Prop :=
  | eq_closure:
    forall t sigma,
      eq_value (Closure t sigma) (Closure t.[up (subst_of_env sigma)] [])
.

Inductive match_conf : state -> term -> Prop :=
  | match_conf_intro: forall s t,
      t = apply_state s ->
      match_conf s t

  (* | match_value:
    forall s v' v,
      apply_state s = Value v' ->
      eq_value v v'  ->
      match_conf s (Value v) *)
.


Parameter match_value: forall {s v v'},
  match_conf s (Value v) ->
  eq_value v v' ->
  match_conf s (Value v').



Section APPLY_EXAMPLES.

  Example test1:
    forall t1 t2 t3,
      fst (apply_conts [CBinopR Add t1; CAppR t2] (t3,[]))
      = App (Binop Add t3 t1) t2.
  Proof.
    intros.
    unfold apply_conts.
    simpl; repeat rewrite subst_env_nil; asimpl.
    eauto.
  Qed.

  Example test2: Binop Add (Value (Int 3)) (Value (Int 5)) = apply_state (mode_eval (Var 0) [CReturn [Int 5]; CBinopR Add (Var 0); CReturn []]
  [Int 3; Int 5]).
  Proof.
    simpl; unfold subst_of_env; simpl.
    eauto.
  Qed.

End APPLY_EXAMPLES.


(* -------------------------------------------------------------------------- *)

Definition env s:=
  match s with
  | mode_eval _ _ sigma => sigma
  | mode_cont _ sigma _ => sigma
  end
.

Lemma match_conf_coherent:
  forall t sigma,
    match_conf (mode_eval t [] sigma) t.[subst_of_env sigma].
Proof.
  econstructor; simpl; eauto.
Qed.

(* -------------------------------------------------------------------------- *)

(* Attempt at proving a first simulation between sred and cred. *)

Lemma apply_state_append_stack kappa s:
  apply_state_aux (append_stack s kappa) = apply_conts kappa (apply_state_aux s).
Proof.
  induction s.
  { induction kappa using List.rev_ind.
    all: simpl.
    all: autorewrite with list using eauto.
    { unfold apply_conts.
      eapply List.fold_left_app.
    }
  }
  { induction kappa using List.rev_ind.
    all: simpl.
    all: autorewrite with list using eauto.
    { unfold apply_conts.
      eapply List.fold_left_app.
    }
  }
Qed.

Lemma with_stack_append_stack_cons:
  forall s k kappa,
  with_stack s (k :: kappa) = append_stack (with_stack s [k]) kappa.
Proof.
  intros.
  induction s; simpl; eauto.
Qed.


Lemma with_stack_append_stack_app:
  forall s kappa1 kappa2,
  with_stack s (kappa1 ++ kappa2) =
    append_stack (with_stack s kappa1) kappa2.
Proof.
  intros.
  induction s; simpl; eauto.
Qed.


Lemma with_stack_stack: forall s, s = with_stack s (stack s).
Proof.
  induction s; simpl; eauto.
Qed.

Lemma snd_appply_conts_inj:
  forall x1 x2,
    snd x1 = snd x2 ->
    forall kappa,
    snd (apply_conts kappa x1) = snd (apply_conts kappa x2).
Proof.
  intros.
  induction x1, x2; induction kappa using List.rev_ind.
  { simpl in *; eauto. }
  { unfold apply_conts in *; repeat rewrite List.fold_left_app; simpl.
    remember (List.fold_left apply_cont kappa (a, b)) as y1.
    remember (List.fold_left apply_cont kappa (t, l)) as y2.
    induction y1, y2; simpl in IHkappa.
    induction x.
    all: unfold apply_cont; simpl in *; eauto; simpl.
  }
Qed.

Lemma apply_conts_app:
  forall kappa1 kappa2 p,
    apply_conts (kappa1 ++ kappa2) p
    = apply_conts kappa2 (apply_conts kappa1 p).
Proof.
  intros.
  unfold apply_conts.
  rewrite List.fold_left_app; eauto.
Qed.

Lemma apply_conts_cons:
  forall k kappa p,
    apply_conts (k :: kappa) p
    = apply_conts kappa (apply_cont p k).
Proof.
  intros.
  unfold apply_conts.
  simpl; eauto.
Qed.

Lemma apply_conts_nil:
  forall p,
    apply_conts [] p = p.
Proof.
  intros.
  unfold apply_conts.
  simpl; eauto.
Qed.

#[global]
Hint Rewrite apply_conts_app apply_conts_cons apply_conts_nil : apply_conts.


Lemma cred_apply_state_sigma_stable s1 s2:
  cred s1 s2 ->
  snd (apply_state_aux s1) = snd (apply_state_aux s2).
Proof.
  remember (stack s1) as kappa.
  intros Hcred; revert Heqkappa; revert Hcred; revert s2; revert s1.
  induction kappa using List.rev_ind.
  { induction 1; simpl; intros; subst; simpl.
    all: tryfalse.
    all: eauto. }
  { intros s1 s2.
    rewrite (with_stack_stack s1) at 3.
    rewrite (with_stack_stack s2) at 2.
    induction 1; simpl stack; intros.
    all: try match goal with [o: option value |- _] => induction o end.
    all: try solve [ simpl; eapply snd_appply_conts_inj; simpl; eauto].
    { simpl; eapply snd_appply_conts_inj; induction phi; simpl; eauto.
      { exfalso. eapply H; eauto. }
    }
  }
Qed.

Lemma creds_apply_state_sigma_stable { s1 s2 }:
  star cred s1 s2 ->
  snd (apply_state_aux s1) = snd (apply_state_aux s2).
Proof.
  induction 1 using star_ind_n1; eauto.
  rewrite IHstar.
  rewrite (cred_apply_state_sigma_stable _ _ H).
  eauto.
Qed.


(* -------------------------------------------------------------------------- *)


(* Lemmas related to reducing substo_of_env_sthg *)

Lemma subst_of_env_Value_Var:
  forall env x,
    (exists y, subst_of_env env x = Var y) \/
    (exists v, subst_of_env env x = Value v).
Proof.
  unfold subst_of_env.
  intros env x.
  remember (List.nth_error env x) as o; induction o.
  { right; eexists; eauto. }
  { left; eexists; eauto. }
Qed.

Lemma subst_of_env_nil {ts' env}:
  [] = ts'..[subst_of_env env] ->
  ts' = [].
Proof.
  destruct ts'; asimpl; intros; inj; eauto.
Qed.

Lemma subst_of_env_cons {x xs ts' env}:
  x :: xs = ts'..[subst_of_env env] ->
  exists x' xs',
       xs = xs'..[subst_of_env env]
    /\ x  = x'.[subst_of_env env]
    /\ ts' = x' :: xs'.
Proof.
  revert x xs env.
  destruct ts'; asimpl; intros; inj.
  repeat eexists.
Qed.

Lemma subst_of_env_app {ts1 ts2 ts' env}:
  ts1 ++ ts2 = ts'..[subst_of_env env] ->
  exists ts1' ts2',
       ts1 = ts1'..[subst_of_env env]
    /\ ts2 = ts2'..[subst_of_env env]
    /\ ts' = ts1' ++ ts2'.
Proof.
  revert ts1 ts2 ts' env.
  induction ts1.
  { exists [], ts'; asimpl in *; repeat split; eauto. }
  { intros ts2 ts' env.
    rewrite <- List.app_comm_cons.
    intro H; edestruct (subst_of_env_cons H); unpack;
    repeat (asimpl in *; subst); injections.
    pose proof (IHts1 _ _ _ H). unpack. subst.
    exists (x :: ts1'), ts2'.
    repeat econstructor.
  }
Qed.

Lemma subst_of_env_App {t1 t2 t' env}:
  App t1 t2 = t'.[subst_of_env env] ->
  exists (t1' t2': term),
    t1 = t1'.[subst_of_env env]
    /\ t2 = t2'.[subst_of_env env]
    /\ t' = App t1' t2'
.
Proof.
  destruct t'; asimpl; intros; tryfalse; inj; eauto;
  match goal with
  | [h: _ = subst_of_env ?env ?x |- _ ] =>
    unfold subst_of_env in h;
    destruct (List.nth_error env x);
    inj
  end.
Qed.

Lemma subst_of_env_Lam {t t' env}:
  Lam (t: {bind term}) = t'.[subst_of_env env] ->
  exists (t1': {bind term}),
    t = t1'.[up (subst_of_env env)] /\
    t' = Lam t1'
.
Proof.
  destruct t'; asimpl; intros; tryfalse; inj; eauto;
  match goal with
  | [h: _ = subst_of_env ?env ?x |- _ ] =>
    unfold subst_of_env in h;
    destruct (List.nth_error env x);
    inj
  end.
Qed.

Lemma subst_of_env_Default {ts tj tc t' env}:
  Default ts tj tc = t'.[subst_of_env env] ->
  exists ts' tj' tc',
    ts = ts'..[subst_of_env env]
    /\ tj = tj'.[subst_of_env env]
    /\ tc = tc'.[subst_of_env env]
    /\ t' = Default ts' tj' tc'
.
Proof.
  destruct t'; asimpl; intros; tryfalse; inj; eauto.
  { match goal with
    | [h: _ = subst_of_env ?env ?x |- _ ] =>
      unfold subst_of_env in h;
      destruct (List.nth_error env x);
      inj
    end.
  }
  { repeat eexists. }
Qed.


Lemma subst_of_env_Binop {op t1 t2 t' env}:
  Binop op t1 t2 = t'.[subst_of_env env] ->
  exists (t1' t2': term),
    t1 = t1'.[subst_of_env env]
    /\ t2 = t2'.[subst_of_env env]
    /\ t' = (Binop op t1' t2')
.
Proof.
  destruct t'; asimpl; intros; tryfalse; inj; eauto;
  match goal with
  | [h: _ = subst_of_env ?env ?x |- _ ] =>
    unfold subst_of_env in h;
    destruct (List.nth_error env x);
    inj
  end.
Qed.

Lemma subst_of_env_Match_ {u t1 t2 t' env}:
  Match_ u t1 t2 = t'.[subst_of_env env] ->
  exists u' t1' t2',
    u = u'.[subst_of_env env]
    /\ t1 = t1'.[subst_of_env env]
    /\ t2 = t2'.[up (subst_of_env env)]
    /\ t' = Match_ u' t1' t2'
.
Proof.
  destruct t'; asimpl; intros; tryfalse; inj; eauto.
  { match goal with
    | [h: _ = subst_of_env ?env ?x |- _ ] =>
      unfold subst_of_env in h;
      destruct (List.nth_error env x);
      inj
    end.
  }
  { repeat eexists. }
Qed.

Lemma subst_of_env_If {u t1 t2 t' env}:
  If u t1 t2 = t'.[subst_of_env env] ->
  exists u' t1' t2',
    u = u'.[subst_of_env env]
    /\ t1 = t1'.[subst_of_env env]
    /\ t2 = t2'.[subst_of_env env]
    /\ t' = If u' t1' t2'
.
Proof.
  destruct t'; asimpl; intros; tryfalse; inj; eauto.
  { match goal with
    | [h: _ = subst_of_env ?env ?x |- _ ] =>
      unfold subst_of_env in h;
      destruct (List.nth_error env x);
      inj
    end.
  }
  { repeat eexists. }
Qed.

Lemma subst_of_env_ESome {t t' env}:
  ESome t = t'.[subst_of_env env] ->
  exists t1',
    t = t1'.[subst_of_env env] /\
    t' = ESome t1'
.
Proof.
  destruct t'; asimpl; intros; tryfalse; injections; eauto;
  match goal with
  | [h: _ = subst_of_env ?env ?x |- _ ] =>
    unfold subst_of_env in h;
    destruct (List.nth_error env x);
    inj
  end.
Qed.

Lemma subst_of_env_ErrorOnEmpty {t t' env}:
  ErrorOnEmpty t = t'.[subst_of_env env] ->
  exists t1',
    t = t1'.[subst_of_env env] /\
    t' = ErrorOnEmpty t1'
.
Proof.
  destruct t'; asimpl; intros; tryfalse; injections; eauto;
  match goal with
  | [h: _ = subst_of_env ?env ?x |- _ ] =>
    unfold subst_of_env in h;
    destruct (List.nth_error env x);
    inj
  end.
Qed.

Lemma subst_of_env_DefaultPure {t t' env}:
  DefaultPure t = t'.[subst_of_env env] ->
  exists t1',
    t = t1'.[subst_of_env env] /\
    t' = DefaultPure t1'
.
Proof.
  destruct t'; asimpl; intros; tryfalse; injections; eauto;
  match goal with
  | [h: _ = subst_of_env ?env ?x |- _ ] =>
    unfold subst_of_env in h;
    destruct (List.nth_error env x);
    inj
  end.
Qed.



Lemma subst_of_env_Conflict {t' env}:
  Conflict = t'.[subst_of_env env] ->
  t' = Conflict.
Proof.
  destruct t'; asimpl; intros; tryfalse; inj; eauto;
  match goal with
  | [h: _ = subst_of_env ?env ?x |- _ ] =>
    unfold subst_of_env in h;
    destruct (List.nth_error env x);
    inj
  end.
Qed.

Lemma subst_of_env_Empty {t' env}:
  Empty = t'.[subst_of_env env] ->
  t' = Empty.
Proof.
  destruct t'; asimpl; intros; tryfalse; inj; eauto;
  match goal with
  | [h: _ = subst_of_env ?env ?x |- _ ] =>
    unfold subst_of_env in h;
    destruct (List.nth_error env x);
    inj
  end.
Qed.

Lemma subst_of_env_ENone {t' env}:
  ENone = t'.[subst_of_env env] ->
  t' = ENone.
Proof.
  destruct t'; asimpl; intros; tryfalse; inj; eauto;
  match goal with
  | [h: _ = subst_of_env ?env ?x |- _ ] =>
    unfold subst_of_env in h;
    destruct (List.nth_error env x);
    inj
  end.
Qed.

(* Lemma subst_of_env_Var {x t' env}:
  Var x = t'.[subst_of_env env] ->
  t' = Var (x - List.length env) /\ x >= List.length env.
Proof.
  destruct t'; asimpl; intros; tryfalse; inj; eauto.
  unfold subst_of_env in H.
  match goal with
  | [h: _ = subst_of_env ?env ?x |- _ ] =>
    unfold subst_of_env in h;
    destruct (List.nth_error env x);
    inj
  end.
Qed. *)


Lemma subst_of_env_Forall_Empty {ts env}:
  List.Forall (eq Empty) ts..[subst_of_env env] ->
  List.Forall (eq Empty) ts.
Proof.
  induction ts; simpl; intros; unpack; econstructor; eauto.
  symmetry.
  eapply subst_of_env_Empty; eauto.
Qed.

Ltac unpack_subst_of_env_cons :=
  repeat progress match goal with
  | [h:  ?x :: _ = _..[subst_of_env _] |- _] =>
    let u := fresh "u" in
    let ts := fresh "ts" in
    let Hu := fresh "Hu" in
    let Hts := fresh "Hts" in
    let Ht := fresh "Ht" in
    destruct (subst_of_env_cons h) as (u & ts & Hu & Hts & Ht);
    subst; clear h
  | [h:  _ ++ _ = _..[subst_of_env _] |- _] =>
    let ts1 := fresh "ts" in
    let ts2 := fresh "ts" in
    let Hts1 := fresh "Hts" in
    let Hts2 := fresh "Hts" in
    let Hteq := fresh "Hts_eq" in
    destruct (subst_of_env_app h) as (ts1 & ts2 & Hts1 & Hts2 & Hteq);
    subst; clear h
  | [h:  [] = _..[subst_of_env _] |- _] =>
    rewrite (subst_of_env_nil h); unpack; subst; clear h
  | [h: Default _ _ _ = _.[subst_of_env _] |- _] =>
    let ts := fresh "ts" in
    let tjust := fresh "tjust" in
    let tcons := fresh "tcons" in
    let Hts := fresh "Hts" in       (*    ts = ts'..[subst_of_env env] *)
    let Htjust := fresh "Htjust" in (* /\ tj = tj'.[subst_of_env env] *)
    let Htcons := fresh "Htcons" in (* /\ tc = tc'.[subst_of_env env] *)
    let Ht := fresh "Ht" in         (* /\ t' = Default ts' tj' tc' *)
    destruct (subst_of_env_Default h) as (ts & tjust & tcons & Hts & Htjust & Hcons & Ht); injections; clear h

  | [h: Match_ _ _ _ = _.[subst_of_env _] |- _] =>
    let u := fresh "u" in
    let t1 := fresh "t1" in
    let t2 := fresh "t2" in
    let Hu := fresh "Hu" in
    let Ht1 := fresh "Ht1" in
    let Ht2 := fresh "Ht2" in
    let Ht := fresh "Ht" in
    destruct (subst_of_env_Match_ h) as (u & t1 & t2 & Hu & Ht1 & Ht2 & Ht); subst; clear h
  | [h: If _ _ _ = _.[subst_of_env _] |- _] =>
    let u := fresh "u" in
    let t1 := fresh "ta" in
    let t2 := fresh "tb" in
    let Hu := fresh "Hu" in
    let Ht1 := fresh "Ht1" in
    let Ht2 := fresh "Ht2" in
    let Ht := fresh "Ht" in
    destruct (subst_of_env_If h) as (u & t1 & t2 & Hu & Ht1 & Ht2 & Ht); subst; clear h
  | [h: Binop _ _ _ = _.[subst_of_env _] |- _] =>
    let t1 := fresh "t1" in
    let t2 := fresh "t2" in
    let Ht1 := fresh "Ht1" in
    let Ht2 := fresh "Ht2" in
    let Ht := fresh "Ht" in
    destruct (subst_of_env_Binop h) as (t1 & t2 & Ht1 & Ht2 & Ht); subst; clear h
  | [h: App _ _ = _.[subst_of_env _] |- _] =>
    let t1 := fresh "t1" in
    let t2 := fresh "t2" in
    let Ht1 := fresh "Ht1" in
    let Ht2 := fresh "Ht2" in
    let Ht := fresh "Ht" in
    destruct (subst_of_env_App h) as (t1 & t2 & Ht1 & Ht2 & Ht); subst; clear h
  | [h: ESome _ = _.[subst_of_env _] |- _] =>
    let t1 := fresh "t1" in
    let Ht1 := fresh "Ht1" in
    let Ht := fresh "Ht" in
    destruct (subst_of_env_ESome h) as (t1 & Ht1 & Ht); subst; clear h
  | [h: ErrorOnEmpty _ = _.[subst_of_env _] |- _] =>
    let t1 := fresh "t1" in
    let Ht1 := fresh "Ht1" in
    let Ht := fresh "Ht" in
    destruct (subst_of_env_ErrorOnEmpty h) as (t1 & Ht1 & Ht); subst; clear h
  | [h: DefaultPure _ = _.[subst_of_env _] |- _] =>
    let t1 := fresh "t1" in
    let Ht1 := fresh "Ht1" in
    let Ht := fresh "Ht" in
    destruct (subst_of_env_DefaultPure h) as (t1 & Ht1 & Ht); subst; clear h

  | [h: Lam _ = _.[subst_of_env _] |- _] =>
    let t1 := fresh "t1" in
    let Ht1 := fresh "Ht1" in
    let Ht := fresh "Ht" in
    destruct (subst_of_env_Lam h) as (t1 & Ht1 & Ht); subst; clear h
  | [h: ENone = _.[subst_of_env _] |- _] =>
    pose proof (subst_of_env_ENone h); subst; clear h
  | [h: Conflict = _.[subst_of_env _] |- _] =>
    pose proof (subst_of_env_Conflict h); subst; clear h
  | [h: Empty = _.[subst_of_env _] |- _] =>
    pose proof (subst_of_env_Empty h); subst; clear h
  | [h: _.[subst_of_env _] = _ |- _ ] =>
    symmetry in h
  | [h: List.Forall (eq Empty) _..[subst_of_env _] |- _] =>
    pose proof (subst_of_env_Forall_Empty h); subst; clear h

  | [h: Value _ = (Var ?x).[subst_of_env ?sigma] |- _] =>
    let o := fresh "o" in
    let v := fresh "v" in
    unfold subst_of_env in h; simpl in h;
    remember (List.nth_error sigma x) as o1;
    induction o1 as [v|];
    tryfalse;
    repeat (injections; subst)
  | [h: Value _ = subst_of_env ?sigma ?x |- _] =>
    let o := fresh "o" in
    let v := fresh "v" in
    unfold subst_of_env in h; simpl in h;
    remember (List.nth_error sigma x) as o1;
    induction o1 as [v|];
    tryfalse;
    repeat (injections; subst)
  | [h: is_value (subst_of_env ?sigma ?x) |- _] =>
    let o := fresh "o" in
    let v := fresh "v" in
    unfold subst_of_env in h; simpl in h;
    remember (List.nth_error sigma x) as o;
    induction o as [v|];
    tryfalse;
    repeat (injections; subst)
  | [Heq: None = List.nth_error _ _ |- _] =>
    progress rewrite <- Heq in *
  | [Heq: Some _ = List.nth_error _ _ |- _] =>
    progress rewrite <- Heq in *

  | [h: Conflict = apply_return ?result |- _] =>
    induction result; simpl in h; tryfalse; injections
  | [h: Empty = apply_return ?result |- _] =>
    induction result; simpl in h; tryfalse; injections
  | [h: Value _ = apply_return ?result |- _] =>
    induction result; simpl in h; tryfalse; injections

  | [h: sred Conflict _ |- _] => inversion h
  | [h: sred Empty _ |- _] => inversion h
  | [h: sred (Value _) _ |- _] => inversion h
  | _ => repeat (simpl in *; injections; subst)
  end; tryfalse
.

(* -------------------------------------------------------------------------- *)

(* The following dead code was related to an old version of the semantics that used the count of non-empty values inside the Default to reduce. *)

(* Definition count_f
  {A}
  (p: A -> bool)
  := fix count_f (l : list A) { struct l} : nat :=
  match l with
  | [] => 0
  | y :: tl => let n := count_f tl in if p y then S n else n
  end.

Lemma count_f_app
  {A}
  (p: A -> bool)
  (l1 l2: list A) :
  count_f p (l1 ++ l2) = count_f p l1 + count_f p l2.
Proof.
  induction l1.
  { simpl; eauto. }
  { simpl; rewrite IHl1.
    induction (p a); lia.
  }
Qed.

Lemma count_f_cons
  {A}
  (p: A -> bool)
  (a: A)
  (l: list A) :
  count_f p (a :: l) = let n := count_f p l in if p a then S n else n.
Proof.
  simpl; eauto.
Qed.

Lemma count_occ_decomp:
  forall [A : Type]
  [p: A -> bool]
	(l : list A)
  [n: nat],
  count_f p l = S n ->
  exists l1 x l2,
    l1 ++ x :: l2 = l /\
    p x = true /\
    List.forallb (fun x => negb (p x)) l1 = true /\
    count_f p l2 = n.
Proof.
Admitted.

Parameter eqb_term: term -> term -> bool.
Parameter eqb_term_ok: forall t1 t2, t1 = t2 <-> eqb_term t1 t2 = true.

(* It is always possible to get a smallest ti and tj. *)
Lemma default_conflict_sort: forall ts ts1 ti ts2 tj ts3,
  List.Forall is_value ts ->
  ti <> Empty ->
  tj <> Empty ->
  ts = ts1 ++ ti :: ts2 ++ tj :: ts3 ->
  exists ts1 ti ts2 tj ts3,
    List.Forall (eq Empty) ts1 /\
    List.Forall (eq Empty) ts2 /\
    ti <> Empty /\
    tj <> Empty /\
    ts = ts1 ++ ti :: ts2 ++ tj :: ts3.
Proof.
  intros ts ts1 ti ts2 tj ts3 Hts Hti Htj Htseq.
  assert (Hcount:
    count_f (fun t => negb (eqb_term Empty t)) ts >= 2
  ).
  { rewrite Htseq.
    assert (Hti': eqb_term Empty ti = false). { admit. }
    assert (Htj': eqb_term Empty tj = false). { admit. }
    repeat (
      try rewrite count_f_app;
      try rewrite count_f_cons;
      try rewrite Hti';
      try rewrite Htj';
      simpl
    ); lia.
  }
  assert (Hcount': exists n, count_f (fun t : term => negb (eqb_term Empty t)) ts = S (S n)).
  { induction Hcount; eauto.
    destruct IHHcount as [n Hn].
    exists (S n); eauto.
  }
  clear Hcount; rename Hcount' into Hcount.
  destruct Hcount as [n Hcount].

  destruct (count_occ_decomp ts Hcount) as
    (ts1' & ti' & ts2' & H1 & H2 & H3 & Hcount').
  destruct (count_occ_decomp ts2' Hcount') as
    (ts2'' & tj'' & ts3'' & H1' & H2' & H3' & _).

  exists ts1', ti', ts2'', tj'', ts3''; repeat split.
  { admit. } { admit. } { admit. } { admit. }
  { clear Htseq. subst; eauto. }
Admitted. *)


Lemma cred_default_head_empty:
  forall ts1 o ts2 e1 e2 env0,
  List.Forall (eq Empty) ts1 ->
  star cred
    (mode_cont [CDefault Hole o (ts1 ++ ts2) e1 e2] env0 REmpty)
    (mode_cont [CDefault Hole o (ts2) e1 e2] env0 REmpty).
Proof.
  induction ts1; intros; unpack; simpl.
  { econstructor. }
  { eapply star_step. { econstructor. }
    eapply star_step. { econstructor. }
    eapply star_step. { econstructor. }
    eapply IHts1; eauto.
  }
Qed.

(* -------------------------------------------------------------------------- *)

(** Inversion lemmas when stack is filled. *)

Import Learn.

Ltac match_conf1 :=
  match goal with
  | [ |- match_conf _ _ ] => econstructor
  (* | [h: match_conf _ _ |- _ ] =>
    inversion h; subst; clear h *)
  | [ h: plus cred ?s1 ?s2 |- _] =>
    learn (plus_star h)
  | [ hs1s2: star cred (mode_eval _ _ _) ?s2 |- _ ] =>
    learn (creds_apply_state_sigma_stable hs1s2)
  | [ hs1s2: star cred (mode_cont _ _ _) ?s2 |- _ ] =>
    learn (creds_apply_state_sigma_stable hs1s2)
  | [ hs1s2: star cred _ _ |- _ ] =>
    learn (creds_apply_state_sigma_stable hs1s2)
  | [ |- context [apply_state_aux (append_stack _ _)]] =>
    rewrite apply_state_append_stack
  | [ |- context [let '(_, _) := ?p in _]] =>
    rewrite (surjective_pairing p)
  | [ |- context [apply_cont]] =>
    unfold apply_cont
  | [h: context [apply_state_aux (append_stack _ _)] |- _] =>
    rewrite apply_state_append_stack in h
  | [h: context [let '(_, _) := ?p in _] |- _] =>
    rewrite (surjective_pairing p) in h
  | [h: context [apply_cont] |- _] =>
    unfold apply_cont in h
  | [h: context [apply_conts (cons _ _) _] |- _] =>
    simpl in h
  | [h: context [apply_conts (app _ _) _] |- _] =>
    rewrite apply_conts_app in h
  | [h: context [fst (_, _)] |- _] =>
    simpl in h

  | [h: _ = apply_CDefault _ _ _ _ _ ?t _ |- _] =>
    learn (EmptyOrNotEmpty t); repeat match goal with
    | [h: _ \/ _ |- _] =>
      destruct h
    | [h1: ?t=Empty, h2: context [apply_CDefault Hole (Some _) _ _ _ ?t _] |- _] =>
      rewrite (apply_CDefault_hole_some_empty _ _ _ _ _ _ h1) in h2
    | [h1: ?t=Empty, h2: context [apply_CDefault Hole None _ _ _ ?t _] |- _] =>
      rewrite (apply_CDefault_hole_none_empty _ _ _ _ _ h1) in h2
    | [h1: ?t<>Empty, h2: context [apply_CDefault Hole (Some _) _ _ _ ?t _] |- _] =>
      rewrite (apply_CDefault_hole_some_nempty _ _ _ _ _ _ h1) in h2
    | [h1: ?t<>Empty, h2: context [apply_CDefault Hole None _ _ _ ?t _] |- _] =>
      rewrite (apply_CDefault_hole_none_nempty _ _ _ _ _ h1) in h2
    | [h: context [apply_CDefault NoHole (Some _) _ _ _ ?t _] |- _] =>
      rewrite apply_CDefault_nohole_some in h
    | [h: context [apply_CDefault NoHole None _ _ _ ?t _] |- _] =>
      rewrite apply_CDefault_nohole_none in h
    end
  | [h: _ \/ _ |- _] =>
    destruct h
  | _ => progress simpl; try solve [repeat f_equal; eauto]
  | _ => progress injections
  end.

Ltac simpl_apply_CDefault' :=
  match goal with
  | [h1: ?t=Empty, h2: context [apply_CDefault Hole (Some _) _ _ _ ?t _] |- _] =>
    rewrite (apply_CDefault_hole_some_empty _ _ _ _ _ _ h1) in h2
  | [h1: ?t=Empty, h2: context [apply_CDefault Hole None _ _ _ ?t _] |- _] =>
    rewrite (apply_CDefault_hole_none_empty _ _ _ _ _ h1) in h2
  | [h1: ?t<>Empty, h2: context [apply_CDefault Hole (Some _) _ _ _ ?t _] |- _] =>
    rewrite (apply_CDefault_hole_some_nempty _ _ _ _ _ _ h1) in h2
  | [h1: ?t<>Empty, h2: context [apply_CDefault Hole None _ _ _ ?t _] |- _] =>
    rewrite (apply_CDefault_hole_none_nempty _ _ _ _ _ h1) in h2
  | [h: context [apply_CDefault NoHole (Some _) _ _ _ ?t _] |- _] =>
    rewrite apply_CDefault_nohole_some in h
  | [h: context [apply_CDefault NoHole None _ _ _ ?t _] |- _] =>
    rewrite apply_CDefault_nohole_none in h
  end.

Lemma Value_apply_CDefault:
  forall v a b c d e f g,
    Value v = apply_CDefault a b c d e f g -> False.
Proof.
  intros.
  induction a, b; destruct (EmptyOrNotEmpty f) as [Heq | Heq].
  all: simpl_apply_CDefault'; tryfalse.
Qed.


Lemma Conflict_apply_CDefault:
  forall a b c d e f g,
    Conflict = apply_CDefault a b c d e f g -> False.
Proof.
  intros.
  induction a, b; destruct (EmptyOrNotEmpty f) as [Heq | Heq].
  all: simpl_apply_CDefault'; tryfalse.
Qed.

Lemma Empty_apply_CDefault:
  forall a b c d e f g,
    Empty = apply_CDefault a b c d e f g -> False.
Proof.
  intros.
  induction a, b; destruct (EmptyOrNotEmpty f) as [Heq | Heq].
  all: simpl_apply_CDefault'; tryfalse.
Qed.

Lemma Lam_apply_CDefault:
  forall t a b c d e f g,
    Lam t = apply_CDefault a b c d e f g -> False.
Proof.
  intros.
  induction a, b; destruct (EmptyOrNotEmpty f) as [Heq | Heq].
  all: simpl_apply_CDefault'; tryfalse.
Qed.

Lemma value_apply_conts_inversion_eval {v kappa t env0}:
  Value v = fst (apply_conts kappa (t, env0)) ->
  List.Forall (fun k => exists sigma, k = CReturn sigma) kappa /\ (
  (Value v = t))
  .
Proof.
  split; revert v kappa t env0 H.
  { induction kappa as [|k kappa] using List.rev_ind.
    { econstructor. }
    { induction k; try induction o.
      all: intros; repeat match_conf1; inj.
      { learn (IHkappa _ _ H); eapply List.Forall_app; eauto. }
      all: exfalso.
      all: eapply Value_apply_CDefault; eauto.
    }
  }
  { induction kappa as [|k kappa] using List.rev_ind.
    { induction t; asimpl; intros; inj; subst; eauto. }
    { destruct t; induction k; try induction o.
      all: intros; repeat match_conf1; inj.
      { destruct (IHkappa (Var x) _ H); inj; unpack; injections; subst; eauto. }
      all: try match goal with
      | [h: Value _ = fst (apply_conts _ (?t, ?env)) |- _] =>
        destruct (IHkappa t env); simpl; eauto
      end.
      all: exfalso; eapply Value_apply_CDefault; eauto.
    }
  }
Qed.

Lemma value_apply_conts_inversion_cont {v kappa result env0}:
  Value v = fst (apply_conts kappa (apply_return result, env0)) ->
  List.Forall (fun k => exists sigma, k = CReturn sigma) kappa /\
  RValue v = result.
Proof.
  intros H.
  destruct (value_apply_conts_inversion_eval H) as (Hkappa & Hv).
  all: induction result; simpl in *.
  all: try congruence.
  { injections; subst; eauto. }
Qed.

Lemma lam_apply_conts_inversion_eval {kappa t t' env0}:
  Lam t' = fst (apply_conts kappa (t, env0)) ->
  List.Forall (fun k => exists sigma, k = CReturn sigma) kappa /\ (
  (Lam t' = t)).
Proof.
  split; revert t' kappa t env0 H.
  { induction kappa as [|k kappa] using List.rev_ind.
    { econstructor. }
    { induction k; try induction o.
      all: intros; repeat match_conf1; inj.
      { learn (IHkappa _ _ H); eapply List.Forall_app; eauto. }
      all: exfalso; eapply Lam_apply_CDefault; eauto.
    }
  }
  { induction kappa as [|k kappa] using List.rev_ind.
    { simpl; eauto. }
    { induction k; try induction o.
      all: intros; repeat match_conf1; inj.
      { learn (IHkappa _ _ H); subst; eauto. }
      all: exfalso; eapply Lam_apply_CDefault; eauto.
    }
  }
Qed.

Lemma empty_apply_conts_inversion_eval {kappa t env0}:
  Empty = fst (apply_conts kappa (t, env0)) ->
  List.Forall (fun k => exists sigma, k = CReturn sigma) kappa /\ (
  (Empty = t)).
Proof.
  split; revert kappa t env0 H.
  { induction kappa as [|k kappa] using List.rev_ind.
    { econstructor. }
    { induction k; try induction o; try induction b.
      all: intros; repeat match_conf1; inj; tryfalse.
      { learn (IHkappa _ _ H); eapply List.Forall_app; eauto. }
    }
  }
  { induction kappa as [|k kappa] using List.rev_ind.
    { simpl; eauto. }
    { induction k; try induction o; try induction b.
      all: intros; repeat match_conf1; inj; tryfalse.
      { learn (IHkappa _ _ H); subst; eauto. }
    }
  }
Qed.

Lemma conflict_apply_conts_inversion_eval {kappa t env0}:
  Conflict = fst (apply_conts kappa (t, env0)) ->
  List.Forall (fun k => exists sigma, k = CReturn sigma) kappa /\ (
  (Conflict = t)).
Proof.
  split; revert kappa t env0 H.
  { induction kappa as [|k kappa] using List.rev_ind.
    { econstructor. }
    { induction k; try induction o.
      all: intros; repeat match_conf1; inj.
      { learn (IHkappa _ _ H); eapply List.Forall_app; eauto. }
      all: exfalso; eapply Conflict_apply_CDefault; eauto.
    }
  }
  { induction kappa as [|k kappa] using List.rev_ind.
    { simpl; eauto. }
    { induction k; try induction o.
      all: intros; repeat match_conf1; inj.
      { learn (IHkappa _ _ H); subst; eauto. }
      all: exfalso; eapply Conflict_apply_CDefault; eauto.
    }
  }
Qed.

Lemma match_conf_eval_app_CReturn {e kappa sigma env0 t}:
  match_conf (mode_eval e (kappa ++ [CReturn sigma]) env0) t ->
  match_conf (mode_eval e (kappa) env0) t.
Proof.
  intros MC; inversion MC; subst; clear MC.
  econstructor.
  simpl; rewrite apply_conts_app; simpl.
  unfold apply_cont.
  rewrite (surjective_pairing (apply_conts kappa (e.[subst_of_env env0], env0))); simpl.
  eauto.
Qed.

Lemma match_conf_cont_app_CReturn {result kappa sigma env0 t}:
  match_conf (mode_cont (kappa ++ [CReturn sigma]) env0 result) t ->
  match_conf (mode_cont (kappa) env0 result) t.
Proof.
  intros MC; inversion MC; subst; clear MC.
  econstructor.
  simpl; rewrite apply_conts_app; simpl.
  unfold apply_cont.
  rewrite (surjective_pairing (apply_conts kappa _)); simpl.
  eauto.
Qed.

Ltac match_conf :=
  repeat match goal with
  | [h: Value _ = fst (apply_conts _ (apply_return _, _)) |- _ ] =>
    learn (value_apply_conts_inversion_cont h);
    clear h
  | [h: Value _ = fst (apply_conts _ (_, _)) |- _ ] =>
    learn (value_apply_conts_inversion_eval h);
    clear h
  | [h: Conflict = fst (apply_conts _ (_, _)) |- _ ] =>
    learn (conflict_apply_conts_inversion_eval h);
    clear h
  | [h: Empty = fst (apply_conts _ (_, _)) |- _ ] =>
    learn (empty_apply_conts_inversion_eval h);
    clear h
  | [h: fst (apply_conts _ (_, _)) = Empty |- _ ] =>
    learn (empty_apply_conts_inversion_eval (eq_sym h));
    clear h
  | _ => progress match_conf1
  | _ => progress unpack
  end; eauto.


(* -------------------------------------------------------------------------- *)

Fixpoint last (l: list cont) (env0: list value) : list value :=
  match l with
  | [] => env0
  | CReturn env1 :: l =>
    last l env1
  | _ :: l =>
    last l env0
  end.

Lemma last_last:
  forall l env0 env1,
    last (l ++ [CReturn env0]) env1 = env0.
Proof.
  induction l.
  { intros; reflexivity. }
  { intros; simpl.
    case a; intros; rewrite IHl; eauto.
  }
Qed.

Lemma cred_process_return {kappa1 env0 result}: forall kappa2,
  List.Forall (fun k => exists sigma, k = CReturn sigma) kappa1 ->
  star cred
    (mode_cont (kappa1 ++ kappa2) env0 result)
    (mode_cont kappa2 (last kappa1 env0) result)
  .
Proof.
  intros. revert env0.
  induction H as [|? kappa1 [env1 Hk]]; subst; simpl; intros.
  { eapply star_refl. }
  { eapply star_step. { econstructor. }
    eapply IHForall.
  }
Qed.

Lemma cred_apply_state_Emtpy {s2}:
  fst (apply_state_aux s2) = Empty ->
  star cred s2 (mode_cont [] (last (stack s2) (env s2)) REmpty).
Proof.
  induction s2; simpl; intros H.
  { learn (empty_apply_conts_inversion_eval (eq_sym H)).
    match_conf; unpack_subst_of_env_cons.

    replace kappa with (kappa ++ []) at 1 by eapply List.app_nil_r .
    eapply star_step. { econstructor. }
    eapply cred_process_return; eauto.
  }
  { learn (empty_apply_conts_inversion_eval (eq_sym H)).
    match_conf; unpack_subst_of_env_cons.

    replace kappa with (kappa ++ []) at 1 by eapply List.app_nil_r .
    eapply cred_process_return; eauto.
  }
Qed.

Lemma last_snd_apply_conts :
  forall kappa env0 t, (snd (apply_conts kappa (t, env0))) = (last kappa env0).
Proof.
  induction kappa.
  { simpl; eauto. }
  { induction a; simpl; intros; try induction o; eapply IHkappa. }
Qed.


Ltac sp :=
  repeat match goal with
  | [ |- context [let '(_, _) := ?p in _]] =>
    rewrite (surjective_pairing p)
  | [h: context [let '(_, _) := ?p in _] |- _] =>
    rewrite (surjective_pairing p) in h
  end
.

Lemma apply_conts_forall_return: forall kappa t env,
        List.Forall (fun k : cont => exists sigma : list value, k = CReturn sigma) kappa -> fst (apply_conts kappa (t, env)) = t.
Proof.
  intros.
  induction kappa using List.rev_ind.
  { simpl; eauto. }
  { unpack; subst.
    rewrite apply_conts_app; simpl; unfold apply_cont; sp; simpl.
    eapply IHkappa; eauto.
  }
Qed.

Ltac cstep :=
  match goal with
  | [h: plus cred ?s1 ?s2 |- star cred ?s1 ?s2] =>
    eapply (plus_star h)
  | [h: plus cred ?s1 ?s2 |- plus cred ?s1 ?s2] =>
    eauto
  | [ |- plus cred ?s1 ?s2] =>
    eapply plus_left; [solve [econstructor; eauto|econstructor; repeat intro; inj]|]
  | [ |- star cred ?s1 ?s2] =>
    eapply star_step; [solve [econstructor; eauto|econstructor; repeat intro; inj]|]
  | [
    h: List.Forall (fun k => exists sigma, k = CReturn sigma) ?kappa1
    |- star cred
        (mode_cont (?kappa1 ++ _) _ _)
        _
    ] =>
      eapply star_trans; [solve [eapply cred_process_return; eauto]|]
  | [
    h: List.Forall (fun k => exists sigma, k = CReturn sigma) ?kappa1
    |- plus cred
        (mode_cont (?kappa1 ++ ?kappa2) ?env ?r)
        _
    ] =>
      eapply star_plus_trans; [solve [eapply cred_process_return; eauto]|]
  | [
    h: List.Forall (fun k => exists sigma, k = CReturn sigma) ?kappa1
    |- star cred
        (mode_cont (?kappa1 ++ ?kappa2) ?env ?r)
        _
    ] =>
      eapply star_trans; [solve [eapply cred_process_return; eauto]|]
  | [
    h: List.Forall (eq Empty) ?ts1
    |- star cred (mode_cont (CDefault _ (?ts1 ++ _) _ _::_) _ REmpty) _
    ] =>
    eapply star_trans; [solve[eapply cred_default_head_empty; eauto]|]
  | [
    h: List.Forall (eq Empty) ?ts1
    |- star cred (mode_cont (CDefault _ ?ts1 _ _::_) _ REmpty) _
    ] =>
    eapply star_trans; [solve[replace ts1 with (ts1 ++ []) by eapply List.app_nil_r; eapply cred_default_head_empty; eauto]|]
  | [h: star cred ?s1 ?s2 |- star cred ?s1' (append_stack ?s2 ?kappa)] =>
    replace s1' with (append_stack s1 kappa); [| solve [simpl; eauto]];
    eapply append_stack_stable_star
  | [h: plus cred ?s1 ?s2 |- plus cred ?s1' (append_stack ?s2 ?kappa)] =>
    replace s1' with (append_stack s1 kappa); [| solve [simpl; eauto]];
    eapply append_stack_stable_plus
  | [ |- star cred ?s1 ?s1] =>
    eapply star_refl
  | _ => try rewrite last_snd_apply_conts in *
end.

(* Same thing as cstep, but write the resulting sequence steps. *)
Ltac cstep_info := cstep;
  match goal with
  | [|- cred ?s _] =>
    idtac s "//";
    remember (apply_state s) as tmp;
    match goal with
    | [h: tmp = ?t |- _] => simpl in h
    end;
    match goal with
    | [h: tmp = ?t |- _] => idtac t "//"; clear tmp h
    end
  | [|- plus cred ?s _] =>
    idtac s "//";
    remember (apply_state s) as tmp;
    match goal with
    | [h: tmp = ?t |- _] => simpl in h
    end;
    match goal with
    | [h: tmp = ?t |- _] => idtac t "//"; clear tmp h
    end
  | [|- star cred ?s _] =>
    idtac s "//";
    remember (apply_state s) as tmp;
    match goal with
    | [h: tmp = ?t |- _] => simpl in h
    end;
    match goal with
    | [h: tmp = ?t |- _] => idtac t "//"; clear tmp h
    end
  end.

Ltac repeat_cstep_info :=
  idtac "--------------------------------------------------------------------------";
  repeat cstep_info;
  idtac "--------------------------------------------------------------------------".

(* -------------------------------------------------------------------------- *)

Ltac aexists t :=
  exists t; unlock; subst; split; [repeat cstep|match_conf].

(* -------------------------------------------------------------------------- *)

Require Import Wellfounded.

(* Well founded version of the rev_ind lemma. It provide both hypothesis: the well founded one ([forall l', length l' < length (l ++ [k]) -> P l']), and the [P l] one to prove [P (l ++ [k])]. This is usefull in the simulation proof because in some cases, we need to be able to apply the induction hypothesis on an empty list. *)

Theorem rev_ind_wf {A}:
  forall P:list A -> Prop,
    P [] ->
    (forall (x:A) (l:list A),
      P l ->
      (forall l', length l' < length (l ++ [x]) -> P l') ->
      P (l ++ [x])) ->
    forall l:list A, P l.
Proof.
  intros P Hnil Hcons l.
  induction l as [l IHl] using (
    well_founded_induction
      (wf_inverse_image _ nat _ (@length _)
      PeanoNat.Nat.lt_wf_0)).
  induction l using List.rev_ind.
  { eapply Hnil. }
  { eapply Hcons.
    { eapply IHl.
      rewrite List.last_length; lia.
    }
    { intros.
      eapply IHl.
      rewrite List.last_length in *; lia.
    }
  }
Qed.



(* -------------------------------------------------------------------------- *)


(* The simulation theorem is as follows *)

Theorem simulation_sred_cred t1 t2:
  sred t1 t2 ->
  forall s1, match_conf s1 t1 ->
  exists s2,
    (plus cred s1 s2)
  /\ match_conf s2 t2.
Abort.

(* The global proof strategy is to do an induction on [sred t1 t2], then we consider all possible [s1] such that [match_conf s1 t1]. Thanks to those two jypothesis ([sred t1 t2] and [match_conf s1 s2]), we know a few things about the general shape of [s1]. So we can do a few reductions on [s1], leading to a new state [s2] when we cannot be sure to reduce anymore. Because our semantics are deterministic, we have a good chance of getting to the correct [s2], ie an state such that [match_conf s2 t2] holds.

In more technicals details, we implement the interpretor to derive [star cred s1 s2] using ltac. All possible transitions (possibly multi-steps) are in the form [match goal with |[... |- star cred (* special shape *) _ /\ _ ] => some lemma]. The second part of the [_ /\ _] is the [match_conf]: since when we reduce we don't know s2, we need to keep this member as long as possible, to in the end do an [star_refl] and try to prove [match_conf s2 t2]. Hence, we leverage the following very basic logic theorem at this point:

*)

Theorem implication_left_and (A B C: Prop):
  (A -> B) -> (A /\ C -> B /\ C).
Proof.
  intros; unpack; eauto.
Qed.

(* Example utilization : *)

Goal forall s1 s2 s3,
  cred s1 s2 ->
  star cred s2 s3 ->
  exists s2,
    (plus cred s1 s2) /\ True.
Proof.
  intros.
  eexists.
  eapply implication_left_and.
  { eapply plus_left; eauto. }
  { eauto. }
Qed.

Lemma inv_state_mode_cont_CDefault_Hole_conts_empty:
  forall kappa o ts tj tc env r,
  inv_state (mode_cont (kappa ++ [CDefault Hole o ts tj tc]) env r) ->
  kappa = [].
Proof.
  induction kappa; intros; eauto.
  exfalso.
  inversion H; subst; unpack; inversion H4.
Qed.


Lemma inv_state_mode_eval_append {e kappa k env0}:
    inv_state (mode_eval e (kappa ++ [k]) env0) ->
    inv_state (mode_eval e (kappa) env0).
Proof.
  induction kappa; inversion 1; unpack; repeat econstructor; eauto.
Qed.

Lemma inv_state_mode_cont_append {r kappa k env0}:
    inv_state (mode_cont (kappa ++ [k]) env0 r) ->
    inv_state (mode_cont (kappa) env0 r).
Proof.
  induction kappa; inversion 1; unpack; repeat econstructor; eauto.
Qed.

Lemma ignore_inv_state s1 t2:
  inv_state s1 ->
  (exists s2, (plus cred s1 s2) /\ match_conf s2 t2) ->
  (exists s2, (plus cred s1 s2) /\ match_conf s2 t2 /\ inv_state s2).
Proof.
  intros; unpack.
  exists s2; repeat split; inversion H1; subst; eauto.
  learn (plus_star H0).
  eapply star_cred_inv_state_stable; eauto.
Qed.

(* The handling of CReturn is orthogonal to the other continuations, hence we proove it in a different way. *)
Lemma induction_case_CReturn
  (sigma: list value)
  (kappa: list cont)
  (IHkappa: forall t1 t2 : term,
            sred t1 t2 ->
            forall s1 : state,
            match_conf s1 t1 ->
            kappa = stack s1 ->
            inv_state s1 ->
            exists s2 : state, plus cred s1 s2 /\ match_conf s2 t2 /\ inv_state s2):
  forall t1 t2 : term,
    sred t1 t2 ->
    forall s1 : state,
      match_conf s1 t1 ->
      kappa ++ [CReturn sigma] = stack s1 ->
      inv_state s1 ->
      exists s2 : state, plus cred s1 s2 /\ match_conf s2 t2 /\ inv_state s2
.
Proof.
  intros t1 t2 Hsred.
  (** In order to be able to apply the induction, we need to remember that t1 reduces to t2, even after the induction on it. *)
  remember Hsred as Hsred'.
  destruct Hsred; clear HeqHsred'.
  all: intros s1 Hs1 tmp Hs1_inv; revert tmp.
  all: induction s1.
  all: simpl; intros; subst.
  all: learn (match_conf_eval_app_CReturn Hs1) +
      learn (match_conf_cont_app_CReturn Hs1).
  all:
    learn (inv_state_mode_cont_append Hs1_inv) +
    learn (inv_state_mode_eval_append Hs1_inv).
  all: eapply ignore_inv_state; eauto.
  all: destruct (IHkappa _ _ Hsred' _ H) as (s2 & Hs1s2 & Hs2 & Hs2_inv); [simpl;eauto|simpl; eauto|].
  all: aexists (append_stack s2 [CReturn sigma]).
  all: inversion Hs2; subst; eauto.
Qed.

Ltac info :=
  match goal with
  | [ |- plus cred ?s1 _ /\ _ ] =>
    idtac s1 "//"
  | [ |- star cred ?s1 _ /\ _ ] =>
    idtac s1 "//"
  | [ |- cred ?s1 _ /\ _ ] =>
    idtac s1 "//"
  | _ => idtac
  end.



Theorem simulation_sred_cred t1 t2:
  sred t1 t2 ->
  forall s1, match_conf s1 t1 -> inv_state s1 ->
  exists s2,
    (plus cred s1 s2)
  /\ match_conf s2 t2 /\ inv_state s2.
Proof.
  intros Hred s1 MC.
  remember (stack s1) as kappa.
  generalize dependent s1.
  generalize dependent t2.
  generalize dependent t1.
  induction kappa as [|k kappa IHkappa IHkappa_wf] using rev_ind_wf.
  { intros t1 t2 Hred.
    assert (Hred_current: sred t1 t2) by eauto.
    induction Hred; subst.
    all: induction s1; intro MC; inversion MC; clear MC; intros; repeat (simpl in *; subst).
    all: eapply ignore_inv_state; [eauto|].
    all: try solve [induction result; simpl in *; tryfalse].
    (* unpack except in the conflict case: we need for now to not unpack here as we first need to modify slightly the definition. *)
    all: unpack_subst_of_env_cons.
    all: repeat multimatch goal with

    (* induction hypothesis *)
    | [h1: forall t1 t2, sred t1 t2 -> _, h2: sred ?t1 ?t2 |- _] =>
      learn (h1 _ _ h2)
    | [h1: forall s, match_conf s ?u.[subst_of_env ?env] -> _ |- _] =>
      let s1 := constr:(mode_eval u [] env) in
      assert (tmp: match_conf s1 u.[subst_of_env env]) by (econstructor; simpl; eauto);
      learn (h1 s1 tmp);
      clear tmp
    | [h1: ?kappa = stack (mode_eval ?u ?kappa ?env0) -> _ |- _] =>
      simpl in h1
    | [h1: forall s, match_conf s (fst (apply_conts ?kappa (?e.[subst_of_env ?sigma], ?sigma))) -> _ |- _] =>
      let s1 := constr:(mode_eval e kappa sigma) in
      assert (tmp: match_conf s1 (fst (apply_conts kappa (e.[subst_of_env sigma], sigma)))) by (econstructor; simpl; eauto);
      learn (h1 s1 tmp)
    | [h1: forall s, match_conf s (fst (apply_conts ?kappa (apply_return ?r, ?sigma))) -> _ |- _] =>
      let s1 := constr:(mode_cont kappa sigma r) in
      assert (tmp: match_conf s1 (fst (apply_conts kappa (apply_return r, sigma)))) by (econstructor; simpl; eauto);
      learn (h1 s1 tmp)
    | [h: inv_state ?s -> _ |- _] =>
      assert (tmp: inv_state s) by (repeat econstructor);
      learn (h tmp);
      clear tmp

    | [h: ?A -> _ |- _] =>
      assert (tmp: A) by (simpl; eauto);
      learn (h tmp);
      clear tmp

    (* Strong induction hypothesis *)
    | [h: forall l': list cont, length l' < length (?kappa ++ [?k]) -> _ |- _] =>
      assert (Hlen: length ([]: list cont) < length (kappa ++ [k])) by (rewrite List.last_length; simpl; lia);
      learn (IHkappa_wf _ Hlen)

    (* basic unfoling & commun lemma learning*)
    | [h: plus _ _ _ |- _] =>
      learn (plus_star h)
    | [h: _ /\ _ |- _] => destruct h
    | [h: exists _, _ |- _] => destruct h
    | [h: match_conf _ _ |- _] =>
      inversion h; clear h; subst
    | _ => progress rewrite last_snd_apply_conts in *

    (* one step computation *)
    | [|- plus cred ?s1 ?s2 /\ _] =>
      info; eapply implication_left_and; [
        eapply plus_left; solve [
          econstructor; eauto|
          econstructor; repeat intro; inj]
      |]
    | [|- star cred ?s1 ?s2 /\ _] =>
      info; eapply implication_left_and; [
        eapply star_step; solve [
          econstructor; eauto|
          econstructor; repeat intro; inj]
      |]

    (* Multi steps computation *)
    | [h: star cred ?s1 ?s2 |- star cred ?s1 _ /\ _] =>
      info; eapply implication_left_and; [
        eapply star_trans; eapply h
      |]
    | [h: plus cred ?s1 ?s2 |- plus cred ?s1 _ /\ _] =>
      info; eapply implication_left_and; [
        eapply plus_star_trans; eapply h
      |]
    | [h: star cred ?s1 ?s2 |- plus cred ?s1 _ /\ _] =>
      match goal with
      [h: plus cred s1 s2 |- _] => fail 1
      end;
      info; eapply implication_left_and; [
        eapply star_plus_trans; eapply h
      |]

    | [
      h: List.Forall (fun k : cont => exists sigma : list value, k = CReturn sigma) ?kappa
      |- star cred (mode_cont (?kappa ++ _) _ _) _ /\ _] =>
      info; eapply implication_left_and;[
        eapply star_trans;
        eapply (cred_process_return _ h)
      |]

    | [
      h: List.Forall (fun k : cont => exists sigma : list value, k = CReturn sigma) ?kappa
      |- plus cred (mode_cont (?kappa ++ _) _ _) _ /\ _] =>
      info; eapply implication_left_and;[
        eapply star_plus_trans;
        eapply (cred_process_return _ h)
      |]

    | [
      h: plus cred _ ?s2
      |- context [mode_eval _ ?kappa _]
    ] =>
      (* check if there is an append stack on the right hand side to avoid looping *)
      match s2 with
      | context [append_stack] => fail 1
      | _ => idtac
      end;
      learn (append_stack_stable_plus _ _ h kappa)
    | [
      h: plus cred _ ?s2
      |- context [mode_eval _ (?kappa ++ [?k]) _]
    ] =>
      (* check if there is an append stack on the right hand side to avoid looping *)
      match s2 with
      | context [append_stack] => fail 1
      | _ => idtac
      end;
      learn (append_stack_stable_plus _ _ h [k])
    | [h: _ |- _] =>
      (* we want to simpl in all, but not in the learnt propositions *)
      let P := type of h in match P with | Learnt => fail 1 | _ => idtac end;
      simpl in h
    | [
      h: plus cred _ ?s2
      |- context [mode_eval _ ?kappa _]
    ] =>
      (* check if there is an append stack on the right hand side to avoid looping *)
      match s2 with
      | context [append_stack] => fail 1
      | _ => idtac
      end;
      learn (append_stack_stable_plus _ _ h kappa)
    | [
      h: plus cred _ ?s2
      |- context [mode_eval _ (?kappa ++ [?k]) _]
    ] =>
      (* check if there is an append stack on the right hand side to avoid looping *)
      match s2 with
      | context [append_stack] => fail 1
      | _ => idtac
      end;
      learn (append_stack_stable_plus _ _ h [k])
    | [h: _ |- _] =>
      (* we want to simpl in all, but not in the learnt propositions *)
      let P := type of h in match P with | Learnt => fail 1 | _ => idtac end;
      simpl in h
    | [
      h: plus cred _ ?s2
      |- context [mode_cont ?kappa _ _]
    ] =>
      (* check if there is an append stack on the right hand side to avoid looping *)
      match s2 with
      | context [append_stack] => fail 1
      | _ => idtac
      end;
      learn (append_stack_stable_plus _ _ h kappa)
    | [
      h: plus cred _ ?s2
      |- context [mode_cont (?kappa ++ [?k]) _ _]
    ] =>
      (* check if there is an append stack on the right hand side to avoid looping *)
      match s2 with
      | context [append_stack] => fail 1
      | _ => idtac
      end;
      learn (append_stack_stable_plus _ _ h [k])
    | [h: _ |- _] =>
      (* we want to simpl in all, but not in the learnt propositions *)
      let P := type of h in match P with | Learnt => fail 1 | _ => idtac end;
      simpl in h

    | [h: star cred ?s1 ?s2 |- _] =>
      learn (creds_apply_state_sigma_stable h)

    | [ h: Value _ = ?t.[subst_of_env _] |- _] =>
      induction t; simpl in h; tryfalse; unpack_subst_of_env_cons

    (* When no more progress is possible, we can finaly introduce the evar corresponding to the goal term. This is to avoid having variable completing our evar that escape the scope they were defined in. *)
    | [ |- exists _, _] =>
    idtac "---"; eexists
    | _ =>
      info;
      solve [split; [eapply star_refl|];
      try solve [
        econstructor; eauto

      (* Majority of the cases *)
      | econstructor; repeat rewrite apply_state_append_stack;
        simpl; unfold apply_cont; simpl; sp; simpl in *;
        repeat match goal with
        | _ => progress eauto
        | _ => progress f_equal
        end
      (* For return cases *)
      | econstructor; simpl; rewrite subst_env_cons; asimpl; eauto
      ]]
    end.
    { (* Lambda case *)
      split; [eapply star_refl|].
      eapply match_value; econstructor; eauto.
    }
    { split; [eapply star_refl|].
      econstructor; repeat rewrite apply_state_append_stack;
      simpl; unfold apply_cont; simpl; sp; simpl in *.
      rewrite apply_CDefault_nohole_none.
      repeat f_equal; eauto.
    }
  }
  { (* induction step.*)
    intros t1 t2 Hred.
    assert (Hred_current: sred t1 t2) by eauto.
    induction Hred; subst.
    all: induction k.
    all: try solve [intros; eapply induction_case_CReturn; eauto; econstructor; eauto].
    all: induction s1.
    all: try (remember o as o' eqn: Heqo; lock Heqo; induction o').
    all: try (remember b as b' eqn: Heqb; lock Heqb; induction b').
    all: intros MC Heqkappa; revert MC; simpl in Heqkappa; subst.
    all: intros MC; inversion MC; simpl; subst.
    all: first [rewrite append_stack_eval in * | repeat rewrite append_stack_cont in *].

    all: match_conf; try solve [tryfalse]; subst.


    (* all: match goal with
      | [|- context [mode_eval ?t (?kappa ++ [?k]) ?env0]] =>
        remember (mode_eval t kappa env0) as s1'; lock Heqs1'
      | [|- context [mode_cont (?kappa ++ [?k]) ?env0 ?r]] =>
        remember (mode_cont kappa env0 r) as s1'; lock Heqs1'
      end. *)
    all: unpack_subst_of_env_cons.
(* 
    88:{
      inversion MC; subst; clear MC.
      rewrite append_stack_eval in *.
      rewrite apply_state_append_stack in *.
      simpl in *.
      unfold apply_cont in *.
      match goal with
        | [h: context [let '(_, _) := ?p in _] |- _] =>
          rewrite (surjective_pairing p) in h
      end.
      simpl in *.
      match goal with
      |[hneq: ?t <> Empty, h: context[apply_CDefault Hole None _ _ _ ?t _] |- _] =>
        rewrite (apply_CDefault_hole_none_nempty _ _ _ _ _  hneq) in h
      end.
      injections.
      simpl in H0.
      injection H0.
      first [
        rewrite apply_CDefault_hole_none_empty in *;
        rewrite apply_CDefault_hole_none_nempty in *;
        rewrite apply_CDefault_hole_some_empty in *;
        rewrite apply_CDefault_hole_some_nempty in *;
        rewrite apply_CDefault_nohole_none in *;
        rewrite apply_CDefault_nohole_some in *].
    } *)
    all: intros H_inv; eapply ignore_inv_state; [eauto|].

    all: repeat multimatch goal with
    (* induction hypothesis *)

    | [h1: forall t1 t2, sred t1 t2 -> _, h2: sred ?t1 ?t2 |- _] =>
      learn (h1 _ _ h2)
    | [h1: forall s, match_conf s ?u.[subst_of_env ?env] -> _ |- _] =>
      let s1 := constr:(mode_eval u [] env) in
      assert (tmp: match_conf s1 u.[subst_of_env env]) by (econstructor; simpl; eauto);
      learn (h1 s1 tmp);
      clear tmp
    | [h1: ?kappa = stack (mode_eval ?u ?kappa ?env0) -> _ |- _] =>
      simpl in h1
    | [h1: forall s, match_conf s (fst (apply_conts ?kappa (?e.[subst_of_env ?sigma], ?sigma))) -> _ |- _] =>
      let s1 := constr:(mode_eval e kappa sigma) in
      assert (tmp: match_conf s1 (fst (apply_conts kappa (e.[subst_of_env sigma], sigma)))) by (econstructor; simpl; eauto);
      learn (h1 s1 tmp)
    | [h1: forall s, match_conf s (fst (apply_conts ?kappa (apply_return ?r, ?sigma))) -> _ |- _] =>
      let s1 := constr:(mode_cont kappa sigma r) in
      assert (tmp: match_conf s1 (fst (apply_conts kappa (apply_return r, sigma)))) by (econstructor; simpl; eauto);
      learn (h1 s1 tmp)

    | [h: inv_state ?s -> _ |- _] =>
      assert (tmp: inv_state s) by (repeat econstructor);
      learn (h tmp);
      clear tmp

    | [h: ?A -> _ |- _] =>
      assert (tmp: A) by (simpl; eauto);
      learn (h tmp);
      clear tmp

    (* Strong induction hypothesis *)
    | [h: forall l': list cont, length l' < length (?kappa ++ [?k]) -> _ |- _] =>
      assert (Hlen: length ([]: list cont) < length (kappa ++ [k])) by (rewrite List.last_length; simpl; lia);
      learn (IHkappa_wf _ Hlen)

    (* basic unfoling & commun lemma learning*)
    | [h: plus _ _ _ |- _] =>
      learn (plus_star h)
    | [h: _ /\ _ |- _] => destruct h
    | [h: exists _, _ |- _] =>
      destruct h
    | [h: match_conf _ _ |- _] =>
      inversion h; clear h; subst
    | _ => progress rewrite last_snd_apply_conts in *


    (* Fact learning about inv_state. *)
    | [h: inv_state (mode_eval _ (_ ++ [_]) _) |- _] =>
      learn (inv_state_mode_eval_append h)
    | [h: inv_state (mode_cont (_ ++ [_]) _ _) |- _] =>
      learn (inv_state_mode_cont_append h)

    | [
      h: plus cred _ ?s2
      |- context [mode_eval _ ?kappa _]
    ] =>
      (* check if there is an append stack on the right hand side to avoid looping *)
      match s2 with
      | context [append_stack] => fail 1
      | _ => idtac
      end;
      learn (append_stack_stable_plus _ _ h kappa)
    | [
      h: plus cred _ ?s2
      |- context [mode_eval _ (?kappa ++ [?k]) _]
    ] =>
      (* check if there is an append stack on the right hand side to avoid looping *)
      match s2 with
      | context [append_stack] => fail 1
      | _ => idtac
      end;
      learn (append_stack_stable_plus _ _ h [k])
    | [h: _ |- _] =>
      (* we want to simpl in all, but not in the learnt propositions *)
      let P := type of h in match P with | Learnt => fail 1 | _ => idtac end;
      simpl in h
    | [
      h: plus cred _ ?s2
      |- context [mode_eval _ ?kappa _]
    ] =>
      (* check if there is an append stack on the right hand side to avoid looping *)
      match s2 with
      | context [append_stack] => fail 1
      | _ => idtac
      end;
      learn (append_stack_stable_plus _ _ h kappa)
    | [
      h: plus cred _ ?s2
      |- context [mode_eval _ (?kappa ++ [?k]) _]
    ] =>
      (* check if there is an append stack on the right hand side to avoid looping *)
      match s2 with
      | context [append_stack] => fail 1
      | _ => idtac
      end;
      learn (append_stack_stable_plus _ _ h [k])
    | [h: _ |- _] =>
      (* we want to simpl in all, but not in the learnt propositions *)
      let P := type of h in match P with | Learnt => fail 1 | _ => idtac end;
      simpl in h
    | [
      h: plus cred _ ?s2
      |- context [mode_cont ?kappa _ _]
    ] =>
      (* check if there is an append stack on the right hand side to avoid looping *)
      match s2 with
      | context [append_stack] => fail 1
      | _ => idtac
      end;
      learn (append_stack_stable_plus _ _ h kappa)
    | [
      h: plus cred _ ?s2
      |- context [mode_cont (?kappa ++ [?k]) _ _]
    ] =>
      (* check if there is an append stack on the right hand side to avoid looping *)
      match s2 with
      | context [append_stack] => fail 1
      | _ => idtac
      end;
      learn (append_stack_stable_plus _ _ h [k])
    | [h: _ |- _] =>
      (* we want to simpl in all, but not in the learnt propositions *)
      let P := type of h in match P with | Learnt => fail 1 | _ => idtac end;
      simpl in h

    | [h: star cred ?s1 ?s2 |- _] =>
      learn (creds_apply_state_sigma_stable h)

    | [ h: Value _ = ?t.[subst_of_env _] |- _] =>
      induction t; simpl in h; tryfalse; unpack_subst_of_env_cons

      (* one step computation *)
      | [|- plus cred ?s1 ?s2 /\ _] =>
        info; eapply implication_left_and; [
          eapply plus_left; solve [
            econstructor; eauto|
            econstructor; repeat intro; inj]
        |]
      | [|- star cred ?s1 ?s2 /\ _] =>
        info; eapply implication_left_and; [
          eapply star_step; solve [
            econstructor; eauto|
            econstructor; repeat intro; inj]
        |]

      (* Multi steps computation *)
      | [h: star cred ?s1 ?s2 |- star cred ?s1 _ /\ _] =>
        info; eapply implication_left_and; [
          eapply star_trans; eapply h
        |]
      | [h: plus cred ?s1 ?s2 |- plus cred ?s1 _ /\ _] =>
        info; eapply implication_left_and; [
          eapply plus_star_trans; eapply h
        |]
      | [h: star cred ?s1 ?s2 |- plus cred ?s1 _ /\ _] =>
        match goal with
        [h: plus cred s1 s2 |- _] => fail 1
        end;
        info; eapply implication_left_and; [
          eapply star_plus_trans; eapply h
        |]

      | [
        h: List.Forall (fun k : cont => exists sigma : list value, k = CReturn sigma) ?kappa
        |- star cred (mode_cont (?kappa ++ _) _ _) _ /\ _] =>
        info; eapply implication_left_and;[
          eapply star_trans;
          eapply (cred_process_return _ h)
        |]

      | [
        h: List.Forall (fun k : cont => exists sigma : list value, k = CReturn sigma) ?kappa
        |- plus cred (mode_cont (?kappa ++ _) _ _) _ /\ _] =>
        info; eapply implication_left_and;[
          eapply star_plus_trans;
          eapply (cred_process_return _ h)
        |]

    (* When no more progress is possible, we can finaly introduce the evar corresponding to the goal term. This is to avoid having variable completing our evar that escape the scope they were defined in. *)
    | [ |- exists _, _] =>
      let P := type of Hred_current in idtac "---"; idtac P "//"; eexists
    | _ =>
      first[solve [split; [info; eapply star_refl|];
      solve [
        econstructor; eauto

      (* Majority of the cases *)
      | econstructor; repeat rewrite apply_state_append_stack;
        simpl; unfold apply_cont; simpl;
        match goal with
        | [ |- context [let '(_, _) := ?p in _]] =>
          rewrite (surjective_pairing p)
        end; simpl in *;
        repeat match goal with
        | _ => progress eauto
        | _ => progress f_equal
        end
      (* For return cases *)
      | econstructor; simpl; rewrite subst_env_cons; asimpl; eauto
      ]; idtac "ok"] | idtac "notok"]
    end.
    
    all: try solve [ repeat match goal with
    | [h: context [apply_conts (_ ++ [?k]) _] |- _ ] =>
      repeat rewrite apply_conts_app in h;
      simpl in h;
      unfold apply_cont in h;
      sp;
      simpl in h;
      injections
    end;
    try match goal with
      | [h: Value _ = _ |- _] =>
        destruct (value_apply_conts_inversion_eval h);
        tryfalse
    end].


    all: try solve [
      split; [eapply star_refl|];
      econstructor;
      rewrite apply_state_append_stack;
      simpl; unfold apply_cont; sp; simpl;
      match goal with
      | [|- _ = apply_CDefault _ _ _ _ _ ?t _] =>
        learn (EmptyOrNotEmpty t)
      end; unpack;
      first
      [
      rewrite apply_CDefault_hole_none_empty|
      rewrite apply_CDefault_hole_none_nempty|
      rewrite apply_CDefault_hole_some_empty|
      rewrite apply_CDefault_hole_some_nempty|
      rewrite apply_CDefault_nohole_none|
      rewrite apply_CDefault_nohole_some
      ];
      eauto; simpl; repeat f_equal; eauto
    ].

    (** Special incorrect case: *)

    all:
      (* oh well, didn't saw this one coming. Hred is inconsistant. In some cases. *)
      try solve [exfalso;
      rewrite apply_conts_forall_return in Hred; eauto;
      inversion Hred].

    { repeat split.
      eapply star_step. }
    { learn (inv_state_mode_cont_CDefault_Hole_conts_empty _ _ _ _ _ _ _ H_inv).
      subst.
      inversion H27.
      inversion H50.
    }
    { inversion H_inv; unpack.
      inversion H57.
    }
    { learn (inv_state_mode_cont_CDefault_Hole_conts_empty _ _ _ _ _ _ _ H_inv).
      subst.
      inversion H27.
      inversion H50.
    }
    {
      exfalso.
      rewrite apply_conts_app in *.
      simpl in *.
      unfold apply_cont in *; sp; simpl in *.
      rewrite apply_conts_forall_return in H10; eauto.
      rewrite apply_CDefault_hole_none_empty in *; eauto.
      repeat injections.
      Require Import common.
      rewrite last_snd_apply_conts in *.
      eapply fuck_stdlib; eauto.
    }
    { exfalso.
      rewrite apply_conts_app in *.
      simpl in *.
      unfold apply_cont in *; sp; simpl in *.
      rewrite apply_conts_forall_return in H10; eauto.
      rewrite apply_CDefault_hole_some_empty in *; eauto.
      repeat injections.
      rewrite last_snd_apply_conts in *.
      eapply fuck_stdlib; eauto.
    }
  }

  Unshelve.
  all: eauto.
  all: exact (mode_eval Empty [] []).
Qed.

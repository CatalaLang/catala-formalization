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
      Default ((Value (VPure v)).[subst_of_env sigma]::t::ts..[subst_of_env sigma]) tj.[subst_of_env sigma] tc.[subst_of_env sigma].
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


Ltac simpl_apply_CDefault := 
  match goal with
  | [h1: ?t=Empty, h2: context [apply_CDefault Hole (Some _) _ _ _ ?t _] |- _] =>
    rewrite apply_CDefault_hole_some_empty in h2
  | [h1: ?t=Empty |- context [apply_CDefault Hole (Some _) _ _ _ ?t _]] =>
    rewrite apply_CDefault_hole_some_empty in h1
  | [h1: ?t=Empty, h2: context [apply_CDefault Hole (None) _ _ _ ?t _] |- _] =>
    rewrite apply_CDefault_hole_none_empty in h2
  | [h1: ?t=Empty |- context [apply_CDefault Hole (None) _ _ _ ?t _]] =>
    rewrite apply_CDefault_hole_none_empty in h1
  | [h1: ?t<>Empty, h2: context [apply_CDefault Hole (Some _) _ _ _ ?t _] |- _] =>
    rewrite apply_CDefault_hole_some_nempty in h2
  | [h1: ?t<>Empty |- context [apply_CDefault Hole (Some _) _ _ _ ?t _]] =>
    rewrite apply_CDefault_hole_some_nempty in h1
  | [h1: ?t<>Empty, h2: context [apply_CDefault Hole (None) _ _ _ ?t _] |- _] =>
    rewrite apply_CDefault_hole_none_nempty in h2
  | [h1: ?t<>Empty |- context [apply_CDefault Hole (None) _ _ _ ?t _]] =>
    rewrite apply_CDefault_hole_none_nempty in h1
  | [h: context [apply_CDefault NoHole (Some _) _ _ _ ?t _] |- _] =>
    rewrite apply_CDefault_nohole_some in h
  | [|- context [apply_CDefault NoHole (Some _) _ _ _ ?t _]] =>
    rewrite apply_CDefault_nohole_some in *
  | [h: context [apply_CDefault NoHole None _ _ _ ?t _] |- _] =>
    rewrite apply_CDefault_nohole_none in h
  | [|- context [apply_CDefault NoHole None _ _ _ ?t _]] =>
    rewrite apply_CDefault_nohole_none in *
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
  | CFold f ts =>
    (Fold f.[subst_of_env sigma] ts..[subst_of_env sigma] t, sigma)
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

Section APPLY_EXAMPLES.

  Example test1:
    forall t1 t2 t3,
      fst (apply_conts [CBinopR Add t1; CAppR t2] (t3,[]))
      = App (Binop Add t3 t1) t2.
  Proof.
    intros.
    unfold apply_conts.
    simpl; repeat rewrite soe_nil; asimpl.
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

Lemma subst_of_env_Value {v t' env}:
  Value v = t'.[subst_of_env env] ->
  t' = Value v \/ exists x, t' = Var x /\ List.nth_error env x = Some v.
Proof.
  destruct t'; asimpl; intros; tryfalse; inj; eauto.
  unfold subst_of_env in *.
  remember (List.nth_error env x) as o.
  induction o; subst; tryfalse; inj; eauto.
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

Lemma subst_of_env_Fold {f ts ti t' env}:
  Fold f ts ti = t'.[subst_of_env env] ->
  exists f' ts' ti',
    f = f'.[subst_of_env env]
    /\ ts = ts'..[subst_of_env env]
    /\ ti = ti'.[subst_of_env env]
    /\ t' = Fold f' ts' ti'
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

  | [h: Value _ = _.[subst_of_env _] |- _] =>
    learn (subst_of_env_Value h); clear h; unzip; subst

  | [h: Match_ _ _ _ = _.[subst_of_env _] |- _] =>
    let u := fresh "u" in
    let t1 := fresh "t1" in
    let t2 := fresh "t2" in
    let Hu := fresh "Hu" in
    let Ht1 := fresh "Ht1" in
    let Ht2 := fresh "Ht2" in
    let Ht := fresh "Ht" in
    destruct (subst_of_env_Match_ h) as (u & t1 & t2 & Hu & Ht1 & Ht2 & Ht); subst; clear h
  | [h: Fold _ _ _ = _.[subst_of_env _] |- _] =>
    let f := fresh "f" in
    let ts := fresh "ts" in
    let ti := fresh "t" in
    let Hf := fresh "Hf" in
    let Hts := fresh "Hts" in
    let Hti := fresh "Hti" in
    let Ht := fresh "Ht" in
    destruct (subst_of_env_Fold h) as (f & ts & ti & Hf & Hts & Hti & Ht); subst; clear h
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
    eapply star_cred_append_stack
  | [h: plus cred ?s1 ?s2 |- plus cred ?s1' (append_stack ?s2 ?kappa)] =>
    replace s1' with (append_stack s1 kappa); [| solve [simpl; eauto]];
    eapply plus_cred_append_stack
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


(*** Main sim_state definition ***)

Inductive sim_state: state -> term -> Prop :=
  | InvBase: forall s,
    sim_state s (apply_state s)
  | InvStep: forall s t1,
    sim_state s t1 ->
    forall t2,
    sim_term t1 t2 ->
    sim_state s t2
.

(* Smart constructors and inversion for the sim_state inductive *)

Lemma sim_state_inversion:
  forall s t1,
  sim_state s t1 ->
  exists t,
    sim_term t1 t /\ apply_state s = t.
Proof.
  induction 1.
  { eexists; split; eauto. reflexivity. }
  { intros; inj; subst.
    edestruct IHsim_state; eauto; unpack.
    eexists; split; eauto.
    symmetry.
    etransitivity.
    symmetry.
    eauto.
    eauto.
  }
Qed.

Lemma sim_state_from_equiv {t2 s}:
  sim_term (apply_state s) t2 ->
  sim_state s t2.
Proof.
  repeat econstructor; eauto.
Qed.

(* The simulation theorem is as follows *)

Theorem simulation_sred_cred s1 t2:
  sred (apply_state s1) t2 ->
  exists s2,
    sim_state s2 t2 /\
    (plus cred s1 s2).
Abort.

(* The global proof strategy is to do an induction on [sred t1 t2], then we consider all possible [s1] such that [match_conf s1 t1]. Thanks to those two jypothesis ([sred t1 t2] and [match_conf s1 s2]), we know a few things about the general shape of [s1]. So we can do a few reductions on [s1], leading to a new state [s2] when we cannot be sure to reduce anymore. Because our semantics are deterministic, we have a good chance of getting to the correct [s2], ie an state such that [match_conf s2 t2] holds.

In more technicals details, we implement the interpretor to derive [star cred s1 s2] using ltac. All possible transitions (possibly multi-steps) are in the form [match goal with |[... |- star cred (* special shape *) _ /\ _ ] => some lemma]. The second part of the [_ /\ _] is the [match_conf]: since when we reduce we don't know s2, we need to keep this member as long as possible, to in the end do an [star_refl] and try to prove [match_conf s2 t2]. Hence, we leverage the following very basic logic theorem at this point:

*)


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

Lemma ignore_inv_state { P : state -> term -> Prop }{ s1 t2 }:
  inv_state s1 ->
  (exists s2, P s2 t2 /\ (plus cred s1 s2)) ->
  (exists s2, (P s2 t2 /\ inv_state s2) /\ (plus cred s1 s2) ).
Proof.
  intros; unpack.
  exists s2; repeat split; inversion H1; subst; eauto.
  eapply star_cred_inv_state_stable; eauto.
  eapply cred_inv_state_stable; eauto.
Qed.

Lemma sim_state_eval_app_CReturn {e kappa sigma env0 t}:
  sim_state (mode_eval e (kappa ++ [CReturn sigma]) env0) t ->
  sim_state (mode_eval e (kappa) env0) t.
Proof.
  intros H.
  pose proof (sim_state_inversion _ _ H); unpack; subst; clear H.
  eapply sim_state_from_equiv.
  simpl in *; rewrite apply_conts_app in *; simpl in *.
  unfold apply_cont in *; sp; simpl in *.
  symmetry; eauto.
Qed.

Lemma sim_state_cont_app_CReturn {result kappa sigma env0 t}:
  sim_state (mode_cont (kappa ++ [CReturn sigma]) env0 result) t ->
  sim_state (mode_cont (kappa) env0 result) t.
Proof.
  intros H.
  pose proof (sim_state_inversion _ _ H); unpack; subst; clear H.
  eapply sim_state_from_equiv.
  simpl in *; rewrite apply_conts_app in *; simpl in *.
  unfold apply_cont in *; sp; simpl in *.
  symmetry; eauto.
Qed.

(* The handling of CReturn is orthogonal to the other continuations, hence we proove it in a different way. *)
Lemma induction_case_CReturn
  (sigma: list value)
  (kappa: list cont)
  (IHkappa: forall s1 : state,
            kappa = stack s1 ->
            forall t2 : term,
            sred (fst (apply_state_aux s1)) t2 ->
            exists s2 : state, (sim_state s2 t2 /\ inv_state s2) /\ plus cred s1 s2 ):

  forall s1 : state,
  kappa ++ [CReturn sigma] = stack s1 ->
  forall t2 : term,
  sred (fst (apply_state_aux s1)) t2 ->
  exists s2 : state, (sim_state s2 t2 /\ inv_state s2) /\ plus cred s1 s2 
  .
Proof.
  intros.
  assert (Heq: fst (apply_state_aux s1) = fst (apply_state_aux (with_stack s1 kappa))).
  { induction s1; simpl in *; subst; rewrite apply_conts_app; simpl; unfold apply_cont; sp; simpl; eauto. }

  rewrite Heq in *.

  epose proof (IHkappa _ _ _ H0); unpack.
  learn (sim_state_inversion _ _ H1); unpack.
  induction s1; simpl in *; subst.

  all: eapply plus_star_trans_prop; [erewrite append_stack_app; [|solve[simpl; reflexivity]]; eapply plus_cred_append_stack; simpl; eauto |].
  all: eapply star_refl_prop; split.
  1,3: eapply sim_state_from_equiv; simpl.
  1-2: induction s2; simpl in *; subst; rewrite apply_conts_app; simpl; unfold apply_cont; sp; simpl; eauto.
  1-4: symmetry; eauto.

  all: eapply inv_state_append_stack; repeat econstructor; eauto.

  Unshelve.
  induction s1; simpl; eauto.
Qed.

(* Ltac info :=
  match goal with
  | [ |- plus cred ?s1 _ /\ _ ] =>
    idtac s1 "//"
  | [ |- star cred ?s1 _ /\ _ ] =>
    idtac s1 "//"
  | [ |- cred ?s1 _ /\ _ ] =>
    idtac s1 "//"
  | _ => idtac
  end. *)

Ltac info := idtac.

Lemma snd_apply_conts_last :
  forall kappa env0 t, (snd (apply_conts kappa (t, env0))) = (last kappa env0).
Proof.
  induction kappa.
  { simpl; eauto. }
  { induction a; simpl; intros; eauto. }
Qed.

Lemma cred_snd_apply_sate {s1 s2}:
  cred s1 s2 ->
  snd (apply_state_aux s1) = snd (apply_state_aux s2).
Proof.
  induction 1; try induction phi; simpl; repeat rewrite snd_apply_conts_last; eauto.
  { exfalso. eapply H; eauto. }
Qed.

Lemma star_cred_snd_apply_sate {s1 s2}:
  star cred s1 s2 ->
  snd (apply_state_aux s1) = snd (apply_state_aux s2).
Proof.
  induction 1; eauto.
  rewrite <- IHstar.
  eapply cred_snd_apply_sate; eauto.
Qed.

Theorem simulation_sred_cred_base s1 t2:
  sred (apply_state s1) t2 ->
  inv_state s1 ->
  exists s2,
    (sim_state s2 t2 /\ inv_state s2) /\ plus cred s1 s2.
Proof.
  intros Hred.
  remember (stack s1) as kappa.
  generalize dependent s1.
  generalize dependent t2.
  induction kappa as [|k kappa IHkappa IHkappa_wf] using rev_ind_wf.
  { intros t2 s1 Hred Hs1.
    pose proof Hred as Hred_current.
    remember (fst (apply_state_aux s1)) as t1.
    generalize dependent s1.
    induction Hred; subst.
    all: induction s1; try induction result; simpl in *; subst; intros.
    all: unfold apply_conts in Heqt1; simpl in Heqt1.
    all: eapply ignore_inv_state; [eauto|].
    all: unpack_subst_of_env_cons.

    all: (* expand and apply induction hypothesis *)
      repeat match goal with
      | [h: sred ?t1.[subst_of_env ?sigma] ?t2 -> (forall s:state, _) , hA: sred ?t1.[subst_of_env ?sigma] ?t2 |- _] =>
      destruct (IHHred Hred (mode_eval t1 [] env0) eq_refl eq_refl); [solve[repeat econstructor; eauto]|]; clear h; unpack
      | [h: plus _ _ _ |- _] => learn (plus_star h)
      | [h: sim_state _ _ |- _] => learn (sim_state_inversion _ _ h); unpack
      | [h: star _ _ _ |- _] => learn (star_cred_snd_apply_sate h)
      end.
    all: (* progress the computation as possible *)
      repeat first
      [ eapply star_trans_prop;
        [solve [rewrite append_stack_all; eapply star_cred_append_stack;simpl;eauto]|]
      | eapply plus_step_prop; 
        [solve[econstructor; repeat intro; inj; eauto]|]
      | eapply star_step_prop;
        [solve[econstructor; repeat intro; inj; eauto]|]
      ].
    all: (* finish it off *)
      eapply star_refl_prop; eapply sim_state_from_equiv.
    all: (* for recursive cases, we apply the induction hypothesis and lift it using append_stack *)
      try rewrite apply_state_append_stack; simpl in *; subst; unfold apply_cont; sp; simpl.
    all: (* for default cases *)
      try simpl_apply_CDefault.
    all: repeat econstructor.
    all: try solve
      [ reflexivity
      | eauto
      | symmetry; eauto
      | rewrite soe_cons; asimpl; reflexivity
    ].
    { rewrite soe_nil; asimpl; reflexivity. }
  }
  { admit "todo". }
Admitted.

Lemma proper_sim_state_sred:
  forall t1 t2,
    sred t1 t2 ->
    forall u1,
      sim_term t1 u1 ->
      exists u2,
        sim_term t2 u2 /\ sred u1 u2.
Proof.
  induction 1; intros; repeat sinv_sim_term; subst.
  (* induction hypothesis *)
  all: repeat match goal with
    | [ih: forall x, ?P x -> _, h: ?P _ |- _] => 
      learn (ih _ h); unpack; subst end.

  (* Most cases are trivial. *)
  all: try solve[repeat econstructor; eauto].

  { repeat econstructor.
    rewrite soe_nil.
    asimpl.
    eauto.
  }
  { repeat econstructor.
    repeat rewrite subst_of_env_decompose.
    eapply sim_term_subst; eauto.
    { induction x; asimpl; repeat econstructor; eauto. }
  }
  { induction op2, v1, v2; simpl in *; tryfalse; inj; repeat sinv_sim_term.
    all: repeat econstructor.
  }
  { repeat econstructor.
    eapply sim_term_subst; eauto.
    induction x; simpl; repeat econstructor; eauto.
  }
Qed.

Lemma proper_sim_state_star_sred:
  forall t1 t2,
    star sred t1 t2 ->
    forall u1,
      sim_term t1 u1 ->
      exists u2,
        sim_term t2 u2 /\ star sred u1 u2.
Proof.
  induction 1 using star_ind_n1.
  { repeat econstructor; eauto. }
  { intros ? Ht1.
    learn (IHstar _ Ht1); unpack.
    learn (proper_sim_state_sred _ _ H _ H1); unpack.
    eexists; split; eauto.
    eapply star_step_n1; eauto.
  }
Qed.


Theorem simulation_sred_cred:
  forall t1 t2,
    sred t1 t2 ->
    forall s1,
      inv_state s1 ->
      sim_state s1 t1 ->
      exists s2,
      inv_state s2 /\ sim_state s2 t2 /\ plus cred s1 s2.
Proof.
  intros ? ? Ht1t2 ? Hs1 Hs1t1.
  learn (sim_state_inversion _ _ Hs1t1); unpack; subst; clear Hs1t1.
  learn (proper_sim_state_sred _ _ Ht1t2 _ H); unpack.
  learn (simulation_sred_cred_base _ _ H3 Hs1); unpack; subst.
  eexists; repeat split; eauto.
  { learn (sim_state_inversion _ _ H4); unpack; subst.
    eapply sim_state_from_equiv.
    symmetry.
    etransitivity; eauto.
  }
Qed.


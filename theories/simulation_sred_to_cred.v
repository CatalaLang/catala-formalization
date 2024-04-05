Require Import syntax continuations small_step sequences tactics.
Require Import Coq.ZArith.ZArith.
Import List.ListNotations.


From Ltac2 Require Import Ltac2.
From Ltac2 Require Import Constr Std Message Control List Int.
Set Default Proof Mode "Classic".


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

(* An other tentative of writing thise would be *)

Definition apply_CDefault_case_hole o ts t sigma := 
  match t with
  | Empty => 
    match o with
    | Some v => ((Value (VPure v)).[subst_of_env sigma]::ts..[subst_of_env sigma])
    | None => ts..[subst_of_env sigma]
    end
  | _ =>
    match o with
    | Some v => ((Value (VPure v)).[subst_of_env sigma]::t::ts..[subst_of_env sigma])
    | None => t::ts..[subst_of_env sigma]
    end
  end.

Lemma apply_CDefault_case_hole_empty {o ts t sigma} :
  (t = Empty) ->
  apply_CDefault_case_hole o ts t sigma = match o with
  | Some v => ((Value (VPure v)).[subst_of_env sigma]::ts..[subst_of_env sigma])
  | None => ts..[subst_of_env sigma]
  end.
Proof. intros; subst; eauto. Qed.

Lemma apply_CDefault_case_hole_nempty {o ts t sigma} :
  (t <> Empty) ->
  apply_CDefault_case_hole o ts t sigma = match o with
  | Some v => ((Value (VPure v)).[subst_of_env sigma]::t::ts..[subst_of_env sigma])
  | None => t::ts..[subst_of_env sigma]
  end.
Proof. induction t; intros; subst; eauto; tryfalse. Qed.

Definition apply_CDefault_usable b o ts tj tc t sigma := 
  Default (
    match b with
    | Hole =>
      apply_CDefault_case_hole o ts t sigma
    | NoHole =>
      match o with
      | Some v => ((Value (VPure v)).[subst_of_env sigma]::t::ts..[subst_of_env sigma])
      | None => t::ts..[subst_of_env sigma]
      end
    end
  ) tj.[subst_of_env sigma] tc.[subst_of_env sigma].

Lemma apply_CDefault_apply_CDefault_usable {b o ts tj tc t sigma}:
  apply_CDefault b o ts tj tc t sigma
  = apply_CDefault_usable b o ts tj tc t sigma.
Proof.
  induction b, o; induction t; subst; simpl; try reflexivity.
Qed.


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

Lemma apply_conts_app:
  forall kappa1 kappa2 p,
    apply_conts (kappa1 ++ kappa2) p
    = apply_conts kappa2 (apply_conts kappa1 p).
Proof.
  intros.
  unfold apply_conts.
  rewrite List.fold_left_app; eauto.
Qed.


(* -------------------------------------------------------------------------- *)

(* Lemmas related to reducing substo_of_env_sthg *)

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

(** Inversion lemmas when stack is filled. *)

Import Learn.

Ltac match_conf1 :=
  match goal with
  | [ h: plus cred ?s1 ?s2 |- _] =>
    learn (plus_star h)
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

Lemma value_apply_conts {v kappa t env}:
  Value v = fst (apply_conts kappa (t, env)) ->
  List.Forall (fun k => exists sigma, k = CReturn sigma) kappa /\ (
  (Value v = t))
  .
Proof.
  split; revert v kappa t env H.
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

Lemma empty_apply_conts {kappa t env}:
  Empty = fst (apply_conts kappa (t, env)) ->
  List.Forall (fun k => exists sigma, k = CReturn sigma) kappa /\ (
  (Empty = t)).
Proof.
  split; revert kappa t env H.
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

Lemma conflict_apply_conts {kappa t env}:
  Conflict = fst (apply_conts kappa (t, env)) ->
  List.Forall (fun k => exists sigma, k = CReturn sigma) kappa /\ (
  (Conflict = t)).
Proof.
  split; revert kappa t env H.
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
  | [h: Value _ = fst (apply_conts _ (_, _)) |- _ ] =>
    learn (value_apply_conts h);
    clear h
  | [h: Conflict = fst (apply_conts _ (_, _)) |- _ ] =>
    learn (conflict_apply_conts h);
    clear h
  | [h: Empty = fst (apply_conts _ (_, _)) |- _ ] =>
    learn (empty_apply_conts h);
    clear h
  | [h: fst (apply_conts _ (_, _)) = Empty |- _ ] =>
    learn (empty_apply_conts (eq_sym h));
    clear h
  | _ => progress match_conf1
  | _ => progress unpack
  end; eauto.


(* -------------------------------------------------------------------------- *)

Fixpoint last (l: list cont) (env: list value) : list value :=
  match l with
  | [] => env
  | CReturn env1 :: l =>
    last l env1
  | _ :: l =>
    last l env
  end.

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


Lemma inv_state_mode_eval_append {e kappa k env}:
    inv_state (mode_eval e (kappa ++ [k]) env) ->
    inv_state (mode_eval e (kappa) env).
Proof.
  induction kappa; inversion 1; unpack; repeat econstructor; eauto.
Qed.

Lemma inv_state_mode_cont_append {r kappa k env}:
    inv_state (mode_cont (kappa ++ [k]) env r) ->
    inv_state (mode_cont (kappa) env r).
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

(* The handling of CReturn is orthogonal to the other continuations, hence we proove it in a different way. *)
Lemma induction_case_CReturn
  (sigma: list value)
  (kappa: list cont)
  (IHkappa: forall s1 : state,
            inv_state s1 ->
            kappa = stack s1 ->
            forall t2 : term,
            sred (fst (apply_state_aux s1)) t2 ->
            exists s2 : state, (sim_state s2 t2 /\ inv_state s2) /\ plus cred s1 s2 ):

  forall s1 : state,
  inv_state s1 ->
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

  epose proof (IHkappa _ _ _ _ H1); unpack.
  learn (sim_state_inversion _ _ H2); unpack.
  induction s1; simpl in *; subst.

  all: eapply plus_star_trans_prop; [erewrite append_stack_app; [|solve[simpl; reflexivity]]; eapply plus_cred_append_stack; simpl; eauto |].
  all: eapply star_refl_prop; split.
  1,3: eapply sim_state_from_equiv; simpl.
  1-2: induction s2; simpl in *; subst; rewrite apply_conts_app; simpl; unfold apply_cont; sp; simpl; eauto.
  1-4: symmetry; eauto.

  all: eapply inv_state_append_stack; repeat econstructor; eauto.

  Unshelve.
  2: induction s1; simpl; eauto.
  1: induction s1; simpl in *; subst;
    progress first [eapply inv_state_mode_eval_append |eapply inv_state_mode_cont_append]; eauto.
Qed.

Lemma snd_apply_conts_last :
  forall kappa env t, (snd (apply_conts kappa (t, env))) = (last kappa env).
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

Lemma fst_apply_conts_CReturn {kappa sigma t}:
  fst (apply_conts (kappa ++ [CReturn sigma]) t) = fst (apply_conts kappa t).
Proof.
  rewrite apply_conts_app; simpl; unfold apply_cont; sp; simpl; eauto.
Qed.

Lemma inv_state_app { s kappa1 }:
  inv_state (append_stack s kappa1) ->
  inv_state s.
Proof.
  induction s; inversion 1; subst; unpack.
  { econstructor; eauto. }
  { destruct kappa; econstructor.
    rewrite <- List.app_comm_cons in *; inj; unpack.
    eauto.
  }
  { destruct kappa; econstructor.
    rewrite <- List.app_comm_cons in *; inj; unpack.
  }
Qed.

Lemma Forall_CReturn_star_cred {kappa1 env result kappa2}:
  List.Forall (fun k => exists sigma, k = CReturn sigma) kappa1 ->
  star cred
    (mode_cont (kappa1 ++ kappa2) env result)
    (mode_cont kappa2 (last kappa1 env) result)
  .
Proof.
  intros. revert env.
  induction H as [|? kappa1 [env1 Hk]]; subst; simpl; intros.
  { eapply star_refl. }
  { eapply star_step. { econstructor. }
    eapply IHForall.
  }
Qed.

Lemma subst_of_env_apply_state { t sigma }:
  t.[subst_of_env sigma] = apply_state (mode_eval t [] sigma).
Proof.
  simpl; eauto.
Qed.

Lemma apply_conts_apply_state {t kappa env}:
(fst (apply_conts kappa (t.[subst_of_env env], env))) = apply_state (mode_eval t kappa env).
Proof.
  simpl; eauto.
Qed.

Lemma apply_conts_apply_state_value {v kappa env}:
(fst (apply_conts kappa (Value v, env))) = apply_state (mode_cont kappa env (RValue v)).
Proof.
  simpl; eauto.
Qed.

Lemma apply_conts_apply_state_conflict {kappa env}:
(fst (apply_conts kappa (Conflict, env))) = apply_state (mode_cont kappa env (RConflict)).
Proof.
  simpl; eauto.
Qed.

Lemma apply_conts_apply_state_empty {kappa env}:
(fst (apply_conts kappa (Empty, env))) = apply_state (mode_cont kappa env (REmpty)).
Proof.
  simpl; eauto.
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
  (* INDUCTION ON KAPPA *)
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
      destruct (IHHred Hred (mode_eval t1 [] env) eq_refl eq_refl); [solve[repeat econstructor; eauto]|]; clear h; unpack
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
  { (* INDUCTION STEP *)
    induction s1; induction k; try induction o; try induction b;
    try match goal with [r: result |- _]=> induction r end; simpl; intros Ht1t2 Hkappa; pose proof Ht1t2 as Ht1t2'; revert Ht1t2'; subst; simpl.
    all: lock Ht1t2.
    all: 
      repeat rewrite apply_conts_app in *; simpl in *; unfold apply_cont in *; sp; simpl in *.
    all: intros Ht2t3 Hs2.

    all: try match goal with [|-context [CReturn ]] =>
    solve [eapply induction_case_CReturn; eauto; simpl;
    try rewrite fst_apply_conts_CReturn; eauto] end.
    all: eapply ignore_inv_state; [eauto|].
    all: match typeof Ht2t3 with sred ?u1 ?u2 => remember u1 as u end.
    (* INDUCTION SRED *)
    all: induction Ht2t3; intros.

    (* HYPOTHESIS SATURATION *)
    all: try rewrite apply_CDefault_apply_CDefault_usable in *; unfold apply_CDefault_usable in *; try match goal with
    [h: context [ apply_CDefault_case_hole _ _ ?t _ ] |- _ ] =>
      let Hrw := fresh "H" in
      destruct (EmptyOrNotEmpty t) as [Hrw|Hrw];
      [
        rewrite (apply_CDefault_case_hole_empty Hrw) in *; symmetry in Hrw|
        rewrite (apply_CDefault_case_hole_nempty Hrw) in *
      ]
    end; inj; tryfalse.

    all: repeat (match goal with
      | [h: Value _ = fst (apply_conts _ _) |- _] =>
        learn (value_apply_conts h); clear h; unpack; repeat unpack_subst_of_env_cons
      | [h: Conflict = fst (apply_conts _ _) |- _] =>
        learn (conflict_apply_conts h); clear h; unpack; repeat unpack_subst_of_env_cons
      | [h: Empty = fst (apply_conts _ _) |- _] =>
        learn (empty_apply_conts h); clear h; unpack; repeat unpack_subst_of_env_cons

      | [h: sred _.[subst_of_env _] _ |- _] =>
        rewrite subst_of_env_apply_state in h;
        unshelve epose proof (IHkappa_wf [] _ _ _ h _ _);
        [ solve[rewrite List.app_length; simpl; lia]
        | solve[eauto]
        | solve[repeat econstructor]|];
        unpack

      | [h: plus _ _ _ |- _] => learn (plus_star h)
      | [h: sim_state _ _ |- _] => learn (sim_state_inversion _ _ h); unpack
      | [h: star _ _ _ |- _] => learn (star_cred_snd_apply_sate h)
      | [h: inv_state (append_stack _ _) |- _] => learn (inv_state_app h)
      | [h: inv_state (mode_eval _ ( _ ++ _) _) |- _] => 
        erewrite append_stack_app in Hs2; [|solve[simpl; eauto]]; simpl with_stack in Hs2
      | [h: inv_state (mode_cont ( _ ++ _) _ _) |- _] => 
        erewrite append_stack_app in Hs2; [|solve[simpl; eauto]]; simpl with_stack in Hs2
      | [h: sred (fst (apply_conts _ _)) _ |- _] =>
        rewrite apply_conts_apply_state in h;
        unshelve epose proof (IHkappa_wf _ _ _ _ Ht2t3 eq_refl _);
        [ solve[rewrite List.app_length; simpl; lia]
        | solve[eauto]
        |];
        unpack

      | [h: sred (fst (apply_conts _ _)) _ |- _] =>
        first
        [ rewrite apply_conts_apply_state_value in h
        | rewrite apply_conts_apply_state_conflict in h
        | rewrite apply_conts_apply_state_empty in h
        ];
        unshelve epose proof (IHkappa_wf _ _ _ _ Ht2t3 eq_refl _);
        [ solve[rewrite List.app_length; simpl; lia]
        | solve[eauto]
        |];
        unpack

      (* unsound sred case *)
      | [h: sred (Value _) _ |- _] => inversion h
      | [h: sred Empty _ |- _] => inversion h
      | [h: sred Conflict _ |- _] => inversion h
      end; repeat rewrite snd_apply_conts_last in *; injections; subst).

    (* INTERPRETOR *)
    all: repeat (
      (* reduction with a stack after, plus version *)
      repeat (eapply plus_star_trans_prop; [solve[
          erewrite append_stack_app;[|solve[simpl; eauto]];
          eapply plus_cred_append_stack;
          simpl;
          eauto
      ]|]);
      (* reduction with a stack after, star then plus (this must be after the previous one) *)
      repeat (eapply star_plus_trans_prop; [solve[
          erewrite append_stack_app;[|solve[simpl; eauto]];
          eapply star_cred_append_stack;
          simpl;
          eauto
      ]|]);
      repeat (eapply star_trans_prop; [solve[
          erewrite append_stack_app;[|solve[simpl; eauto]];
          eapply star_cred_append_stack;
          simpl;
          eauto
      ]|]);
      repeat (eapply star_trans_prop; [solve[
          rewrite append_stack_all;
          eapply star_cred_append_stack;
          simpl;
          eauto
      ]|]);
      repeat (eapply plus_step_prop;[solve[
        econstructor;
        repeat intro;
        inj;
        eauto
      ]|]);
      repeat (eapply star_step_prop; [solve[econstructor; repeat intro; inj; eauto]|]);
      repeat (eapply star_plus_trans_prop; [solve[eapply Forall_CReturn_star_cred; eauto]|]);
      repeat (eapply star_trans_prop; [solve[eapply Forall_CReturn_star_cred; eauto]|]);
      simpl
    ).

    all: (* FINISH *)
      try (eapply star_refl_prop; eapply sim_state_from_equiv).
    all: (* for recursive cases, we apply the induction hypothesis and lift it using append_stack *)
      try rewrite apply_state_append_stack; simpl in *; subst; unfold apply_cont; sp; simpl.
    all: try rewrite apply_CDefault_apply_CDefault_usable; unfold apply_CDefault_usable.
    all: try rewrite snd_apply_conts_last in *.
    all: repeat econstructor.
    all: repeat match goal with
    | [h: _ = snd (apply_state_aux _) |- _] => rewrite <- h in *
    end.
    all: try solve
      [ reflexivity
      | eauto
      | symmetry; eauto
      | rewrite soe_cons; asimpl; reflexivity
    ].

    { inversion Hs2; subst; unpack; inversion H15. }
    { inversion Hs2; subst; unpack; inversion H15. }
    { learn (inv_state_mode_cont_CDefault_Hole_conts_empty _ _ _ _ _ _ _ Hs2); subst.
      inversion H3; subst.
      inversion H11.
    }
    { 
      learn (inv_state_mode_cont_CDefault_Hole_conts_empty _ _ _ _ _ _ _ Hs2); subst.
      inversion H3; subst.
      inversion H11.
    }
    { learn (inv_state_mode_cont_CDefault_Hole_conts_empty _ _ _ _ _ _ _ Hs2); subst.
      inversion H3; subst.
      inversion H11.
    }
    { learn (inv_state_mode_cont_CDefault_Hole_conts_empty _ _ _ _ _ _ _ Hs2); subst.
      inversion H3; subst.
      inversion H11.
    }
    { learn (inv_state_mode_cont_CDefault_Hole_conts_empty _ _ _ _ _ _ _ Hs2); subst.
      inversion H3; subst.
      inversion H11.
    }
    { learn (inv_state_mode_cont_CDefault_Hole_conts_empty _ _ _ _ _ _ _ Hs2); subst.
      inversion H3; subst.
      inversion H11.
    }
  }
Qed.


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

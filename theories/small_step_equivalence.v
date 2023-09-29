Require Import syntax continuations small_step sequences tactics.
Require Import Coq.ZArith.ZArith.
Import List.ListNotations.

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
  | CDefault (Some v) ts tj tc =>
    (Default (t::((Value v)::ts)..[subst_of_env sigma]) tj.[subst_of_env sigma] tc.[subst_of_env sigma], sigma)
  | CDefault None ts tj tc =>
    (Default (t::(ts)..[subst_of_env sigma]) tj.[subst_of_env sigma] tc.[subst_of_env sigma], sigma)
  | CDefaultBase tc =>
    (Default nil t tc.[subst_of_env sigma], sigma)
  | CMatch t1 t2 =>
    (Match_ t t1.[subst_of_env sigma] t2.[up (subst_of_env sigma)], sigma)
  | CSome =>
    (ESome t, sigma)
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
    (apply_conts stack ((apply_return r),env))
  end.

(* We use an notation to be apple to simplify this definition. *)
Notation "'apply_state' s" := (fst (apply_state_aux s)) (at level 50, only parsing).

Inductive match_conf : state -> term -> Prop :=
  | match_conf_intro: forall s t,
      t = apply_state s ->
      match_conf s t

  (* | match_conf_empty:
    match_conf s (Default ts2 tj tc) ->
    List.Forall (Eq Empty) ts1 ->
    match_conf s (Default (ts1++ts2) tj tc) *)

  (* | match_value:
    apply_state s = Value v' ->
    eq_value v v'  ->
    match_conf s (Value v) *)
.

Parameter match_conf_filter_empty :
  forall {s ts tj tc},
  match_conf s (Default (List.filter (fun ti => match ti with | Empty => false | _ => false end) ts) tj tc) ->
  match_conf s (Default ts tj tc)
.

Parameter match_conf_filter_empty' :
  forall {s ts tj tc},
  match_conf s (Default ts tj tc) ->
  match_conf s (Default (List.filter (fun ti => match ti with | Empty => false | _ => false end) ts) tj tc)
.

Lemma match_conf_heads_empty:
  forall {s ts1 ts2 tj tc},
    match_conf s (Default ts2 tj tc) ->
    List.Forall (eq Empty) ts1 ->
    match_conf s (Default (ts1++ts2) tj tc).
Proof.
  intros.
  assert (Hfilter:
    (List.filter (fun ti => match ti with | Empty => false | _ => false end) ts2) =
    (List.filter (fun ti => match ti with | Empty => false | _ => false end) (ts1++ts2))
  ).
  { induction ts1; simpl; unpack; eauto. }
  eapply match_conf_filter_empty.
  rewrite <- Hfilter.
  eapply match_conf_filter_empty'.
  eauto.
Qed.

Lemma match_conf_empty:
  forall {s ts1 tj tc},
    match_conf s (Default [] tj tc) ->
    List.Forall (eq Empty) ts1 ->
    match_conf s (Default ts1 tj tc).
Proof.
  intros.
  replace ts1 with (ts1 ++ []) by (autorewrite with list; eauto).
  eapply match_conf_heads_empty; eauto.
Qed.

Inductive eq_value: value -> value -> Prop :=
  | eq_closure:
    forall t sigma,
      eq_value (Closure t sigma) (Closure t.[up (subst_of_env sigma)] [])
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
    { induction o; simpl; eauto. }
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
      { exfalso. eapply H0; eauto. }
      { exfalso. eapply H; eauto. }
    }
    { simpl; eapply snd_appply_conts_inj; induction phi; simpl; eauto.
      { exfalso. eapply H; eauto. }
      { induction o; simpl; eauto. }
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

Lemma creds_apply_state_sigma_stable_eq s1 s2 p1 p2:
  p1 = apply_state_aux s1 ->
  p2 = apply_state_aux s2 ->
  star cred s1 s2 ->
  snd p1 = snd p2.
Proof.
  intros; subst; eapply creds_apply_state_sigma_stable; eauto.
Qed.

Lemma cred_plus_apply_state_sigma_stable_eq s1 s2 p1 p2:
  p1 = apply_state_aux s1 ->
  p2 = apply_state_aux s2 ->
  plus cred s1 s2 ->
  snd p1 = snd p2.
Proof.
  intros; subst; eapply creds_apply_state_sigma_stable; eauto with sequences.
Qed.

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
    edestruct (IHts1 _ _ _ H); unpack; repeat (asimpl in *; subst).
    exists (x :: x1), x2.
    repeat eexists.
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
    destruct (subst_of_env_nil h); unpack; subst; clear h
  | [h: Default _ _ _ = _.[subst_of_env _] |- _] =>
    let ts := fresh "ts" in
    let tjust := fresh "tjust" in
    let tcons := fresh "tcons" in
    let Hts := fresh "Hts" in       (*    ts = ts'..[subst_of_env env] *)
    let Htjust := fresh "Htjust" in (* /\ tj = tj'.[subst_of_env env] *)
    let Htcons := fresh "Htcons" in (* /\ tc = tc'.[subst_of_env env] *)
    let Ht := fresh "Ht" in         (* /\ t' = Default ts' tj' tc' *)
    destruct (subst_of_env_Default h) as (ts & tjust & tcons & Hts & Htjust & Hcons & Ht); subst; clear h
  
  | [h: Match_ _ _ _ = _.[subst_of_env _] |- _] =>
    let u := fresh "u" in
    let t1 := fresh "t1" in
    let t2 := fresh "t2" in
    let Hu := fresh "Hu" in
    let Ht1 := fresh "Ht1" in
    let Ht2 := fresh "Ht2" in
    let Ht := fresh "Ht" in
    destruct (subst_of_env_Match_ h) as (u & t1 & t2 & Hu & Ht1 & Ht2 & Ht); subst; clear h
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
  | _ => repeat (simpl in *; injections; subst)
  end
.

Definition count_f
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
Admitted.


Lemma default_head_empty:
  forall ts1 o ts2 e1 e2 env0,
  List.Forall (eq Empty) ts1 ->
  star cred
    (mode_cont [CDefault o (ts1 ++ ts2) e1 e2] env0 REmpty)
    (mode_cont [CDefault o (ts2) e1 e2] env0 REmpty).
Proof.
  induction ts1; intros; unpack; simpl.
  { econstructor. }
  { eapply star_step. { econstructor. }
    eapply star_step. { econstructor. }
    eapply IHts1; eauto.
  }
Qed.


Import Learn.

Ltac match_conf1 :=
  match goal with
  | [ |- match_conf _ _ ] => econstructor
  | [h: match_conf _ _ |- _ ] =>
    inversion h; subst; clear h
  | [ h: plus cred ?s1 ?s2 |- _] =>
    learn (plus_star h)
  | [ hs1s2: star cred (mode_eval ?t [] ?env) ?s2 |- _ ] =>
    replace env with (snd (apply_state_aux (mode_eval t [] env))) by (simpl; eauto);
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
  | _ => progress simpl; try solve [repeat f_equal; eauto]
  | _ => progress injections
  end.

Lemma value_apply_conts_inversion_eval {v kappa t env0}:
  Value v = fst (apply_conts kappa (t, env0)) ->
  List.Forall (fun k => exists sigma, k = CReturn sigma) kappa /\ (
  (exists x, t = Var x /\ Value v = subst_of_env env0 x) \/
  (t = Value v))
  .
Proof.
  split; revert v kappa t env0 H.
  { induction kappa as [|k kappa] using List.rev_ind.
    { econstructor. }
    { induction k; try induction o.
      all: intros; repeat match_conf1; inj.
      { learn (IHkappa _ _ H); eapply List.Forall_app; eauto. }
    }
  }
  { induction kappa as [|k kappa] using List.rev_ind.
    { induction t; asimpl; intros; inj; subst; eauto. }
    { destruct t; induction k.
      all: intros; try induction o; repeat match_conf1; inj.
      { destruct (IHkappa (Var x) _ H); inj; unpack; injections; subst; eauto. }
      all: try match goal with
      | [h: Value _ = fst (apply_conts _ (?t, ?env)) |- _] =>
        destruct (IHkappa t env); simpl; eauto
      end.
    }
  }
Qed.

Lemma value_apply_conts_inversion_cont {v kappa result env0}:
  Value v = fst (apply_conts kappa (apply_return result, env0)) ->
  List.Forall (fun k => exists sigma, k = CReturn sigma) kappa /\
  result = RValue v.
Proof.
  intros H.
  destruct (value_apply_conts_inversion_eval H) as (Hkappa & [(x & Hx & Hv)|Hv]).
  all: induction result; simpl in *.
  all: try congruence.
  { injections; subst; eauto. }
Qed.

Lemma process_return {kappa1 env0 result}: forall kappa2,
  List.Forall (fun k => exists sigma, k = CReturn sigma) kappa1 ->
  exists env1,
    star cred
      (mode_cont (kappa1 ++ kappa2) env0 result)
      (mode_cont kappa2 env1 result)
  .
Proof.
  intros. revert env0.
  induction H as [|? kappa1 [env1 Hk]]; simpl; subst.
  { eexists; eapply star_refl. }
  { destruct (IHForall env1).
    eexists.
    eapply star_step. { econstructor. }
    eauto.
  }
Qed.

Ltac match_conf :=
  repeat match goal with
  | [h: Value _ = fst (apply_conts _ (apply_return _, _)) |- _ ] =>
    learn (value_apply_conts_inversion_cont h)
  | [h: Value _ = fst (apply_conts _ (_, _)) |- _ ] =>
    learn (value_apply_conts_inversion_eval h)
  | [h: _ \/ _ |- _] =>
    destruct h
  | _ => progress match_conf1
  | _ => progress unpack
  end.

Ltac cstep :=
  match goal with
  | [h: plus cred ?s1 ?s2 |- star cred ?s1 ?s2] =>
    eapply (plus_star h)
  | [h: plus cred ?s1 ?s2 |- plus cred ?s1 ?s2] =>
    eauto
  | [ |- plus cred ?s1 ?s2] =>
    eapply plus_left; [solve [econstructor; eauto]|]
  | [ h: plus cred ?s1 ?s2 |- _] =>
    learn (plus_star h)
  | [ |- star cred ?s1 ?s2] =>
    eapply star_step; [solve [econstructor; eauto|econstructor; repeat intro; inj]|]
  | [
    h: List.Forall (fun k => exists sigma, k = CReturn sigma) ?kappa1
    |- star cred
        (mode_cont (?kappa1 ++ _) _ _)
        _
    ] =>
      eapply star_trans; [solve [eapply process_return; eauto]]
  | [
    h: List.Forall (fun k => exists sigma, k = CReturn sigma) ?kappa1
    |- plus cred
        (mode_cont (?kappa1 ++ ?kappa2) ?env ?r)
        _
    ] =>
      let env' := fresh "env" in
      let h' := fresh "h" in
      destruct (@process_return _ env r kappa2 h) as (env' & h');
      eapply (star_plus_trans h');
      clear h'
  | [
    h: List.Forall (fun k => exists sigma, k = CReturn sigma) ?kappa1
    |- star cred
        (mode_cont (?kappa1 ++ ?kappa2) ?env ?r)
        _
    ] =>
      let env' := fresh "env" in
      let h' := fresh "h" in
      destruct (@process_return _ env r kappa2 h) as (env' & h');
      eapply (star_trans h');
      clear h'
  | [
    h: List.Forall (eq Empty) ?ts1
    |- star cred (mode_cont (CDefault _ (?ts1 ++ _) _ _::_) _ REmpty) _
    ] =>
    eapply star_trans; [solve[eapply default_head_empty; eauto]|]
  | [
    h: List.Forall (eq Empty) ?ts1
    |- star cred (mode_cont (CDefault _ ?ts1 _ _::_) _ REmpty) _
    ] =>
    eapply star_trans; [solve[replace ts1 with (ts1 ++ []) by eapply List.app_nil_r; eapply default_head_empty; eauto]|]
  | [h: star cred ?s1 ?s2 |- star cred ?s1' (append_stack ?s2 ?kappa)] =>
    replace s1' with (append_stack s1 kappa); [| solve [simpl; eauto]];
    eapply append_stack_stable_star
  | [h: plus cred ?s1 ?s2 |- plus cred ?s1' (append_stack ?s2 ?kappa)] =>
    replace s1' with (append_stack s1 kappa); [| solve [simpl; eauto]];
    eapply append_stack_stable_plus
  | [ |- star cred ?s1 ?s1] =>
    eapply star_refl
end.


Theorem simulation_sred_cred t1 t2:
  sred t1 t2 ->
  forall s1, match_conf s1 t1 ->
  exists s2,
    (plus cred s1 s2)
  /\ match_conf s2 t2.
Ltac process_induction :=
  match goal with
  | [h: match_conf (mode_eval ?e (?kappa ++ [?_k]) ?env) _ |- _] =>
    remember (mode_eval e kappa env) as s1;
    remember _k as k;
    replace (mode_eval e (kappa ++ [k]) env)
      with (append_stack s1 [k])
      by (subst; eauto)
  | [h: match_conf (mode_cont (?kappa ++ [?_k]) ?env ?r) _ |- _] =>
    remember (mode_cont kappa env r) as s1;
    remember _k as k;
    replace (mode_cont (kappa ++ [k]) env r)
      with (append_stack s1 [k])
      by (subst; eauto)
  end.
Ltac simpl_apply_cont :=
  match goal with
  | [ |- context [apply_cont (apply_state_aux ?s)]] =>
    rewrite (surjective_pairing (apply_state_aux s));
    unfold apply_cont;
    simpl
  | [ |- context [apply_cont (apply_conts ?a ?b)]] =>
    rewrite (surjective_pairing (apply_conts a b));
    unfold apply_cont;
    simpl
  | [h: context [apply_cont (apply_state_aux ?s)] |- _ ] =>
    rewrite (surjective_pairing (apply_state_aux s)) in h;
    simpl in h
  | [h: context [apply_cont (apply_conts ?a ?b)] |- _ ] =>
    rewrite (surjective_pairing (apply_conts a b)) in h;
    simpl in h
  end.


Ltac aexists t :=
  exists t; split; [repeat cstep|match_conf].
Proof.
  intros Hred s1 MC.
  remember (stack s1) as kappa.
  generalize dependent s1.
  generalize dependent t2.
  generalize dependent t1.
  induction kappa as [|k kappa] using List.rev_ind.
  { induction 1.
    all: induction s1; intro MC; inversion MC; clear MC; intros; repeat (simpl in *; subst).
    all: try solve [induction result; simpl in *; tryfalse].
    (* unpack except in the conflict case: we need for now to not unpack here as we first need to modify slightly the definition. *)
    all: match goal with
    | [_:  context G [ _ ++ _ :: _ ++ _ :: _] |- _ ] => idtac
    | _ => unpack_subst_of_env_cons
    end
    .
    { induction t1; tryfalse;
      induction t2; tryfalse.
      all: exists (mode_eval t [CReturn env0] (v::sigma')); split.
      all: unpack_subst_of_env_cons.
      all: try solve [match_conf | repeat cstep].
    }
    { exists (mode_cont [] env0 (RValue (Closure t1 env0))); split.
      { repeat cstep. }
      { eapply match_value.
        { match_conf. }
        { econstructor. }
        (* "small problem here: because of the decision to store closures as equal modulo substition of their environement, there is an issue here." *)
      }
    }
    { (* apply induction hypothesis. *)
      destruct IHHred with ((mode_eval t0 [] env0)) as (s2 & Hs1s2 & MCs2).
      { econstructor; simpl; eauto. }
      { simpl; eauto. }

      exists (append_stack s2 [CAppR t3]); split.
      { repeat cstep. }
      { (* Then let us show it is indeed linked to our new term. This is
            thanks to our previous lemma about stability of the environement upon reduction. *)
        inversion MCs2; subst; clear MCs2.
        match_conf.
      }
    }
    { destruct IHHred with (mode_eval t2 [] env0) as (s2 & Hs1s2 & Hs2).
      { econstructor; simpl; eauto. }
      { simpl; eauto. }

      exists (append_stack s2 [ CClosure t sigma]); split.
      { induction t1; tryfalse; unpack_subst_of_env_cons.
        all: repeat cstep.
      }
      { inversion Hs2; subst; clear Hs2.
        match_conf.
      }
    }
    { destruct IHHred with (mode_eval t0 [] env0) as (s2 & Hs1s2 & Hs2).
      { econstructor; simpl; eauto. }
      { simpl; eauto. }

      exists (append_stack s2 [CBinopR op t3]); split.
      { repeat cstep. }
      { inversion Hs2; subst; clear Hs2.
        match_conf.
      }
    }
    { destruct IHHred with (mode_eval t2 [] env0) as (s2 & Hs1s2 & Hs2).
      { econstructor; simpl; eauto. }
      { simpl; eauto. }

      exists (append_stack s2 [ CBinopL op v]); split.
      { induction t1; tryfalse; unpack_subst_of_env_cons.
        all: repeat cstep.
      }
      { inversion Hs2; subst; clear Hs2.
        match_conf.
      }
    }
    { (* binop *)
      induction t1; induction t2; tryfalse.
      all: exists (mode_cont [] env0 (RValue v)); split.
      all: try solve [ match_conf ].
      all: unpack_subst_of_env_cons.
      all: repeat cstep.
    }
    { exists (mode_cont [] env0 RConflict); split.
      { repeat cstep. }
      { match_conf. }
    }
    { exists (mode_cont [] env0 REmpty); split.
      { repeat cstep. }
      { match_conf. }
    }
    { induction t1; unpack_subst_of_env_cons; tryfalse;
      exists (mode_cont [] env0 RConflict); split.
      all: match_conf.
      all: repeat cstep.
    }
    { induction t1; unpack_subst_of_env_cons; tryfalse;
      exists (mode_cont [] env0 REmpty); split.
      { repeat cstep. }
      { match_conf. }
      { repeat cstep. }
      { match_conf. }
    }

    { (* Conflict *)
      unpack_subst_of_env_cons.
      unpack.
      exists (mode_cont [] env0 RConflict); split.
      { rename
          u   into ti,
          u0 into tj.

        induction ti; simpl in *; tryfalse;
        induction tj; simpl in *; tryfalse.
        (* Two cases: ti is a variable, ti is a value. *)

        all: unpack_subst_of_env_cons.
        all: repeat cstep.
      }
      { match_conf. }
    }
    { induction u; unpack_subst_of_env_cons; tryfalse.
      { exists (mode_cont [] env0 (RValue v)); split.
        { repeat cstep. }
        { match_conf. }
      }
      { exists (mode_cont [] env0 (RValue v)); split.
        { repeat cstep. }
        { match_conf. }
      }
    }
    { exists (mode_cont [] env0 RConflict); split.
      { repeat cstep. }
      { match_conf. }
    }

    { destruct IHHred
        with (mode_eval u [] env0)
        as (s2 & Hs1s2 & Hs2);
      try solve [simpl; econstructor; eauto].

      exists (append_stack s2 [CDefault None ts tjust tcons]); split.
      { repeat cstep. }
      { inversion Hs2; clear Hs2; subst.
        match_conf.
        admit "same issue as before.".
      }
    }
    { unpack_subst_of_env_cons.
      destruct IHHred
        with (mode_eval u0 [] env0)
        as (s2 & Hs1s2 & Hs2).
      { match_conf. }
      { simpl; eauto. }

      induction u; unpack_subst_of_env_cons; tryfalse.
      { exists (append_stack s2 [CDefault (Some v) ts tjust0 tcons0]); split.
        { repeat cstep. }
        { match_conf.
          admit "same issue as before".
        }
      }
      { exists (append_stack s2 [CDefault (Some v) ts tjust0 tcons0]); split.
        { repeat cstep. }
        { match_conf.
          admit "same issue as before".
        }
      }
    }

    { destruct IHHred with (mode_eval tjust [] env0) as (s2 & Hs1s2 & Hs2).
      { match_conf. }
      { simpl; eauto. }

      exists (append_stack s2 [CDefaultBase tcons]); split.
      { repeat cstep. }
      { match_conf.
        admit "same issue as before".
      }
    }
    { induction tjust; tryfalse; eauto; unpack_subst_of_env_cons.
      { exists (mode_eval tcons [] env0); split.
        { repeat cstep. }
        { econstructor; simpl; eauto. }
      }
      { exists (mode_eval tcons [] env0); split.
        { repeat cstep. }
        { econstructor; simpl; eauto. }
      }
    }
    { induction tjust; tryfalse; eauto; unpack_subst_of_env_cons.
      { exists (mode_cont [] env0 REmpty); split.
        { repeat cstep. }
        { econstructor; simpl; eauto. }
      }
      { exists (mode_cont [] env0 REmpty); split.
        { repeat cstep. }
        { econstructor; simpl; eauto. }
      }
    }
    { exists (mode_cont [] env0 REmpty); split.
      { repeat cstep. }
      {econstructor; simpl; eauto. }
    }
    { exists (mode_cont [] env0 RConflict); split.
      { repeat cstep. }
      { econstructor; simpl; eauto. }
    }
    { destruct IHHred with (mode_eval u [] env0) as (s2 & Hs1s2 & Hs2).
      { econstructor; simpl; eauto. }
      { simpl; eauto. }

      exists (append_stack s2 [CMatch t0 t3]); split.
      { repeat cstep. }
      { inversion Hs2; subst; clear Hs2.
        match_conf.
      }
    }
    { induction u; tryfalse; unpack_subst_of_env_cons.
      { exists (mode_eval t0 [] (env0)); split.
        { repeat cstep. }
        { match_conf. }
      }
      { exists (mode_eval t0 [] (env0)); split.
        { repeat cstep. }
        { match_conf. }
      }
    }
    { induction u; tryfalse; unpack_subst_of_env_cons.
      { exists (mode_eval t3 [CReturn env0] (v::env0)); split.
        { repeat cstep. }
        { econstructor; asimpl. rewrite subst_env_cons; eauto. }
      }
      { exists (mode_eval t3 [CReturn env0] (v::env0)); split.
        { repeat cstep. }
        { econstructor; asimpl. rewrite subst_env_cons; eauto. }
      }
    }
    { exists (mode_cont [] env0 (RValue VNone)); split.
      { repeat cstep. }
      { econstructor; simpl; eauto. }
    }
    { destruct IHHred with (mode_eval t0 [] env0) as (s2 & Hs1s2 & Hs2).
      { econstructor; simpl; eauto. }
      { simpl; eauto. }

      exists (append_stack s2 [CSome]); split.
      { repeat cstep. }
      { inversion Hs2; subst; clear Hs2.
        match_conf.
      }
    }
    { induction t1; tryfalse; unpack_subst_of_env_cons.
      all: exists (mode_cont [] env0 (RValue (VSome v0))); split.
      { repeat cstep. }
      { econstructor; simpl; eauto. }
      { repeat cstep. }
      { econstructor; simpl; eauto. }
    }
  }
  { induction 1.
    { admit. }
    { admit. }
    {
      match goal with [x: cont |- _] => induction x end;
      induction s1; inversion 1; intros;
      repeat (simpl in *; autorewrite with apply_conts in *; subst).

      (* Getting rid of all the cases that are not real. *)
      all: try match goal with [o: option value |- _] => induction o end.
      all: match goal with
        | [ h: context [apply_cont (apply_conts ?kappa ?p)] |- _] =>
          rewrite (surjective_pairing (apply_conts kappa p)) in h;
          unfold apply_cont in h;
          simpl in h;
          inj
        end.
      all: try solve [inversion Hred].
      { process_induction.
        destruct (IHkappa _ _ Hred s1)
          as (s2 & Hs1s2 & Hs2);
          try solve [subst; econstructor; simpl; eauto].
        exists (append_stack s2 [k]); split.
        { eapply append_stack_stable_plus; eauto with sequences. }
        { econstructor.
          inversion Hs2.
          rewrite apply_state_append_stack; simpl; rewrite Heqk.
          simpl_apply_cont.
          f_equal; eauto; do 2 f_equal.
          eapply cred_plus_apply_state_sigma_stable_eq; eauto; subst; eauto.
        }
      }
      { process_induction.
        destruct (IHkappa _ _ Hred s1)
          as (s2 & Hs1s2 & Hs2);
          try solve [subst; econstructor; simpl; eauto].
        exists (append_stack s2 [k]); split.
        { eapply append_stack_stable_plus; eauto with sequences. }
        { econstructor.
          inversion Hs2.
          rewrite apply_state_append_stack; simpl; rewrite Heqk.
          simpl_apply_cont.
          f_equal; eauto; do 2 f_equal.
          eapply cred_plus_apply_state_sigma_stable_eq; eauto; subst; eauto.
        }
      }
      { process_induction.
        assert (Hred': sred (App t1 u) (App t2 u)) by (econstructor; eauto).
        destruct (IHkappa _ _ Hred' s1)
          as (s2 & Hs1s2 & Hs2);
          try solve [subst; econstructor; simpl; eauto].
        exists (append_stack s2 [k]); split.
        { eapply append_stack_stable_plus; eauto with sequences. }
        { econstructor.
          inversion Hs2.
          rewrite apply_state_append_stack; simpl; rewrite Heqk.
          simpl_apply_cont.
          f_equal; eauto; do 2 f_equal.
        }
      }
      { process_induction.
        assert (Hred': sred (App t1 u) (App t2 u)) by (econstructor; eauto).
        destruct (IHkappa _ _ Hred' s1)
          as (s2 & Hs1s2 & Hs2);
          try solve [subst; econstructor; simpl; eauto].
        exists (append_stack s2 [k]); split.
        { eapply append_stack_stable_plus; eauto with sequences. }
        { econstructor.
          inversion Hs2.
          rewrite apply_state_append_stack; simpl; rewrite Heqk.
          simpl_apply_cont.
          f_equal; eauto; do 2 f_equal.
        }
      }
    }
    { admit. }
    { admit. }
    { admit. }
    { admit. }
    { admit. }
    { admit. }
    { admit. }
    { admit. }
    { admit. }
    { admit. }
    { admit. }
    { admit. }
    { admit. }
    { admit. }
    { admit. }
    { admit. }
    { admit. }
    { admit. }
    { admit. }
    { admit. }
    { admit. }
    { admit. }
    { induction s1;
      intros MC; inversion MC; subst; clear MC; simpl;
      intro Heq; rewrite <- Heq in *; clear Heq;
      induction k; try induction o;
      repeat rewrite append_stack_eval in *;
      repeat rewrite append_stack_cont in *;
      match_conf; tryfalse.
      { assert (Hsred': sred (ESome t1) (ESome t2)). { econstructor; eauto. }
        edestruct (IHkappa _ _ Hsred' (mode_eval e kappa env0)) as (s2 & Hs1s2 & Hs2).
        { match_conf. }
        { simpl; eauto. }

        aexists (append_stack s2 [CReturn sigma]).
      }
      { injections.
        edestruct (IHkappa _ _ Hred (mode_eval e kappa env0)) as (s2 & Hs1s2 & Hs2).
        { match_conf. }
        { simpl; eauto. }

        aexists (append_stack s2 [CSome]).
      }
      { assert (Hsred': sred (ESome t1) (ESome t2)). { econstructor; eauto. }
        edestruct (IHkappa _ _ Hsred' (mode_cont kappa env0 result)) as (s2 & Hs1s2 & Hs2).
        { match_conf. }
        { simpl; eauto. }

        aexists (append_stack s2 [CReturn sigma]).
      }
      { injections.
        edestruct (IHkappa _ _ Hred (mode_cont kappa env0 result)) as (s2 & Hs1s2 & Hs2).
        { match_conf. }
        { simpl; eauto. }

        aexists (append_stack s2 [CSome]).
      }
    }
    { induction s1;
      intros MC; inversion MC; subst; clear MC; simpl;
      intro Heq; rewrite <- Heq in *; clear Heq;
      induction k; try induction o;
      repeat rewrite append_stack_eval in *;
      repeat rewrite append_stack_cont in *;
      try solve [match_conf; tryfalse].
      { assert (Hred': sred (ESome (Value v)) (Value (VSome v))). { econstructor; eauto. }

        edestruct (IHkappa _ _ Hred' (mode_eval e kappa env0)) as (s2 & Hs1s2 & Hs2).
        { match_conf. }
        { simpl; eauto. }

        aexists (append_stack s2 [CReturn sigma]).
      }
      { admit.
      }
      { assert (Hred': sred (ESome (Value v)) (Value (VSome v))). { econstructor; eauto. }
        edestruct (IHkappa _ _ Hred' (mode_cont kappa env0 result)) as (s2 & Hs1s2 & Hs2).
        { match_conf. }
        { simpl; eauto. }

        aexists (append_stack s2 [CReturn sigma]).
      }
      { match_conf; subst; simpl in *; try congruence; repeat injections.
        eexists; split.
        { repeat cstep. }

      }
    }
  }
Admitted.

Require Import syntax continuations small_step sequences tactics.
Import List.ListNotations.

Definition subst_of_env sigma :=
  fun n =>
  match List.nth_error sigma n with
  | None => ids (n - List.length sigma)
  | Some t => Value t
  end
.

Lemma subst_env_0: forall t v, t.[subst_of_env [v]] = t.[Value v/].
Proof.
  intros.
  repeat f_equal.
  eapply FunctionalExtensionality.functional_extensionality.
  unfold subst_of_env.
  induction x; simpl; eauto.
  induction x; simpl; eauto.
Qed.

Definition apply_cont
  (k: cont)
  (param1: term * list value)
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
    (Default (t::(Value v)::ts)..[subst_of_env sigma] tj.[subst_of_env sigma] tc.[subst_of_env sigma], sigma)
  | CDefault None ts tj tc =>
    (Default (t::ts)..[subst_of_env sigma] tj.[subst_of_env sigma] tc.[subst_of_env sigma], sigma)
  | CDefaultBase tc =>
    (Default nil t tc.[subst_of_env sigma], sigma)
  | CMatch t1 t2 =>
    (Match_ t t1.[subst_of_env sigma] t2.[up (subst_of_env sigma)], sigma)
  | CSome =>
    (ESome t, sigma)
  end.

Definition apply_conts
  (kappa: list cont)
  (t: term)
  (sigma: list value): term * list value :=
  List.fold_right apply_cont (t, sigma) kappa.

Definition apply_return (r: result) :=
  match r with
  | RValue v => Value v
  | REmpty => Empty
  | RConflict => Conflict
  end.

Definition apply_state (s: state): term :=
  match s with
  | mode_eval t stack env =>
    fst (apply_conts stack t env)
  | mode_cont stack env r =>
    fst (apply_conts stack (apply_return r) env)
  end.


Definition subst_cont
  (k: cont)
  (sigma: list value): cont :=
  match k with
  | CAppR t2 => CAppR t2.[subst_of_env sigma]
  | CBinopL op v1 => CBinopL op v1
  | CBinopR op t2 => CBinopR op t2.[subst_of_env sigma]
  | CClosure t_cl sigma_cl => CClosure t_cl sigma_cl
  | CReturn sigma' => CReturn sigma'
  | CDefault (Some v) ts tj tc =>
    CDefault
      (Some v)
      ts..[subst_of_env sigma]
      tj.[subst_of_env sigma]
      tc.[subst_of_env sigma]
  | CDefault None ts tj tc =>
    CDefault
      None
      ts..[subst_of_env sigma]
      tj.[subst_of_env sigma]
      tc.[subst_of_env sigma]
  | CDefaultBase tc =>
    CDefaultBase tc.[subst_of_env sigma]
  | CMatch t1 t2 =>
    CMatch t1.[subst_of_env sigma] t2.[up (subst_of_env sigma)]
  | CSome => CSome
  end
.

Fixpoint subst_conts
  (kappa: list cont)
  (sigma: list value): list cont :=
  match kappa with
  | (CReturn sigma) :: t =>
    t
  | h :: t =>
    subst_cont h sigma :: subst_conts t sigma
  | [] =>
    []
  end
.

Inductive equiv: state -> state -> Prop :=
| EQ_trans:
  forall s1 s2 s3,
    equiv s1 s2 -> equiv s2 s3 -> equiv s1 s3
| EQ_relf:
  forall s1,
     equiv s1 s1
| EQ_sym:
  forall s1 s2,
    equiv s1 s2 -> equiv s2 s1
| EQ_subst_env_eval:
  forall t kappa env,
    equiv
      (mode_eval t kappa env)
      (mode_eval t.[subst_of_env env] (subst_conts kappa env) [])
| EQ_step:
  forall s1 s2,
    cred s1 s2 -> equiv s1 s2
  (* forall t t' k kappa env,
    cred (mode_eval t kappa env) (mode_eval t' (k::kappa) env) ->
    equiv (mode_eval t kappa env) (mode_eval t' (k :: kappa) env) *)
.

Definition env s:=
  match s with
  | mode_eval _ _ sigma => sigma
  | mode_cont _ sigma _ => sigma
  end
.

Lemma equiv_append_stack:
  forall s1 s2,
  equiv s1 s2 ->
  forall kappa,
  equiv (append_stack s1 kappa) (append_stack s2 kappa).
Proof.
  intros s1 s2.
  induction 1; intros.
  { eapply EQ_trans; eauto. }
  { eapply EQ_relf; eauto. }
  { eapply EQ_sym; eauto. }
  { simpl in *; subst. }
  { eapply EQ_step.
    eapply append_stack_stable; eauto.
  }
Admitted.

Theorem sred_cred t1 t2 :
  sred t1 t2 ->
    exists s2,
    star cred (mode_eval t1 [] []) s2 /\
    equiv s2 (mode_eval t2 [] []).
Proof.
  induction 1.
  {
    eexists; split.
    { repeat (eapply star_step; [solve [econstructor]|]).
      eapply star_refl.
    }
    subst.
    replace (t.[Value v/]) with (t.[subst_of_env [v]]).
    replace ([]) with (subst_conts [CReturn []] [v]).
    eapply EQ_subst_env_eval.
    simpl; eauto.
    eapply subst_env_0.
  }
  {
    unpack.
    eexists; split.
    { repeat (eapply star_step; [solve [econstructor]|]).
      rewrite append_stack_all_eval.
      eapply append_stack_stable_star.
      eauto.
    }
    { eapply EQ_trans. eapply equiv_append_stack. eauto. simpl.
      eapply EQ_sym. eapply EQ_step. econstructor. }
  }
  {
    unpack; eexists; split.
    { repeat (eapply star_step; [solve [econstructor]|]).
      rewrite append_stack_all_eval.
      eapply append_stack_stable_star.
      eauto.
    }
    { eapply EQ_trans. eapply equiv_append_stack. eauto. simpl.
      eapply EQ_sym. eapply EQ_trans. eapply EQ_step.
      econstructor.
      eapply EQ_trans.
      eapply EQ_step. econstructor.
      eapply EQ_step. econstructor.
    }
  }
  { (* DConflict case. *)
    unpack; subst; eexists; split.
    { repeat (eapply star_step; [solve [econstructor]|]). admit alain. }
  }
  { induction ti; simpl in *; tryfalse.

  }

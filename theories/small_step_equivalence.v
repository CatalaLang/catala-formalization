Require Import syntax continuations small_step sequences tactics.
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
Notation "'apply_state' s" := (fst (apply_state_aux s)) (at level 50).

Inductive match_conf : state -> term -> Prop :=
  | match_conf_intro: forall s t,
      t = apply_state s ->
      match_conf s t.


Section APPLY_EXAMPLES.
  Require Import Coq.ZArith.ZArith.

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



(* Remark red_apply_cont:
  forall k c1 s1 c2 s2,
    sred c1.[subst_of_env s1] c2.[subst_of_env s2] ->
    sred
      (let (c1', s1') := apply_cont (c1, s1) k in
        c1'.[subst_of_env s1])
      (let (c2', s2') := apply_cont (c2, s2) k in
        c2'.[subst_of_env s2]).
Proof.
  induction k; intros; cbn.
Abort. *)


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
  { induction 1.
    all: try solve [simpl; intros; subst; eauto].
    17: {
      (* simplfy apply_conts. *)
      all: match goal with 
      | [|- context[snd (apply_state_aux ?_s1) = snd (apply_state_aux (?_s2))]] =>
        remember _s1 as s1;
        remember _s2 as s2;
        rewrite Heqs1, Heqs2
      end.
      assert (Hcred: cred (with_stack s1 kappa) (with_stack s2 kappa)); try (subst; econstructor; eauto).
      try (specialize (IHkappa _ _ Hcred); subst; simpl in *).
      intros; subst; unfold apply_conts in *; repeat rewrite List.fold_left_app; simpl.
      match goal with 
      | [|- context[snd (apply_cont (?_y1) _) = snd (apply_cont (?_y2) _)]] =>
        remember _y1 as y1;
        remember _y2 as y2;
        induction y1; induction y2
      end.
      induction x; simpl; eauto.
      induction o; simpl; eauto.
    }

    induction x; simpl.
    induction a.
    { induction 1; simpl; intros; subst; simpl; tryfalse. }
    induction 1; simpl; intros; subst; tryfalse; eauto. }

  induction 1.
  asimpl.
Admitted.

Theorem simulation_sred_cred t1 t2:
  sred t1 t2 ->
  forall s1, match_conf s1 t1 ->
  exists s2,
    (plus cred s1 s2)
  /\ match_conf s2 t2.
Proof.
  induction 1; intros s1 MC; inversion MC; subst; clear MC; cbn.
  3:{
    induction s1.
    induction kappa using List.rev_ind.
    { simpl in H0.
      induction e; try solve [exfalso; simpl in *; inj].
      { unfold subst_of_env in *. admit. }
      { asimpl in *.
        inj.
        clear IHe1 IHe2.
        assert (MCe1: match_conf (mode_eval e1 [] env0) e1.[subst_of_env env0]).
        { econstructor; simpl; eauto. }
        destruct (IHsred _ MCe1); unpack.
        rename x into s2.
        exists (append_stack s2 [CAppR e2]); repeat split.
        { eapply plus_left. { econstructor. }
          replace (mode_eval e1 [CAppR e2] env0) with (append_stack (mode_eval e1 [] env0) [CAppR e2]). 2:{ simpl; eauto. }
          eapply append_stack_stable_star.
          eapply plus_star; eauto.
        }
        { rewrite apply_state_append_stack.
          asimpl.
          inversion H1; subst; clear H1; eauto.
          remember (apply_state_aux s2) as y; induction y; simpl.
          repeat f_equal.
          eapply cred_apply_state_sigma_stable.
        }

          }
      }




      assert 
    }
  }
Theorem simulation_sred_cred t1 t2:
  sred t1 t2 ->
  forall s1, match_conf s1 t1 ->
  exists s2,
    (plus cred s1 s2)
  /\ match_conf s2 t2.
Proof.
  induction 1; intros s1 MC; inversion MC; subst; clear MC; cbn.
  3: {
    destruct (inversion_App_apply_state _ _ _ H0) as [h|[h|[h|[h|h]]]];
    unpack; inj; subst.
    { repeat match goal with
      | [h: list value |- _] =>
        progress (rename h into sigma)
      | [h: list cont |- _] =>
        progress (rename h into kappa)
      end.
      rewrite apply_conts_returns in *; eauto.
      asimpl in H0; inj; rename x into t1.
      assert (match_conf (mode_eval t1 kappa sigma) t1.[subst_of_env sigma]).
      { repeat econstructor; rewrite apply_conts_returns; eauto. }
      rename x0 into u.
      destruct (IHsred _ H0) as [s2 [? ?]].
      exists (mode_eval t2 ((CAppR u) :: kappa) sigma); split.
      { eapply plus_left. { econstructor. }
        
      } 

       }  ; asimpl in *; inj.
    { simpl in *.    }

  }

  { admit. }
  { induction T1.
    { induction e.
      { induction kappa; simpl in H.
        { (* impossible since subst_of_env is always a value or a variable. *)
          unfold subst_of_env in H.
          exfalso. remember (List.nth_error env0 x) as o. induction o; inj.
        }
        { (* impossible since apply_cont cannot produce a lambda. *)
          remember (apply_conts kappa (Var x) env0) as y.
          induction y as [y1 y2].
          induction a; try solve [exfalso; simpl in H; inj].
          * admit "I don't understand this case.".
          * induction o; exfalso; simpl in H; inj.
        }
      }
    }
  }


Theorem simulation_cred_sred s1 s2:
  cred s1 s2 ->
  forall t1, match_conf s1 t1 ->
  exists t2,
    (plus sred t1 t2)
  /\ match_conf s2 t2.
Proof.
  destruct 1; intros T1 MC; inversion MC; subst; cbn.


Theorem simulation_red_cont t1 t2:
  sred t1 t2 ->
  forall s1, match_conf s1 t1 ->
  exists s2,
    (plus cred s1 s2 (*\/ (star step s1 s2 /\ rmeasure C1' < rmeasure C1)%nat*))
  /\ match_conf s2 t2.
Proof.
  induction 1.
  { inversion 1; subst.

  }

  
  induction 1.

    equiv s2 (mode_eval t2 [] []).


Theorem sred_cred t1 t2 :
  sred t1 t2 ->
    exists s2,
    star cred (mode_eval t1 [] []) s2 /\
    equiv s2 (mode_eval t2 [] []).
Proof.
  induction 1.
  { (* Case Beta *)
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
  { (* AppL *)
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
  { (* AppR *)
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
Abort.
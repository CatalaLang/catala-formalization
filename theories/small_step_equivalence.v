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
Notation "'apply_state' s" := (fst (apply_state_aux s)) (at level 50, only parsing).

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

Lemma creds_apply_state_sigma_stable s1 s2:
  star cred s1 s2 ->
  snd (apply_state_aux s1) = snd (apply_state_aux s2).
Proof.
  induction 1 using star_ind_n1; eauto.
  rewrite IHstar.
  rewrite (cred_apply_state_sigma_stable _ _ H).
  eauto.
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

Theorem simulation_sred_cred t1 t2:
  sred t1 t2 ->
  forall s1, match_conf s1 t1 ->
  exists s2,
    (plus cred s1 s2)
  /\ match_conf s2 t2.
Proof.
  intros Hred s1 MC.
  remember (stack s1) as kappa.
  generalize dependent s1.
  generalize dependent t2.
  generalize dependent t1.
  induction kappa using List.rev_ind.
  { induction 1.
    3: {
      induction s1; inversion 1; intros; repeat (simpl in *; subst).
      { (* eval mode *)
        match goal with
        | [h: _ = ?e.[subst_of_env ?env] |- _ ] =>
          induction e; asimpl in h; inj;
          try solve
          [ clear -h;
            match goal with [ _: context [subst_of_env ?env ?x] |- _] =>
              destruct (subst_of_env_Value_Var env x) end;
            unpack; congruence
          ]
        end.

        (* apply induction hypothesis. *)
        destruct IHHred with ((mode_eval e1 [] env0)) as (s2 & Hs1s2 & MCs2).
        { econstructor; simpl; eauto. }
        { simpl; eauto. }

        (* This is the new term. *)
        exists (append_stack s2 [CAppR e2]); split.
        { (* Let us first prove it is indeed the successor of s1. *)
          eapply plus_left. { econstructor. }
          match goal with
            [h: plus cred ?s1 ?s2 |- star cred ?s1' (append_stack ?s2 ?kappa)] =>
              replace s1' with (append_stack s1 kappa);
              try solve [simpl; eauto]
          end.
          eapply append_stack_stable_star; eauto with sequences.
        }
        { (* Then let us show it is indeed linked to our new term. This is
             thanks to our previous lemma about stability of the environement upon reduction. *)
          inversion MCs2; subst; clear MCs2.
          econstructor.
          rewrite apply_state_append_stack.
          simpl; unfold apply_cont.
          rewrite (surjective_pairing (apply_state_aux s2)); simpl.
          repeat f_equal.
          match goal with
            [h: plus cred ?s1 ?s2 |- ?env = snd (apply_state_aux ?s2)] =>
              replace env with (snd (apply_state_aux s1));
              try solve [simpl; eauto]
          end.
          eapply creds_apply_state_sigma_stable; eauto with sequences.
        }
      }
      { (* It is not possible for an empty list to have such a case. *)
        induction result; unfold apply_return in *; inj.
      }
    }
    all: admit "for now...".
  }
  {
    induction 1.
    3: {
      match goal with [x: cont |- _] => induction x end;
      induction s1; inversion 1; intros;
      repeat (simpl in *; autorewrite with apply_conts in *; subst).
      all: match goal with
        | [ h: context [apply_cont (apply_conts ?kappa ?p)] |- _] =>
          rewrite (surjective_pairing (apply_conts kappa p)) in h;
          unfold apply_cont in h;
          simpl in h;
          inj
        end.
      
    }
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
  3:{
    induction s1.
    {
      { simpl in H0.
        induction e; try solve [exfalso; simpl in *; inj].
        { exfalso.
          unfold subst_of_env in *.
          asimpl in *.
          remember (List.nth_error env0 x) as o.
          induction o; inj.
        }
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
            replace env0 with (snd (apply_state_aux (mode_eval e1 [] env0))).
            replace b with (snd (apply_state_aux s2)).
            eapply creds_apply_state_sigma_stable; eauto with sequences.
            all: try rewrite <- Heqy; simpl; eauto.
          }
        }
      }
    }
  }
Admitted.
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
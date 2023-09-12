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

Definition apply_state (s: state): term :=
  fst (apply_state_aux s).

(* Require Import Coq.Arith.Arith.
Require Import Coq.ZArith.ZArith.

Goal forall x, x = apply_state (mode_eval (Var 0) [CReturn [Int 5]; CBinopR Add (Var 0); CReturn []]
[Int 3; Int 5]) -> True.
simpl;unfold subst_of_env;simpl. *)


Definition env s:=
  match s with
  | mode_eval _ _ sigma => sigma
  | mode_cont _ sigma _ => sigma
  end
.

Inductive match_conf : state -> term -> Prop :=
  | match_conf_intro: forall s t,
      t = apply_state s ->
      match_conf s t.

Remark red_apply_cont:
  forall k c1 s1 c2 s2,
    sred c1.[subst_of_env s1] c2.[subst_of_env s2] ->
    sred
      (let (c1', s1') := apply_cont (c1, s1) k in
        c1'.[subst_of_env s1])
      (let (c2', s2') := apply_cont (c2, s2) k in
        c2'.[subst_of_env s2]).
Proof.
  induction k; intros; cbn.
Abort.


Lemma match_conf_coherent:


(* Lemma inversion_App_apply_state:
  forall t1 t2 s,
    App t1 t2 = apply_state s ->
    (exists e1 e2 sigma kappa,
      s = mode_eval (App e1 e2) kappa sigma
      /\ List.Forall (fun k => exists sigma', k = CReturn sigma') kappa
    ) \/
    (exists e1 e2 kappa1 kappa2 sigma,
      s = mode_eval e1 (kappa1 ++ (CAppR e2) :: kappa2) sigma
      /\ List.Forall (fun k => exists sigma', k = CReturn sigma') kappa2
    ) \/
    (exists e1 t_cl sigma_cl kappa1 kappa2 sigma,
      s = mode_eval e1 (kappa1 ++ (CClosure t_cl sigma_cl) :: kappa2) sigma
      /\ List.Forall (fun k => exists sigma', k = CReturn sigma') kappa2
    ) \/
    (exists e1 e2 kappa1 kappa2 sigma,
      s = mode_cont (kappa1 ++ (CAppR e2) :: kappa2) sigma e1
      /\ List.Forall (fun k => exists sigma', k = CReturn sigma') kappa2
    ) \/
    (exists e1 t_cl sigma_cl kappa1 kappa2 sigma,
      s = mode_cont (kappa1 ++ (CClosure t_cl sigma_cl) :: kappa2) sigma e1
      /\ List.Forall (fun k => exists sigma', k = CReturn sigma') kappa2
    )
.
Proof.
  intros.
  induction s.
  { (* mode_eval *)
    induction kappa using List.rev_ind.
    {
      match goal with [_: context [ mode_eval ?_t _ ?_env] |- _] =>
        rename _t into e;
        rename _env into sigma
      end
      .
      induction e; try solve [exfalso; simpl in *; inj].
      { exfalso;
        simpl in *.
        unfold subst_of_env in *.
        remember (List.nth_error sigma x) as o.
        induction o; simpl in *; inj.
      }
      { left. repeat econstructor. }
    }
    { match goal with [_h: cont |- _] => rename _h into k end.
      induction k;
        simpl in H;
        unfold apply_conts in H;
        rewrite List.fold_left_app in H;
        remember (List.fold_left apply_cont kappa (e.[subst_of_env env0], env0)) as y;
        induction y;
        simpl in H; inj
        .
      { right; left.
        repeat econstructor.
      }
      { right; right; left.
        repeat econstructor.
      }
      { destruct IHkappa as [H1|[H2|[H3|[H4|H5]]]].
        { subst; simpl.
          unfold apply_conts.
          rewrite <- Heqy; eauto.
        }
        { left.
          unpack; inj.
          repeat econstructor.
          eapply List.Forall_app; eauto.
        }
        { right; left.
          unpack; inj.
          rewrite <- List.app_assoc.
          rewrite <- List.app_comm_cons.
          repeat econstructor.
          eapply List.Forall_app; eauto.
        }
        { right; right; left.
          unpack; inj.
          rewrite <- List.app_assoc.
          rewrite <- List.app_comm_cons.
          repeat econstructor.
          eapply List.Forall_app; eauto.
        }
        { unpack; inj. }
        { unpack; inj. }
      }
      { induction o; inj. }
    }
  }
  { (* mode_cont *)
    induction kappa using List.rev_ind.
    {
      match goal with [_: context [ mode_cont _ ?_env ?_t] |- _] =>
        rename _t into e;
        rename _env into sigma
      end
      .
      induction e; try solve [exfalso; simpl in *; inj].
    }
    { match goal with [_h: cont |- _] => rename _h into k end.
      induction k.
      all: simpl in H.
      all: unfold apply_conts in H.
      all: rewrite List.fold_left_app in H.
      all: remember (List.fold_left apply_cont kappa (apply_return result, env0)) as y.
      all: induction y.
      all: simpl in H; inj.
      { right; right; right; left.
        repeat econstructor.
      }
      { right; right; right; right.
        repeat econstructor.
      }
      { destruct IHkappa as [H1|[H2|[H3|[H4|H5]]]].
        { subst; simpl.
          unfold apply_conts.
          rewrite <- Heqy; eauto.
        }
        all: try solve [unpack; inj].
        { right; right; right; left.
          unpack; inj.
          rewrite <- List.app_assoc.
          rewrite <- List.app_comm_cons.
          repeat econstructor.
          eapply List.Forall_app; eauto.
        }
        { right; right; right; right.
          unpack; inj.
          rewrite <- List.app_assoc.
          rewrite <- List.app_comm_cons.
          repeat econstructor.
          eapply List.Forall_app; eauto.
        }
      }
      { induction o; inj. }
    }
  }
Qed.

Lemma apply_conts_returns t kappa sigma:
  List.Forall (fun k => exists sigma', k = CReturn sigma') kappa ->
  apply_state (mode_eval t kappa sigma) = t.[subst_of_env sigma].
Proof.
  induction kappa using List.rev_ind.
  { eauto. }
  { intros; unpack; subst.
    simpl; unfold apply_conts.
    rewrite List.fold_left_app.
    remember (List.fold_left apply_cont kappa (t.[subst_of_env sigma], sigma)) as y; induction y; simpl.
    simpl in IHkappa.
    unfold apply_conts in IHkappa.
    rewrite <- Heqy in IHkappa.
    simpl in IHkappa.
    eapply IHkappa.
    eauto.
  }
Qed. *)


(* Lemma subst_of_env_nil_id:
  subst_of_env [] = ids.
Proof.
  eapply FunctionalExtensionality.functional_extensionality.
  induction x; asimpl; eauto.
Qed.


Lemma sred_DefaultE_first:
forall ti ti' ts2 tj tc,
  sred ti ti' ->
  sred (Default (ti::ts2) tj tc) (Default (ti'::ts2) tj tc).
Proof.
  intros.
  replace (ti :: ts2) with ([] ++ ti :: ts2); eauto.
  replace (ti' :: ts2) with ([] ++ ti' :: ts2); eauto.
  econstructor; eauto.
Qed.

Remark red_apply_cont_easy:
  forall k c1 c2,
  sred c1 c2 ->
  let '(t1, _) := (apply_cont (c1, []) k) in
  let '(t2, _) := (apply_cont (c2, []) k) in
  sred t1 t2.
Proof.
  induction k; intros.
  all: try solve [ simpl; try econstructor; eauto ].
  { induction o.
    all: unfold apply_cont.
    all: rewrite subst_of_env_nil_id.
    all: eapply sred_DefaultE_first.
    all: asimpl; eauto.
  }
Qed.

Remark red_apply_cont:
  forall k c1 c2 sigma,
  sred c1.[subst_of_env sigma] c2.[subst_of_env sigma] ->
  forall t1 t2 sigma1 sigma2,
  (t1, sigma1) = (apply_cont (c1.[subst_of_env sigma], sigma) k) ->
  (t2, sigma2) = (apply_cont (c2.[subst_of_env sigma], sigma) k) ->
  sred t1 t2.
Proof.
  induction k; intros.
  all: try solve [ simpl in *; inj; try econstructor; eauto ].
  {
    induction o.
    all: unfold apply_cont in *; inj.
    all: eapply sred_DefaultE_first.
    all: asimpl; eauto.
  }
Qed.

Require Import Autosubst_FreeVars.

(* extension of free variables to continuations. *)
Inductive fv_cont: nat -> cont -> Prop :=
| fv_CAppR:
  forall k t2,
    fv k t2 ->
    fv_cont k (CAppR t2)
| fv_CBinopL (op: op) (v1: value):
  forall k,
    fv_cont k (CBinopL op v1)
| fv_CBinopR (op: op) (t2: term):
  forall k,
    fv k t2 ->
    fv_cont k (CBinopR op t2)
| fv_CClosure (t_cl: {bind term}) (sigma_cl: list value):
  forall k, fv (S k) t_cl -> fv_cont (k - (List.length sigma_cl)) (CClosure t_cl sigma_cl)
| fv_CReturn (sigma: list value):
  forall k,
    fv_cont k (CReturn sigma)
| fv_CDefault (o: option value) (ts: list term) (tj: term) (tc: term):
  forall k,
    (* fv k o -> *)
    (List.Forall (fv k) ts ) ->
    (fv k tj) ->
    (fv k tc) ->
    fv_cont k (CDefault o ts tj tc)
| fv_CDefaultBase (tc: term):
  forall k,
    fv k tc ->
    fv_cont k (CDefaultBase tc)
| fv_CMatch (t1: term) (t2: {bind term}):
  forall k,
    fv k t1 ->
    fv (S k) t2 ->
    fv_cont k (CMatch t1 t2)
| fv_CSome:
  forall k, fv_cont k (CSome)
.


(** Defintion of free variables for a list of continuation. The main
    difficulity in this definition is the handling of CReturn. Here we choose
    to consider CReturn as an binder for the rest of the continuations. Hence, if [fv_conts (k + List.length sigma) conts] then [fv_conts k (CReturn sigma :: conts)].

*)
Inductive fv_conts: nat -> list cont -> Prop :=
| fv_nil:
  forall k,
    fv_conts k []
| fv_cons cont conts:
  forall k,
    (forall sigma, cont <> CReturn sigma) ->
    fv_cont k cont ->
    fv_conts k conts ->
    fv_conts k (cont :: conts)
| fv_cons_CReturn sigma conts:
  forall k,
    fv_cont k (CReturn sigma) ->
    fv_conts (k + List.length sigma) conts ->
    fv_conts k (CReturn sigma :: conts)
.

Lemma fv_conts_append kappa:
  forall k cont,
    fv_conts k (kappa++[cont])-> fv_conts k kappa.
Proof.
  induction kappa; asimpl.
  * econstructor.
  * intros; induction a; inversion H; subst; clear H.
    all: try solve [econstructor; eauto].
Qed.

Lemma apply_cont_inversion:
  forall k c1 sigma,
    fv_cont (List.length sigma) k ->
    fv (List.length sigma) c1 ->
    exists t1 sigma',
    fv (List.length sigma') t1 /\
    (t1.[subst_of_env sigma'], sigma') =
      apply_cont (c1.[subst_of_env sigma], sigma) k.
Proof.
  induction k; simpl.
  all: try rename sigma into sigma'. (* case CReturn *)
  all: intros c1 sigma HfvC Hfv; inversion HfvC; subst; clear HfvC.
  * exists (App c1 t2); asimpl; repeat econstructor; fv.
  * exists (Binop op (Value v1) c1); repeat econstructor; fv.
  * exists (Binop op c1 t2); repeat econstructor; fv.
  * exists (App (Value (Closure t_cl sigma_cl)) c1); repeat econstructor; fv.
  * exists (c1.[subst_of_env sigma]), sigma'.
    assert (Hclosed: closed c1.[subst_of_env sigma]).
    { eapply subst_env_fv_closed; eauto. }
    split.
    { unfold closed in *. eapply fv_monotonic; eauto with lia. }
    { rewrite (closed_unaffected_regular _ _ Hclosed); eauto.
      eapply subst_env_regular.
    }
  * induction o.
    { exists (Default (c1 :: Value a :: ts) tj tc); repeat econstructor; fv.
      { repeat split; repeat econstructor; eauto. }
    }
    { exists (Default (c1 :: ts) tj tc); repeat econstructor; fv. }
  * exists (Default [] c1 tc); repeat econstructor; fv.
  * exists (Match_ c1 t1 t2); repeat econstructor; fv.
  * exists (ESome c1); repeat econstructor; fv.
Qed.

Lemma apply_conts_inversion:
  forall kappa c1 sigma,
    fv (List.length sigma) c1 ->
    fv_conts (List.length sigma) kappa ->
    exists t1 sigma',
    fv (List.length sigma') t1 /\
    (t1.[subst_of_env sigma'], sigma') =
      apply_conts kappa (c1.[subst_of_env sigma]) sigma.
Proof.
  (* induction kappa using List.rev_ind; intros.
  { asimpl; eauto. }
  { unfold apply_conts in *; rewrite List.fold_left_app; simpl.
    pose proof (fv_conts_append _ _ _ H0).
    specialize (IHkappa c1 sigma H H1).
    unpack.
    rewrite <- H3.
    rename x1 into sigma''.
    pose proof (apply_cont_inversion x x0.[subst_of_env sigma''] sigma'').
    rewrite 
    remember (List.fold_left apply_cont kappa (c1.[subst_of_env sigma], sigma)) as y; induction y as [y1 y2].
    admit. *)
Admitted.

Remark red_apply_conts:
  forall kappa c1 c2 sigma,
  sred c1.[subst_of_env sigma] c2.[subst_of_env sigma] ->
  forall t1 t2 sigma1 sigma2,
  (t1, sigma1) = (apply_conts kappa c1.[subst_of_env sigma] sigma) ->
  (t2, sigma2) = (apply_conts kappa c2.[subst_of_env sigma] sigma) ->
  sred t1 t2.
Proof.
  induction kappa using List.rev_ind; intros.
  { simpl in *; inj; eauto. }
  { unfold apply_conts in *.
    repeat rewrite List.fold_left_app in *.
    simpl in *.
    (* match goal with
    [h: _ = apply_cont _ _ => destruct]
    apply_conts_inversion.
    remember (List.fold_left apply_cont kappa (c1.[subst_of_env sigma], sigma)) as y1.
    remember (List.fold_left apply_cont kappa (c2.[subst_of_env sigma], sigma)) as y2.
    induction y1; induction y2.
    eapply red_apply_cont.
    eapply IHkappa.
    eapply H.
    assert (sred a.[subst_of_env sigma] a0.[subst_of_env sigma]).
    { eapply red_apply_cont; eauto. admit. }
    { eapply IHkappa. eapply H2. }
    simpl List.fold_left.
  }
  all: try solve [ simpl; try econstructor; eauto ].
  {
    induction o.
    all: unfold apply_cont.
    all: eapply sred_DefaultE_first.
    all: asimpl; eauto.
  }
Qed. *)
Admitted.


(* Theorem simulation_cred_sred s1 s2:
  cred s1 s2 ->
  forall t1, match_conf s1 t1 ->
  exists t2,
    (plus sred t1 t2)
  /\ match_conf s2 t2.
Proof.
  induction 1; intros s1 MC; inversion MC; subst; cbn.
  (* Binops cases are 20, 21, 22. *)
  20:{
    econstructor; split.
    simpl.
  }

(* simplified version without anything but binary operators. *)
Theorem simulation_sred_cred t1 t2:
  sred t1 t2 ->
  forall s1, match_conf s1 t1 ->
  exists s2,
    (plus cred s1 s2)
  /\ match_conf s2 t2.
Proof.
  induction 1; intros s1 MC; inversion MC; subst; cbn.
  * induction s1.
    induction kappa using List.rev_ind. *) *)

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
        { assert (
            forall s kappa,
          (apply_state_aux (append_stack s kappa)) = (apply_conts kappa (apply_state_aux s))).
          { admit. }
          rewrite H2.
          asimpl.
          f_equal.
          { inversion H1; subst; eauto. }

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
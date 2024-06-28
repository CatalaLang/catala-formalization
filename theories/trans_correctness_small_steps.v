Require Import syntax.
Require Import small_step tactics.
Require Import sequences.
Require Import typing.

Require Import trans_definition.

Import List.ListNotations.
Open Scope list.


Theorem term_ind' : forall P : term -> Prop,
  (forall x : var, P (Var x)) ->
  (forall t1 : term, P t1 -> forall t2 : term, P t2 -> P (App t1 t2)) ->
  (forall t : {bind term}, P t -> P (Lam t)) ->
  (forall arg : term, P arg -> P (ErrorOnEmpty arg)) ->
  (forall arg : term, P arg -> P (DefaultPure arg)) ->
  forall (IHDef: forall (ts : list term), List.Forall P ts -> forall (tj : term),
  P tj -> forall tc : term, P tc -> P (Default ts tj tc)),
  P Empty ->
  P Conflict ->
  (forall v : value, P (Value v)) ->
  (forall (op : op) (t1 : term),
  P t1 -> forall t2 : term, P t2 -> P (Binop op t1 t2)) ->
  (forall u : term,
  P u ->
  forall t1 : term,
  P t1 -> forall t2 : {bind term}, P t2 -> P (Match_ u t1 t2)) ->
  P ENone ->
  (forall t : term, P t -> P (ESome t)) ->
  forall (IHFold: forall f : {bind 2 of term},
  P f -> forall ts, P ts -> forall (t : term), P t -> P (Fold f ts t)),
  forall IHArray: (forall (ts : list term), List.Forall P ts -> P (EArray ts)),
  (forall t : term,
  P t ->
  forall ta : term, P ta -> forall tb : term, P tb -> P (If t ta tb)) ->
  forall t : term, P t.
Proof.
  intros until t; revert t.
  fix IHt 1; lock IHt.
  induction t; eauto.
  { eapply IHDef; eauto.
    unlock IHt; clear -IHt.  
    induction ts; econstructor; eauto.
  }
  { eapply IHArray; eauto.
    unlock IHt; clear -IHt.  
    induction ts; econstructor; eauto.
  }
Qed.


Lemma trans_te_renaming:
  forall t u,
  trans t = u ->
  forall xi,
  trans t.[ren xi] = u.[ren xi].
Proof.
  induction t using term_ind'; repeat (asimpl; intros; subst; f_equal; eauto).
  { induction H; simpl; f_equal; eauto. }
  { induction H; simpl; f_equal; eauto. }
Qed.



Theorem trans_te_substitution_aux:
  forall t u,
  trans t = u ->
  forall sigma1 sigma2,
  (forall x, trans (sigma1 x) = sigma2 x) ->
  trans t.[sigma1] = u.[sigma2].
Proof.
  induction t using term_ind'; try solve [repeat (asimpl; intros; subst; f_equal; eauto)].
  { asimpl; intros; subst. asimpl. f_equal.
    eapply IHt; eauto.
    { intros. induction x; asimpl; eauto.
      eapply trans_te_renaming.
      eauto.
    }
  }
  { repeat (asimpl; intros; subst).
    repeat f_equal; eauto.
    induction H; asimpl; eauto; repeat f_equal; eauto.
  }
  { intros; subst; asimpl; f_equal; eauto.
    eapply IHt3; eauto.
    { intros. induction x; asimpl; eauto.
      eapply trans_te_renaming.
      eauto.
    }
  }
  { repeat (asimpl; intros; subst).
    repeat f_equal; eauto.
    induction H; asimpl; eauto; repeat f_equal; eauto.
  }
Qed.

Theorem trans_te_substitution:
  forall t,
  forall sigma1 sigma2,
  List.Forall2 (fun v1 v2 => trans_value v1 = v2) sigma1 sigma2 ->
  trans t.[subst_of_env sigma1] = (trans t).[subst_of_env sigma2].
Proof.
  intros.
  eapply trans_te_substitution_aux; eauto.
  intro a; revert a.
  induction H, a; asimpl; eauto. rewrite H; eauto.
Qed. 

Require Import common.

Theorem trans_te_substitution_0:
  forall t v,
  trans t.[Value v/] = (trans t).[Value (trans_value v)/].
Proof.
  intros.
  replace (scons (Value v) ids) with (subst_of_env (v::nil)).
  replace (scons (Value (trans_value v)) ids) with (subst_of_env ((trans_value v)::nil)).
  eapply trans_te_substitution; eauto.

  
  { eapply FunctionalExtensionality.functional_extensionality; intros.
    induction x; unfold subst_of_env; simpl; eauto; rewrite nth_error_nil; f_equal; lia. }
  { eapply FunctionalExtensionality.functional_extensionality; intros.  
    induction x; unfold subst_of_env; simpl; eauto; rewrite nth_error_nil; f_equal; lia.
  }
Qed.


Lemma Forall2_map: forall sigma,
  List.Forall2 (fun v1 v2 : value => trans_value v1 = v2) sigma
    (List.map trans_value sigma).
Proof.
  induction sigma; econstructor; eauto.
Qed.

Lemma array_one_value:
  forall v,
  [(Value v)] = (List.map (fun vi => Value vi) [v]).
Proof.
  simpl; eauto.
Qed.

Lemma array_nil_value:
  [] = (List.map (fun vi => Value vi) []).
Proof.
  simpl; eauto.
Qed.

Lemma cons_is_app [A]:
  forall (h: A) t,
  h::t = [h] ++ t.
Proof.
  simpl; eauto.
Qed.

Lemma trans_comm_value:
  forall v,
  trans (Value v) = Value (trans_value v).
Proof.
  simpl; eauto.
Qed.

Lemma map_trans_comm_value:
  forall vs,
  List.map trans (List.map (fun vi => Value vi) vs)
  = List.map (fun vi => Value vi) (List.map trans_value vs).
Proof.
  induction vs; simpl; eauto.
  { rewrite IHvs.
    eauto.
  }
Qed.



Theorem correction_small_steps:
  forall s1 s2,
  sred s1 s2 ->
  exists target,
    star sred
      (trans s1) target /\
    star sred
      (trans s2) target.
Proof.

  Local Ltac step := (
    try (eapply step_left; [solve [repeat econstructor; simpl; eauto; repeat intro; tryfalse]|]);
    try (eapply step_right; [solve [repeat econstructor; simpl; eauto; repeat intro; tryfalse]|])
  ).

  intros s1 s2.
  intros Hsred.
  induction Hsred; intros; unpack.
  (* When the right hand side is the result of the left hand side. *)
  all: try solve [simpl; repeat step; eapply diagram_finish].
  { asimpl. repeat step. eexists; split; simpl trans; [|eapply star_refl; fail].
    rewrite <- List.map_cons.
    eapply star_refl_eq.
    symmetry.
    eapply trans_te_substitution; eauto.
    eapply Forall2_map.
  }
  { simpl; repeat step; eexists; split; asimpl; eapply star_trans; eauto with sred; eapply star_refl. }
  { simpl; repeat step; eexists; split; asimpl; eapply star_trans; eauto with sred; eapply star_refl. }
  { simpl; repeat step.
    eapply step_left. { econstructor; simpl; eapply trans_value_op_correct; eauto. }
    eapply diagram_finish.
  }
  { simpl; repeat step; eexists; split; asimpl; eapply star_trans; eauto with sred; eapply star_refl. }
  { simpl; repeat step; eexists; split; asimpl; eapply star_trans; eauto with sred; eapply star_refl. }
  { simpl.
    (* Sadly, direct application of econstructor does not work here. Hence we need to apply the correct steps by hand. *)
    eapply step_left.
    { econstructor. econstructor.
      replace nil with (List.map (fun vi => Value vi) nil) by (simpl; 
      eauto).
      econstructor.
    }
    eapply step_left.
    { econstructor.
      (* econstructor fails here because fold tries first to apply the first argument, whereas it should first apply the second one *)
      Fail solve [econstructor; eauto].

      eapply sred_Fold_step.
      econstructor.
    }
    eapply step_left.
    { econstructor.
      eapply sred_Fold_finish.
    }

    (* After those manual steps, we finally arrive to the correct term *)
    eapply step_left; [econstructor|].
    eapply step_left; [econstructor|].
    eapply diagram_finish.
  }
  { simpl.
    (* Sadly, direct application of econstructor does not work here. Hence we need to apply the correct steps by hand. *)
    eapply step_left.
    { econstructor. econstructor.
      replace nil with (List.map (fun vi => Value vi) nil) by (simpl; 
      eauto).
      econstructor.
    }
    eapply step_left.
    { econstructor.
      (* econstructor fails here because fold tries first to apply the first argument, whereas it should first apply the second one *)
      Fail solve [econstructor; eauto].

      eapply sred_Fold_step.
      econstructor.
    }
    eapply step_left.
    { econstructor.
      eapply sred_Fold_finish.
    }

    (* After those manual steps, we finally arrive to the correct term *)
    eapply step_left; [econstructor|].
    eapply step_left; [econstructor|].
    eapply diagram_finish.
  }
  { simpl.
    eapply step_left. {
      replace nil with (List.map (fun vi => Value vi) nil) by (simpl; eauto).
      repeat econstructor.
    }
    eapply step_left. {
      econstructor.
      eapply sred_Fold_step.
      econstructor.
    }
    eapply step_left. {
      econstructor.
      eapply sred_Fold_finish.
    }
    eapply step_left; [econstructor|].
    eapply step_left; [econstructor|].
    eapply diagram_finish.
  }
  { simpl.
    eapply step_left. {
      replace nil with (List.map (fun vi => Value vi) nil) by (simpl; eauto).
      repeat econstructor.
    }
    eapply step_left. {
      econstructor.
      eapply sred_Fold_step.
      econstructor.
    }
    eapply step_left. {
      econstructor.
      eapply sred_Fold_finish.
    }
    eapply step_right. {
      replace nil with (List.map (fun vi => Value vi) nil) by (simpl; eauto).
      repeat econstructor.
    }
    eapply step_right. {
      econstructor.
      eapply sred_Fold_step.
      econstructor.
    }
    eapply step_right. {
      econstructor.
      eapply sred_Fold_finish.
    }
    eapply step_left; [econstructor|].
    eapply step_right; [econstructor|].
    eapply star_step_left; [eapply star_sred_if_cond; eauto|].
    eapply star_step_right; [eapply star_sred_if_cond; eauto|].
    eapply diagram_finish.
  }
  { simpl.
    (* need termination for this proof. *)
    admit.
  }
  { simpl.
    eapply step_left. {
      rewrite array_one_value.
      repeat econstructor.
    }
    eapply step_left. {
      econstructor.
      eapply sred_Fold_step.
      econstructor.
    }
    eapply step_left. {
      econstructor.
      eapply sred_Fold_rec.
    }
    eapply step_left. { econstructor; eapply sred_Fold_step; repeat econstructor. }
    eapply step_left. { econstructor; eapply sred_Fold_step; repeat econstructor. }
    eapply step_left. { econstructor; eapply sred_Fold_step; repeat econstructor. }
    eapply step_left. { econstructor; eapply sred_Fold_step; repeat econstructor. }
    eapply step_left. { econstructor; eapply sred_Fold_step; repeat econstructor. }
    simpl.
    eapply step_left. { econstructor; eapply sred_Fold_finish; repeat econstructor. }
    eapply step_left. { repeat econstructor. }
    simpl.
    eapply step_left. { repeat econstructor. }
    eapply diagram_finish.
  }
  { simpl.
    eapply step_left. {
      econstructor.
      eapply sred_Fold_args.
      rewrite <- (List.app_nil_l (Conflict :: List.map trans ts2)).
      rewrite array_nil_value.
      eapply sred_array_conflict.
    }
    eapply step_left. {
      econstructor.
      eapply sred_Fold_args_Conflict.
    }
    eapply step_left; [econstructor|].
    eapply diagram_finish.
  }

  { simpl.
    eapply step_left. {
      econstructor.
      eapply sred_Fold_args.
      rewrite cons_is_app.
      rewrite array_one_value.
      eapply sred_array_conflict.
    }
    eapply step_left. {
      econstructor.
      eapply sred_Fold_args_Conflict.
    }
    eapply step_left; [econstructor|].
    eapply diagram_finish.
  }
  { simpl.
    admit "need terminaison".
  }
  { simpl.
    admit "need terminaison".
  }
  { simpl.
    eapply star_step_left. {
      eapply star_sred_match_cond.
      eapply star_sred_fold_args.
      rewrite cons_is_app.
      rewrite array_one_value.
      eapply star_sred_array_ctx.
      eauto.
    }
    eapply star_step_right. {
      eapply star_sred_match_cond.
      eapply star_sred_fold_args.
      rewrite cons_is_app.
      rewrite array_one_value.
      eapply star_sred_array_ctx.
      eauto.
    }
    eapply diagram_finish.
  }
  { simpl.
    eapply star_step_left. {
      eapply star_sred_match_cond.
      eapply star_sred_fold_args.
      rewrite <- (List.app_nil_l (trans ti :: List.map trans ts2)).
      rewrite array_nil_value.
      eapply star_sred_array_ctx.
      eauto.
    }
    eapply star_step_right. {
      eapply star_sred_match_cond.
      eapply star_sred_fold_args.
      rewrite <- (List.app_nil_l (trans ti' :: List.map trans ts2)).
      rewrite array_nil_value.
      eapply star_sred_array_ctx.
      eauto.
    }
    eapply diagram_finish.
  }
  { simpl; repeat step. eexists; split; asimpl; eapply star_refl_eq; eauto.
    eapply trans_te_substitution_0. }
  { simpl; repeat step; eexists; split; asimpl; eapply star_trans; eauto with sred; eapply star_refl. }
  { simpl; repeat step; eexists; split; asimpl; eapply star_trans; eauto with sred; eapply star_refl. }
  { simpl; repeat step; eexists; split; asimpl; eapply star_trans; eauto with sred; eapply star_refl. }
  { simpl; repeat step; eexists; split; asimpl; eapply star_trans; eauto with sred; eapply star_refl. }
  { simpl; repeat step; eexists; split; asimpl; eapply star_trans; eauto with sred; eapply star_refl. }
  { simpl.
    eapply star_step_left. { eapply star_sred_fold_args; eauto. }
    eapply star_step_right. { eapply star_sred_fold_args; eauto. }
    eapply diagram_finish.
  }
  { simpl.
    eapply star_step_left. { eapply star_sred_fold; eauto. }
    eapply star_step_right. { eapply star_sred_fold; eauto. }
    eapply diagram_finish.
  }
  { simpl.
    eapply star_step_left. {
      rewrite List.map_app.
      rewrite List.map_cons.
      rewrite map_trans_comm_value.
      eapply star_sred_array_ctx; eauto.
    }
    eapply star_step_right. {
      rewrite List.map_app.
      rewrite List.map_cons.
      rewrite map_trans_comm_value.
      eapply star_sred_array_ctx; eauto.
    }
    eapply diagram_finish.
  }
  { simpl.
    eapply step_left. {
      rewrite List.map_app.
      rewrite List.map_cons.
      rewrite map_trans_comm_value.
      simpl.
      eapply sred_array_conflict; eauto.
    }
    eapply diagram_finish.
  }
  { simpl.
    eapply step_left. {
      rewrite map_trans_comm_value.
      econstructor.
    }
    eapply diagram_finish.
  }
Admitted.

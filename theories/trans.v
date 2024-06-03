Require Import syntax.
Require Import small_step tactics.
Require Import sequences.
Require Import typing.

Definition process_exceptions := 
  (Lam (* x => *) (Lam (* y => *) 
    (Match_ (Var 0 (* y *)) (* with *)
      (* | None => *)
        (Var 1 (* y *))
      (* | Some z => *)
        (Match_ (Var 2 (* x *)) (* with *)
          (* | None => *)
            (Var 1 (* y *))
          (* | Some w => *)
            (Conflict)
        )
      ))).


Fixpoint trans_ty (ty: type): type :=
  match ty with
  | TBool => TBool
  | TInteger => TInteger
  | TFun T1 T2 => TFun (trans_ty T1) (trans_ty T2)
  | TOption T => TOption (trans_ty T)
  | TUnit => TUnit
  | TDefault T => TOption (trans_ty T)
  | TArray T => TArray (trans_ty T)
  end
.

Fixpoint trans (t: term) : term :=
  match t with
  | Var x => Var x
  | App t1 t2 => App (trans t1) (trans t2)
  | Lam t => Lam (trans t)

  | Value v => Value (trans_value v)
  | Binop op t1 t2 => Binop op (trans t1) (trans t2)

  | Match_ u t1 t2 =>
    Match_ (trans u) (trans t1) (trans t2)
  | ENone => ENone
  | ESome t => ESome (trans t)

  | If t ta tb =>
    If (trans t) (trans ta) (trans tb)
  | Fold f ts acc =>
    Fold (trans f) (trans ts) (trans acc)

  | ErrorOnEmpty t => Match_ (trans t) Conflict (Var 0)
  | DefaultPure t => ESome (trans t)
  | Default ts tj tc =>
    Match_
      (Fold 
        process_exceptions
        (EArray (List.map trans ts)) ENone)
      (If (trans tj) (trans tc) ENone)
      (ESome (Var 0))
  | Empty => ENone
  | Conflict => Conflict
  | EArray ts => EArray (List.map trans ts)
  end

with trans_value v :=
  match v with
  | Bool b => Bool b
  | Int i => Int i
  | Closure t sigma => Closure (trans t) (List.map trans_value sigma)
  | VNone => VNone
  | VUnit => VUnit
  | VSome v => VSome (trans_value v)
  | VPure v => VSome (trans_value v)
  | VArray vs => VArray (List.map trans_value vs)
  end
.

Inductive no_default: term -> Prop :=
  | NDVar: forall x, no_default (Var x)
  | NDApp: forall t1 t2,
    no_default t1 ->
    no_default t2 ->
    no_default (App t1 t2)
  | NDLam: forall t,
    no_default t ->
    no_default (Lam t)

  | NDConflict:
    no_default Conflict

  | NDValue: forall v,
    no_default_value v ->
    no_default (Value v)
  | NDBinop: forall op t1 t2,
    no_default t1 ->
    no_default t2 ->
    no_default (Binop op t1 t2)

  | NDMatch_: forall u t1 t2,
    no_default u ->
    no_default t1 ->
    no_default t2 ->
    no_default (Match_ u t1 t2)
  | NDENone:
    no_default ENone
  | NDESome: forall t,
    no_default t ->
    no_default (ESome t)
  | NDFold: forall f ts t,
    no_default f ->
    no_default ts ->
    no_default t ->
    no_default (Fold f ts t)
  | NDIf: forall t ta tb,
    no_default t ->
    no_default ta ->
    no_default tb ->
    no_default (If t ta tb)

  | NDArray: forall ts,
    List.Forall no_default ts ->
    no_default (EArray ts)

with no_default_value: value -> Prop :=
  | NDBool: forall b, no_default_value (Bool b)
  | NDInt: forall i, no_default_value (Int i)
  | NDClosure: forall t sigma,
    no_default t ->
    List.Forall no_default_value sigma ->
    no_default_value (Closure t sigma)
  | NDVNone:
    no_default_value VNone
  | NDVUnit:
    no_default_value VUnit
  | NDVSome: forall v,
    no_default_value v ->
    no_default_value (VSome v)
  | NDVPure: forall v,
    no_default_value v ->
    no_default_value (VPure v)
  | NDVArray: forall vs,
    List.Forall no_default_value vs ->
    no_default_value (VArray vs)
.



Theorem no_more_defaults:
  forall t, no_default (trans t)
with no_more_defaults_value:
  forall v, no_default_value (trans_value v).
Proof.
{ induction t; simpl; repeat econstructor; eauto.
  { induction ts; econstructor; eauto. }
  { induction ts; econstructor; eauto. }
}
{ induction v; simpl; repeat econstructor; eauto.
  { induction sigma; econstructor; eauto. }
  { induction ts; econstructor; eauto. }
}
Qed.


Lemma trans_ty_inv_base {T}:
  inv_base (trans_ty T)
with trans_ty_inv_no_immediate_default {T}:
  inv_no_immediate_default (trans_ty T).
Proof.
  all: induction T; simpl; econstructor; eauto.
Qed.

Lemma trans_ty_correct:
  forall t Delta Gamma T,
    jt_term Delta Gamma t T ->
    jt_term Delta (List.map trans_ty Gamma) (trans t) (trans_ty T)
with trans_value_ty_correct:
  forall v Delta T,
    jt_value Delta v T ->
    jt_value Delta (trans_value v) (trans_ty T)
.
Proof.
  induction 1; simpl.
  all: repeat econs_jt; simpl.
  all: eauto using trans_ty_inv_base.
  all: eauto using trans_ty_inv_no_immediate_default.
  all: repeat econs_inv; simpl; eauto using trans_ty_inv_base, trans_ty_inv_no_immediate_default.

  { symmetry; eapply List.map_nth_error. eauto. }

  { induction H; simpl; econstructor; eauto.
  }
Admitted.

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

Lemma trans_value_op_correct:
  forall v op v1 v2,
    Some v = get_op op v1 v2 ->
    Some (trans_value v) = get_op op (trans_value v1) (trans_value v2).
Proof.
  induction op, v1 , v2; intros; simpl in *; inj; simpl; eauto.
Qed.

Import List.ListNotations.
Open Scope list.


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


(** Translation correctness using continuations. *)


(* To prove the translation correctness using continuations, we first need to extend the trans statement to states. This require to expand the definition to `cont`, `state`, `return` as well to `environements`. *)

Require Import continuations.



(* Executing (mode_eval (trans (Default (t::ts) tj tc)) [] sigma) *)
Goal forall t ts tj tc sigma, exists s, star cred
  (mode_eval (trans (Default (t::ts) tj tc)) nil sigma) s.
Proof.
  intros; eexists; simpl.
  repeat (eapply star_step; [econstructor|]).
Abort.

(* Executing (mode_eval (trans (Default (Value v :: t::ts) tj tc)) [] sigma) *)
Goal forall v t ts tj tc sigma, exists s, star cred
  (mode_eval (trans (Default (Value (VPure v)::t::ts) tj tc)) nil sigma) s.
Proof.
  intros; eexists; simpl.
  repeat (eapply star_step; [econstructor; simpl; eauto|]).
Abort.

Goal forall f vs init sigma, exists s, star cred
  (mode_eval (trans (Fold f (Value (VArray vs)) init)) nil sigma) s.
Proof.
  intros; eexists; simpl.
  repeat (eapply star_step; [econstructor; simpl; eauto|]).
Abort.

Goal forall h ts sigma, exists s, star cred
  (mode_eval (trans (EArray (h::ts))) nil sigma) s.
Proof.
  intros; eexists; simpl.
  repeat (eapply star_step; [econstructor; simpl; eauto|]).
Abort.

Fixpoint trans_conts (kappa: list cont) (sigma: list value): list cont :=
  (* This is the main function that translate continuations. For most continuation, it does not change anything, it is basically an `map` function.

  This is expected since the translation only modify Default terms. 
  *)
  match kappa with
  | nil => nil
  | CAppR t2 :: kappa => CAppR (trans t2) :: trans_conts kappa sigma
  | CBinopL op v1 :: kappa => CBinopL op (trans_value v1) :: trans_conts kappa sigma
  | CBinopR op t2 :: kappa => CBinopR op (trans t2) :: trans_conts kappa sigma
  | CClosure t_cl sigma_cl :: kappa => CClosure (trans t_cl) (List.map trans_value sigma_cl) :: trans_conts kappa sigma
  | CReturn sigma' :: kappa => CReturn (List.map trans_value sigma') :: trans_conts kappa (List.map trans_value sigma')
  | CDefaultBase tc :: kappa => CIf (trans tc) ENone :: trans_conts kappa sigma
  | CMatch t1 t2 :: kappa => CMatch (trans t1) (trans t2) :: trans_conts kappa sigma
  | CSome :: kappa => CSome :: trans_conts kappa sigma
  | CIf t1 t2 :: kappa => CIf (trans t1) (trans t2) :: trans_conts kappa sigma
  | CErrorOnEmpty :: kappa => CMatch Conflict (Var 0) :: trans_conts kappa sigma
  | CDefaultPure :: kappa => CSome :: trans_conts kappa sigma
  | CFold f ts :: kappa =>
    CFold (trans f) (trans ts) :: trans_conts kappa sigma
  | CFoldAcc f vs :: kappa =>
    CFoldAcc (trans f) (trans_value vs) :: trans_conts kappa sigma
  | CArray ts vs :: kappa =>
    CArray (List.map trans ts) (List.map trans_value vs) :: trans_conts kappa sigma

  | CDefault b None ts tj tc :: kappa =>
    (CArray (List.map trans ts) [])::
    (CFold 
      process_exceptions
      ENone)::
    (CMatch
      (If (trans tj) (trans tc) ENone)
      (ESome (Var 0))) ::
      trans_conts kappa sigma
  | CDefault b (Some v) ts tj tc :: kappa =>
    (CArray (List.map trans ts) [VSome (trans_value v)])::
    (CFold 
      process_exceptions
      ENone)::
    (CMatch
      (If (trans tj) (trans tc) ENone)
      (ESome (Var 0))) ::
      trans_conts kappa sigma
  end.

Definition trans_return (r: result): result:=
  match r with
  | RValue v => RValue (trans_value v)
  | REmpty => RValue VNone
  | RConflict => RConflict
  end.

Definition trans_state (s: state) : state :=
  match s with
  | mode_eval e kappa env =>
    mode_eval (trans e) (trans_conts kappa (List.map trans_value env)) (List.map trans_value env)
  | mode_cont kappa env r =>
    mode_cont (trans_conts kappa (List.map trans_value env)) (List.map trans_value env) (trans_return r)
  end
.

Lemma CArray_reduces:
  forall t ts vs sigma,
  exists vs' r,
    star cred
      (mode_eval t [CArray ts vs] sigma)
      (mode_cont [CArray [] (vs'++vs)] sigma r)
.
Admitted.


Local Ltac step' := (
  (* This tatic try to advance the computation on the right or on the left of the diagram. *)
  try (eapply step_left; [solve
    (* generic case *)
    [ econstructor; simpl; eauto using List.map_nth_error
    (* for contextual error cases *)
    | econstructor; repeat intro; tryfalse
    | econstructor; eapply trans_value_op_correct; eauto
  ]|])
  ; try (eapply step_right; [solve
    [ econstructor; simpl; eauto using List.map_nth_error
    | econstructor; repeat intro; tryfalse
    | econstructor; eapply trans_value_op_correct; eauto
  ]|])
).

Lemma vnone_dont_cont_filter vs :
  forall o sigma Delta Gamma T,
  jt_state Delta Gamma (mode_cont [CFoldAcc process_exceptions (VArray vs)] sigma o) (TOption T) ->
  exists target,
    star cred
      (mode_cont [CFoldAcc process_exceptions (VArray vs)] sigma o)
      target /\
    star cred
    (mode_cont [CFoldAcc process_exceptions (VArray (List.filter (fun v => match v with VNone => false | _ => true end) vs))] sigma o)
      target
  .
Proof.
  induction vs; intros.
  { simpl; intros; repeat econstructor. }
  { induction o; unfold process_exceptions in *; repeat (sinv_jt; inj; subst; simpl in *; subst).
    all: fold process_exceptions in *.
    all: repeat step'.
    { eapply IHvs; repeat econs_jt; simpl; eauto. }
    { eapply IHvs; repeat econs_jt; simpl; eauto. }
    { eapply IHvs; repeat econs_jt; simpl; eauto. }
    all: try solve [repeat step'; repeat econstructor].
  }
Qed.

Lemma vnone_dont_count:
  forall t ts vs sigma o,
  exists target,
    star cred
      (mode_eval t [CArray ts (vs); CFold process_exceptions o] sigma)
      target
    /\
    star cred
      (mode_eval t [CArray ts (VNone::vs); CFold process_exceptions o] sigma)
      target
.
Admitted.

Lemma double_value_conflict:
  forall Delta Gamma T,
  forall t ts v1 v2  sigma,
    jt_state Delta Gamma (mode_eval (trans t) [CArray ts [VSome v1; VSome v2]; CFold process_exceptions ENone] sigma) (trans_ty T) ->
    star cred
      (mode_eval (trans t) [CArray ts [VSome v1; VSome v2]; CFold process_exceptions ENone] sigma)
      (mode_cont [] sigma RConflict)
.
Proof.
  intros.
  learn (CArray_reduces (trans t) ts [VSome v1; VSome v2] sigma); unpack.

  eapply star_trans.
  { erewrite append_stack_1; [simpl with_stack|simpl; eauto].
    eapply star_cred_append_stack.
    eauto.
  }
  simpl.
  induction r.

  { eapply star_step; [econstructor|].
    rewrite List.app_comm_cons.
    rewrite List.rev_app_distr.
    simpl.
    repeat first
      [ eapply star_refl
      | eapply star_step; [econstructor; simpl; eauto|]].
  }
  {
    (* The returned value cannot be REmpty, since its type is Defualt T, and the original type is well typed withtout Default. *)
    repeat sinv_jt.

    assert (Hjt_start: 
      jt_state
        Delta
        Gamma
        (mode_eval (trans t) [CArray ts [VSome v1; VSome v2]] sigma) (TArray (TOption T2))).
    { repeat econs_jt; eauto.
      repeat econs_inv; eauto.
      inv H13; eauto.
    }

    learn (star_preservation _ _ H0 _ _ _ Hjt_start).

    repeat sinv_jt.
  }
  { repeat first
    [ eapply star_refl
    | eapply star_step; [econstructor; simpl; eauto|]].
  }
Qed.

Import List.ListNotations.
Require Import sequences.

Theorem correction_continuations:
  forall s1 s2 Gamma Delta T,
  jt_state Delta Gamma s1 T ->
  cred s1 s2 ->
  exists target,
    star cred
      (trans_state s1) target /\
    star cred
      (trans_state s2) target.
Proof.

  Local Ltac step' := (
    (* This tatic try to advance the computation on the right or on the left of the diagram. *)
    try (eapply step_left; [solve
      (* generic case *)
      [ econstructor; simpl; eauto using List.map_nth_error
      (* for contextual error cases *)
      | econstructor; repeat intro; tryfalse
      | econstructor; eapply trans_value_op_correct; eauto
    ]|])
    ; try (eapply step_right; [solve
      [ econstructor; simpl; eauto using List.map_nth_error
      | econstructor; repeat intro; tryfalse
      | econstructor; eapply trans_value_op_correct; eauto
    ]|])
  ).

  intros ? ? ? ? ? Hjt Hsred.
  induction Hsred;
    try induction phi;
    try induction o;
    intros; unpack.

  all:
    try solve [
      repeat step';
      try eapply diagram_finish;
      eauto
    ].

  { simpl. repeat step'.
    case ts.
    { repeat step'; eapply diagram_finish. }
    { intros; simpl.
      eapply step_left. econstructor.
      eapply step_right. econstructor.
      (* Need an external lemma here to show that both side reduces to the same thing. This is a property of CFold process exception, and is linked to the fact that they do not care about VNone. *)

      (* This is the lemma vnone_dont_count. *)
      learn (vnone_dont_count
        (trans t)
        (List.map trans l)
        ([])
        (List.map trans_value sigma)
        ENone).
      unpack.

      eapply star_step_left.
      { erewrite append_stack_2; [simpl with_stack|simpl; eauto].
        eapply star_cred_append_stack; eauto.
      }

      eapply star_step_right.
      { erewrite append_stack_2; [simpl with_stack|simpl; eauto].
        eapply star_cred_append_stack; eauto.
      }
      eapply diagram_finish.
    }
  }
  { simpl. repeat step'.
    (* same *)
    learn (vnone_dont_count
      (trans th)
      (List.map trans ts)
      ([VSome (trans_value a)])
      (List.map trans_value sigma)
      ENone).
    unpack.

    eapply star_step_left.
    { erewrite append_stack_2; [simpl with_stack|simpl; eauto].
      eapply star_cred_append_stack; eauto.
    }

    eapply star_step_right.
    { erewrite append_stack_2; [simpl with_stack|simpl; eauto].
      eapply star_cred_append_stack; eauto.
    }
    eapply diagram_finish.
  }
  { simpl. repeat step'.
    (* same *)
    
    learn (vnone_dont_count
      (trans th)
      (List.map trans ts)
      ([])
      (List.map trans_value sigma)
      ENone).
    unpack.

    (* could be automated *)
    eapply star_step_left.
    { erewrite append_stack_2; [simpl with_stack|simpl; eauto].
      eapply star_cred_append_stack; eauto.
    }

    eapply star_step_right.
    { erewrite append_stack_2; [simpl with_stack|simpl; eauto].
      eapply star_cred_append_stack; eauto.
    }
    eapply diagram_finish.
  }
  { simpl; repeat step'.
    induction ts; simpl.
    { repeat step'; eapply diagram_finish. }
    { repeat step'.
      (* same *)
      learn (vnone_dont_count
        (trans a)
        (List.map trans ts)
        ([VSome (trans_value v)])
        (List.map trans_value sigma)
        ENone).
      unpack.

      eapply star_step_left.
      { erewrite append_stack_2; [simpl with_stack|simpl; eauto].
        eapply star_cred_append_stack; eauto.
      }

      eapply star_step_right.
      { erewrite append_stack_2; [simpl with_stack|simpl; eauto].
        eapply star_cred_append_stack; eauto.
      }
      eapply diagram_finish.
    }
  }
  { simpl; repeat step'.
    induction ts; simpl.
    { repeat step'. eapply diagram_finish. }
    { repeat step'.
      (* require an variant of the previous mentionned lemma to inducate we will go into a fatal error. *)

      learn (double_value_conflict
        (trans a)
        (List.map trans ts)
        (trans_value v')
        (trans_value v)
        ENone
        (List.map trans_value sigma)
      ).

      eapply star_step_left.
      { erewrite append_stack_2; [simpl with_stack|simpl; eauto].
        eapply star_cred_append_stack; eauto.
      }
      repeat step'.
      eapply diagram_finish.
    }
  }
  (* Only two cases are left. *)
  { tryfalse. }
  { (* require list rewriting. *)
    simpl; repeat step'; simpl.
    rewrite List.map_app, List.map_rev; simpl.
    eapply diagram_finish.
  }
Qed.

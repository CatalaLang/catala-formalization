Require Import syntax.
Require Import small_step tactics.
Require Import sequences.
Require Import typing.



Notation monad_bind t1 t2 := (Match_ t1 ENone t2).


Fixpoint monad_handle_one res (ts: list term) : term :=
  match ts with
  | nil => ESome res
  | cons thead ttail =>
    Match_ thead
      (monad_handle_one res ttail)
      (Conflict)
  end.

Fixpoint monad_handle_zero ts tj tc: term :=
  match ts with
  | nil => If tj tc ENone
  | cons thead ttail =>
    Match_ thead
      (monad_handle_zero ttail tj tc)
      (monad_handle_one (Var 0) (List.map (fun t => lift 1 t) ttail))
  end.

Definition monad_handle ts tj tc: term :=
  monad_handle_zero ts tj tc
.

Lemma subst_monad_handle_one :
  forall res ts sigma,
  (monad_handle_one res ts).[sigma] = monad_handle_one res.[sigma] ts..[sigma].
Proof.
  induction ts; repeat (asimpl; intros; f_equal; eauto).
Qed.

Lemma subst_monad_handle_zero :
  forall ts tj tc sigma,
  (monad_handle_zero ts tj tc).[sigma] = monad_handle_zero ts..[sigma] tj.[sigma] tc.[sigma].
Proof.
  induction ts; repeat (asimpl; intros; f_equal; eauto).
Admitted.

Lemma subst_monad_handle:
  forall ts tj tc sigma,
  (monad_handle ts tj tc).[sigma] = monad_handle ts..[sigma] tj.[sigma] tc.[sigma].
Proof.
  eapply subst_monad_handle_zero.
Qed.


Fixpoint trans (t: term) : term :=
  match t with
  | Var x => Var x
  | FreeVar x => FreeVar x
  | App t1 t2 => App (trans t1) (trans t2)
  | Lam t => Lam (trans t)

  | ErrorOnEmpty t => Match_ (trans t) Conflict (Var 0)
  | DefaultPure t => ESome (trans t)
  | Default ts tj tc =>
    Match_
      (Fold 
        (Lam (Lam 
          (Match_
            (Var 0)
            (Var 1)
            (Match_
              (Var 2)
              (Var 1)
              (Conflict)
            )
          )))
        (List.map trans ts) ENone)
      (If (trans tj) (trans tc) ENone)
      (ESome (Var 0))
  | Empty => ENone
  | Conflict => Conflict

  | Value v => Value (trans_value v)
  | Binop op t1 t2 => Binop op (trans t1) (trans t2)

  | Match_ u t1 t2 =>
    Match_ (trans u) (trans t1) (trans t2)
  | ENone => ENone
  | ESome t => ESome (trans t)

  | If t ta tb =>
    If (trans t) (trans ta) (trans tb)
  | Fold f ts acc =>
    Fold (trans f) (List.map trans ts) (trans acc)
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
  end
.


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
  (forall x : String.string, P (FreeVar x)) ->
  (forall (op : op) (t1 : term),
  P t1 -> forall t2 : term, P t2 -> P (Binop op t1 t2)) ->
  (forall u : term,
  P u ->
  forall t1 : term,
  P t1 -> forall t2 : {bind term}, P t2 -> P (Match_ u t1 t2)) ->
  P ENone ->
  (forall t : term, P t -> P (ESome t)) ->
  forall (IHFold: forall f : {bind 2 of term},
  P f -> forall (ts : list term), List.Forall P ts -> forall (t : term), P t -> P (Fold f ts t)),
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
  { eapply IHFold; eauto.
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


Lemma trans_te_renaming_0:
  forall t u,
  trans t = u ->
  trans (lift 1 t) = (lift 1 u).
Proof.
  intros.
  eapply trans_te_renaming; eauto.
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
      eapply trans_te_renaming_0.
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
      eapply trans_te_renaming_0.
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


Theorem correction_small_steps:
  forall s1 s2,
  (exists GGamma Gamma T, jt_term GGamma Gamma s1 T) ->
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
  intros (GGamma & Gamma & T & Hty).
  intros Hsred.
  generalize dependent GGamma.
  generalize dependent Gamma.
  generalize dependent T.
  induction Hsred; intros.
  all: repeat multimatch goal with
  | _ => sinv_jt
  | [h1: forall _ _ _, jt_term _ _ ?u _ -> _, h2: jt_term _ _ ?u _ |- _] =>
    learn (h1 _ _ _ h2);
    clear h1
  | [h: exists var, _ |- _] =>
    let var := fresh var in
    destruct h as (var & ?)
  | [h: _ /\ _ |- _] =>
    destruct h
  
  end.
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
  { simpl; repeat step; eexists; split; asimpl; eapply star_trans; eauto with sred; eapply star_refl. }
  { simpl; repeat step; eexists; split; asimpl; eapply star_trans; eauto with sred; eapply star_refl. }
  { simpl; repeat step; eexists; split; asimpl; eapply star_trans; eauto with sred; eapply star_refl. }
  { simpl; repeat step. eexists; split; asimpl; eapply star_refl_eq; eauto.
    eapply trans_te_substitution_0. }
  { simpl; repeat step; eexists; split; asimpl; eapply star_trans; eauto with sred; eapply star_refl. }
  { simpl; repeat step; eexists; split; asimpl; eapply star_trans; eauto with sred; eapply star_refl. }
  { simpl; repeat step; eexists; split; asimpl; eapply star_trans; eauto with sred; eapply star_refl. }
  { simpl; repeat step; eexists; split; asimpl; eapply star_trans; eauto with sred; eapply star_refl. }
  { simpl; repeat step; eexists; split; asimpl; eapply star_trans; eauto with sred; eapply star_refl. }
Qed.


(** Translation correctness using continuations. *)


(* To prove the translation correctness using continuations, we first need to extend the trans statement to states. This require to expand the definition to `cont`, `state`, `return` as welle as `environements`. *)

Require Import continuations.

Definition option_map {A B} (f: A -> B) (o: option A) :=
  match o with
  | None => None
  | Some v => Some (f v)
  end.


(* Naively, we would think that translating cont would be simply. In ocaml, we would have a function

map_cont: (term -> term) -> (value -> value) -> cont -> cont

Then, [trans_cont] would be simply be [map_cont trans_term trans_value] and [trans_conts] would be simply [List.map trans_cont].

This is mostly the case, except for the default related continuations.
*)

Fixpoint trans_conts (kappa: list cont) (sigma: list value): list cont :=
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
  | CDefault b None ts tj tc :: kappa =>
    magic
  | CDefault b (Some v) ts tj tc :: kappa =>
    magic
  | CFold f ts :: kappa =>
    CFold (trans f) (List.map trans ts) :: trans_conts kappa sigma
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


Import List.ListNotations.


Require Import sequences.

Lemma append_stack_nil_eval:
  forall {t kappa sigma},
    mode_eval t kappa sigma = append_stack (mode_eval t [] sigma) kappa.
Proof.
  intros; simpl; eauto.
Qed.

Lemma append_stack_nil_cont:
  forall {kappa sigma r},
    mode_cont kappa sigma r = append_stack (mode_cont [] sigma r) kappa.
Proof.
  intros; simpl; eauto.
Qed.

Theorem correction_continuations:
  forall s1 s2,
  (exists GGamma Gamma T, jt_state GGamma Gamma s1 T) ->
  cred s1 s2 ->
  exists target,
    star cred
      (trans_state s1) target /\
    star cred
      (trans_state s2) target.
Proof.

  Local Ltac step' := (
    try (eapply step_left; [solve [econstructor; simpl; eauto; repeat intro; tryfalse]|]);
    try (eapply step_right; [solve [econstructor; simpl; eauto; repeat intro; tryfalse]|])
  ).

  intros s1 s2.
  intros (GGamma & Gamma & T & Hty).
  intros Hsred.
  generalize dependent GGamma.
  generalize dependent Gamma.
  generalize dependent T.
  induction Hsred; intros.
  all: repeat multimatch goal with
  | _ => sinv_jt
  | [h1: forall _ _ _, jt_state _ _ ?u _ -> _, h2: jt_state _ _ ?u _ |- _] =>
    learn (h1 _ _ _ h2);
    clear h1
  | [h: exists var, _ |- _] =>
    let var := fresh var in
    destruct h as (var & ?)
  | [h: _ /\ _ |- _] =>
    destruct h
  end.

  all: try induction phi; try induction o.
  all:
    try solve [simpl; repeat step'; tryfalse; try eapply diagram_finish; eauto].
  {
    eexists; split; asimpl; [|eapply star_refl].
    eapply star_one; simpl; econstructor. eauto using List.map_nth_error.
  }
  { simpl. repeat step.  }
  { eexists; split; asimpl; [|eapply star_refl].
    eapply star_step; [econstructor|]. { eapply trans_value_op_correct; eauto. }
    eapply star_refl.
  }
  Fail next goal.
Abort.

Require Import syntax.
Require Import small_step tactics.
Require Import sequences.
Require Import typing.



Notation monad_bind t1 t2 := (Match_ t1 ENone t2).


Fixpoint monad_handle_one res (ts: list term) : term :=
  match ts with
  | nil => ESome res
  | cons thead ttail =>
    Match_ (lift 1 thead)
      (monad_handle_one res ttail)
      (Conflict)
  end.

Fixpoint monad_handle_one' res (ts: list term) : term :=
  match ts with
  | nil => ESome res
  | cons thead ttail =>
    Match_ thead
      (monad_handle_one' res ttail)
      (Conflict)
  end.

Fixpoint monad_handle_zero ts tj tc: term :=
  match ts with
  | nil => If tj tc ENone
  | cons thead ttail =>
    Match_ thead
      (monad_handle_zero ttail tj tc)
      (monad_handle_one (Var 0) ttail)
  end.

Definition monad_handle ts tj tc: term :=
  monad_handle_zero ts tj tc
.

Lemma subst_monad_handle_one :
  forall res ts sigma,
  (monad_handle_one res ts).[up sigma] = monad_handle_one res.[up sigma] ts..[sigma].
Proof.
  induction ts; repeat (asimpl; intros; f_equal; eauto).
Qed.

Lemma subst_monad_handle_zero :
  forall ts tj tc sigma,
  (monad_handle_zero ts tj tc).[sigma] = monad_handle_zero ts..[sigma] tj.[sigma] tc.[sigma].
Proof.
  induction ts; repeat (asimpl; intros; f_equal; eauto).
  eapply subst_monad_handle_one.
Qed.

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
    monad_handle (List.map trans ts) (trans tj) (trans tc)
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
       forall (IHDef:forall (ts : list term),
        List.Forall P ts ->
        forall (tj : term),
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
Qed.


Lemma trans_te_renaming:
  forall t u,
  trans t = u ->
  forall xi,
  trans t.[ren xi] = u.[ren xi].
Proof.
  induction t using term_ind'; repeat (asimpl; intros; subst; f_equal; eauto).
  { rewrite subst_monad_handle;
    repeat (asimpl; intros; subst; f_equal; eauto).
    induction H.
    { simpl; eauto. }
    { simpl. f_equal.
      { eapply H; eauto. }
      { eapply IHForall. }
    }
  }
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
  { asimpl; intros; subst.
    rewrite subst_monad_handle; repeat (f_equal; eauto).
    induction H; asimpl; eauto; f_equal; eauto.
  }
  { intros; subst; asimpl; f_equal; eauto.
    eapply IHt3; eauto.
    { intros. induction x; asimpl; eauto.
      eapply trans_te_renaming_0.
      eauto.
    }
  }
Qed.

Theorem trans_te_substitution:
  forall t u,
  trans t = u ->
  forall sigma1 sigma2,
  List.Forall2 (fun v1 v2 => trans_value v1 = v2) sigma1 sigma2 ->
  trans t.[subst_of_env sigma1] = u.[subst_of_env sigma2].
Proof.
  intros.
  eapply trans_te_substitution_aux; eauto.
  intro a; revert a.
  induction H0, a; asimpl; eauto. rewrite H0; eauto.
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

  Ltac step := (
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
  all: try solve [
    eexists; split; asimpl;
    [|eapply star_refl];
    eapply star_one; simpl; econstructor; eauto
    ].
  { eexists; split; simpl trans; [|eapply star_refl; fail].
    eapply star_step; [econstructor|].
    rewrite <- List.map_cons.
    eapply star_refl_eq.
    symmetry.
    eapply trans_te_substitution; eauto.

    eapply Forall2_map.
  }
  { eexists; split; asimpl; eapply star_trans; eauto with sred; eapply star_refl. }
  { eexists; split; asimpl; eapply star_trans; eauto with sred; eapply star_refl. }
  { eexists; split; simpl trans; [|eapply star_refl; fail].
    eapply star_step; [econstructor|]. { eapply trans_value_op_correct; eauto. }
    eapply star_refl.
  }
  { eexists; split; asimpl; eapply star_trans; eauto with sred; eapply star_refl. }
  { eexists; split; asimpl; eapply star_trans; eauto with sred; eapply star_refl. }
  { eexists; split; asimpl; eapply star_trans; eauto with sred; eapply star_refl. }
  { eexists; split; simpl trans; [|eapply star_refl; fail].
    eapply star_step; [econstructor|].
    eapply star_step; [econstructor|].
    asimpl.
    eapply star_refl.
  }
  { eexists; split; simpl trans; [|eapply star_refl; fail].
    eapply star_step; [econstructor|].
    eapply star_step; [econstructor|].
    eapply star_refl.
  }
  {
    eexists; split; simpl trans; [|eapply star_refl; fail].
    eapply star_step; [econstructor|].
    asimpl.
    eapply star_step; [econstructor|].
    eapply star_refl.
  }
  { eexists; split; simpl trans.
    2:{
      eapply star_step; [econstructor|].
      eapply star_refl.
    }
    eapply star_step; [econstructor|].
    asimpl.
    eapply star_step; [econstructor; econstructor|].
    eapply star_step; [econstructor|].
    eapply star_refl.
  }
  { eexists; split; simpl trans; [|eapply star_refl; fail].
    eapply star_step; [econstructor; econstructor|].
    eapply star_step; [econstructor|].
    eapply star_refl.
  }
  { eexists; split; asimpl.
    { eapply star_step; [econstructor|].
      eapply star_sred_match_cond; asimpl; eauto. }
    { eapply star_step; [econstructor|].
      eapply star_sred_match_cond; asimpl; eauto. }
  }
  { eexists; split; asimpl; eapply star_trans; eauto with sred; eapply star_refl. }
  { eexists; split; simpl trans; [|eapply star_refl; fail].
    eapply star_step; [econstructor|].
    eapply star_refl_eq.
    rewrite trans_te_substitution_0; eauto.
  }
  { eexists; split; asimpl; eapply star_trans; eauto with sred; eapply star_refl. }
  { eexists; split; asimpl; eapply star_trans; eauto with sred; eapply star_refl. }
  { eexists; split; asimpl; eapply star_trans; eauto with sred; eapply star_refl. }
  { eexists; split; asimpl; eapply star_trans; eauto with sred; eapply star_refl. }
  { eexists; split; simpl trans; [|eapply star_refl; fail].
    eapply star_step; [econstructor; econstructor|].
    eapply star_step; [econstructor|].
    eapply star_refl.
  }
  { eexists; split; asimpl; eapply star_trans; eauto with sred; eapply star_refl. }
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
    CMatch (monad_handle_zero (List.map trans ts) (trans tj) (trans tc)) (monad_handle_one (Var 0) (List.map trans ts)) :: trans_conts kappa sigma

  | CDefault b (Some v) ts tj tc :: kappa =>
    CReturn (trans_value v::sigma) ::
    CMatch (
      monad_handle_one
        (Var 0)
        (List.map trans ts)
      )
      (Conflict) :: CReturn sigma :: trans_conts kappa sigma

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


(* Require Import simulation_sred_to_cred. *)

Import List.ListNotations.

(* Lemma lift_cred:
forall v e ts sigma, exists target,
  star cred
    (mode_eval (lift 1 e) [CMatch (monad_handle_one (Var 0) ts) Conflict; CReturn sigma] (v :: sigma))
    target
  /\
  star cred
    (mode_eval e [CMatch (monad_handle_one' (Value v) ts) Conflict] sigma)
    target.
Proof.

Admitted.


Lemma thing: forall ts sigma v GGamma Gamma T,
  List.Forall (fun ti : term => jt_term GGamma Gamma ti (TDefault T)) ts ->
  exists target : state,
    star cred (mode_eval (monad_handle_one (Var 0) (List.map trans ts))
                ([CReturn (List.map trans_value sigma)])
                (trans_value v :: List.map trans_value sigma))
              target /\
    star cred (mode_eval (monad_handle_one' (Value (trans_value v)) (List.map trans ts))
                [] (List.map trans_value sigma))
              target.
Proof.
  intros.
  induction ts; simpl; unpack.
  { repeat step; eapply diagram_finish. }
  { repeat step.
    edestruct (lift_cred (trans_value v) (trans a) (List.map trans ts) (List.map trans_value sigma)) as (target1 & Ht1 & Ht2).
    exists target1; eauto.
  }
Qed. *)

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

Definition map_cont (map_term: term -> term) (map_value: value -> value) (k: cont) : cont :=
  match k with
  | CAppR t2 => CAppR (map_term t2)
  | CBinopL op v1 => CBinopL op (map_value v1)
  | CBinopR op t2 => CBinopR op (map_term t2)
  | CClosure t_cl sigma_cl => CClosure (t_cl) (List.map map_value sigma_cl)
  | CReturn sigma' => CReturn (List.map map_value sigma')
  | CDefaultBase tc => CIf (map_term tc) ENone
  | CMatch t1 t2 => CMatch (map_term t1) (map_term t2)
  | CSome => CSome
  | CIf t1 t2 => CIf (map_term t1) (map_term t2)
  | CErrorOnEmpty => CErrorOnEmpty
  | CDefaultPure => CDefaultPure
  | CDefault b None ts tj tc =>
    CDefault b (None) (List.map map_term ts) (map_term tj) (map_term tc)
  | CDefault b (Some v) ts tj tc =>
    CDefault b (Some (map_value v)) (List.map map_term ts) (map_term tj) (map_term tc)
  end.

Fixpoint map_conts_until_return
  map_term map_value (kappa: list cont) : list cont :=
  match kappa with
  | CReturn sigma :: kappa =>
    CReturn (List.map map_value sigma) :: kappa
  | h :: t =>
    (map_cont map_term map_value h) :: (map_conts_until_return map_term map_value t)
  | [] => [] 
  end.

Definition lift_state a s :=
  match s with
  | mode_eval t kappa sigma =>
    mode_eval (lift 1 t) (map_conts_until_return (fun t => lift 1 t) (fun x => x) kappa) (a::sigma)
  | mode_cont kappa sigma r =>
    mode_cont (map_conts_until_return (fun t => lift 1 t) (fun x => x) kappa) (a::sigma) r
  end.

Goal
  forall {v s1 s2},
  cred s1 s2 ->
  cred (lift_state v s1) (lift_state v s2).
Proof.
  induction 1.
  all: try solve [simpl; econstructor].
  all: admit.
Abort.



Lemma thing:
  forall {t sigma sigma' r v},
  star cred (mode_eval t [] sigma) (mode_cont [] sigma' r ) ->
  star cred (mode_eval (lift 1 t) [] (v :: sigma)) (mode_cont [] (v:: sigma') r).
Admitted.

Require Import simulation_sred_to_cred.

Lemma cred_last:
  forall s1 s2,
    cred s1 s2 ->
    last (stack s1) (env s1) = last (stack s2) (env s2).
Proof.
  induction 1; try induction phi; simpl; eauto.
  { exfalso. eapply H; eauto. }
Qed.

Lemma star_cred_last:
  forall s1 s2,
    star cred s1 s2 ->
    last (stack s1) (env s1) = last (stack s2) (env s2).
Proof.
  induction 1 as [|? ? ? Hstep Hstar].
  { eauto. }
  { pose proof (cred_last _ _ Hstep).
    rewrite H; eauto.
  }
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
    try solve [simpl; repeat step; tryfalse; try eapply diagram_finish; eauto].
  {
    eexists; split; asimpl; [|eapply star_refl].
    eapply star_one; simpl; econstructor. eauto using List.map_nth_error.
  }
  { simpl trans_state.
    repeat step.
    assert (Hty: exists T', jt_state GGamma Gamma (mode_eval (trans th) [] (List.map trans_value sigma)) (T')). { admit. }

    unpack.

    pose proof (correctness.correctness_technical _ _ _ _ Hty); unpack.

    eapply star_step_right.
    {
      rewrite append_stack_nil_eval.
      eapply append_stack_stable_star.
      eauto.
    }
  
    eapply star_step_left.
    {
      rewrite append_stack_nil_eval.
      eapply append_stack_stable_star.
      eapply thing.
      eauto. 
    }
    simpl.
    repeat step.
    repeat eexists; eapply star_refl_eq; eauto; repeat f_equal.
    pose proof (star_cred_last _ _ H); simpl in *; eauto.
  }
  { eexists; split; asimpl; [|eapply star_refl].
    eapply star_step; [econstructor|]. { eapply trans_value_op_correct; eauto. }
    eapply star_refl.
  }
  Fail next goal.
Admitted.


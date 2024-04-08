Require Import syntax.
Require Import tactics.
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
    Fold (trans f) (List.map trans ts) (trans acc)

  | ErrorOnEmpty t => Match_ (trans t) Conflict (Var 0)
  | DefaultPure t => ESome (trans t)
  | Default ts tj tc =>
    Match_
      (Fold 
        process_exceptions
        (List.map trans ts) ENone)
      (If (trans tj) (trans tc) ENone)
      (ESome (Var 0))
  | Empty => ENone
  | Conflict => Conflict
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
  {
    induction 1.
    4:{ (* Default case *)
      simpl in *; repeat econs_jt; try reflexivity.
      all: repeat econstructor; eauto using trans_ty_inv_base, trans_ty_inv_no_immediate_default.
      { induction H; simpl; econstructor; eauto.
        replace (TOption (trans_ty T)) with (trans_ty (TDefault T)) by eauto.
        eapply trans_ty_correct; eauto.
      }
    }
    9:{ (* Fold case *)
      (* This is only penible for the same reason as in the typing preservation lemma: fold introduce an extential variable (the type of the list being modified) and coq fails to instanciate correctly this variable. This might be fiex by modifiying the order of the constructor in the inductive *)
      simpl.
      repeat econs_jt; eauto using trans_ty_inv_base, trans_ty_inv_no_immediate_default.
      { simpl in *.
        induction H2; simpl; econstructor; eauto.
      }
    }
    all: simpl; repeat econstructor; eauto using trans_ty_inv_base, trans_ty_inv_no_immediate_default.
    { symmetry. erewrite List.map_nth_error; eauto. }
    { induction op; simpl in *; inj; simpl; eauto. }
  }
  { induction 1; try solve [simpl; repeat econstructor; eauto using trans_ty_inv_no_default].
    { simpl trans_value; simpl trans_ty.
      assert (List.Forall2 (jt_value Delta) (List.map trans_value sigma_cl) (List.map trans_ty Gamma_cl)).
      { clear -H trans_value_ty_correct. induction H; simpl; econstructor; eauto. }
      econstructor.
      eapply H1.
      replace (Lam (trans tcl)) with (trans (Lam tcl)) by eauto.
      replace (TFun (trans_ty T1) (trans_ty T2)) with (trans_ty (TFun T1 T2)) by eauto.
      eapply trans_ty_correct.
      eauto.
    }
    { simpl in *; econstructor; eauto. }
    { simpl in *; econstructor; eauto. }
  }
Qed.


Require Import common.

Lemma trans_value_op_correct:
  forall v op v1 v2,
    Some v = get_op op v1 v2 ->
    Some (trans_value v) = get_op op (trans_value v1) (trans_value v2).
Proof.
  induction op, v1 , v2; intros; simpl in *; inj; simpl; eauto.
Qed.


(** Translation correctness using continuations. *)


(* To prove the translation correctness using continuations, we first need to extend the trans statement to states. This require to expand the definition to `cont`, `state`, `return` as well to `environements`. *)

Require Import continuations.


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
    CFold (trans f) (List.map trans ts) :: trans_conts kappa sigma

  | CDefault b None ts tj tc :: kappa =>
    (* This term can be derived from the trans fonction by taking the (mode_eval (trans (Default (t::ts) tj tc)) [] sigma) term and executing it. *)
    (CClosure
      (Lam (Match_ (Var 0) (Var 1) (Match_ (Var 2) (Var 1) Conflict)))
      (sigma))::
    (CAppR (Value VNone))::
    (CFold 
      process_exceptions
      (List.map trans ts))::
    (CMatch
      (If (trans tj) (trans tc) ENone)
      (ESome (Var 0))) ::
      trans_conts kappa sigma
  | CDefault b (Some v) ts tj tc :: kappa =>
    (* This term can be derived from the trans fonction by taking the (mode_eval (trans (Default (Value (VPure v)::t::ts) tj tc)) [] []) term and executing it. *)
    (CClosure
      (Lam (Match_ (Var 0) (Var 1) (Match_ (Var 2) (Var 1) Conflict)))
      (sigma))::
    (CAppR (Value (VSome (trans_value v))))::
    (CFold 
      process_exceptions
      (List.map trans ts))::
    (CMatch
      (If (trans tj) (trans tc) ENone)
      (ESome (Var 0))) ::
      trans_conts kappa sigma
  end.

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

Theorem correction_continuations:
  forall s1 s2,
  cred s1 s2 ->
  exists target,
    star cred
      (trans_state s1) target /\
    star cred
      (trans_state s2) target.
Proof.

  Local Ltac step := ( idtac
    (* This tatic try to advance the computation on the right or on the left of the diagram. *)
    ; try (eapply step_left; [solve [ econstructor; simpl; eauto using List.map_nth_error, trans_value_op_correct]|])
    ; try (eapply step_right; [solve [ econstructor; simpl; eauto using List.map_nth_error, trans_value_op_correct]|])
  ).

  intros s1 s2 Hsred.
  induction Hsred;
    try induction phi;
    try induction o;
    intros; unpack; tryfalse.

  all:
    try solve [
      repeat step;
      try eapply diagram_finish;
      eauto
    ].
Qed.

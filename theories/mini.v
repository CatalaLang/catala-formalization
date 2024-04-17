Require Import String.
Require Import Coq.ZArith.ZArith.
Require Import tactics.
Import List.ListNotations.
Require Import common.
Require Import sequences.



Require Import Coq.Classes.SetoidClass.
Require Import Wellfounded.


(*** Definitions of terms and continuations for mini-ml ***)

Inductive op :=
  | Add
  | Eq
.


Inductive term :=
  (* Lambda calculus part of the language*)
  | Var (x: nat)
  | App (t1 t2: term)
  | Lam (t: term) (* binds *)
  | Value (v: value)

  | Binop (op: op) (t1 t2: term)
  | If (t ta tb: term)

with value :=
  | Closure (t: term) (* binds *) (sigma: list value)
  | Bool (b: bool)
  | Int (i: Z)
  (* | VPair (a b: value) *)
.

(* concrete interpretation of operators *)

Definition get_op op i1 i2 :=
  match op, i1, i2 with
  | Add, Int i1, Int i2 => Some (Int (Z.add i1 i2))
  | Eq, Int i1, Int i2 => Some (Bool (Z.eqb i1 i2))
  | _, _, _ => None
  end.


Inductive cont :=
  | CAppR (t2: term) (* [\square t2] *)
  | CClosure (t_cl: term (* binds *)) (sigma_cl: list value)
  (* [Clo(x, t_cl, sigma_cl) \square] Since we are using De Bruijn indices,
     there is no variable x. *)
  | CReturn (sigma: list value) (* call return *)
  | CBinopL (op: op) (v1: value) (* [op t1 \square] *)
  | CBinopR (op: op) (t2: term) (* [op \square t2] *)

  | CIf (ta: term) (tb: term)
.

Inductive result :=
  | RValue (v: value)
.


Inductive state :=
  | mode_eval (e: term) (kappa: list cont) (env: list value)
  | mode_cont (kappa: list cont) (env: list value) (result: result)
.


(*** continuation step semantics ***)

Inductive cred: state -> state -> Prop :=

  (** Rules related to the lambda calculus *)
  | cred_var:
    forall x kappa sigma v,
    List.nth_error sigma x = Some v ->
    cred
      (mode_eval (Var x) kappa sigma)
      (mode_cont kappa sigma (RValue v))

  | cred_app:
    forall t1 t2 kappa sigma,
    cred
      (mode_eval (App t1 t2) kappa sigma)
      (mode_eval t1 ((CAppR t2) :: kappa) sigma)

  | cred_clo:
    forall t kappa sigma,
    cred
      (mode_eval (Lam t) kappa sigma)
      (mode_cont kappa sigma (RValue (Closure t sigma)))

  | cred_arg:
    forall t2 kappa sigma tcl sigmacl,
    cred
      (mode_cont ((CAppR t2)::kappa) sigma (RValue (Closure tcl sigmacl)))
      (mode_eval t2 ((CClosure tcl sigmacl)::kappa) sigma)
  
  | cred_value:
    forall v kappa sigma,
    cred
      (mode_eval (Value v) kappa sigma)
      (mode_cont kappa sigma (RValue v))
      

  | cred_beta:
    forall t_cl sigma_cl kappa sigma v,
    cred
      (mode_cont ((CClosure t_cl sigma_cl)::kappa) sigma (RValue v))
      (mode_eval t_cl (CReturn sigma::kappa)  (v :: sigma_cl))

  | cred_return:
    forall sigma_cl kappa sigma r,
    cred
      (mode_cont (CReturn sigma::kappa) sigma_cl r)
      (mode_cont kappa sigma r)

  | cred_if:
    forall u t1 t2 kappa sigma,
    cred
      (mode_eval (If u t1 t2) kappa sigma)
      (mode_eval u ((CIf t1 t2)::kappa) sigma)
  | cred_if_true:
    forall t1 t2 kappa sigma,
    cred
      (mode_cont ((CIf t1 t2)::kappa) sigma (RValue (Bool true)))
      (mode_eval t1 kappa sigma)
  | cred_if_false:
    forall t1 t2 kappa sigma,
    cred
      (mode_cont ((CIf t1 t2) :: kappa) sigma (RValue (Bool false)))
      (mode_eval t2 kappa sigma)

  | cred_value_intro:
    forall v kappa sigma,
    cred
      (mode_eval (Value v) kappa sigma)
      (mode_cont kappa sigma (RValue v))

  | cred_op_intro:
    forall op e1 e2 kappa sigma,
    cred
      (mode_eval (Binop op e1 e2) kappa sigma)
      (mode_eval e1 (CBinopR op e2::kappa) sigma)

  | cred_op_mid:
    forall op e2 kappa sigma v,
    cred
      (mode_cont (CBinopR op e2 :: kappa) sigma (RValue v))
      (mode_eval e2 (CBinopL op v :: kappa) sigma)

  | cred_op_final:
    forall op v v1 v2 kappa sigma,
    Some v = get_op op v1 v2 ->
    cred
      (mode_cont (CBinopL op v1 :: kappa) sigma (RValue v2))
      (mode_cont kappa sigma (RValue v))
.

(* [AD: Add typing rules], but check where it is used. It was in boolean  conditions. Soundness and completeness was proved using all inputs that satisfy path constrains, it is a valid execution for the concrete semantics. We need to have some typing constrains here to check the path constraints are well-formed. 

It might be better to directly separate what the well-formeness and pathc onstraints, and the correctness of the typing.

*)




(******************************************************************************)
(* Continuation-Based Symbolic Semantics                                      *)
(******************************************************************************)

(** Possible to include here the path constraints (?) *)
Inductive sstate : Type :=.

Inductive scred: sstate -> sstate -> Prop :=.

Inductive srefine: state -> sstate -> Prop :=.


Theorem scred_sound:
  forall ss1 ss2,
    scred ss1 ss2 ->
      forall s1,
        srefine s1 ss1 ->
        exists s2, srefine s2 ss2 /\ cred s1 s2.
Abort.


(** This theorem might not be true under resonable conditions. *)
Theorem scred_complete:
  forall s1 s2,
    cred s1 s2 ->
      forall ss1,
        srefine s1 ss1 ->
        exists ss2, srefine s2 ss2 /\ scred ss1 ss2.
Abort.

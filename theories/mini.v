Require Import String.
Require Import Coq.ZArith.ZArith.
Require Import tactics.
Import List.ListNotations.
Require Import common.
Require Import sequences.



Require Import Coq.Classes.SetoidClass.
Require Import Wellfounded.


(*** Definitions of terms and continuations for mini-ml ***)


Inductive term :=
  (* Lambda calculus part of the language*)
  | Var (x: nat)
  | App (t1 t2: term)
  | Lam (t: term) (* binds *)
  | Value (v: value)

with value :=
  | Closure (t: term) (* binds *) (sigma: list value)
.


Inductive cont :=
  | CAppR (t2: term) (* [\square t2] *)
  | CClosure (t_cl: term (* binds *)) (sigma_cl: list value)
  (* [Clo(x, t_cl, sigma_cl) \square] Since we are using De Bruijn indices,
     there is no variable x. *)
  | CReturn (sigma: list value) (* call return *)
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
.

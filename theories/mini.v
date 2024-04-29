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

Inductive svalue :=
  | SClosure (t: term) (* binds *) (sigma: list svalue)
  | SBinop (op: op) (v1 v2: svalue)
  | SBool (b: bool)
  | SInt (i: Z)
  | SVar (x: nat)
.

Fixpoint reduce {A} (l : list (option A)) : option (list A) :=
  match l with
  | nil => Some nil
  | cons None l => None
  | cons (Some x) l =>
    match reduce l with
    | Some l => Some (cons x l)
    | None => None
    end
  end.

Fixpoint seval (ctx: list value) (v : svalue) { struct v } : option value :=
  match v with
  | SVar x => List.nth_error ctx x
  | SBool b => Some (Bool b)
  | SInt i => Some (Int i)
  | SBinop op v1 v2 =>
    match seval ctx v1, seval ctx v2 with
    | Some x1, Some x2 => get_op op x1 x2
    | _, _ => None
    end
  | SClosure term sigma =>
    match reduce (List.map (seval ctx) sigma) with
    | Some l => Some (Closure term l)
    | None => None
    end
  end.

Fixpoint symbolize (v : value) : svalue :=
  match v with
  | Closure term sigma => SClosure term (List.map symbolize sigma)
  | Bool b => SBool b
  | Int i => SInt i
  end.

Fixpoint value_ind'
  (P : value -> Prop)
  (IHbool : forall b, P (Bool b))
  (IHint  : forall i, P (Int i))
  (IHclo  : forall (t : term) (sigma : list value), List.Forall P sigma -> P (Closure t sigma))
  (v : value) : P v :=
    match v as v0 return (P v0) with
    | Bool b => IHbool b
    | Int i => IHint i
    | Closure t sigma => 
      let helper := fix F l :=
        match l as l' return List.Forall P l' with
        | nil => List.Forall_nil P
        | cons x xs =>
          @List.Forall_cons _ P x xs (value_ind' P IHbool IHint IHclo x) (F xs)
        end
      in
      IHclo t sigma (helper sigma)
    end.

Lemma reduce_map_Some {A}:
  forall (l : list A), reduce (List.map Some l) = Some l.
Proof.
  induction l as [ | x xs IH ]; simpl; auto.
  now rewrite IH.
Qed.

Lemma seval_symbolize:
  forall ctx v, seval ctx (symbolize v) = Some v.
Proof.
  induction v as [ | | t sigma IH ] using value_ind' ; simpl; auto.
  assert (Haux : List.map (seval ctx) (List.map symbolize sigma) = List.map Some sigma). {
    induction IH as [ | x sigma Hhead Htail IH ]; simpl; try easy.
    now rewrite Hhead, IH.
  }
  now rewrite Haux, reduce_map_Some.
Qed.

(** Symbolic continuations *)
Inductive scont :=
  | SCAppR (t2: term) (* [\square t2] *)
  | SCClosure (t_cl: term (* binds *)) (sigma_cl: list svalue)
  (* [Clo(x, t_cl, sigma_cl) \square] Since we are using De Bruijn indices,
     there is no variable x. *)
  | SCReturn (sigma: list svalue) (* call return *)
  | SCBinopL (op: op) (v1: svalue) (* [op t1 \square] *)
  | SCBinopR (op: op) (t2: term) (* [op \square t2] *)

  | SCIf (ta: term) (tb: term)
.

Inductive sresult :=
  | SRValue (v: svalue)
.

Definition constraint := list value -> Prop.

(** interprets a symbolic value as a constraint *)
Definition as_constraint (s : svalue) : option constraint :=
  match s with
  | SBool true => Some (fun _ => True)
  | SBool false => Some (fun _ => False)
  | SBinop Eq v1 v2 => Some (fun env => exists v, seval env v1 = Some v /\ seval env v2 = Some v)
  | _ => None
  end.

Definition cand (c1 c2 : constraint) : constraint :=
  fun env => c1 env /\ c2 env.

Definition cnot (c : constraint) : constraint :=
  fun env => ~c env.

(* Probably need to change that to account for typing ? *)
Definition get_sym_op op v1 v2 :=
  Some (SBinop op v1 v2).

(** Possible to include here the path constraints (?) *)
Inductive sstate : Type :=
  | mode_seval (phi : constraint) (e: term) (kappa: list scont) (env: list svalue)
  | mode_scont (phi : constraint) (kappa: list scont) (env: list svalue) (result: sresult).

Inductive scred: sstate -> sstate -> Prop :=

  (** Rules related to the lambda calculus
      Remark:
        scred_var, scred_app, scred_clo, scred_arg, scred_beta, etc
        are exactly the same as in the concrete semantic!
        This is because these rules are purely about control!
        There is certainly interesting comments to make here,
        and we could probably factor a lot by having a semantic
        more "modular" base semantics that separates control and data.
        As expected, the only rules that has to change is the rules that don't
        talk about control but talk about data (e.g., scred_value).
        For theses rules, data are made symbolic to represent sets
        of concrete values isntead of a single one.
  *)
  | scred_var:
    forall x phi kappa sigma v,
    List.nth_error sigma x = Some v ->
    scred
      (mode_seval phi (Var x) kappa sigma)
      (mode_scont phi kappa sigma (SRValue v))

  | scred_app:
    forall t1 t2 phi kappa sigma,
    scred
      (mode_seval phi (App t1 t2) kappa sigma)
      (mode_seval phi t1 ((SCAppR t2) :: kappa) sigma)

  | scred_clo:
    forall t phi kappa sigma,
    scred
      (mode_seval phi (Lam t) kappa sigma)
      (mode_scont phi kappa sigma (SRValue (SClosure t sigma)))

  | scred_arg:
    forall t2 phi kappa sigma tcl sigmacl,
    scred
      (mode_scont phi ((SCAppR t2)::kappa) sigma (SRValue (SClosure tcl sigmacl)))
      (mode_seval phi t2 ((SCClosure tcl sigmacl)::kappa) sigma)

  (* This rule change! we need to symbolize values (this rule is about data, not control !!!!) *)
  | scred_value:
    forall v phi kappa sigma,
    scred
      (mode_seval phi (Value v) kappa sigma)
      (mode_scont phi kappa sigma (SRValue (symbolize v)))

  | scred_beta:
    forall t_cl sigma_cl phi kappa sigma v,
    scred
      (mode_scont phi ((SCClosure t_cl sigma_cl)::kappa) sigma (SRValue v))
      (mode_seval phi t_cl (SCReturn sigma::kappa) (v :: sigma_cl))

  | scred_return:
    forall sigma_cl phi kappa sigma r,
    scred
      (mode_scont phi (SCReturn sigma::kappa) sigma_cl r)
      (mode_scont phi kappa sigma r)

  | scred_if:
    forall u t1 t2 phi kappa sigma,
    scred
      (mode_seval phi (If u t1 t2) kappa sigma)
      (mode_seval phi u ((SCIf t1 t2)::kappa) sigma)

  (** Rules for choices, these are also changing because they are mixing control and data!
      More precisely, "if" is THE construction that makes the connection between data and control.
  *)

  | scred_if_true:
    forall t1 t2 phi kappa sigma v c,
    as_constraint v = Some c ->
    scred
      (mode_scont phi ((SCIf t1 t2)::kappa) sigma (SRValue v))
      (mode_seval (cand phi c) t1 kappa sigma)
  
  | scred_if_false:
    forall t1 t2 phi kappa sigma v c,
    as_constraint v = Some c ->
    scred
      (mode_scont phi ((SCIf t1 t2) :: kappa) sigma (SRValue v))
      (mode_seval (cand phi (cnot c)) t2 kappa sigma)

  | scred_value_intro:
    forall v phi kappa sigma,
    scred
      (mode_seval phi (Value v) kappa sigma)
      (mode_scont phi kappa sigma (SRValue (symbolize v)))

  | scred_op_intro:
    forall op e1 e2 phi kappa sigma,
    scred
      (mode_seval phi (Binop op e1 e2) kappa sigma)
      (mode_seval phi e1 (SCBinopR op e2::kappa) sigma)

  | scred_op_mid:
    forall op e2 phi kappa sigma v,
    scred
      (mode_scont phi (SCBinopR op e2 :: kappa) sigma (SRValue v))
      (mode_seval phi e2 (SCBinopL op v :: kappa) sigma)

  | scred_op_final:
    forall op v v1 v2 phi kappa sigma,
    Some v = get_sym_op op v1 v2 ->
    scred
      (mode_scont phi (SCBinopL op v1 :: kappa) sigma (SRValue v2))
      (mode_scont phi kappa sigma (SRValue v)).

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

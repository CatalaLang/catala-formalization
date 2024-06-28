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

Lemma trans_ty_correct_term:
  forall {t Delta Gamma T},
    jt_term Delta Gamma t T ->
    jt_term Delta (List.map trans_ty Gamma) (trans t) (trans_ty T)
.
Proof.
  intros.
  apply (
    jt_term_ind'
      (fun Delta Gamma t T => jt_term Delta (List.map trans_ty Gamma) (trans t) (trans_ty T))
      (fun Delta t T => jt_value Delta (trans_value t) (trans_ty T))).

  (* TODO: remove the timeout to put something else. *)
  all: try solve [timeout 3 (intros; simpl; repeat econs_jt; simpl in *; eauto; repeat econs_inv; eauto using trans_ty_inv_base, trans_ty_inv_no_immediate_default)].
  { intros; simpl; econstructor.
    { erewrite List.map_nth_error; eauto. }
    { eapply trans_ty_inv_base. }
  }
  { intros; simpl; repeat econs_jt; simpl in *; eauto using trans_ty_inv_base, trans_ty_inv_no_immediate_default.
    12:{ clear -f2'. induction f2'; simpl; econstructor; eauto. }

    all: try solve [repeat econs_inv; eauto using trans_ty_inv_base, trans_ty_inv_no_immediate_default].
  }
  { intros; simpl; repeat econs_jt; simpl in *; eauto using trans_ty_inv_base, trans_ty_inv_no_immediate_default. 
    { induction op; simpl in *; inj; eauto. }
  }
  { intros; simpl; repeat econs_jt; simpl in *; eauto using trans_ty_inv_base, trans_ty_inv_no_immediate_default.
    { clear -f8'; induction f8'; simpl; econstructor; eauto. }
  }
  { intros; simpl. eapply (JTValueClosure _ _ _ (List.map trans_ty Gamma_cl)); repeat econs_jt; simpl in *; repeat econs_inv; eauto using trans_ty_inv_base, trans_ty_inv_no_immediate_default.
    { clear - f17'; induction f17'; econstructor; simpl; eauto. }
    {  repeat sinv_jt; eauto. }
  }
  { intros; simpl; repeat econs_jt; simpl in *; eauto using trans_ty_inv_base, trans_ty_inv_no_immediate_default.
    { clear -f22'; induction f22'; simpl; econstructor; eauto. }
  }
Qed.

Lemma trans_ty_correct_value:
  forall {v Delta T},
    jt_value Delta v T ->
    jt_value Delta (trans_value v) (trans_ty T).
Proof.
  intros.
  apply (
    jt_value_ind'
      (fun Delta Gamma t T => jt_term Delta (List.map trans_ty Gamma) (trans t) (trans_ty T))
      (fun Delta t T => jt_value Delta (trans_value t) (trans_ty T))).

  (* TODO: remove the timeout to put something else. *)
  all: try solve [timeout 3 (intros; simpl; repeat econs_jt; simpl in *; eauto; repeat econs_inv; eauto using trans_ty_inv_base, trans_ty_inv_no_immediate_default)].
  { intros; simpl; econstructor.
    { erewrite List.map_nth_error; eauto. }
    { eapply trans_ty_inv_base. }
  }
  { intros; simpl; repeat econs_jt; simpl in *; eauto using trans_ty_inv_base, trans_ty_inv_no_immediate_default.
    12:{ clear -f2'. induction f2'; simpl; econstructor; eauto. }

    all: try solve [repeat econs_inv; eauto using trans_ty_inv_base, trans_ty_inv_no_immediate_default].
  }
  { intros; simpl; repeat econs_jt; simpl in *; eauto using trans_ty_inv_base, trans_ty_inv_no_immediate_default. 
    { induction op; simpl in *; inj; eauto. }
  }
  { intros; simpl; repeat econs_jt; simpl in *; eauto using trans_ty_inv_base, trans_ty_inv_no_immediate_default.
    { clear -f8'; induction f8'; simpl; econstructor; eauto. }
  }
  { intros; simpl. eapply (JTValueClosure _ _ _ (List.map trans_ty Gamma_cl)); repeat econs_jt; simpl in *; repeat econs_inv; eauto using trans_ty_inv_base, trans_ty_inv_no_immediate_default.
    { clear - f17'; induction f17'; econstructor; simpl; eauto. }
    {  repeat sinv_jt; eauto. }
  }
  { intros; simpl; repeat econs_jt; simpl in *; eauto using trans_ty_inv_base, trans_ty_inv_no_immediate_default.
    { clear -f22'; induction f22'; simpl; econstructor; eauto. }
  }
Qed.

Lemma trans_value_op_correct:
  forall v op v1 v2,
    Some v = get_op op v1 v2 ->
    Some (trans_value v) = get_op op (trans_value v1) (trans_value v2).
Proof.
  induction op, v1 , v2; intros; simpl in *; inj; simpl; eauto.
Qed.

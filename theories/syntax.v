Require Export Autosubst.Autosubst.
Require Import String.
Require Import Coq.ZArith.ZArith.

Require Import tactics.

Inductive op :=
    | Add
    | Eq
.

Inductive term :=
    | Var (x: var)
    | FreeVar (x: string) (* external variables *)
    | App (t1 t2: term)
    | Lam (t: {bind term})
    | Default (ts: list term) (tj tc: term)
    | Empty
    | Conflict

    | Value (v: value)
    | Binop (op: op) (t1 t2: term)

    | Match_ (u t1: term) (t2: {bind term})
    | ENone
    | ESome (t: term)

with value :=
    | Bool (b: bool)
    | Int (i: Z)
    | Closure (t: {bind term}) (sigma: list value)
    | VNone
    | VSome (v: value)
.

#[export] Instance Ids_term : Ids term. derive. Defined.
#[export] Instance Rename_term : Rename term. derive. Defined.
#[export] Instance Subst_term : Subst term. derive. Defined.
#[export] Instance SubstLemmas_term : SubstLemmas term. derive. Qed.

Lemma ids_inj:
    forall x y, ids x = ids y -> x = y.
intros; inj; eauto.
Qed.




Definition get_op op i1 i2:=
    match op, i1, i2 with
    | Add, Int i1, Int i2 => Some (Int (Z.add i1 i2))
    | Eq, Int i1, Int i2 => Some (Bool (Z.eqb i1 i2))
    | _, _, _ => None
    end
.

Definition value_eqb (v1 v2 : value) : bool :=
    match v1, v2 with
    | Bool b1, Bool b2 => Bool.eqb b1 b2
    | Int i1, Int i2 => Z.eqb i1 i2
    | _, _ => false
    end.
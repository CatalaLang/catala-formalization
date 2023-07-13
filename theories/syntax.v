Require Export Autosubst.Autosubst.
Require Import String.
Require Import Coq.ZArith.ZArith.

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
        (* induction principle is not strong enought on the default. But this is known. *)
    | Empty
    | Conflict

    | Value (v: value)
    | Binop (op: op) (t1 t2: term)

with value :=
    | Bool (b: bool)
    | Int (i: Z.t)
    | Closure (t: term) (sigma: var -> value)
.

Definition value_eqb (v1 v2 : value) : bool :=
    match v1, v2 with
    | Bool b1, Bool b2 => Bool.eqb b1 b2
    | Int i1, Int i2 => Z.eqb i1 i2
    | _, _ => false
    end.
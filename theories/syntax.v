Require Export Autosubst.Autosubst.
Require Import String.
Require Import Coq.ZArith.ZArith.



Inductive value :=
    | Bool (b: bool)
    | Int (i: Z.t)
.

Inductive op :=
    | Add
    | Eq
.

Inductive term :=
    | Var (x: var)
    | FreeVar (x: string)
    | App (t1 t2: term)
    | Lam (t: {bind term})
    | Default (ts: list term) (tj tc: term)
    | Empty
    | Conflict

    | Value (v: value)
    | Binop (op: op) (t1 t2: term)
    .



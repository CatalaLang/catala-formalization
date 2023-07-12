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

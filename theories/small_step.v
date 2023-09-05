Require Import syntax.

Definition is_value v :=
    match v with
    | Value _ => True
    | Empty => True
    | Conflict => True
    | _ => False
    end.

Inductive sred: term -> term -> Prop :=
  | sred_beta:
    forall t u v,
      t.[Value v/] = u ->
      sred (App (Lam t) (Value v)) u
  | sred_app_left:
    forall t1 t2 u,
      sred t1 t2 ->
      sred (App t1 u) (App t2 u)
  | sred_app_right:
    forall t sigma u1 u2,
      sred u1 u2 ->
      sred (App (Value (Closure t sigma)) u1) (App (Value (Closure t sigma)) u2)

  | sred_default_conflict:
    forall ts ts1 ti ts2 tj ts3 tjust tcons,
    List.Forall is_value ts ->
    ti <> Empty ->
    tj <> Empty ->
    ts = (ts1 ++ ti::ts2++tj::ts3)%list ->
    sred (Default ts tjust tcons) Conflict
  | sred_DefaultEValue:
    forall ts1 ti ts2 tjust tcons,
    List.Forall (eq Empty) ts1 ->
    List.Forall (eq Empty) ts2 ->
    ti <> Empty ->
    is_value ti ->
    sred (Default (ts1++ti::ts2) tjust tcons) ti
 | sred_DefaultE:
    forall ts1 ti ti' ts2 tj tc,
    sred ti ti' ->
    (List.Forall is_value ts1) ->
    sred (Default (ts1++ti::ts2) tj tc) (Default (ts1++ti'::ts2) tj tc)
  | sred_DefaultJ:
    forall ts tj1 tj2 tc,
    List.Forall (eq Empty) ts ->
    sred tj1 tj2 ->
    sred (Default ts tj1 tc) (Default ts tj2 tc)
  | sred_DefaultJTrue:
    forall ts tc,
    List.Forall (eq Empty) ts ->
    sred (Default ts (Value (Bool true)) tc) tc
  | sred_DefaultJFalse:
    forall ts tc,
    List.Forall (eq Empty) ts ->
    sred (Default ts (Value (Bool false)) tc) Empty
  | sred_DefaultJEmpty:
    forall ts tc,
    List.Forall (eq Empty) ts ->
    sred (Default ts Empty tc) Empty
  | sred_DefaultJConflict:
    forall ts tc,
    List.Forall (eq Empty) ts ->
    sred (Default ts Conflict tc) Empty
.


Definition subst_of_env sigma :=
  fun n =>
  match List.nth_error sigma n with
  | None => ids n
  | Some t => Value t
  end
.
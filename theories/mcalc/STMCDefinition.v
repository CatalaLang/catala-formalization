Require Import MyTactics.
Require Import MCSyntax.

Require Import LibTactics.
(*|

-----
Types
-----

Here is the syntax of simple types:

|*)

Inductive ty :=
| TyVar (x : var)
| TyBool
| TyFun (A B : ty)
| TyOption (A: ty)
| TyUnit
.

(*|

A type environment is viewed as a total function of variables to types.

In principle, an environment should be modeled as a list of types, which
represents a partial function of variables to types. This introduces a few
complications, and is left as an exercise for the reader.

|*)

Definition tyenv := var -> ty.

(*|

--------------------
The typing judgement
--------------------

The simply-typed lambda-calculus is defined by the following three
typing rules.

|*)

Inductive jt_binop: operator -> ty -> ty -> ty -> Prop :=
  | TOAdd: jt_binop OAdd TyBool TyBool TyBool
.


Inductive jt : tyenv -> term -> ty -> Prop :=
| JTVar:
    forall Gamma x T,
    Gamma x = T ->
    jt Gamma (Var x) T
| JTLam:
    forall Gamma t T U,
    jt (T .: Gamma) t U ->
    jt Gamma (Lam t) (TyFun T U)
| JTApp:
    forall Gamma t1 t2 T U,
    jt Gamma t1 (TyFun T U) ->
    jt Gamma t2 T ->
    jt Gamma (App t1 t2) U
| JTConst:
  forall Gamma b,
  jt Gamma (Const b) TyBool
| JTBinOp:
  forall Gamma op t1 t2 T1 T2 U,
  jt_binop op T1 T2 U ->
  jt Gamma t1 T1 ->
  jt Gamma t2 T2 ->
  jt Gamma (BinOp op t1 t2) U

| JTMReturn:
  forall Gamma t T,
  jt Gamma t T ->
  jt Gamma (MReturn t) (TyOption T)
| JTMEmpty:
  forall Gamma T,
  jt Gamma (MEmpty) (TyOption T)
| JTMBind:
  forall Gamma arg t T1 T2,
  jt Gamma arg (TyOption T1) ->
  jt (T1 .: Gamma) t (TyOption T2) ->
  jt Gamma (MBind arg t) (TyOption T2)
| JTMErrorOnEmpty:
  forall Gamma t T,
  jt Gamma t (TyOption T) ->
  jt Gamma (MErrorOnEmpty t) T
| JTMHandle:
  forall Gamma ts tj tc T,
  List.Forall (fun ti => jt Gamma ti (TyOption T)) ts ->
  jt Gamma tj (TyFun TyUnit (TyOption TyBool)) ->
  jt Gamma tc (TyFun TyUnit (TyOption T)) ->
  jt Gamma (MHandle ts tj tc) (TyOption T)
| JTMRaise:
  forall Gamma exp T,
  jt Gamma (MRaise exp) T
.

Lemma jt_ind'
: forall P : tyenv -> term -> ty -> Prop,
    (forall (Gamma : var -> ty) (x : var) (T : ty),
     Gamma x = T -> P Gamma (Var x) T) ->
    (forall (Gamma : var -> ty) (t : term) (T U : ty),
     jt (T .: Gamma) t U ->
     P (T .: Gamma) t U -> P Gamma (Lam t) (TyFun T U)) ->
    (forall (Gamma : tyenv) (t1 t2 : term) (T U : ty),
     jt Gamma t1 (TyFun T U) ->
     P Gamma t1 (TyFun T U) ->
     jt Gamma t2 T -> P Gamma t2 T -> P Gamma (App t1 t2) U) ->
    (forall (Gamma : tyenv) (b : bool), P Gamma (Const b) TyBool) ->
    (forall (Gamma : tyenv) (op : operator) (t1 t2 : term) (T1 T2 U : ty),
     jt_binop op T1 T2 U ->
     jt Gamma t1 T1 ->
     P Gamma t1 T1 ->
     jt Gamma t2 T2 -> P Gamma t2 T2 -> P Gamma (BinOp op t1 t2) U) ->
    (forall (Gamma : tyenv) (t : term) (T : ty),
     jt Gamma t T -> P Gamma t T -> P Gamma (MReturn t) (TyOption T)) ->
    (forall (Gamma : tyenv) (T : ty), P Gamma MEmpty (TyOption T)) ->
    (forall (Gamma : tyenv) (arg t : term) (T1 T2 : ty),
     jt Gamma arg (TyOption T1) ->
     P Gamma arg (TyOption T1) ->
     jt (T1 .: Gamma) t (TyOption T2) ->
     P (T1 .: Gamma) t (TyOption T2) ->
     P Gamma (MBind arg t) (TyOption T2)) ->
    (forall (Gamma : tyenv) (t : term) (T : ty),
     jt Gamma t (TyOption T) ->
     P Gamma t (TyOption T) -> P Gamma (MErrorOnEmpty t) T) ->
    (forall (Gamma : tyenv) (ts : list term) (tj tc : term) (T : ty),
     List.Forall (fun ti : term => jt Gamma ti (TyOption T)) ts ->
     List.Forall (fun ti : term => P Gamma ti (TyOption T)) ts ->
     jt Gamma tj (TyFun TyUnit (TyOption TyBool)) ->
     P Gamma tj (TyFun TyUnit (TyOption TyBool)) ->
     jt Gamma tc (TyFun TyUnit (TyOption T)) ->
     P Gamma tc (TyFun TyUnit (TyOption T)) ->
     P Gamma (MHandle ts tj tc) (TyOption T)) ->
    (forall (Gamma : tyenv) (exp : except) (T : ty),
     P Gamma (MRaise exp) T) ->
    forall (t : tyenv) (t0 : term) (t1 : ty), jt t t0 t1 -> P t t0 t1
.
Admitted.


(*|

The tactic [pick_jt t] picks a hypothesis [h] whose statement is a typing
judgement about the term [t], and passes [h] to the Ltac continuation [k].

Thus, for instance, [pick_jt t invert] selects a typing judgement that is
at hand for the term [t] and inverts it.

|*)

Ltac pick_jt t k :=
  match goal with h: jt _ t _ |- _ => k h end.

(*|

The following hint allows `eauto with jt` to apply the above typing rules.

|*)

Global Hint Constructors jt : jt.


Lemma jt_te_renaming:
  forall Gamma t U,
  jt Gamma t U ->
  forall Gamma' xi,
  Gamma = xi >>> Gamma' ->
  jt Gamma' t.[ren xi] U.
Proof.
  induction 1 using jt_ind'; intros; subst; asimpl;
  econstructor; eauto with autosubst.
  { admit. }
Admitted.


Lemma jt_te_renaming_0:
  forall Gamma t T U,
  jt Gamma t U ->
  jt (T .: Gamma) (lift 1 t) U.
Proof.
  intros. eapply jt_te_renaming. eauto. autosubst.
Qed.

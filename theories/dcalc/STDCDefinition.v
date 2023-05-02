Require Import MyTactics.
Require Import DCSyntax.
Require Import DCValues.

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
| TyFun (A B : ty).

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
| JTDefault:
    forall Gamma ts tj tc T,
    List.Forall (fun ti => jt Gamma ti T) ts ->
    jt Gamma tj TyBool ->
    jt Gamma tc T ->
    jt Gamma (Default ts tj tc) T
| JTConfict:
  forall Gamma T,
  jt Gamma Conflict T
| JTEmpty:
  forall Gamma T,
  jt Gamma Empty T
| JTConst:
  forall Gamma b,
  jt Gamma (Const b) TyBool
.


Theorem jt_ind'
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
    (forall (Gamma : tyenv) (ts : list term) (tj tc : term) (T : ty),
     List.Forall (fun ti : term => jt Gamma ti T) ts ->
     List.Forall (fun ti : term => P Gamma ti T) ts -> 
     jt Gamma tj TyBool ->
     P Gamma tj TyBool ->
     jt Gamma tc T -> P Gamma tc T -> P Gamma (Default ts tj tc) T) ->
    (forall (Gamma: tyenv) (T: ty), P Gamma Conflict T) ->
    (forall (Gamma: tyenv) (T: ty), P Gamma Empty T) ->
    (forall (Gamma: tyenv) (b: bool), P Gamma (Const b) TyBool) ->
    forall (Gamma : tyenv) (t : term) (T : ty), jt Gamma t T -> P Gamma t T.
Proof.
  introv HVar HLam HApp HDefault HConflict HEmpty HConst.
  fix IH 4.
  introv Hjt; case Hjt.
  * now eapply HVar.
  * intros; eapply HLam; try eassumption; now eapply IH.
  * intros; eapply HApp; try eassumption; now eapply IH.
  * intros; eapply HDefault; try solve [try eapply IH; eassumption].
    - (* we make an induction direclty on the Forall, else coq generate a wrongly typed term. *)
      induction H; econstructor.
      { now eapply IH. }
      { now eapply IHForall. }
  * apply HConflict.
  * apply HEmpty.
  * apply HConst.
Qed.

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

Require Import Coq.Wellfounded.Inverse_Image.
Require Import MyTactics.
Require Export Autosubst.Autosubst.
Require Export AutosubstExtra.
Require Export Autosubst_IsRen.

Require Import MyList.

Require Import Arith.
Require Import PeanoNat.

Require Import Arith.Wf_nat.
Require Export Autosubst_FreeVars.

Require Import MySequences.


Inductive operator :=
| OAdd.

Inductive except :=
| EConflict
| ENoValueProvided
| ECompile
.

Inductive term :=
(* lambda calculus *)
| Var (x : var)
| Lam (t : {bind term})
| App (t1 t2 : term)
| Const (b: bool)
| BinOp (op: operator) (t1 t2: term)


(* | Op: (op: operator)
| App (f: term) (args: list term) *)

(* monadic catala *)
| MReturn (t: term)
| MEmpty
| MBind (arg: term) (t: {bind term})
| MErrorOnEmpty (t: term)
| MHandle (ts: list term) (tj: term) (tc: term)
| MRaise (exp: except)
.

#[global] Instance Ids_term : Ids term. derive. Defined.  
#[global] Instance Rename_term : Rename term. derive. Defined.
#[global] Instance Subst_term : Subst term. derive. Defined.
#[global] Instance SubstLemmas_term : SubstLemmas term. derive. Qed.
#[global] Instance IdsLemmas_term : IdsLemmas term.
Proof.
  econstructor.
  intros.
  injections.
  eauto.
Qed.


Lemma lift_inj_Var:
  forall t x,
  lift 1 t = Var (S x) <-> t = Var x.
Proof.
  split; intros.
  { eauto using lift_inj. }
  { subst. eauto. }
Qed.

(* -------------------------------------------------------------------------- *)

(* The predicate [fv] is characterized by the following lemmas. *)

Lemma fv_Var_eq:
  forall k x,
  fv k (Var x) <-> x < k.
Proof.
  unfold fv. asimpl. induction k; intros.
  (* Base case. *)
  { asimpl. split; intros; false.
    { unfold ids, Ids_term in *. injections.
      eapply Nat.neq_succ_diag_l. eauto. }
    { lia. }
  }
  (* Step. *)
  { destruct x; asimpl.
    { split; intros. { lia. } { reflexivity. } }
    rewrite lift_inj_Var. rewrite IHk. lia. }
Qed.

Lemma fv_Lam_eq:
  forall k t,
  fv k (Lam t) <-> fv (S k) t.
Proof.
  unfold fv. intros. asimpl. split; intros.
  { injections. eauto. }
  { unpack. congruence. }
Qed.

Lemma fv_App_eq:
  forall k t1 t2,
  fv k (App t1 t2) <-> fv k t1 /\ fv k t2.
Proof.
  unfold fv. intros. asimpl. split; intros.
  { injections. eauto. }
  { unpack. congruence. }
Qed.

Lemma fv_BinOp_eq:
  forall k op t1 t2,
  fv k (BinOp op t1 t2) <-> fv k t1 /\ fv k t2.
Proof.
  unfold fv. intros. asimpl. split; intros.
  { injections. eauto. }
  { unpack. congruence. }
Qed.

Global Hint Rewrite fv_Var_eq fv_Lam_eq fv_App_eq fv_BinOp_eq : fv.


Lemma closed_Var:
  forall x,
  closed (Var x) ->
  False.
Proof.
  unfold closed; intros; fv. lia.
Qed.


Lemma closed_AppL:
  forall t1 t2,
  closed (App t1 t2) ->
  closed t1.
Proof.
  unfold closed; intros; fv. tauto.
Qed.

Lemma closed_AppR:
  forall t1 t2,
  closed (App t1 t2) ->
  closed t2.
Proof.
  unfold closed; intros; fv. tauto.
Qed.

Lemma closed_BinOpL:
  forall op t1 t2,
  closed (BinOp op t1 t2) ->
  closed t1.
Proof.
  unfold closed; intros; fv. tauto.
Qed.

Lemma closed_BinOpR:
  forall op t1 t2,
  closed (BinOp op t1 t2) ->
  closed t2.
Proof.
  unfold closed; intros; fv. tauto.
Qed.


Global Hint Resolve
  closed_Var
: closed.





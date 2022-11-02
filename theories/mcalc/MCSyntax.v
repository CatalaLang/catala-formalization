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


Inductive term :=
| Var (x : var)
| Lam (t : {bind term})
| App (t1 t2 : term)
| Const (b: bool)
.

#[global] Instance Ids_term : Ids term. derive. Defined.  
#[global] Instance Rename_term : Rename term. derive. Defined.
#[global] Instance Subst_term : Subst term. derive. Defined.
#[global] Instance SubstLemmas_term : SubstLemmas term. derive. Qed.
#[global] Instance IdsLemmas_term : IdsLemmas term. Proof. econstructor. intros. injections. eauto. Qed.

Inductive monad :=
| Fake (x: var)
| Pure (x: term)
| Empty
| Conflict
| Default (ts: list monad) (tj tc: monad)
| Bind (m: monad) (x: {bind term in monad})
.

#[global] Instance Ids_monad : Ids monad. derive. Defined.  
#[global] Instance Rename_monad : Rename monad. derive. Defined.
#[global] Instance Subst_monad : Subst monad. derive. Defined.
#[global] Instance HSubst_term : HSubst term monad. derive. Defined.
#[global] Instance SubstLemmas_monad : SubstLemmas monad. derive. Qed.
#[global] Instance IdsLemmas_monad : IdsLemmas monad. Proof. econstructor. intros. injections. eauto. Qed.
#[global] Instance HSubstLemmas_monad : HSubstLemmas term monad. derive. Qed.

Definition is_value v := match v with Const _ | Lam _ => True | _ => False end.

Inductive red: term -> term -> Prop :=
| RedBetaV : forall (t v u: term),
  is_value v ->
  t.[v/] = u ->
  red (App (Lam t) v) u
| RedAppL : forall t1 t2 u,
    red t1 t2 ->
    red (App t1 u) (App t2 u)
| RedAppVR:
    forall v u1 u2,
    is_value v ->
    red u1 u2 ->
    red (App v u1) (App v u2)
.

Global Hint Constructors red : red obvious.

Definition is_valuem v :=
  match v with
  Empty | Conflict => True
  | Pure v => is_value v
  | _ => False
  end.


Inductive redm : monad -> monad -> Prop :=
| RedmBind t1 t2 t1':
    redm t1 t1' -> redm (Bind t1 t2) (Bind t1' t2)
| RedmBindEmpty t2: redm (Bind Empty t2) Empty
| RedmBindConflict t2: redm (Bind Conflict t2) Conflict
| RedmBindPureV t1 t2: is_value t1 -> redm (Bind (Pure t1) t2) t2.|[t1/]
| RedmPure t1 t1': red t1 t1' -> redm (Pure t1) (Pure t1')
| RedmDefaultEConflict:
  forall ts ts1 ti ts2 tj ts3 tjust tcons,
  List.Forall is_valuem ts ->
  ti <> Empty ->
  tj <> Empty ->
  ts = (ts1 ++ ti::ts2++tj::ts3)%list ->
  redm (Default ts tjust tcons) Conflict
| RedmDefaultEValue:
  forall ts1 ti ts2 tjust tcons,
  List.Forall (eq Empty) ts1 ->
  List.Forall (eq Empty) ts2 ->
  ti <> Empty ->
  is_valuem ti ->
  redm (Default (ts1++ti::ts2) tjust tcons) ti
| RedmDefaultE:
  forall ts1 ti ti' ts2 tj tc,
  redm ti ti' ->
  (List.Forall is_valuem ts1) ->
  redm (Default (ts1++ti::ts2) tj tc) (Default (ts1++ti'::ts2) tj tc)
| RedmDefaultJ:
  forall ts tj1 tj2 tc,
  List.Forall (eq Empty) ts ->
  redm tj1 tj2 ->
  redm (Default ts tj1 tc) (Default ts tj2 tc)
| RedmDefaultJTrue:
  forall ts tc,
  List.Forall (eq Empty) ts ->
  redm (Default ts (Pure (Const true)) tc) tc
| RedmDefaultJFalse:
  forall ts tc,
  List.Forall (eq Empty) ts ->
  redm (Default ts (Pure (Const false)) tc) Empty
| RedmDefaultJEmpty:
  forall ts tc,
  List.Forall (eq Empty) ts ->
  redm (Default ts Empty tc) Empty
| RedmDefaultJConflict:
  forall ts tc,
  List.Forall (eq Empty) ts ->
  redm (Default ts Conflict tc) Empty
.

Global Hint Constructors redm : redm obvious.


Ltac invert_red :=
  pick red invert;
  try solve [ false; eauto 3 with obvious ].

Ltac invert_redm :=
  pick redm invert;
  try solve [ false; eauto 3 with obvious ].
  


Lemma is_value_irred:
  forall v, is_value v -> irred red v.
Proof.
  induction v; repeat intro; invert_red.
Qed.


Lemma is_valuem_irred:
forall v, is_valuem v -> irred redm v.
Proof.
  induction v; repeat intro; simpl in *; invert_redm.
  { eapply is_value_irred; eauto. }
Qed.

Lemma values_do_not_reduce:
  forall t1 t2,
  red t1 t2 ->
  ~ is_value t1.
Proof.
  inversion 1; obvious.
Qed.

Lemma valuesm_do_not_reduce:
  forall t1 t2,
  redm t1 t2 ->
  ~ is_valuem t1.
Proof.
  repeat intro. eapply is_valuem_irred; eauto.
Qed.


Global Hint Extern 1 (False) => (eapply values_do_not_reduce) : obvious.
Global Hint Extern 1 (False) => (eapply valuesm_do_not_reduce) : obvious.
Global Hint Extern 1 (is_value _) => (simpl; tauto) : obvious.
Global Hint Extern 1 (is_valuem _) => (simpl; tauto) : obvious.


Global Hint Resolve is_value_irred is_valuem_irred : obvious.


Lemma red_deterministic:
  forall t t1,
  red t t1 ->
  forall t2,
  red t t2 ->
  t1 = t2.
Proof.
  induction 1; try solve [
    intros; subst; invert_red; eauto; f_equal; try solve
    [ now eapply IHred  ]
  ].
Qed.

Ltac split_list :=
  (* this tactic search for a hypothesis in the form of _ ++ _ :: _ = _ ++ _ :: _  and applies to split_list lemma to it. *)
  match goal with [h: (_ ++ _ :: _ = _ ++ _ :: _)%list |- _] => destruct (split_list h) as [hl | [hl | hl]] end; unzip;
  repeat rewrite <- List.app_assoc, <- List.app_comm_cons in *
.

Ltac test1 :=
  match goal with [h1: redm ?ti _, h2: is_valuem ?ti |- _] => eapply (valuesm_do_not_reduce _ _ h1 h2) end.

Lemma redm_deterministic:
  forall t t1,
  redm t t1 ->
  forall t2,
  redm t t2 ->
  t1 = t2.
Proof.
  induction 1; try solve
  [ tauto
  | intros; subst; invert_redm; eauto; f_equal; try solve
    [ now eapply IHredm 
    | eapply red_deterministic; eauto 
    | try split_list;
      solve
      [ repeat f_equal; eapply IHredm; eauto
      | false; inverts_Forall; eauto with obvious]
    ]
  ].
  {
    intros; subst; invert_redm; eauto; try split_list; inverts_Forall; eauto with obvious; false; try test1.
    - split_list; inverts_Forall; try test1.
  }
Qed.



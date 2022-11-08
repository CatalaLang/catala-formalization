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

Global Hint Rewrite fv_Var_eq fv_Lam_eq fv_App_eq : fv.


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



Global Hint Resolve
  closed_Var
: closed.

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



Inductive ty :=
| TyVar (x : var)
| TyFun (A B : ty)
| TyBool.

Definition tyenv := var -> ty.

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
.

Global Hint Constructors jt : jt.

Ltac pick_jt t k :=
  match goal with h: jt _ t _ |- _ => k h end.

Lemma jt_te_renaming:
  forall Gamma t U,
  jt Gamma t U ->
  forall Gamma' xi,
  Gamma = xi >>> Gamma' ->
  jt Gamma' t.[ren xi] U.
Proof.
  induction 1; intros; subst; asimpl;
  econstructor; eauto with autosubst.
Qed.

Lemma jt_te_renaming_0:
  forall Gamma t T U,
  jt Gamma t U ->
  jt (T .: Gamma) (lift 1 t) U.
Proof.
  intros; eapply jt_te_renaming; eauto; autosubst.
Qed.

Definition js Gamma sigma Delta :=
  forall x : var,
  jt Gamma (sigma x) (Delta x).

Lemma js_ids:
  forall Gamma,
  js Gamma ids Gamma.
Proof.
  unfold js; eauto with jt.
Qed.

Lemma js_cons:
  forall Gamma t sigma T Delta,
  jt Gamma t T ->
  js Gamma sigma Delta ->
  js Gamma (t .: sigma) (T .: Delta).
Proof.
  intros. intros [|x]; asimpl; eauto.
Qed.

Lemma js_up:
  forall Gamma sigma Delta T,
  js Gamma sigma Delta ->
  js (T .: Gamma) (up sigma) (T .: Delta).
Proof.
  intros. eapply js_cons.
  { eauto with jt. }
  { intro x. asimpl. eauto using jt_te_renaming_0. }
Qed.

Require Import MyList.

Lemma jt_te_substitution:
  forall Delta t U,
  jt Delta t U ->
  forall Gamma sigma,
  js Gamma sigma Delta ->
  jt Gamma t.[sigma] U.
Proof.
  induction 1; intros; subst; asimpl; eauto using js_up with jt.
Qed.


Lemma jt_te_substitution_0:
  forall Gamma t1 t2 T U,
  jt (T .: Gamma) t1 U ->
  jt Gamma t2 T ->
  jt Gamma t1.[t2/] U.
Proof.
  eauto using jt_te_substitution, js_ids, js_cons.
Qed.

Lemma jt_preservation:
  forall Gamma t T,
  jt Gamma t T ->
  forall t',
  red t t' ->
  jt Gamma t' T.
Proof.
  induction 1; intros; subst; invert_red; try eauto with jt.
  { pick_jt (Lam t) invert. eauto using jt_te_substitution_0. }
Qed.

Lemma invert_jt_TyFun:
  forall Gamma t T1 T2,
  jt Gamma t (TyFun T1 T2) ->
  closed t ->
  is_value t ->
  (exists t', t = Lam t').
Proof.
  induction t; intros; inverts H; subst; try eauto; tryfalse.
Qed.

Lemma invert_jt_TyBool:
  forall Gamma t,
  jt Gamma t TyBool ->
  closed t ->
  is_value t ->
  (exists b, t = Const b).
Proof.
induction t; intros; inverts H; subst; try eauto; tryfalse.
Qed.


Lemma jt_progress:
  forall Gamma t T,
  jt Gamma t T ->
  closed t ->
  (exists t', red t t')
  \/ is_value t.
Proof.
  induction t;
  try solve [
    intros; subst; right; eauto with obvious
  ]; left.
  * false; eauto with closed.
  * pick_jt (App t1 t2) invert.
    match goal with h: jt _ t1 _ |- _ => destruct (IHt1 _ h) end.
    { eauto using closed_AppL. }
    { unzip. eexists. eapply RedAppL. all: eauto. }

    match goal with h: jt _ t2 _ |- _ => destruct (IHt2 _ h) end.
    { eauto using closed_AppR. }
    { unzip. eexists. eapply RedAppVR. all: eauto. }


    match goal with h: jt _ _ (TyFun _ _) |- _ => destruct (invert_jt_TyFun _ _ _ _ h) end.
    { eauto using closed_AppL. }
    { eauto with obvious. }
    { subst. eexists. eapply RedBetaV; eauto.  }
Qed.

(* notation idea: t $(jt _ _ _ ) for match goal with h: jt _ _ _ |- _ => t h end. *)



Inductive jtm : tyenv -> monad -> ty -> Prop :=
| JTMPure:
    forall Gamma t T,
    jt Gamma t T ->
    jtm Gamma (Pure t) T
| JTMEmpty:
    forall Gamma T,
    jtm Gamma Empty T
| JTMConflict:
  forall Gamma T,
  jtm Gamma Conflict T
| JTMBind:
  forall Gamma t cont T U,
  jtm (T .: Gamma) cont U ->
  jtm Gamma t T ->
  jtm Gamma (Bind t cont) U
| JTMDefault:
  forall Gamma ts tj tc T,
  List.Forall (fun ti => jtm Gamma ti T) ts ->
  jtm Gamma tj TyBool ->
  jtm Gamma tc T ->
  jtm Gamma (Default ts tj tc) T
.

Global Hint Constructors jtm : jtm.

Ltac pick_jtm t k :=
  match goal with h: jtm _ t _ |- _ => k h end.

Theorem  jtm_ind'
  : forall P : tyenv -> monad -> ty -> Prop,
      (forall (Gamma : tyenv) (t : term) (T : ty),
       jt Gamma t T -> P Gamma (Pure t) T) ->
      (forall (Gamma : tyenv) (T : ty), P Gamma Empty T) ->
      (forall (Gamma : tyenv) (T : ty), P Gamma Conflict T) ->
      (forall (Gamma : var -> ty) (t cont : monad) (T U : ty),
       jtm (T .: Gamma) cont U ->
       P (T .: Gamma) cont U ->
       jtm Gamma t T -> P Gamma t T -> P Gamma (Bind t cont) U) ->
      (forall (Gamma : tyenv) (ts : list monad) (tj tc : monad) (T : ty),
       List.Forall (fun ti : monad => jtm Gamma ti T) ts ->
       List.Forall (fun ti => P Gamma ti T)  ts ->
       jtm Gamma tj TyBool ->
       P Gamma tj TyBool ->
       jtm Gamma tc T -> P Gamma tc T -> P Gamma (Default ts tj tc) T) ->
      forall (t : tyenv) (m : monad) (t0 : ty), jtm t m t0 -> P t m t0.
Proof.
Admitted.



Lemma jtm_te_renaming:
  forall Gamma t U,
  jtm Gamma t U ->
  forall Gamma' xi,
  Gamma = xi >>> Gamma' ->
  jtm Gamma' t.|[ren xi] U.
Proof.
  induction 1 using jtm_ind'; intros; subst; asimpl;
  econstructor; eauto with autosubst.
  { eapply jt_te_renaming; eauto. }
  { match goal with h: List.Forall _ _ |- _ => induction h end; econstructor; inverts_Forall; eauto. }
Qed.


Require Import MyList.

Lemma jtm_te_substitution:
  forall Delta t U,
  jtm Delta t U ->
  forall Gamma sigma,
  js Gamma sigma Delta ->
  jtm Gamma t.|[sigma] U.
Proof.
  induction 1 using jtm_ind'; intros; subst; asimpl; eauto using js_up with jtm.
  { econstructor. eapply jt_te_substitution; eauto. }
  { econstructor; eauto.
    match goal with h: List.Forall _ _ |- _ => induction h end;
    econstructor; eauto; inverts_Forall; eauto. }
Qed.


Lemma jtm_te_substitution_0:
  forall Gamma t1 t2 T U,
  jtm (T .: Gamma) t1 U ->
  jt Gamma t2 T ->
  jtm Gamma t1.|[t2/] U.
Proof.
  eauto using jtm_te_substitution, js_ids, js_cons.
Qed.

Lemma Forall_app_inverts {A} {P: A -> Prop} {l1 l2}:
  List.Forall P l1 -> List.Forall P l2 -> List.Forall P (l1 ++ l2).
Proof.
  intros; eapply List.Forall_app; eauto.
Qed.

Lemma Forall_cons_inverts {A} {P: A -> Prop} {l1 l2}:
P l1 -> List.Forall P l2 -> List.Forall P (l1 :: l2)%list .
Proof.
  intros H; econstructor; eauto.
Qed.

Lemma jtm_preservation:
  forall Gamma t T,
  jtm Gamma t T ->
  forall t',
  redm t t' ->
  jtm Gamma t' T.
Proof.
  induction 1 using jtm_ind'; intros; subst; invert_redm; try eauto with jtm.
  { econstructor. eapply jt_preservation; eauto. }
  { pick_jtm (Pure t1) invert.
    eapply jtm_te_substitution_0; eauto. }
  { inverts_Forall. eauto. }
  { econstructor; eauto.
    inverts_Forall.
    repeat eapply Forall_app_inverts, Forall_cons_inverts; eauto.
  }
Qed.


(* in the next lemmas, the main issue is that closed in not the same for term and monad kinds. Indeed, fv is defined as "t.[upn k (ren (+1))] = t". But what we need for monad is t.|[upn k (ren (+1))]. *)

Definition hfv k t :=
  t.|[upn k (ren (+1))] = t.

Definition hclosed := hfv 0.


Lemma hfv_Pure_eq:
  forall k t,
  hfv k (Pure t) <-> fv k t.
Proof.
  intros.
  unfold hfv, fv; asimpl. split; intros.
  { injections; eauto. }
  { unpack; congruence. }
Qed.

Lemma hfv_Bind_eq:
  forall k t1 t2,
  hfv k (Bind t1 t2) <-> hfv k t1 /\ hfv (S k) t2.
Proof.
  unfold hfv. intros. asimpl. split; intros.
  { injections. eauto. }
  { unpack. congruence. }
Qed.

Lemma efe k ts:
ts..|[upn k (ren (+1))] = ts -> List.Forall (fun ti => ti.|[upn k (ren(+1))] = ti) ts.
Proof.
  induction ts.
  * asimpl.
    econstructor.
  * asimpl; intros.
    injections.
    econstructor; eauto.
Qed.

Lemma fef k ts:
List.Forall (fun ti => ti.|[upn k (ren(+1))] = ti) ts -> ts..|[upn k (ren (+1))] = ts .
Proof.
  induction ts.
  * asimpl.
    econstructor.
  * asimpl; intros.
    inverts_Forall.
    replace (a.|[upn k (ren (+1))]) with a.
    rewrite IHts; eauto.
Qed.

Lemma hfv_Default_eq:
  forall k ts tj tc,
  hfv k (Default ts tj tc) <->
    (List.Forall (fun ti => hfv k ti) ts) /\ hfv k tj /\ hfv k tc.
Proof.
  unfold hfv. intros. asimpl. split; intros.
  { injections. eauto.
    forwards Hts: (efe _ _ H1).
    induction Hts; repeat split; eauto.
  }
  { unpack.
    forwards Hts: (fef _ _ H).
    congruence.
  }
Qed.

Lemma invert_jtm_TyBool:
  forall Gamma t,
  jtm Gamma t TyBool ->
  hclosed t ->
  is_valuem t ->
  (exists b, t = Pure (Const b)) \/ (t = Empty \/ t = Conflict).
Proof.
  intros.
  induction t; simpl in *; tryfalse; eauto.
  - left.
    inverts H.
    edestruct invert_jt_TyBool; eauto.
    { unfold hclosed, closed in *. now eapply hfv_Pure_eq. }
    subst.
    eexists; eauto.
Qed.

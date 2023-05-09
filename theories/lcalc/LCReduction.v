Require Import MyTactics.
Require Import MySequences.
Require Import LCSyntax.
Require Import LCValues.
Require Import LCFreeVars.

(* We give a symbolic name to each reduction rule. *)

Inductive rule :=
| RuleBetaV     (* reduction of a beta-v redex: (\x.t) v                   *)
| RuleLetV      (* reduction of a let-v redex:  let x = v in t             *)
| RuleBeta      (* reduction of a beta   redex: (\x.t) u                   *)
| RuleParBetaV  (* reduction of a beta-v redex and reduction in both sides *)
| RuleEMatchNone (* reduction of a match when None                          *)
| RuleEMatchSome (* reduction of a match when Some                          *)
| RuleEMatchSomeV(* reduction of a match when Some when it is a value       *)
| RuleEVar       (* no reduction                                            *)
| RuleNone      (* no reduction                                            *)
| RuleSome      (* reduction in [EVariantSome _]                            *)
| RuleEMatchCond (* reduction in [EMatch _ t1 t2]                            *)
| RuleEMatchL    (* reduction in [EMatch tc _ t2]                            *)
| RuleEMatchR    (* reduction in [EMatch tc t1 _]                            *)
| RuleELam       (* reduction in [ELam _]                                    *)
| RuleEAppL      (* reduction in [EApp _ u]                                  *)
| RuleEAppR      (* reduction in [EApp u _]                                  *)
| RuleEAppVR     (* reduction in [EApp v _], if [v] is a value               *)
| RuleEAppLR     (* reduction in both sides of [EApp _ _]                    *)
.

(* A mask is a set of rules. *)

Definition mask :=
  rule -> Prop.

(* A generic small-step reduction semantics, parameterized with a mask. *)

Inductive red (mask : mask) : term -> term -> Prop :=
| RedBetaV:
    forall t v u,
    mask RuleBetaV ->
    is_value v ->
    t.[v/] = u ->
    red mask (EApp (ELam t) v) u
| RedBeta:
    forall t1 t2 u,
    mask RuleBeta ->
    t1.[t2/] = u ->
    red mask (EApp (ELam t1) t2) u
| RedParBetaV:
    forall t1 v1 t2 v2 u,
    mask RuleParBetaV ->
    is_value v1 ->
    red mask t1 t2 ->
    red mask v1 v2 ->
    t2.[v2/] = u ->
    red mask (EApp (ELam t1) v1) u
| RedEVar:
    forall x,
    mask RuleEVar ->
    red mask (EVar x) (EVar x)
| RedELam:
    forall t1 t2,
    mask RuleELam ->
    red mask t1 t2 ->
    red mask (ELam t1) (ELam t2)
| RedEAppL:
    forall t1 t2 u,
    mask RuleEAppL ->
    red mask t1 t2 ->
    red mask (EApp t1 u) (EApp t2 u)
| RedEAppVR:
    forall v u1 u2,
    mask RuleEAppVR ->
    is_value v ->
    red mask u1 u2 ->
    red mask (EApp v u1) (EApp v u2)
| RedEAppLR:
    forall t1 t2 u1 u2,
    mask RuleEAppLR ->
    red mask t1 t2 ->
    red mask u1 u2 ->
    red mask (EApp t1 u1) (EApp t2 u2)
| RedEAppR:
    forall t1 u1 u2,
    mask RuleEAppR ->
    red mask u1 u2 ->
    red mask (EApp t1 u1) (EApp t1 u2)
| RedEMatchNone:
    forall tc t1 t2,
    mask RuleEMatchNone ->
    tc = EVariantNone ->
    red mask (EMatch tc t1 t2) t1
| RedEMatchSomeV:
    forall tc vc t1 t2 u,
    mask RuleEMatchSomeV ->
    tc = EVariantSome vc ->
    is_value vc ->
    t2.[vc/] = u ->
    red mask (EMatch tc t1 t2) u
| RedEMatchCond:
    forall tc tc' t1 t2,
    mask RuleEMatchCond ->
    red mask tc tc' ->
    red mask (EMatch tc t1 t2) (EMatch tc' t1 t2)
| RedEMatchL:
    forall tc t1 t1' t2,
    mask RuleEMatchL ->
    red mask t1 t1' ->
    red mask (EMatch tc t1 t2) (EMatch tc t1' t2)
| RedEMatchR:
    forall tc t1 t2 t2',
    mask RuleEMatchR ->
    red mask t2 t2' ->
    red mask (EMatch tc t1 t2) (EMatch tc t1 t2')

| RedNone:
    mask RuleNone ->
    red mask EVariantNone EVariantNone

| RedSome:
    forall t t',
    mask RuleSome ->
    red mask t t' ->
    red mask (EVariantSome t) (EVariantSome t')
.

Global Hint Constructors red : red obvious.

(* The following mask defines the call-by-value reduction semantics. *)

Definition cbv_mask rule :=
  match rule with
  | RuleBetaV    (* reduction of a beta-v redex: (\x.t) v                 *)
  | RuleLetV     (* reduction of a let-v redex:  let x = v in t           *)
  | RuleEAppL     (* reduction in [EApp _ u]                                *)
  | RuleEAppVR    (* reduction in [EApp v _], if [v] is a value             *)
  | RuleEMatchNone
  | RuleEMatchSomeV
  | RuleEMatchCond
  | RuleEMatchSome
  | RuleSome
      => True
  | _ => False
  end.

Notation cbv := (red cbv_mask).
(* 
(* The following mask defines the call-by-name reduction semantics. *)

Definition cbn_mask rule :=
  match rule with
  | RuleBeta     (* reduction of a beta   redex: (\x.t) v                 *)
  | RuleLet      (* reduction of a let redex:    let x = v in t           *)
  | RuleEAppL     (* reduction in [EApp _ u]                                *)
  | RuleIteTrue
  | RuleIteFalse
  | RuleIteCond
      => True
  | _ => False
  end.

Notation cbn := (red cbn_mask).

(* The parallel by-value reduction semantics allows beta-v reductions under
   arbitrary contexts, including under lambda-abstractions. Furthermore, it
   allows parallel reductions (and allows no reduction at all). *)

Definition pcbv_mask rule :=
  match rule with
  | RuleParBetaV (* reduction of a beta redex and reduction in both sides *)
  | RuleParLetV  (* reduction of a let redex and reduction in both sides  *)
  | RuleEVar      (* no reduction                                          *)
  | RuleELam      (* reduction in [ELam _]                                  *)
  | RuleEAppLR    (* reduction in both sides of [EApp _ _]                  *)
  | RuleLetLR    (* reduction in both sides of [Let _ _]                  *)
  | RuleIteTrue
  | RuleIteFalse
  | RuleIteCond
  | RuleIteL
  | RuleIteR
  | RuleConst
      => True
  | _ => False
  end.

Notation pcbv := (red pcbv_mask). *)

(* The tactic [obvious] should be able to prove goals of the form
   [red mask t1 t2], where [mask] is a known mask. *)

Global Hint Extern 1 (cbv_mask _)  => (simpl; tauto) : red obvious.
(* Global Hint Extern 1 (cbn_mask _)  => (simpl; tauto) : red obvious.
Global Hint Extern 1 (pcbv_mask _) => (simpl; tauto) : red obvious. *)

(*
Goal pcbv (EApp (EApp (ELam (EVar 0)) (EVar 0)) (EApp (ELam (EVar 0)) (EVar 0)))
          (EApp (EVar 0) (EVar 0)).
Proof.
  eauto 8 with obvious.
Qed. *)

(* The tactic [step] applies to a goal of the form [star (red mask) t1 t2]. It
   causes the term [t1] to take one step of reduction towards [t1'], turning
   the goal into [star (red mask) t1' t2]. *)

Ltac step :=
  eapply star_step; [ obvious |].

(* The tactic [finished] applies to a goal of the form [star (red mask) t1 t2].
   It turns the goal into [t1 = t2]. *)

Ltac finished :=
  eapply star_refl_eq.

(* The tactic [invert_cbv] inverts a hypothesis of the form [cbv t1 t2]. *)

Ltac invert_cbv :=
  pick (red cbv_mask) invert;
  try solve [ false; eauto 3 with obvious ].

Ltac invert_star_cbv :=
  pick (star cbv) invert.
(* 
Ltac invert_cbn :=
  pick (red cbn_mask) invert;
  try solve [ false; eauto 3 with obvious ]. *)

(* If the following four rules are enabled, then reduction is reflexive. *)

Lemma red_refl:
  forall mask : mask,
  mask RuleEVar ->
  mask RuleELam ->
  mask RuleEAppLR ->
  mask RuleEMatchCond ->
  mask RuleNone ->
  mask RuleSome ->
  forall t,
  red mask t t.
Proof.
  induction t; eauto with red.
Abort.

(* [RuleBetaV] and [RuleLetV] are special cases of [RuleParBetaV] and
   [RuleParLetV], hence are admissible in parallel call-by-value reduction. *)
(* 
Lemma pcbv_RedBetaV:
  forall t v u,
  is_value v ->
  t.[v/] = u ->
  pcbv (EApp (ELam t) v) u.
Proof.
  eauto using red_refl with obvious.
Qed.

Lemma pcbv_RedLetV:
  forall t v u,
  is_value v ->
  t.[v/] = u ->
  pcbv (Let v t) u.
Proof.
  eauto using red_refl with obvious.
Qed.

(* MySequences of reduction, [star cbv], can be carried out under a context. *)



Lemma star_pcbv_EAppL:
  forall t1 t2 u,
  star pcbv t1 t2 ->
  star pcbv (EApp t1 u) (EApp t2 u).
Proof.
  induction 1; eauto using red_refl with sequences obvious.
Qed.

Lemma plus_pcbv_EAppL:
  forall t1 t2 u,
  plus pcbv t1 t2 ->
  plus pcbv (EApp t1 u) (EApp t2 u).
Proof.
  induction 1.
  econstructor; [ | eauto using star_pcbv_EAppL ].
  eapply RedEAppLR; eauto using red_refl with obvious.
Qed. *)

Lemma star_cbv_EAppL:
  forall t1 t2 u,
  star cbv t1 t2 ->
  star cbv (EApp t1 u) (EApp t2 u).
Proof.
  induction 1; eauto with sequences obvious.
Qed.

Lemma star_cbv_EAppR:
  forall t u1 u2,
  is_value t ->
  star cbv u1 u2 ->
  star cbv (EApp t u1) (EApp t u2).
Proof.
  induction 2; eauto with sequences obvious.
Qed.

Global Hint Resolve
  (* star_cbv_EAppL star_pcbv_EAppL plus_pcbv_EAppL *)
  star_cbv_EAppL
  star_cbv_EAppR : red obvious.

Lemma star_cbv_EAppLR:
  forall t1 t2 u1 u2,
  star cbv t1 t2 ->
  star cbv u1 u2 ->
  is_value t2 ->
  star cbv (EApp t1 u1) (EApp t2 u2).
Proof.
  eauto with sequences obvious.
Qed.

Global Hint Resolve star_cbv_EAppLR : red obvious.

(* Reduction commutes with substitutions of values for variables. (This
   includes renamings.) This is true of every reduction strategy, with
   the proviso that if [RuleEVar] is enabled, then [RuleELam], [RuleEAppLR]
   and [RuleLetLR] must be enabled as well, so that reduction is reflexive. *)

Lemma red_subst:
  forall mask : mask,
  (mask RuleEVar -> mask RuleELam) ->
  (mask RuleEVar -> mask RuleEAppLR) ->
  (mask RuleEVar -> mask RuleEMatchCond) ->
  (mask RuleEVar -> mask RuleSome) ->
  (mask RuleEVar -> mask RuleNone) ->
  forall t1 t2,
  red mask t1 t2 ->
  forall sigma,
  is_value_subst sigma ->
  red mask t1.[sigma] t2.[sigma].
Proof.
  admit.
  (* induction 6; simpl; intros; subst;
  try solve [ econstructor; solve [ eauto with is_value | autosubst ]].
  (* Case: [EVar] *)
  { eapply red_refl; eauto. } *)
Abort.

Lemma star_red_subst:
  forall mask : mask,
  (mask RuleEVar -> mask RuleELam) ->
  (mask RuleEVar -> mask RuleEAppLR) ->
  (mask RuleEVar -> mask RuleEMatchCond) ->
  (mask RuleEVar -> mask RuleSome) ->
  (mask RuleEVar -> mask RuleNone) ->
  forall t1 t2 sigma,
  star (red mask) t1 t2 ->
  is_value_subst sigma ->
  star (red mask) t1.[sigma] t2.[sigma].
Proof.
  admit.
  (* induction 6; eauto using red_subst with sequences. *)
Abort.

(* Call-by-value reduction is contained in parallel call-by-value. *)
(* 
Lemma cbv_subset_pcbv:
  forall t1 t2,
  cbv t1 t2 ->
  pcbv t1 t2.
Proof.
  induction 1; try solve [ tauto ]; eauto using red_refl with red.
Qed. *)

(* Under call-by-value, values do not reduce. *)

Lemma values_do_not_reduce:
  forall t1 t2,
  cbv t1 t2 ->
  ~ is_value t1.
Proof.
  induction t1; inversion 1; is_value.
Qed.

Lemma None_do_not_reduce:
  forall t1 t2,
  cbv t1 t2 ->
  ~ t1 = EVariantNone.
Proof.
  unfold cbv_mask in *.
  inversion 1; try solve [assumption | discriminate | congruence].
Qed.

Global Hint Resolve
  values_do_not_reduce
  None_do_not_reduce
  : is_value obvious.

Global Hint Extern 1 (False) => (eapply values_do_not_reduce) : is_value obvious.
Global Hint Extern 1 (False) => (eapply None_do_not_reduce) : is_value obvious.

Lemma is_value_irred:
  forall v,
  is_value v ->
  irred cbv v.
Proof.
  intros. intro. obvious.
Qed.
Global Hint Resolve is_value_irred : irred obvious.

(* Under every strategy, the property of being a value is preserved by
   reduction. *)

Lemma values_are_stable:
  forall mask v1 v2,
  red mask v1 v2 ->
  is_value v1 ->
  is_value v2.
Proof.
  induction 1; is_value.
Qed.

Lemma nonvalues_are_stable:
  forall mask v1 v2,
  red mask v1 v2 ->
  ~ is_value v2 ->
  ~ is_value v1.
Proof.
  induction 1; is_value.
Qed.

Global Hint Resolve values_are_stable nonvalues_are_stable : is_value obvious.

(* [cbv] is deterministic. *)

Lemma cbv_deterministic:
  forall t t1,
  cbv t t1 ->
  forall t2,
  cbv t t2 ->
  t1 = t2.
Proof.
  (* Induction over [cbv t t1]. *)
  induction 1; try solve [ tauto ]; intros; 
  (* Invert the second hypothesis, [cbv t t2]. The fact that values do not
     reduce is used to eliminate some cases. *)
  try solve [subst; invert_cbv; repeat f_equal; injections; eauto; try discriminate].  
Qed.

(* Inversion lemmas for [irred]. *)

Lemma invert_irred_cbv_EApp_1:
  forall t u,
  irred cbv (EApp t u) ->
  irred cbv t.
Proof.
  intros. eapply irred_irred; obvious.
Qed.

Lemma invert_irred_cbv_EApp_2:
  forall t u,
  irred cbv (EApp t u) ->
  is_value t ->
  irred cbv u.
Proof.
  intros. eapply irred_irred; obvious.
Qed.

Lemma invert_irred_cbv_EApp_3:
  forall t u,
  irred cbv (EApp t u) ->
  is_value t ->
  is_value u ->
  forall t', t <> ELam t'.
Proof.
  intros ? ? Hirred. repeat intro. subst.
  eapply Hirred. obvious.
Qed.

Global Hint Resolve
  invert_irred_cbv_EApp_1
  invert_irred_cbv_EApp_2
: irred.

(* An analysis of irreducible terms for call-by-value reduction. A stuck
   term is either an application [v1 v2] where [v1] is not a function or
   a stuck term in an evaluation context. *)

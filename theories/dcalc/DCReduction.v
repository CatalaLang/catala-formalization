Require Import MyTactics.
Require Import MySequences.
Require Import DCSyntax.
Require Import DCValues.
Require Import DCValuesRes.
Require Import DCFreeVars.
Require Import MyList.

Require Import AutosubstExtra.
Require Import LibTactics.

(* We give a symbolic name to each reduction rule. *)

Inductive rule :=
| RuleBetaV    (* reduction of a beta-v redex: (\x.t) v                   *)
| RuleLetV     (* reduction of a let-v redex:  let x = v in t             *)
| RuleBeta     (* reduction of a beta   redex: (\x.t) u                   *)
| RuleLet      (* reduction of a let redex:    let x = u in t             *)
| RuleParBetaV (* reduction of a beta-v redex and reduction in both sides *)
| RuleParLetV  (* reduction of a let redex and reduction in both sides    *)
| RuleVar      (* no reduction                                            *)
| RuleLam      (* reduction in [Lam _]                                    *)
| RuleAppL     (* reduction in [App _ u]                                  *)
| RuleAppR     (* reduction in [App u _]                                  *)
| RuleAppVR    (* reduction in [App v _], if [v] is a value               *)
| RuleAppLR    (* reduction in both sides of [App _ _]                    *)
| RuleLetL     (* reduction in [Let _ u]                                  *)
| RuleLetR     (* reduction in [Let t _]                                  *)
| RuleLetLR    (* reduction in both sides of [Let _ _]                    *)
| RuleConflict (* no reduction of Conflict *)
| RuleEmpty    (* no reduction of Empty *)
| RuleDefaultJ
| RuleDefaultJFalse
| RuleDefaultJTrue
| RuleConst
| RuleDefaultE
| RuleDefaultEConflict
| RuleDefaultEValue
| RuleAppRConflict
| RuleAppLConflict
| RuleLetRConflict
| RuleLetLConflict
| RuleAppREmpty
| RuleAppLEmpty
| RuleLetREmpty
| RuleLetLEmpty
.

(* A mask is a set of rules. *)

Definition mask :=
  rule -> Prop.

(* A generic small-step reduction semantics, parameterized with a mask. *)

Notation "'is_nerror' t" :=
  (match t with
  | Conflict | Empty => False
  | _ => True
  end) (at level 70).

Inductive red (mask : mask) : term -> term -> Prop :=
| RedBetaV:
    forall t v u,
    mask RuleBetaV ->
    is_value v ->
    is_nerror v ->
    t.[v/] = u ->
    red mask (App (Lam t) v) u
| RedLetV:
    forall t v u,
    mask RuleLetV ->
    is_value v ->
    t.[v/] = u ->
    red mask (Let v t) u
| RedBeta:
    forall t1 t2 u,
    mask RuleBeta ->
    t1.[t2/] = u ->
    red mask (App (Lam t1) t2) u
| RedLet:
    forall t1 t2 u,
    mask RuleLet ->
    t2.[t1/] = u ->
    red mask (Let t1 t2) u
| RedParBetaV:
    forall t1 v1 t2 v2 u,
    mask RuleParBetaV ->
    is_value v1 ->
    red mask t1 t2 ->
    red mask v1 v2 ->
    t2.[v2/] = u ->
    red mask (App (Lam t1) v1) u
| RedParLetV:
    forall t1 t2 v1 v2 u,
    mask RuleParLetV ->
    is_value v1 ->
    red mask t1 t2 ->
    red mask v1 v2 ->
    t2.[v2/] = u ->
    red mask (Let v1 t1) u
| RedVar:
    forall x,
    mask RuleVar ->
    red mask (Var x) (Var x)
| RedConflict:
    mask RuleConflict ->
    red mask Conflict Conflict
| RedEmpty:
    mask RuleEmpty ->
    red mask Empty Empty
| RedConst:
    forall b,
    mask RuleConst ->
    red mask (Const b) (Const b)
| RedLam:
    forall t1 t2,
    mask RuleLam ->
    red mask t1 t2 ->
    red mask (Lam t1) (Lam t2)
| RedAppL:
    forall t1 t2 u,
    mask RuleAppL ->
    is_nerror t1 ->
    is_nerror u ->
    red mask t1 t2 ->
    red mask (App t1 u) (App t2 u)
| RedAppVR:
    forall v u1 u2,
    mask RuleAppVR ->
    is_value v ->
    is_nerror v ->
    is_nerror u1 ->
    red mask u1 u2 ->
    red mask (App v u1) (App v u2)
| RedAppLR:
    forall t1 t2 u1 u2,
    mask RuleAppLR ->
    red mask t1 t2 ->
    red mask u1 u2 ->
    red mask (App t1 u1) (App t2 u2)
| RedAppR:
    forall t1 u1 u2,
    mask RuleAppR ->
    red mask u1 u2 ->
    red mask (App t1 u1) (App t1 u2)
| RedAppRConflict:
  forall t,
  mask RuleAppRConflict ->
  red mask (App t Conflict) Conflict
| RedAppLConflict:
  forall t,
  mask RuleAppLConflict ->
  red mask (App Conflict t) Conflict
| RedLetLConflict:
  forall t,
  mask RuleLetLConflict ->
  red mask (Let Conflict t) Conflict
| RedAppREmpty:
  forall t,
  mask RuleAppREmpty ->
  match t with Conflict => False | _ => True end ->
  red mask (App t Empty) Empty
| RedAppLEmpty:
  forall t,
  mask RuleAppLEmpty ->
  match t with | Confict => False end ->
  red mask (App Empty t) Empty
| RedLetREmpty:
  forall t,
  mask RuleLetREmpty ->
  red mask (Let t Empty) Empty
| RedLetLEmpty:
  forall t,
  mask RuleLetLEmpty ->
  red mask (Let Empty t) Empty
| RedLetL:
  forall t1 t2 u,
  mask RuleLetL ->
  red mask t1 t2 ->
  red mask (Let t1 u) (Let t2 u)
| RedLetR:
  forall t u1 u2,
  mask RuleLetR ->
  red mask u1 u2 ->
  red mask (Let t u1) (Let t u2)
| RedLetLR:
  forall t1 t2 u1 u2,
  mask RuleLetLR ->
  red mask t1 t2 ->
  red mask u1 u2 ->
  red mask (Let t1 u1) (Let t2 u2)
| RedDefaultEConflict:
  forall ts ts1 ti ts2 tj ts3 tjust tcons,
  mask RuleDefaultEConflict ->
  List.Forall is_value_res ts ->
  ti <> Empty ->
  tj <> Empty ->
  ts = (ts1 ++ ti::ts2++tj::ts3)%list ->
  red mask (Default ts tjust tcons) Conflict
| RedDefaultEValue:
  forall ts1 ti ts2 tjust tcons,
  mask RuleDefaultEValue ->
  List.Forall (eq Empty) ts1 ->
  List.Forall (eq Empty) ts2 ->
  ti <> Empty ->
  is_value_res ti ->
  red mask (Default (ts1++ti::ts2) tjust tcons) ti
| RedDefaultE:
  forall ts1 ti ti' ts2 tj tc,
  mask RuleDefaultE ->
  red mask ti ti' ->
  (List.Forall is_value_res ts1) ->
  red mask (Default (ts1++ti::ts2) tj tc) (Default (ts1++ti'::ts2) tj tc)
| RedDefaultJ:
  forall ts tj1 tj2 tc,
  mask RuleDefaultJ ->
  List.Forall (eq Empty) ts ->
  red mask tj1 tj2 ->
  red mask (Default ts tj1 tc) (Default ts tj2 tc)
| RedDefaultJTrue:
  forall ts tc,
  mask RuleDefaultJTrue ->
  List.Forall (eq Empty) ts ->
  red mask (Default ts (Const true) tc) tc
| RedDefaultJFalse:
  forall ts tc,
  mask RuleDefaultJFalse ->
  List.Forall (eq Empty) ts ->
  red mask (Default ts (Const false) tc) Empty
.


(* Definition rule_to_red { mask: mask } (r: rule) :=
    match r return
    match r with | RuleBetaV => forall t v u, mask RuleBetaV -> is_value v -> t.[v/] = u -> red mask (App (Lam t) v) u
    | RuleLetV => forall t v u, mask RuleLetV -> is_value v -> t.[v/] = u -> red mask (Let v t) u
    | RuleBeta => forall t1 t2 u, mask RuleBeta -> t1.[t2/] = u -> red mask (App (Lam t1) t2) u
    | RuleLet => forall t1 t2 u, mask RuleLet -> t2.[t1/] = u -> red mask (Let t1 t2) u
    | RuleParBetaV => forall t1 v1 t2 v2 u, mask RuleParBetaV -> is_value v1 -> red mask t1 t2 -> red mask v1 v2 -> t2.[v2/] = u -> red mask (App (Lam t1) v1) u
    | RuleParLetV => forall t1 t2 v1 v2 u, mask RuleParLetV -> is_value v1 -> red mask t1 t2 -> red mask v1 v2 -> t2.[v2/] = u -> red mask (Let v1 t1) u
    | RuleVar => forall x, mask RuleVar -> red mask (Var x) (Var x)
    | RuleConflict => mask RuleConflict -> red mask Conflict Conflict
    | RuleEmpty => mask RuleEmpty -> red mask Empty Empty
    | RuleConst => forall b, mask RuleConst -> red mask (Const b) (Const b)
    | RuleLam => forall t1 t2, mask RuleLam -> red mask t1 t2 -> red mask (Lam t1) (Lam t2)
    | RuleAppL => forall t1 t2 u, mask RuleAppL -> red mask t1 t2 -> red mask (App t1 u) (App t2 u)
    | RuleAppVR => forall v u1 u2, mask RuleAppVR -> is_value v -> red mask u1 u2 -> red mask (App v u1) (App v u2)
    | RuleAppLR => forall t1 t2 u1 u2, mask RuleAppLR -> red mask t1 t2 -> red mask u1 u2 -> red mask (App t1 u1) (App t2 u2)
    | RuleAppR => forall t1 u1 u2, mask RuleAppR -> red mask u1 u2 -> red mask (App t1 u1) (App t1 u2)
    | RuleLetL => forall t1 t2 u, mask RuleLetL -> red mask t1 t2 -> red mask (Let t1 u) (Let t2 u)
    | RuleLetR => forall t u1 u2, mask RuleLetR -> red mask u1 u2 -> red mask (Let t u1) (Let t u2)
    | RuleLetLR => forall t1 t2 u1 u2, mask RuleLetLR -> red mask t1 t2 -> red mask u1 u2 -> red mask (Let t1 u1) (Let t2 u2)
    | RuleDefaultEConflict => forall ts ts1 ti ts2 tj ts3 tjust tcons, mask RuleDefaultEConflict -> List.Forall is_value_res ts -> ti <> Empty -> tj <> Empty -> ts = (ts1 ++ ti::ts2++tj::ts3)%list -> red mask (Default ts tjust tcons) Conflict
    | RuleDefaultEValue => forall ts1 ti ts2 tjust tcons, mask RuleDefaultEValue -> List.Forall (eq Empty) ts1 -> List.Forall (eq Empty) ts2 -> ti <> Empty -> is_value_res ti -> red mask (Default (ts1++ti::ts2) tjust tcons) ti
    | RuleDefaultE => forall ts1 ti ti' ts2 tj tc, mask RuleDefaultE -> red mask ti ti' -> (List.Forall is_value_res ts1) -> red mask (Default (ts1++ti::ts2) tj tc) (Default (ts1++ti'::ts2) tj tc)
    | RuleDefaultJ => forall ts tj1 tj2 tc, mask RuleDefaultJ -> List.Forall (eq Empty) ts -> red mask tj1 tj2 -> red mask (Default ts tj1 tc) (Default ts tj2 tc)
    | RuleDefaultJTrue => forall ts tc, mask RuleDefaultJTrue -> List.Forall (eq Empty) ts -> red mask (Default ts (Const true) tc) tc
    | RuleDefaultJFalse => forall ts tc, mask RuleDefaultJFalse -> List.Forall (eq Empty) ts -> red mask (Default ts (Const false) tc) Empty end
    with
| RuleBetaV => RedBetaV mask
| RuleLetV => RedLetV mask
| RuleBeta => RedBeta mask
| RuleLet => RedLet mask
| RuleParBetaV => RedParBetaV mask
| RuleParLetV => RedParLetV mask
| RuleVar => RedVar mask
| RuleConflict => RedConflict mask
| RuleEmpty => RedEmpty mask
| RuleConst => RedConst mask
| RuleLam => RedLam mask
| RuleAppL => RedAppL mask
| RuleAppVR => RedAppVR mask
| RuleAppLR => RedAppLR mask
| RuleAppR => RedAppR mask
| RuleLetL => RedLetL mask
| RuleLetR => RedLetR mask
| RuleLetLR => RedLetLR mask
| RuleDefaultEConflict => RedDefaultEConflict mask
| RuleDefaultEValue => RedDefaultEValue mask
| RuleDefaultE => RedDefaultE mask
| RuleDefaultJ => RedDefaultJ mask
| RuleDefaultJTrue => RedDefaultJTrue mask
| RuleDefaultJFalse => RedDefaultJFalse mask
end.

Ltac rconstructor :=
  match reverse goal with
  | [ h : ?mask ?r |- _ ] =>
    eapply (@rule_to_red mask r)
  end
. *)




(* List.length (List.filter (neq Empty) ts) >= 2 *)
(* List.length (List.filter (neq Empty) ts) = 1 *)
(* List.length (List.filter (neq Empty) ts) = 0 *)

(* 2022-05-03 TODO: réduire le nombre de constructeurs inductifs ?

   ajouter une autre version avec la une verifcation boolean
 *)

(* forall t v u,
 mask RuleBetaV ->
 is_value v ->
 t.[v/] = u ->
 red mask (App (Lam t) v) u *)

(* Definition red_fun mask t1 t2 : (option rule) :=
  match t1, t2 with
  | (App (Lam t) v), u  =>
    if (t.[v/] =? u and is_value v) then
      Some RuleBetaV
    else None
  | _ => None
  end
. *)

(* 2022-05-03 TODO : representation alternative, transformer l'inductif en un inductif générique avec des noeuds et des feuilles, pour ensuite faire la comparaison sur un arbre ou les noeuds sont des entiers. *)


(* TODO: regarder si c'est possible d'avoir une fonction qui permet d'executer en small step ces défintions. *)

Global Hint Constructors red : red obvious.

(* The following mask defines the call-by-value reduction semantics. *)

Definition cbv_mask rule :=
  match rule with
  | RuleBetaV    (* reduction of a beta-v redex: (\x.t) v                 *)
  | RuleLetV     (* reduction of a let-v redex:  let x = v in t           *)
  | RuleAppL     (* reduction in [App _ u]                                *)
  | RuleAppVR    (* reduction in [App v _], if [v] is a value             *)
  (* | RuleLetL     (* reduction in [Let _ u]                                *) *)
  | RuleDefaultJ
  | RuleDefaultJFalse
  | RuleDefaultJTrue
  | RuleDefaultE
  | RuleDefaultEConflict
  | RuleDefaultEValue
  | RuleAppRConflict
  | RuleAppLConflict
  (* | RuleLetRConflict *)
  (* | RuleLetLConflict *)
  | RuleAppREmpty
  | RuleAppLEmpty
  (* | RuleLetREmpty *)
  (* | RuleLetLEmpty *)
    => True
  | _ => False
  end.

Notation cbv := (red cbv_mask).

(* The following mask defines the call-by-name reduction semantics. *)

Definition cbn_mask rule :=
  match rule with
  | RuleBeta     (* reduction of a beta   redex: (\x.t) v                 *)
  | RuleLet      (* reduction of a let redex:    let x = v in t           *)
  | RuleAppL     (* reduction in [App _ u]                                *)
  | RuleDefaultJ
  | RuleDefaultJFalse
  | RuleDefaultJTrue
  | RuleDefaultE
  | RuleDefaultEConflict
  | RuleDefaultEValue
  | RuleAppRConflict
  | RuleAppLConflict
  | RuleLetRConflict
  | RuleLetLConflict
  | RuleAppREmpty
  | RuleAppLEmpty
  | RuleLetREmpty
  | RuleLetLEmpty
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
  | RuleVar      (* no reduction                                          *)
  | RuleConflict
  | RuleEmpty
  | RuleDefaultJ
  | RuleDefaultJFalse
  | RuleDefaultJTrue
  | RuleConst
  | RuleLam      (* reduction in [Lam _]                                  *)
  | RuleAppLR    (* reduction in both sides of [App _ _]                  *)
  | RuleLetLR    (* reduction in both sides of [Let _ _]                  *)
  | RuleDefaultE
  | RuleDefaultEConflict
  | RuleDefaultEValue
  | RuleAppRConflict
  | RuleAppLConflict
  | RuleLetRConflict
  | RuleLetLConflict
  | RuleAppREmpty
  | RuleAppLEmpty
  | RuleLetREmpty
  | RuleLetLEmpty
      => True
  | _ => False
  end.

Notation pcbv := (red pcbv_mask).

(* The tactic [obvious] should be able to prove goals of the form
   [red mask t1 t2], where [mask] is a known mask. *)

Global Hint Extern 1 (cbv_mask _)  => (simpl; tauto) : red obvious.
Global Hint Extern 1 (cbn_mask _)  => (simpl; tauto) : red obvious.
Global Hint Extern 1 (pcbv_mask _) => (simpl; tauto) : red obvious.

(* Goal cbv (Let (App (Lam (Var 0)) (Var 0)) (Var 0)) (Let (Var 0) (Var 0)).
Proof. obvious. Qed.

Goal cbv (Let (Var 0) (Var 0)) (Var 0).
Proof. obvious. Qed.

Goal cbn (Let (Var 0) (Var 0)) (Var 0).
Proof. obvious. Qed. *)

Goal
  let id := Lam (Var 0) in
  let t := (Let (Lam (Var 0)) (Var 0)) in
  cbn (App id t) t.
Proof. simpl. obvious. Qed.

Goal pcbv (App (App (Lam (Var 0)) (Var 0)) (App (Lam (Var 0)) (Var 0)))
          (App (Var 0) (Var 0)).
Proof.
  eauto 8 with obvious.
Qed.

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

Ltac invert_cbn :=
  pick (red cbn_mask) invert;
  try solve [ false; eauto 3 with obvious ].

(* If the following four rules are enabled, then reduction is reflexive. *)

Lemma red_refl:
  forall mask : mask,
  mask RuleVar ->
  mask RuleLam ->
  mask RuleAppLR ->
  mask RuleLetLR ->
  mask RuleConflict ->
  mask RuleEmpty ->
  mask RuleDefaultJ ->
  mask RuleDefaultJFalse ->
  mask RuleDefaultJTrue ->
  mask RuleDefaultE ->
  mask RuleDefaultEConflict ->
  mask RuleDefaultEValue ->
  mask RuleConst ->
  forall t,
  red mask t t.
Proof.
  induction t using term_ind'; eauto with red.
  * induction ts.
    - apply RedDefaultJ; eauto.
    - inverts H12. 
      replace ((cons a ts)) with (app nil (cons a ts)) by eauto using List.app_nil_l.
      eapply RedDefaultE; try eassumption.
      econstructor.
Qed.

(* [RuleBetaV] and [RuleLetV] are special cases of [RuleParBetaV] and
   [RuleParLetV], hence are admissible in parallel call-by-value reduction. *)

Lemma pcbv_RedBetaV:
  forall t v u,
  is_value v ->
  t.[v/] = u ->
  pcbv (App (Lam t) v) u.
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

(* Lemma star_cbv_AppL:
  forall t1 t2 u,
  star cbv t1 t2 ->
  star cbv (App t1 u) (App t2 u).
Proof.
  induction 1; eauto with sequences obvious.
Qed. *)

Lemma star_pcbv_AppL:
  forall t1 t2 u,
  star pcbv t1 t2 ->
  star pcbv (App t1 u) (App t2 u).
Proof.
  induction 1; eauto using red_refl with sequences obvious.
Qed.

Lemma plus_pcbv_AppL:
  forall t1 t2 u,
  plus pcbv t1 t2 ->
  plus pcbv (App t1 u) (App t2 u).
Proof.
  induction 1.
  econstructor; [ | eauto using star_pcbv_AppL ].
  eapply RedAppLR; eauto using red_refl with obvious.
Qed.

(* Lemma star_cbv_AppR:
  forall t u1 u2,
  is_value t ->
  star cbv u1 u2 ->
  star cbv (App t u1) (App t u2).
Proof.
  induction 2; eauto with sequences obvious.
Qed. *)
(* 
Global Hint Resolve star_cbv_AppL star_pcbv_AppL plus_pcbv_AppL star_cbv_AppR : red obvious. *)

(* Lemma star_cbv_AppLR:
  forall t1 t2 u1 u2,
  star cbv t1 t2 ->
  star cbv u1 u2 ->
  is_value t2 ->
  star cbv (App t1 u1) (App t2 u2).
Proof.
  eauto with sequences obvious.
Qed. *)
(*
Lemma star_cbv_LetL:
  forall t1 t2 u,
  star cbv t1 t2 ->
  star cbv (Let t1 u) (Let t2 u).
Proof.
  induction 1; eauto with sequences obvious.
Qed.

Global Hint Resolve star_cbv_AppLR star_cbv_LetL : red obvious.
*)
(* Reduction commutes with substitutions of values for variables. (This
   includes renamings.) This is true of every reduction strategy, with
   the proviso that if [RuleVar] is enabled, then [RuleLam], [RuleAppLR]
   and [RuleLetLR] must be enabled as well, so that reduction is reflexive. *)

Lemma technical:
  forall ts sigma,
  List.Forall (eq Empty) ts -> List.Forall (eq Empty) ts..[sigma].
Proof.
  induction ts; introv H; inverts H; asimpl; econstructor; eauto.
Qed.

Lemma subst_app:
  forall ts1 ts2 sigma,
  ((ts1 ++ ts2)..[sigma] = ts1..[sigma] ++ ts2..[sigma])%list.
Proof.
  induction ts1; intros; asimpl; eauto.
  * now rewrite IHts1.
Qed.

Lemma subst_cons:
  forall ti ts sigma,
  ((ti::ts)..[sigma] = (ti.[sigma] :: ts..[sigma]))%list.
Proof.
  autosubst.
Qed.

Lemma subst_empty_list:
  forall ts sigma,
  List.Forall (eq Empty) ts ->
  List.Forall (eq Empty) ts..[sigma].
Proof.
  induction ts; asimpl; econstructor; inverts_Forall; asimpl; eauto.
Qed.

Lemma subst_is_value_list:
  forall ts sigma,
  List.Forall is_value_res ts ->
  List.Forall is_value_res ts..[sigma].
Proof.
  induction ts; asimpl; econstructor; inverts_Forall; asimpl; eauto.
  - induction a; eauto; tryfalse.
Qed.

Create HintDb subst.

Global Hint Resolve
  subst_app
  subst_cons
  subst_empty_list
  subst_is_value_list: subst.

Global Hint Rewrite subst_app subst_cons: subst.


Global Hint Resolve subst_is_value_list : is_value_res obvious.


Definition is_nerror_subst (sigma : var -> term) :=
  forall x, is_nerror (sigma x).

Lemma red_subst:
  forall mask : mask,
  (mask RuleVar -> mask RuleLam) ->
  (mask RuleVar -> mask RuleAppLR) ->
  (mask RuleVar -> mask RuleLetLR) ->
  (mask RuleVar -> mask RuleConflict) ->
  (mask RuleVar -> mask RuleEmpty) ->
  (mask RuleVar -> mask RuleDefaultJ) ->
  (mask RuleVar -> mask RuleDefaultJTrue) ->
  (mask RuleVar -> mask RuleDefaultJFalse) ->
  (mask RuleVar -> mask RuleDefaultE) ->
  (mask RuleVar -> mask RuleDefaultEConflict) ->
  (mask RuleVar -> mask RuleDefaultEValue) ->
  (mask RuleVar -> mask RuleConst) ->
  forall t1 t2,
  red mask t1 t2 ->
  forall sigma,
  is_value_subst sigma ->
  is_nerror_subst sigma ->
  red mask t1.[sigma] t2.[sigma].
Proof.
Local Ltac ok :=
  solve [ idtac
    | eauto with is_value
    | eauto with autosubst
    | eauto with subst
  ].

  admit.
  (* 
  induction 13; simpl; intros; subst;
  try solve [
    autorewrite with subst;
    econstructor;
    ok
  ].
  { econstructor; eauto with is_value; eauto with autosubst.
    induction v; simpl in *; eauto.
    unfold is_nerror_subst in *.
    eapply H16.
  }
  { eapply RedParBetaV; try ok.
    - simpl.
  }
  { apply red_refl; eauto. }
  { autorewrite with subst.
    eapply RedDefaultEConflict.
    5: reflexivity.
    - ok.
    - repeat (rewrite <- subst_cons; rewrite <- subst_app).
      eauto using subst_is_value_list.
    - inverts_Forall; induction ti; simpl in *; repeat intro; tryfalse.
    - inverts_Forall; induction tj; simpl in *; repeat intro; tryfalse.
  }
  {
    autorewrite with subst.
    eapply RedDefaultEValue; eauto using is_value_res_subst_list_stable;
    try solve [
      induction ti; simpl in *; repeat intro; tryfalse; eauto with subst
    ].
  }
Admitted.
*)
Admitted.


Lemma star_red_subst:
  forall mask : mask,
  (mask RuleVar -> mask RuleLam) ->
  (mask RuleVar -> mask RuleAppLR) ->
  (mask RuleVar -> mask RuleLetLR) ->
  (mask RuleVar -> mask RuleDefaultJ) ->
  (mask RuleVar -> mask RuleDefaultJTrue) ->
  (mask RuleVar -> mask RuleDefaultJFalse) ->
  (mask RuleVar -> mask RuleDefaultE) ->
  (mask RuleVar -> mask RuleDefaultEConflict) ->
  (mask RuleVar -> mask RuleDefaultEValue) ->
  (mask RuleVar -> mask RuleEmpty) ->
  (mask RuleVar -> mask RuleConflict) ->
  (mask RuleVar -> mask RuleConst) ->
  forall t1 t2 sigma,
  star (red mask) t1 t2 ->
  is_value_subst sigma ->
  is_nerror_subst sigma ->
  star (red mask) t1.[sigma] t2.[sigma].
Proof.
  induction 13; eauto using red_subst with sequences.
Qed.

(* Call-by-value reduction is contained in parallel call-by-value. *)

Lemma cbv_subset_pcbv:
  forall t1 t2,
  cbv t1 t2 ->
  pcbv t1 t2.
Proof.
  induction 1; try solve [ tauto ]; eauto using red_refl with red.
Qed.

(* Under call-by-value, values do not reduce. *)


Lemma values_do_not_reduce:
  forall t1 t2,
  cbv t1 t2 ->
  ~ is_value t1.
Proof.
  inversion 1; is_value.
Qed.

Lemma values_res_do_not_reduce:
  forall t1 t2,
  cbv t1 t2 ->
  ~ is_value_res t1.
Proof.
  inversion 1; is_value_res.
Qed.

Global Hint Resolve values_do_not_reduce : is_value obvious.
Global Hint Resolve values_res_do_not_reduce : is_value_res obvious.

Global Hint Extern 1 (False) => (eapply values_do_not_reduce) : is_value obvious.
Global Hint Extern 1 (False) => (eapply values_res_do_not_reduce) : is_value_res obvious.

Lemma is_value_irred:
  forall v,
  is_value v ->
  irred cbv v.
Proof.
  intros. intro. obvious.
Qed.

Lemma is_value_res_irred:
  forall v,
  is_value_res v ->
  irred cbv v.
Proof.
  intros. intro. obvious.
Qed.

Global Hint Resolve is_value_irred is_value_res_irred : irred obvious.


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

Lemma values_res_are_stable:
  forall mask v1 v2,
  red mask v1 v2 ->
  is_value_res v1 ->
  is_value_res v2.
Proof.
  induction 1; is_value_res.
Qed.

Lemma nonvalues_are_stable:
  forall mask v1 v2,
  red mask v1 v2 ->
  ~ is_value v2 ->
  ~ is_value v1.
Proof.
  induction 1; is_value.
Qed.

Lemma nonvalues_res_are_stable:
  forall mask v1 v2,
  red mask v1 v2 ->
  ~ is_value_res v2 ->
  ~ is_value_res v1.
Proof.
  induction 1; is_value_res.
Qed.

Global Hint Resolve values_are_stable nonvalues_are_stable : is_value obvious.
Global Hint Resolve values_res_are_stable nonvalues_res_are_stable : is_value_res obvious.

(* [cbv] is deterministic. *)
(* This one require quite some amount of work since it is not true in the current setting. *)


(* can be replaced by inverts_Forall *)
Lemma congruence1:
forall ts1 ts2 ti ti',
List.Forall is_value_res (ts1 ++ ti :: ts2) -> cbv ti ti' -> False.
Proof.
  intros.
  assert (is_value_res ti).
  { eapply List.Forall_forall.
    { apply H. }
    { apply List.in_elt. }
  }
  assert (irred cbv ti).
  { obvious. }
  unfold irred in *.
  eapply H2. apply H0.
Qed.

(* can be replaced by inverts_Forall *)
Lemma congruence2:
  forall ts,
  (exists ti tj : term, List.In ti ts /\ List.In tj ts /\ ti <> tj) ->
  List.Forall (eq Empty) ts ->
  False.
Proof.
  intros.
  unpack.
  apply H2.

  asserts_rewrite (ti = Empty).
  { symmetry; eapply (List.Forall_forall (eq Empty) ts); eassumption. }
  asserts_rewrite (tj = Empty).
  { symmetry; eapply (List.Forall_forall (eq Empty) ts); eassumption. }

  reflexivity.
Qed.

(* can be replaced by inverts_Forall *)
Lemma congruence3:
forall ts1 ts2 ti ti',
List.Forall (eq Empty) (ts1 ++ ti :: ts2) -> cbv ti ti' -> False.
Proof.
  intros.
  assert (List.Forall is_value_res (ts1 ++ ti :: ts2)).
  {
    gen ts1 ts2 ti.
    intros ts1 ts2 ti.
    generalize (ts1 ++ ti :: ts2)%list.
    intros ts; clear; intros.
    induction ts; inverts H; econstructor; eauto.
    { is_value_res. }
  }
  eapply congruence1; eauto.
Qed.

(* instance of is_value_res *)
Lemma congruence4:
  forall t b, cbv (Const b) t -> False.
Proof.
  intros.
  is_value.
Qed.

Open Scope list_scope.
Import Lists.List.

(* Lemme faux! *)
Lemma elt_eq_inv {A}: forall (x y : A) l1 l2 l1' l2',
(l1 ++ x :: l2) = (l1' ++ y :: l2') ->
In x l1' \/ In x l2' \/ (x = y /\ l1 = l1' /\ l2 = l2').
Proof.
intros x y l1 l2 l1' l2' Heq.
assert (In y (l1 ++ x :: l2)).
{ rewrite Heq. apply in_elt. }
induction l1; simpl in *.
- destruct H. 
  * repeat right; split; simpl.
Abort.


Lemma in_elt_inv' {A}:
  forall (ti tj : A) ts1 ts2,
  forall ts1' ts2' (tk: A),
  (ts1' ++ tk :: ts2' = ts1 ++ ti::ts2)%list ->
  List.In ti ts1' \/ (tk = ti) \/ List.In ti ts2'.
Proof.
  intros.

  intros.
  assert (List.In ti (ts1' ++ tk :: ts2')).
  { rewrite H. apply List.in_elt. }
  forward List.in_elt_inv.
  destruct H1; subst; eauto.
  forward List.in_app_or.
  destruct H2; eauto.
Qed.

Lemma bli:
  forall ti ts1 ts2 tj ts3,
  Forall (eq Empty) (ts1 ++ ti :: ts2 ++ tj :: ts3) ->
  ti = Empty.
Proof.
  intros; revert H; generalize (ts2 ++ tj :: ts3) as ts4; intros.
  symmetry; eapply Forall_elt.
  apply H.
Qed.


Lemma very_easy:
  forall ts1 ti ts2,
  Forall (eq Empty) (ts1 ++ ti :: ts2) ->
  ti <> Empty ->
  False.
Proof.
  intros; apply H0; symmetry; eapply Forall_elt; eassumption.
Qed.

Lemma very_easy2 {ts1 ti ts2}:
  Forall (eq Empty) (ts1 ++ ti :: ts2) -> Empty = ti.
Proof.
  intros; eapply Forall_elt; eassumption.
Qed.

Lemma is_value_res_Empty:
  forall ti, 
  Empty = ti ->
  is_value_res ti.
Proof.
  intros; subst; 
  now repeat unfolds.
Qed.

Global Hint Resolve
  very_easy
: obvious.
(* 2022-05-03 TODO: nombre de cas dans une liste en le calculant, ça ira plus vite. *)

Lemma RuleDefaultEConflict_RuleDefaultEValue_incompat:
  let mask r := match r with
    | RuleDefaultEConflict
    | RuleDefaultEValue => True
    | _ => False
  end in
  
  forall t t1 t2,
  red mask t t1 ->
  red mask t t2 ->
  t1 = t2
  .
Proof.
  induction 1; try solve [ tryfalse ].
  * intros; pick red invert; try tauto.
    admit.
  * (* symetric case *) 
Admitted.

Ltac split_list :=
  (* this tactic search for a hypothesis in the form of _ ++ _ :: _ = _ ++ _ :: _  and applies to split_list lemma to it. *)
  match goal with [h: _ ++ _ :: _ = _ ++ _ :: _ |- _] => destruct (split_list h) as [hl | [hl | hl]] end; unzip;
  repeat rewrite <- app_assoc, <- app_comm_cons in *
.

Lemma cbv_deterministic:
  forall t t1,
  cbv t t1 ->
  forall t2,
  cbv t t2 ->
  t1 = t2.
Proof.
  induction 1; try solve [ tauto ];
  try solve [
    intros; subst; invert_cbv; eauto; f_equal; try solve
    [ now eapply IHred 
    | try split_list;
      solve
      [ repeat f_equal; eapply IHred; eauto
      | false; inverts_Forall; eauto with is_value]
    ]
  ].
  { intros; subst; invert_cbv; eauto; f_equal; try (now eapply IHred).
    - split_list;
      try solve
      [ repeat f_equal; eapply IHred; eauto
      | false; inverts_Forall; eauto with is_value].
    - false.
      rewrite <- H3 in H0.
      inverts_Forall.
      eauto with is_value.
  }
Qed.

(* Inversion lemmas for [irred]. *)

Lemma invert_irred_cbv_App_1:
  forall t u,
  irred cbv (App t u) ->
  irred cbv t.
Proof.
  intros. eapply irred_irred; obvious.
Qed.

Lemma invert_irred_cbv_App_2:
  forall t u,
  irred cbv (App t u) ->
  is_value t ->
  irred cbv u.
Proof.
  intros. eapply irred_irred; obvious.
Qed.

Lemma invert_irred_cbv_App_3:
  forall t u,
  irred cbv (App t u) ->
  is_value t ->
  is_value u ->
  forall t', t <> Lam t'.
Proof.
  intros ? ? Hirred. repeat intro. subst.
  eapply Hirred. obvious.
Qed.

Lemma invert_irred_cbv_Let_1:
  forall t u,
  irred cbv (Let t u) ->
  irred cbv t.
Proof.
  intros. eapply irred_irred; obvious.
Qed.

Lemma invert_irred_cbv_Let_2:
  forall t u,
  irred cbv (Let t u) ->
  ~ is_value t.
Proof.
  intros ? ? Hirred ?. eapply Hirred. obvious.
Qed.

Lemma invert_irred_cbv_DefaultE:
  forall ts1 ti ts2 tj tc,
  irred cbv (Default (ts1 ++ ti :: ts2) tj tc) ->
  Forall is_value_res ts1 ->
  irred cbv ti
  .
Proof.
  introv Hirred Hts1.
  eapply irred_irred; obvious.
Qed.

Lemma invert_irred_cbv_DefaultJ_1:
  forall ts tj tc,
  irred cbv (Default ts tj tc) ->
  Forall (eq Empty) ts ->
  irred cbv tj.
Proof.
  intros.
  eapply irred_irred; obvious.
Qed.

Lemma invert_irred_cbv_DefaultJ_2:
  forall ts tj tc,
  irred cbv (Default ts tj tc) ->
  Forall (eq Empty) ts ->
  is_value tj ->
  forall b, tj <> Const b.
Proof.
  introv Hirred. repeat intro; subst.
  induction b; eapply Hirred; obvious.
Qed.


Global Hint Resolve
  invert_irred_cbv_App_1
  invert_irred_cbv_App_2
  invert_irred_cbv_Let_1
  invert_irred_cbv_Let_2
  invert_irred_cbv_DefaultJ_1
  invert_irred_cbv_DefaultJ_2
: irred.



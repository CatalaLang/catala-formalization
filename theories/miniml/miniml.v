Require Export Autosubst.Autosubst.
Require Import String.
Require Import Coq.ZArith.ZArith.
Require Import tactics.
Import List.ListNotations.
Require Import common.
Require Import sequences.

Require Import Coq.Classes.SetoidClass.
Require Import Wellfounded.


(*** Definitions of terms and continuations for mini-ml ***)


Inductive term :=
  (* Lambda calculus part of the language*)
  | Var (x: var)
  | App (t1 t2: term)
  | Value (v: value)
with value :=
  | Lam (t: {bind term}).

Inductive expressible_value :=
  | Closure (t: {bind term}) (sigma: list expressible_value).

#[export] Instance Ids_term : Ids term. derive. Defined.

Fixpoint rename_term (xi : var -> var) (s : term) {struct s} : term :=
  match s as t return (annot term t) with
  | Var x => (fun x0 : var => Var (xi x0)) x
  | App t1 t2 =>
    (fun s1 s2 : term => App (rename_term xi s1) (rename_term xi s2)) t1 t2
  | Value v => Value (rename_value xi v)
  end
with rename_value (xi: var -> var) (s: value) {struct s} : value :=
  match s as v return (annot value v) with
  | Lam t => Lam (rename_term (upren xi) t)
  end.

#[export] Instance Rename_term : Rename term := rename_term.
#[export] Instance Rename_value : Rename value := rename_value.

Locate "..[".

Fixpoint subst_term (xi : var -> term) (s : term) {struct s} : term :=
  match s as t return (annot term t) with
  | Var x => (fun x0 : var => (xi x0)) x
  | App t1 t2 =>
    (fun s1 s2 : term => App (subst_term xi s1) (subst_term xi s2)) t1 t2
  | Value v => Value (subst_value xi v)
  end
with subst_value (xi: var -> term) (s: value) {struct s} : value :=
  match s as v return (annot value v) with
  | Lam t => Lam (subst_term (up xi) t)
  end.

Definition subst_value' (xi: var -> value) (s: value) := subst_value (xi >>> Value) (s).

#[export] Instance Subst_term : Subst term := subst_term.
#[export] Instance Subst_value : Subst value := subst_value'.



(*** Strong induction principle for terms ***)


Fixpoint size_term t := 
  match t with
  | Var _ => 0
  | App t1 t2 => S (size_term t1 + size_term t2)
  | Value v => S (size_value v)
  end
with size_value v :=
  match v with
  | Lam t => S (size_term t)
  end.

Definition size x := match x with | inl t => size_term t | inr v => size_value v end.

Fixpoint size_value_expressible v :=
  match v with
  | Closure t env => S (size_term t + (List.list_sum (List.map size_value_expressible env)))
  end.

Theorem term_value_induction
: forall {P : term -> Prop} {Q : value -> Prop}
    {HVar: forall x : var, P (Var x)}
    {HApp: forall t1 : term, P t1 -> forall t2 : term, P t2 -> P (App t1 t2)}
    {HValue: forall v: value, Q v -> P (Value v)}
    {HLam: forall t : {bind term}, P t -> Q (Lam t)},
    (forall x : term + value, match x with | inl t => P t | inr v => Q v end).
Proof.
  induction x as [x IHx] using (
    well_founded_induction
      (wf_inverse_image _ nat _ size 
      PeanoNat.Nat.lt_wf_0)).
  { destruct x.
    { destruct t; try first [
        eapply HVar|
        eapply HApp|
        eapply HValue
      ].
      1: eapply (IHx (inl t1)).
      2: eapply (IHx (inl t2)).
      3: eapply (IHx (inr v)).
      all: simpl; lia.
    }
    { destruct v; try first [
        eapply HLam
      ].
      { eapply (IHx (inl t)).
        all: simpl; lia.
      }
    }
  }
Qed.

Definition term_value_induction_term P Q HVar
HApp
HValue
HLam t : P t := @term_value_induction P Q HVar
HApp
HValue
HLam (inl t).

Lemma SubstLemmas_term1: forall (xi : var -> var) (s : term), rename xi s = s.[ren xi].
Proof.
  intros xi s.
  revert s xi.
  eapply (term_value_induction_term
    (fun t => forall xi, rename_term xi t = subst_term (ren xi) t)
    (fun v => forall xi, rename_value xi v = subst_value (ren xi) v)).
  { simpl; eauto. }
  { intros; simpl; eauto.
    unfold rename in *.
    unfold Rename_term in *.
    unfold subst in *.
    unfold Subst_term in *.
    rewrite H, H0.
    eauto.
  }
  { intros; simpl; eauto.
    unfold rename in *.
    unfold Rename_value in *.
    unfold subst in *.
    unfold Subst_value in *.
    unfold subst_value' in *.
    rewrite H.
    eauto.
  }
  {
    intros; simpl; eauto.
    unfold rename in *.
    unfold Rename_term in *.
    unfold subst in *.
    unfold Subst_term in *.
    rewrite H.

    rewrite up_upren_internal; simpl; eauto.
  }
Qed.

Lemma SubstLemmas_term2: forall s : term, s.[ids] = s.
Proof.
  eapply (term_value_induction_term
    (fun t => subst_term ids t = t)
    (fun v => subst_value ids v = v)).
  
  all: intros; simpl; eauto; unfold subst, Subst_term, Subst_value, subst_value' in *.
  { rewrite H, H0; eauto. }
  { rewrite H; eauto. }
  { rewrite up_id_internal, H; eauto. }
Qed.

Lemma SubstLemmas_term3:
  forall (sigma : var -> term) (x : var), (ids x).[sigma] = sigma x.
Proof.
  simpl; eauto.
Qed.

Lemma SubstLemmas_term4_ren_left: forall (xi : var -> var) (sigma0 : var -> term) (s : term),
(rename xi s).[sigma0] = s.[xi >>> sigma0].
Proof.
  intros sigma tau s.
  revert s sigma tau.
  eapply (term_value_induction_term
    (fun t => forall sigma tau, subst_term tau (rename_term sigma t) = subst_term (sigma >>> tau) t)
    (fun v => forall sigma tau, subst_value tau (rename_value sigma v) = subst_value (sigma >>> tau) v)).
  all: intros; simpl; eauto.
  { rewrite H, H0; eauto. }
  { rewrite H; eauto. }
  { rewrite H.
    autosubst.
  }
Qed.

Lemma SubstLemmas_term4_ren_right:
  forall (sigma0 : var -> term) (xi : var -> var) (s : term),
  rename xi s.[sigma0] = s.[sigma0 >>> rename xi].
Proof.
  intros sigma tau s.
  revert s sigma tau.
  eapply (term_value_induction_term
    (fun t => forall sigma tau, rename_term tau (subst_term sigma t) = subst_term (sigma >>> rename tau) t)
    (fun v => forall sigma tau, rename_value tau (subst_value sigma v) = subst_value (sigma >>> rename tau) v)).
  all: intros; simpl; eauto.
  { rewrite H, H0. eauto. }
  { rewrite H. eauto. }
  { rewrite H.
    rewrite up_comp_subst_ren_internal; simpl; eauto.
    { eapply SubstLemmas_term1. }
    { eapply SubstLemmas_term4_ren_left. }
  }
Qed.

Lemma SubstLemmas_term4: forall (sigma tau : var -> term) (s : term), s.[sigma].[tau] = s.[sigma >> tau].
Proof.
  intros sigma tau s.
  revert s sigma tau.
  eapply (term_value_induction_term
    (fun t => forall sigma tau, subst_term tau (subst_term sigma t) = subst_term (sigma >> tau) t)
    (fun v => forall sigma tau, subst_value tau (subst_value sigma v) = subst_value (sigma >> tau) v)).
  all: intros; simpl; eauto.
  {
    rewrite H, H0.
    eauto.
  }
  { rewrite H; eauto. }
  { rewrite H; eauto.

    rewrite up_comp_internal; asimpl; eauto.
    { eapply SubstLemmas_term4_ren_left. }
    { eapply SubstLemmas_term4_ren_right. }
  }
Qed.

#[export] Instance SubstLemmas_term : SubstLemmas term. 
  split.
  { eapply SubstLemmas_term1. }
  { eapply SubstLemmas_term2. }
  { eapply SubstLemmas_term3. }
  { eapply SubstLemmas_term4. }
Defined.

Lemma ids_inj:
  forall x y, ids x = ids y -> x = y.
intros; inj; eauto.
Qed.

(* TODO: update this lemma.
Theorem term_ind'
  : forall (P : term -> Prop) (P0 : expressible_value -> Prop),
      (forall x : var, P (Var x)) ->
      (forall t1 : term, P t1 -> forall t2 : term, P t2 -> P (App t1 t2)) ->
      (forall t : {bind term}, P t -> P0 (Lam t)) ->
      (forall t,
       P t -> forall sigma, (List.Forall P0 sigma) -> P0 (Closure t sigma)) ->
      (forall t : term, P t) /\ (forall v : expressible_value, P0 v).
Proof.
  split; intros.
  unshelve eapply (term_value_induction (inl t)); eauto.
  unshelve eapply (term_value_induction (inr v)); eauto.
Qed. *)





(*** Syntax for continuations ***)

Inductive cont :=
  | CAppR (t2: term) (sigma: list expressible_value) (* [\square t2] *)
  | CClosure (t_cl: {bind term}) (sigma_cl: list expressible_value)
  (* [Clo(x, t_cl, sigma_cl) \square] Since we are using De Bruijn indices,
     there is no variable x. *)
.

Inductive state :=
  | mode_eval (e: term) (kappa: list cont) (env: list expressible_value)
  | mode_cont (kappa: list cont) (result: expressible_value)
.


(*** Continuation step semantics ***)

Inductive cred: state -> state -> Prop :=
  (** Rules related to the lambda calculus *)
  | cred_var:
    forall x kappa sigma v,
    List.nth_error sigma x = Some v ->
    cred
      (mode_eval (Var x) kappa sigma)
      (mode_cont kappa v)

  | cred_app:
    forall t1 t2 kappa sigma,
    cred
      (mode_eval (App t1 t2) kappa sigma)
      (mode_eval t1 ((CAppR t2 sigma) :: kappa) sigma)

  | cred_clo:
    forall t kappa sigma,
    cred
      (mode_eval (Value (Lam t)) kappa sigma)
      (mode_cont kappa (Closure t sigma))

  | cred_arg:
    forall t2 kappa sigma tcl sigmacl,
    cred
      (mode_cont ((CAppR t2 sigma)::kappa) (Closure tcl sigmacl))
      (mode_eval t2 ((CClosure tcl sigmacl)::kappa) sigma)

  | cred_beta:
    forall t_cl sigma_cl kappa v,
    cred
      (mode_cont ((CClosure t_cl sigma_cl)::kappa) (v))
      (mode_eval t_cl kappa (v :: sigma_cl))
.


Coercion App : term >-> Funclass.
Notation "'λ.' t" := (Lam t) (at level 50).
Notation "'S(' t , kappa , sigma )" := (mode_eval t kappa sigma).
Notation "'C(' v , kappa )" := (mode_cont kappa v).
Notation "'λ' sigma '.' t " := (Closure t sigma) (at level 10).
(* Notation "'λ' sigma '.' t " := (RValue (Closure t sigma)) (at level 10). *)
Notation "'k_app1' ( t )" := (CAppR t) (at level 50).
Notation "'k_app2' ( t , sigma )" := (CClosure t sigma) (at level 50).
(* Notation "'k_ret' ( sigma )" := (CReturn sigma) (at level 50). *)
Notation "s1 ~> s2" := (cred s1 s2) (at level 20).
Definition id_var (n: nat): var := n.
Coercion id_var: nat >-> var.
(* Coercion RValue: expressible_value >-> result. *)
Coercion Var: var >-> term.



(*** small step semantics ***)

Import List.ListNotations.
Open Scope list.

Definition subst_of_env sigma :=
  fun n =>
  match List.nth_error sigma n with
  | None => ids (n - List.length sigma)
  | Some t => t
  end
.




Inductive sred: term -> term -> Prop :=
  | sred_beta:
    forall t v,
      sred
        (App (Value (Lam t)) (Value v))
        (t.[Value v/])
  | sred_app_right:
    forall t u1 u2,
      sred (u1) (u2) ->
      sred
        (App (Value (Lam t)) u1)
        (App (Value (Lam t)) u2)
  | sred_app_left:
    forall t1 t2 u,
      sred (t1) (t2) ->
      sred
        (App t1 u)
        (App t2 u)
.


(*** Typing ***)

Inductive type :=
  | TBool
  | TFun (T1 T2: type)
.

(* Standard typing rules for lambda calculus *)

Inductive jt_term:
  list type -> term -> type -> Prop :=
  | JTVar:
    forall Gamma x T,
      Some T = List.nth_error Gamma x ->
      jt_term Gamma (Var x) T
  | JTApp:
    forall Gamma t1 t2 T1 T2,
      jt_term Gamma t1 (TFun T1 T2) ->
      jt_term Gamma t2 T1 ->
      jt_term Gamma (App t1 t2) T2
  | JTValue:
    forall Gamma v T,
      jt_value Gamma v T ->
      jt_term Gamma (Value v) T
with jt_value: list type -> value -> type -> Prop :=
  | JTLam:
  forall Gamma t T1 T2,
    jt_term (T1::Gamma) t T2 ->
    jt_value Gamma (Lam t) (TFun T1 T2)

  (* | JTEIf:
    forall Gamma u ta tb T,
      jt_term Gamma u TBool ->
      jt_term Gamma ta T ->
      jt_term Gamma tb T ->
      jt_term Gamma (If u ta tb) T *)
.

Inductive jt_expressible_value:
   expressible_value -> type -> Prop :=
  | JTValueClosure:
    forall  tcl sigma_cl Gamma_cl T1 T2,
      List.Forall2 jt_expressible_value sigma_cl Gamma_cl ->
      jt_value Gamma_cl (Lam tcl) (TFun T1 T2) ->
      jt_expressible_value (Closure tcl sigma_cl) (TFun T1 T2)
.

(** Expanding the rules of typing to continuation-bases semantics requires to define the typing jugment for continuations. This typing judgement have two additional informations: the "hole" type, and the "environement" in the hole. Both are required with our presentation since the hole is filed when the jt_state judgement is defined. *)


Inductive jt_cont:
  type -> cont -> type -> Prop :=
  | JTCAppR:
    forall {Gamma t2 T1 T2 sigma},
      jt_term Gamma t2 T1 ->
      List.Forall2 jt_expressible_value sigma Gamma ->
      jt_cont (TFun T1 T2) (CAppR t2 sigma) T2
  | JTCClosure:
    forall {Gamma_cl sigma_cl T1 T2 tcl},
      jt_value Gamma_cl (Lam tcl) (TFun T1 T2) ->
      List.Forall2 (jt_expressible_value) sigma_cl Gamma_cl ->
      jt_cont T1 (CClosure tcl sigma_cl)  T2
  (* | JTCIf:
    forall Gamma T ta tb,
      jt_term Gamma ta T ->
      jt_term Gamma tb T ->
      jt_cont Gamma Gamma (CIf ta tb) (TBool) T *)
.

Inductive jt_conts: type -> list cont -> type -> Prop :=
| JTNil:
  forall {T},
    jt_conts T nil T
| JTCons:
  forall {cont kappa T1 T2 T3},
    jt_cont T1 cont T2 ->
    jt_conts T2 kappa T3 ->
    jt_conts T1 (cont :: kappa) T3
.

(** Finall well-typeness of the state. *)
Inductive jt_state: state -> type -> Prop :=
| JTmode_eval:
  forall Gamma t T1 T2 kappa sigma,
    List.Forall2 (jt_expressible_value) sigma Gamma ->
    jt_term Gamma t T1 ->
    jt_conts T1 kappa T2 ->
    jt_state (mode_eval t kappa sigma) T2
| JTmode_cont:
  forall r T1 T2 kappa,
    jt_expressible_value r T1 ->
    jt_conts T1 kappa T2 ->
    jt_state (mode_cont kappa r) T2
. 


Require Import Ltac2.Ltac2.
Set Default Proof Mode "Classic".


(** Specialized tactics to invert typing judgement if one argument is a known constructor. *)
Ltac2 inv_jt () :=
  match! goal with
  | [ h: jt_term _ ?c _ |- _ ] => smart_inversion c h
  | [ h: jt_value _ ?c _ |- _ ] => smart_inversion c h
  | [ h: jt_value _ _ ?c |- _ ] => smart_inversion c h
  | [ h: jt_expressible_value _ ?c |- _ ] => smart_inversion c h
  | [ h: jt_cont _ ?c _ |- _ ] => smart_inversion c h
  | [ h: jt_conts _ ?c _ |- _ ] => smart_inversion c h
  | [ h: jt_state ?c _ |- _ ] => smart_inversion c h
  | [ h: List.Forall _ ?c |- _ ] => smart_inversion c h
  | [ h: List.Forall2 _ ?c _ |- _ ] => smart_inversion c h
  | [ h: List.Forall2 _ _ ?c |- _ ] => smart_inversion c h
end.

Ltac inv_jt := ltac2:(inv_jt ()).


(** Specialiazed tactic to apply econstructor when possible. *)
Ltac2 econs_jt () :=
  match! goal with
  | [ |- jt_term _ _ _] => econstructor
  | [ |- jt_value _ _ _] => econstructor
  | [ |- jt_expressible_value _ _] => econstructor
  | [ |- jt_cont _ _ _] => econstructor
  | [ |- jt_conts _ _ _] => econstructor
  | [ |- jt_state _ _] => econstructor
  | [ |- List.Forall _ _] => econstructor
  | [ |- List.Forall2 _ _ _] => econstructor
  end.
Ltac econs_jt := ltac2:(econs_jt ()).


Theorem Forall2_nth_error_Some {A B F l1 l2}:
  List.Forall2 F l1 l2 ->
  forall k (x: A) (y: B),
    List.nth_error l1 k = Some x ->
    List.nth_error l2 k = Some y ->
    F x y.
Proof.
  induction 1, k; simpl; intros; inj; eauto.
Qed.


(** Main preservation lemma for continuation-based semantics. *)
Theorem preservation_cont s1 s2:
  cred s1 s2 ->
  forall T,
  jt_state s1 T ->
  jt_state s2 T.
Proof.
  (* Case analysis over all possible rules *)
  induction 1.
(* 
  6:{
    (* beta reduction. *)
    intros; repeat inv_jt.
    econstructor.

  }
   *)
  (* Most of the cases are easilly handle by the automation. *)
  all: intros; repeat inv_jt; repeat (econs_jt; eauto).

  (** One case is left. It requires an external lemma. *)
  { pose proof (Forall2_nth_error_Some H4); eauto. }
Qed.

Definition is_mode_cont s :=
  match s with
  | mode_cont _ _ => true
  | _ => false
  end.

Definition stack s :=
  match s with
  | mode_eval _ k _ => k
  | mode_cont k _  => k
  end.

Theorem Forall2_nth_error_Some_right {A B F l1 l2}:
  List.Forall2 F l1 l2 ->
  forall {k} {y: A},
    List.nth_error l2 k = Some y ->
    exists (x: B), List.nth_error l1 k = Some x.
Proof.
  induction 1, k; simpl; intros; inj; eauto.
Qed.

(** Main progress lemma for continuation-based semantics. *)
Theorem progress_cont s1:
  forall T,
    jt_state s1 T ->
    (exists s2, cred s1 s2) \/ (is_mode_cont s1 = true /\ stack s1 = nil).
Proof.
  (* Precise case analysis. *)
  induction s1 as [t kappa env|kappa r]; [induction t; try induction v|(induction kappa as [|k kappa]; [|induction k]); induction r].


  (** Using inversion on each of the cases *)
  all: intros; repeat inv_jt.

  (** Most of the cases are easily handled using the automation *)
  all: try solve [left; eexists; econstructor; eauto].
  all: try solve [right; simpl; eauto].

  (* One case is left that requires an additional lemma on lists. *)
  { pose proof (Forall2_nth_error_Some_right H3 (eq_sym H1)); unpack.
    left; eexists; econstructor; eauto.
  }
Qed.

(*** Typing for tss ***)

Definition fv k t :=
  t.[upn k (ren (+1))] = t.

(* Lemma fv_Lam_eq:
  forall k t,
  fv k (Lam t) <-> fv (S k) t.
Proof.
  unfold fv. intros. asimpl. split; intros.
  { injections. eauto. }
  { unpack. congruence. }
Qed. *)



Lemma fv_App_eq:
  forall k t1 t2,
  fv k (App t1 t2) <-> fv k t1 /\ fv k t2.
Proof.
  unfold fv. intros. asimpl. split; intros.
  { injections. eauto. }
  { unpack. congruence. }
Qed.


Notation lift i t := (t.[ren(+i)]).



Lemma lift_inj_Var:
  forall t x,
  lift 1 t = Var (S x) <-> t = Var x.
Proof.
  split; intros.
  { apply lift_inj; eauto. }
  { subst. eauto. }
Qed. 

Lemma fv_Var_eq:
  forall k x,
  fv k (Var x) <-> x < k.
Proof.
  unfold fv. asimpl. induction k; intros.
  (* Base case. *)
  { asimpl. split; intros; tryfalse.
    { unfold ids, Ids_term in *. injections. lia. }
    { lia. }
  }
  (* Step. *)
  { destruct x; asimpl.
    { split; intros. { lia. } { reflexivity. } }
    rewrite lift_inj_Var. rewrite IHk. lia. }
Qed.


(* Hint Rewrite fv_Var_eq fv_Lam_eq fv_App_eq : fv. *)


(** Main progress lemma for continuation-based semantics. *)
Theorem progress_trad t1:
  forall Gamma T,
    jt_term Gamma t1 T ->
    fv 0 t1 ->
    (exists t2, sred t1 t2) \/ (match t1 with |Value _ => True | _ => False end).
Proof.
  induction 1.

  (** Using inversion on each of the cases *)
  all: intros; repeat inv_jt.
  all: unzip; subst.

  (** Less cases than in the normal cases. *)
  all: try solve [left; eexists; econstructor; eauto].
  all: try solve [right; simpl; eauto].
  
  { rewrite fv_Var_eq in *. lia. }

  { (** Manual handling of the proof here. *)
    rewrite fv_App_eq in *; unpack.
    pose proof (IHjt_term1 H1).
    pose proof (IHjt_term2 H2).
    unzip; subst.
    all: intros; repeat inv_jt.
    (* automation here depends on the order of the constructors. *)
    all: try solve [left; eexists; econstructor; eauto].
    { (* The automation does not even work *)
      induction t1.
      { rewrite fv_Var_eq in H1. lia. }
      { tryfalse. }
      { left; eexists. induction v. eapply sred_app_right. eauto. }
    }
    { induction t1; induction t2; try rewrite fv_Var_eq in *; try lia; tryfalse.
      { induction v. left; eexists. eapply sred_beta. }
    }
  }
Qed.

(* Lemma jt_term_firstn_fv:
  forall Gamma t T,
    jt_term Gamma t T ->
    forall k,
    fv k t ->
    jt_term (List.firstn k Gamma) t T.
Proof.
  induction 1.
  { intros. rewrite fv_Var_eq in *.
    rewrite <- (List.firstn_skipn k Gamma) in H.
    rewrite List.nth_error_app1 in H.
    2:{ rewrite List.length_firstn. rewrite List.firstn_skipn in *.
        pose proof (nth_error_Some' (eq_sym H)).
        lia.
    }

    econstructor; eauto.
  }
  { intros; rewrite fv_App_eq in *; unpack; eauto.
    pose proof (IHjt_term1 _ H1).
    pose proof (IHjt_term2 _ H2).
    repeat econs_jt; eauto.
  }
  { intros. rewrite fv_Lam_eq in *; unpack; eauto.
    pose proof (IHjt_term _ H0).
    repeat econs_jt; eauto.
  }
Qed. *)

(* Compute (Var 0).[upn 0 (subst_of_env [Closure (Var 0) []])]. *)


Lemma upn_k_sigma_x:
  forall k sigma x,
  x < k ->
  upn k sigma x = ids x.
Proof.
  induction k; intros; asimpl.
  { lia. }
  { destruct x; asimpl.
    { eauto. }
    { rewrite IHk by lia. autosubst. }
  }
Qed.

(* Lemma upn_k_sigma_x':
  forall k sigma x,
  x >= k ->
  x < List.length sigma + k ->
  upn k (subst_of_env sigma) x = (subst_of_env sigma) (x - k).
Proof.
  induction k; intros; asimpl.
  { repeat f_equal; lia. }
  { destruct x; asimpl.
    { lia. }
    { rewrite IHk by lia.
      assert (Hx: x - k < List.length sigma) by lia.
      unfold subst_of_env.
      remember (List.nth_error sigma (x - k)) as o; induction o.
      { autosubst. }
      { exfalso.
        eapply List.nth_error_Some; eauto.
      }
    }
  }
Qed. *)


(* Theorem jt_term_subst_aux: forall {Gamma t T},
  jt_term Gamma t T ->
  forall Gamma1 Gamma2,
  Gamma1++Gamma2 = Gamma ->
  forall sigma,
  List.Forall2 jt_value sigma Gamma2 ->
  jt_term Gamma1 t.[upn (List.length Gamma1) (subst_of_env sigma)] T
  .
Proof.
  induction 1.
  repeat intros.
  { rewrite <- H0 in H.
    pose proof (nth_error_Some' (eq_sym H)).
    rewrite List.length_app in *.
    destruct (lt_dec x (List.length Gamma1)).
    { simpl.
      rewrite upn_k_sigma_x by eauto.
      unfold ids; unfold Ids_term.
      econs_jt.
      erewrite <- List.nth_error_app1; eauto.
    }
    { assert (x >= List.length Gamma1). { clear -n; lia. }
      simpl.
      rewrite List.nth_error_app2 in * by lia.
      assert (exists v, List.nth_error sigma (x - List.length Gamma1) = Some v).
      { eapply Forall2_nth_error_Some_right; eauto. }
      unpack.
      pose proof (Forall2_nth_error_Some H1 _ _ _ H4 (eq_sym H)). 
      rewrite upn_k_sigma_x'.
      {
        unfold subst_of_env. rewrite H4.
        econstructor.
        eauto.
      }
      { lia. }
      { pose proof (List.Forall2_length H1).
        lia.
      }
    }
  }
  { intros ? ? HGamma ? H'.
    pose proof (IHjt_term1 _ _ HGamma _ H').
    pose proof (IHjt_term2 _ _ HGamma _ H').
    asimpl.
    econstructor; eauto.
  }
  { intros ? ? HGamma ? H'.
    simpl. econstructor. asimpl.
    assert (HGamma': (T1 :: Gamma1) ++ Gamma2 = T1 :: Gamma).
    { simpl. congruence. }

    pose proof (IHjt_term _ _ HGamma' _ H').
    simpl in *.
    eauto.
  }
  { intros; simpl; repeat econs_jt; eauto.
  }
Qed.

Theorem jt_term_subst: forall {Gamma t T},
  jt_term Gamma t T ->
  forall sigma,
  List.Forall2 jt_value sigma Gamma ->
  jt_term [] t.[subst_of_env sigma] T
  .
Proof.
  intros.
  replace (subst_of_env sigma) with (upn (List.length ([]: list type)) (subst_of_env sigma)) by (unfold upn; simpl; eauto).
  eapply jt_term_subst_aux; simpl; eauto.
Qed.

Lemma jt_term_more_env:
  forall Gamma1 t T,
  jt_term Gamma1 t T ->
  forall Gamma2,
    jt_term (Gamma1 ++ Gamma2) t T.
Proof.
  induction 1; intros; repeat econs_jt; eauto.
  { rewrite List.nth_error_app1; eauto.
    eapply nth_error_Some'; eauto.    
  }
Qed. *)


Theorem preservation_trad t1:
  fv 0 t1 ->
  forall t2,
    sred t1 t2 ->
    forall Gamma T,
      jt_term Gamma t1 T ->
      jt_term Gamma t2 T.
Proof.
  intros Hfv.
  induction 1; intros; repeat inv_jt; repeat econs_jt; eauto.
  (* { ugly thing is here. Untold invarant : the terms are free of variables inside lambda.
    rewrite fv_App_eq in Hfv.
    rewrite fv_Lam_eq in Hfv.
    admit.
    (* progress replace [T1] with (List.firstn 1 (T1::Gamma)) by (simpl; eauto).
    eapply jt_term_firstn_fv; eauto. *)
  } *)
  (* { 
    (* should be provable with substitution lemma *)
    (* assert (H: List.Forall2 jt_value (v :: sigma') (T1 :: Gamma_cl)) by (econstructor; eauto). *)
    (* pose proof (jt_term_subst H3 _ H). *)
    replace Gamma with ([] ++ Gamma) by (simpl; eauto).
    (* apply jt_term_more_env. *)
    eauto.
  } *)
  { 
    admit "requires an substitution theorem". }
  { rewrite fv_App_eq in *; unpack. eapply IHsred; eauto. }
  { rewrite fv_App_eq in *; unpack; eapply IHsred; eauto. }
Admitted.



(*** Determinism of the relation *)

Theorem cred_deterministic:
  forall s1 s2, cred s1 s2 -> forall s2', cred s1 s2' -> s2 = s2'.
Proof.
  induction 1; inversion 1; subst; simpl in *; eauto.
  { rewrite H in H5; inj; eauto. }
Qed.

Theorem sred_deterministic:
  forall t1 t2, sred t1 t2 -> forall t2', sred t1 t2' -> t2 = t2'.
Proof.
  induction 1; inversion 1; subst; simpl in *; eauto.
  { inversion H4; subst; tryfalse. }
  { inversion H4; subst; tryfalse. }
  { inversion H; subst; tryfalse. }
  { repeat f_equal. eapply IHsred. eauto. }
  { inversion H4; subst; tryfalse. }
  { inversion H; subst; tryfalse. }
  { inversion H; subst; tryfalse. }
  { repeat f_equal. eapply IHsred. eauto. }
Qed.


(*** Equivalence relation definition ***)

(* This equivalence relation is used in the simulation theorem. The goal of this simulation is to say that closures should be the same up to substitution of their environement. The other rules are only here to indicate this relation should be congrugent.*)

(* This part is not presented in the paper. *)

Inductive sim_term: term -> term -> Prop :=
  | sim_term_1: forall x y, x = y -> sim_term (Var x) (Var y)
  | sim_term_2: forall t1 t2 u1 u2,
    sim_term t1 u1 ->
    sim_term t2 u2 ->
    sim_term (App t1 t2) (App u1 u2)
  | sim_term_3: forall t1 u1,
    sim_term t1 u1 ->
    sim_term (Lam t1) (Lam u1)
.

(* This equivalence relation is indeed reflexive, symmetric and transitive. Moreother, it is invariant with respect to renaming and substitution. We show those facts bellow, after defining a more general induction principle. *)

Instance Reflexive_sim_term : Reflexive sim_term. Abort.
Instance Symmetric_sim_term : Symmetric sim_term. Abort.
Instance Transtive_sim_term : Transitive sim_term. Abort.

(* It is proper with respect to substitution *)


Lemma sim_term_ren:
  forall t1 t2,
    sim_term t1 t2 ->
    forall xi,
      sim_term t1.[ren xi] t2.[ren xi].
Abort.

Lemma sim_term_subst:
  forall t1 t2,
    sim_term t1 t2 ->
    forall sigma1 sigma2,
      (forall x, sim_term (sigma1 x) (sigma2 x)) ->
      sim_term t1.[sigma1] t2.[sigma2].
Abort.

Section SIM_PROPERTIES.

Scheme sim_term_sim_value_ind := Induction for sim_term Sort Prop
  with sim_value_sim_term_ind := Induction for sim_value Sort Prop.


(* To generate the following precise induction principle, just show the sim_term_sim_value_ind and copy the common hypothesis, and change the output. *)

Theorem sim_ind
	 : forall (P : forall t t0 : term, sim_term t t0 -> Prop)
         (P0 : forall v v0 : value, sim_value v v0 -> Prop),
       (forall (x y : var) (e : x = y), P (Var x) (Var y) (sim_term_1 x y e)) ->
       (forall (t1 t2 u1 u2 : term) (s : sim_term t1 u1),
        P t1 u1 s ->
        forall s0 : sim_term t2 u2,
        P t2 u2 s0 -> P (App t1 t2) (App u1 u2) (sim_term_2 t1 t2 u1 u2 s s0)) ->
       (forall (t1 u1 : term) (s : sim_term t1 u1),
        P t1 u1 s -> P (Lam t1) (Lam u1) (sim_term_3 t1 u1 s)) ->
       (forall (v1 w1 : value) (s : sim_value v1 w1),
        P0 v1 w1 s -> P (Value v1) (Value w1) (sim_term_4 v1 w1 s)) ->
       (forall (t1 t2 : term) (sigma1 sigma2 : list value)
          (s : sim_term t1.[up (subst_of_env sigma1)]
                 t2.[up (subst_of_env sigma2)]),
        P t1.[up (subst_of_env sigma1)] t2.[up (subst_of_env sigma2)] s ->
        P0 (Closure t1 sigma1) (Closure t2 sigma2)
          (sim_value_1 t1 t2 sigma1 sigma2 s)) ->
       (forall (t t0 : term) (s : sim_term t t0), P t t0 s) /\ (forall (v v0 : value) (s : sim_value v v0), P0 v v0 s)
.
Proof.
  split.
  eapply sim_term_sim_value_ind; eauto.
  eapply sim_value_sim_term_ind; eauto.
Qed.


Lemma sim_term_ren:
  forall t1 t2,
    sim_term t1 t2 ->
    forall xi,
      sim_term t1.[ren xi] t2.[ren xi].
Proof.
  induction 1; intros; subst; asimpl.
  all: try econstructor; eauto.
Qed.

Lemma sim_term_subst:
  forall t1 t2,
    sim_term t1 t2 ->
    forall sigma1 sigma2,
      (forall x, sim_term (sigma1 x) (sigma2 x)) ->
      sim_term t1.[sigma1] t2.[sigma2].
Proof.
  induction 1; intros; subst; asimpl.
  all: try econstructor; eauto.
  { eapply IHsim_term.
    induction x; asimpl.
    { econstructor; eauto. }
    { eapply sim_term_ren; eauto. }
  }
Qed.

Lemma subst_of_env_nil_ids:
  subst_of_env [] = ids.
Proof.
  eapply FunctionalExtensionality.functional_extensionality.
  induction x; unfold subst_of_env; simpl; eauto.
Qed.

Lemma subst_of_env_cons_S {t ts n}:
  subst_of_env (t :: ts) (S n) = subst_of_env ts n.
Proof.
  unfold subst_of_env.
  simpl.
  eauto.
Qed.


Lemma sim_term_reflexive: Reflexive sim_term /\ Reflexive sim_value.
  eapply term_ind'.
  all: econstructor; eauto.
  {
    eapply sim_term_subst.
    { eauto. }
    { intro x; case x; asimpl.
      { econstructor; eauto. }
      { intros; eapply sim_term_ren.
        revert n.
        induction sigma.
        { rewrite subst_of_env_nil_ids; econstructor; eauto. }
        { inversion H0; subst; intros. case n; asimpl.
          { econstructor; eauto. }
          { intros. rewrite subst_of_env_cons_S.
            eapply IHsigma; eauto.
          }
        }
      }
    }
  }
Qed.

Lemma sim_symmetric: Symmetric sim_term /\ Symmetric sim_value.
  eapply sim_ind; econstructor; eauto.
Qed.

Lemma sim_transitive:
  (forall x y : term, sim_term x y -> forall z, sim_term y z -> sim_term x z) /\
  (forall x y : value, sim_value x y -> forall z, sim_value y z -> sim_value x z).
  unfold Transitive.
  eapply sim_ind.
  { inversion 1; eauto. }
  { intros. inversion H1; subst; econstructor; eauto. }
  { intros. inversion H0; subst; econstructor; eauto. }
  { intros. inversion H0; subst; econstructor; eauto. }
  { intros. inversion H0; subst; econstructor; eauto. }
Qed.

End SIM_PROPERTIES.

Instance Reflexive_sim_term : Reflexive sim_term. eapply sim_term_reflexive. Qed.
Instance Symmetric_sim_term : Symmetric sim_term. destruct sim_symmetric; eauto. Qed.
Instance Transtive_sim_term : Transitive sim_term. destruct sim_transitive; eauto. Qed.

(*** Translating state into terms by unfolding the continuations stack len ***)

Definition apply_cont
  (t: term)
  (k: cont)
  : term :=
  match k with
  | CAppR t2 sigma =>
    App t t2.[subst_of_env sigma]
  | CClosure t_cl sigma_cl =>
    App (Value (Closure t_cl sigma_cl)) t
  end.

Definition apply_conts
  (kappa: list cont)
  : term -> term :=
  List.fold_left apply_cont kappa.

Definition apply_return (r: result) :=
  match r with
  | RValue v => Value v
  end.

Definition apply_state (s: state): term :=
  match s with
  | mode_eval t stack env =>
    apply_conts stack t.[subst_of_env env]
  | mode_cont stack r =>
    apply_conts stack (apply_return r) 
  end.


(*** Main sim_state definition ***)

Inductive sim_state: state -> term -> Prop :=
  | InvBase: forall s,
    sim_state s (apply_state s)
  | InvStep: forall s t1,
    sim_state s t1 ->
    forall t2,
    sim_term t1 t2 ->
    sim_state s t2
.

(* Smart constructors and inversion for the sim_state inductive *)

Lemma sim_state_inversion:
  forall s t1,
  sim_state s t1 ->
  exists t,
    sim_term t1 t /\ apply_state s = t.
Proof.
  induction 1.
  { eexists; split; eauto. reflexivity. }
  { intros; inj; subst.
    edestruct IHsim_state; eauto; unpack.
    eexists; split; eauto.
    symmetry.
    etransitivity.
    symmetry.
    eauto.
    eauto.
  }
Qed.

Lemma sim_state_from_equiv {t2 s}:
  sim_term (apply_state s) t2 ->
  sim_state s t2.
Proof.
  repeat econstructor; eauto.
Qed.


Lemma apply_conts_app:
  forall kappa1 kappa2 p,
    apply_conts (kappa1 ++ kappa2) p
    = apply_conts kappa2 (apply_conts kappa1 p).
Proof.
  intros.
  unfold apply_conts.
  rewrite List.fold_left_app; eauto.
Qed.


(* Fixpoint last (l: list cont) (env0: list value) : list value :=
  match l with
  | [] => env0
  | CReturn env1 :: l =>
    last l env1
  | _ :: l =>
    last l env0
  end.

Lemma snd_apply_conts_last :
  forall kappa env0 t, (snd (apply_conts kappa (t, env0))) = (last kappa env0).
Proof.
  induction kappa.
  { simpl; eauto. }
  { induction a; simpl; intros; eauto. }
Qed. *)

Theorem sred_apply_conts: forall kappa t t',
  sred t t' ->
  sred
    (apply_conts kappa t)
    (apply_conts kappa t')
.
Proof.
  induction kappa as [|k kappa] using List.rev_ind.
  { induction 1; simpl; econstructor; eauto. }
  { induction k; intros t t' Htt'.

    all: pose proof (IHkappa _ _ Htt').
    all: repeat rewrite apply_conts_app;
    simpl; unfold apply_cont; repeat match goal with
    | [ |- context [let '(_, _) := ?p in _]] =>
      rewrite (surjective_pairing p)
    | [h: context [let '(_, _) := ?p in _] |- _] =>
      rewrite (surjective_pairing p) in h
    end; simpl.

    all: repeat rewrite snd_apply_conts_last.
    
    all: try econstructor; eauto.
  }
Qed.


Theorem star_sred_apply_conts: forall kappa t t',
  star sred t t' ->
  star sred
    (apply_conts kappa t)
    (apply_conts kappa t')
.
Proof.
  induction 1; econstructor; eauto using sred_apply_conts.
Qed.

Lemma sim_state_apply_conts {kappa t1 t2}:
  sim_term t1 t2 ->
  sim_term
    (apply_conts kappa t1)
    (apply_conts kappa t2)
.
Proof.
  revert t1 t2.
  induction kappa as [|k kappa] using List.rev_ind; simpl; eauto.
  induction k; intros; repeat rewrite apply_conts_app; simpl; unfold apply_cont; sp; simpl.
  { econstructor. eapply IHkappa; eauto.
    reflexivity.
  }
  { econstructor.
    { reflexivity. }
    { eapply IHkappa; eauto. }
  }
Qed.

(* Base theorem *)
Theorem simulation_cred_sred_base:
  forall s1 s2,
    cred s1 s2 ->
    exists t,
      sim_state s2 t /\
      star sred (apply_state s1) t.
Proof.
  intros s1 s2 Hs1s2'.
  pose proof (Hs1s2') as Hs1s2.
  induction Hs1s2'; try induction o.
  all: simpl.
  all: try solve [eexists; split; [eapply InvBase|]; eapply star_refl].
  { eexists; split; [eapply InvBase|].
    simpl; unfold subst_of_env; rewrite H; eauto with sequences.
  }
  {
    eexists; split.
    2:{ eapply star_sred_apply_conts. eapply star_one. econstructor. }
    eapply sim_state_from_equiv.
    eapply sim_state_apply_conts.
    simpl.
    econstructor.
    econstructor.
    replace (t.[up (subst_of_env sigma)].[up (subst_of_env [])]) with (t.[up (subst_of_env sigma)]).
    reflexivity.
    rewrite subst_of_env_nil_ids.
    asimpl.
    eauto.
  }
  { eexists; split; [eapply InvBase|]; simpl.
    eapply star_sred_apply_conts.
    repeat econstructor.
  }
Qed.

Lemma nth_error_subst_of_env {x sigma v}:
  List.nth_error sigma x = Some v ->
  Value v = subst_of_env sigma x.
Proof.
  intros.
  unfold subst_of_env.
  rewrite H.
  eauto.
Qed.

Lemma star_sred_Value { v t}:
  star sred (Value v) t -> t = Value v.
Proof.
  induction 1 using star_ind_n1; eauto; subst.
  inversion H.
Qed.


Notation "'sim_term' t1 t2" :=
  (sim_term t1 t2) (
  at level 50,
  t1 at level 3,
  t2 at level 3,
  only printing,
  format "'sim_term'  '[hv' t1  '/' t2 ']'"
).

Notation "'sim_value' t1 t2" :=
  (sim_value t1 t2) (
  at level 50,
  t1 at level 3,
  t2 at level 3,
  only printing,
  format "'sim_value'  '[hv' t1  '/' t2 ']'"
).



Lemma subst_of_env_cons v sigma:
  subst_of_env (v :: sigma) = (Value v) .: subst_of_env sigma.
Proof.
  eapply FunctionalExtensionality.functional_extensionality.
  induction x; asimpl; eauto.
Qed.


Lemma proper_sim_state_sred:
  forall t1 t2,
    sred t1 t2 ->
    forall u1,
      sim_term t1 u1 ->
      exists u2,
        sim_term t2 u2 /\ sred u1 u2.
Proof.
  induction 1; inversion 1; subst.
  { repeat econstructor.
    rewrite subst_of_env_nil_ids.
    rewrite up_id; asimpl.
    eauto.
  }
  { inversion H2; inversion H4; inversion H1; subst.
    repeat econstructor.
    clear -H6 H11.
    replace (t.[subst_of_env (v :: sigma')]) with t.[up (subst_of_env sigma')].[Value v/] by (rewrite subst_of_env_cons; asimpl; eauto).
    replace (t2.[subst_of_env (w0 :: sigma2)]) with t2.[up (subst_of_env sigma2)].[Value w0/] by (rewrite subst_of_env_cons; asimpl; eauto).
    eapply sim_term_subst; eauto.
    { induction x; simpl; econstructor; eauto. }
    
  }
  { learn (IHsred _ H5); unpack.
    inversion H3; subst.
    inversion H7; subst.
    repeat econstructor; eauto.
  }
  {
    learn (IHsred _ H3); unpack.
    repeat econstructor; eauto.
  }
Qed.


Lemma proper_sim_state_star_sred:
  forall t1 t2,
    star sred t1 t2 ->
    forall u1,
      sim_term t1 u1 ->
      exists u2,
        sim_term t2 u2 /\ star sred u1 u2.
Proof.
  induction 1 using star_ind_n1.
  { repeat econstructor; eauto. }
  { intros ? Ht1.
    learn (IHstar _ Ht1); unpack.
    learn (proper_sim_state_sred _ _ H _ H1); unpack.
    eexists; split; eauto.
    eapply star_step_n1; eauto.
  }
Qed.

Theorem simulation_cred_sred:
  forall s1 s2,
    cred s1 s2 ->
    forall t1,
      sim_state s1 t1 ->
      exists t2,
        sim_state s2 t2 /\ star sred t1 t2.
Proof.
  intros ? ? Hs1s2 ? Hs1t1.
  learn (simulation_cred_sred_base _ _ Hs1s2); unpack; subst.
  repeat match goal with
  | [h: sim_state  _ _ |- _] =>
    learn (sim_state_inversion _ _ h); unpack; subst
  end.
  learn (proper_sim_state_star_sred _ _ H1 _ (symmetry H4)); unpack.
  eexists; split; [|eauto].
  eapply sim_state_from_equiv.
  etransitivity; [symmetry|]; eauto.
Qed.


(*** From sred to cred ***)

(* Already defined *)
(* Definition stack s :=
  match s with
  | mode_cont kappa _ _ => kappa
  | mode_eval _ kappa _ => kappa
  end. *)

Definition with_stack s kappa :=
  match s with
  | mode_cont _ r => mode_cont kappa r
  | mode_eval t _ sigma => mode_eval t kappa sigma
end.

Definition append_stack s kappa :=
  with_stack s (stack s ++ kappa).

Lemma append_stack_all {s}:
  s = append_stack (with_stack s []) (stack s).
Proof.
  induction s; intros; simpl in *; subst; reflexivity.
Qed.

Lemma append_stack_app {s kappa1 kappa2}:
  stack s = kappa1 ++ kappa2 ->
  s = append_stack (with_stack s kappa1) kappa2.
Proof.
  induction s; intros; simpl in *; subst; reflexivity.
Qed.

Lemma cred_append_stack {s1 s2}:
  cred s1 s2 ->
  forall {kappa},
  cred (append_stack s1 kappa) (append_stack s2 kappa).
Proof.
  induction 1; intros; simpl; econstructor; eauto.
Qed.

Lemma star_cred_append_stack {s1 s2}:
  star cred s1 s2 ->
  forall {kappa},
  star cred (append_stack s1 kappa) (append_stack s2 kappa).
Proof.
  induction 1; intros; econstructor; eauto using cred_append_stack.
Qed.

Lemma apply_state_append_stack {s kappa}:
  apply_state (append_stack s kappa) =
  apply_conts kappa (apply_state s).
Proof.
  induction s; simpl; unfold apply_conts; eapply List.fold_left_app.
Qed.

Lemma subst_of_env_App {t1 t2 t' env}:
  App t1 t2 = t'.[subst_of_env env] ->
  exists (t1' t2': term),
    t1 = t1'.[subst_of_env env]
    /\ t2 = t2'.[subst_of_env env]
    /\ t' = App t1' t2'
.
Proof.
  destruct t'; asimpl; intros; tryfalse; inj; eauto;
  match goal with
  | [h: _ = subst_of_env ?env ?x |- _ ] =>
    unfold subst_of_env in h;
    destruct (List.nth_error env x);
    inj
  end.
Qed.

Lemma subst_of_env_Lam {t t' env}:
  Lam (t: {bind term}) = t'.[subst_of_env env] ->
  exists (t1': {bind term}),
    t = t1'.[up (subst_of_env env)] /\
    t' = Lam t1'
.
Proof.
  destruct t'; asimpl; intros; tryfalse; inj; eauto;
  match goal with
  | [h: _ = subst_of_env ?env ?x |- _ ] =>
    unfold subst_of_env in h;
    destruct (List.nth_error env x);
    inj
  end.
Qed.

Lemma subst_of_env_Value {v t' env}:
  Value v = t'.[subst_of_env env] ->
  t' = Value v \/ exists x, t' = Var x /\ List.nth_error env x = Some v.
Proof.
  destruct t'; asimpl; intros; tryfalse; inj; eauto.
  unfold subst_of_env in *.
  remember (List.nth_error env x) as o.
  induction o; subst; tryfalse; inj; eauto.
Qed.

Ltac subst_of_env :=
  match goal with
  | [h: App _ _ = _.[subst_of_env _] |- _] =>
    learn (subst_of_env_App h); clear h; unzip; subst
  | [h: Lam _ = _.[subst_of_env _] |- _] =>
    learn (subst_of_env_Lam h); clear h; unzip; subst
  | [h: Value _ = _.[subst_of_env _] |- _] =>
    learn (subst_of_env_Value h); clear h; unzip; subst
  end.

(* Lemma cred_snd_apply_sate {s1 s2}:
  cred s1 s2 ->
  snd (apply_state s1) = snd (apply_state s2).
Proof.
  induction 1; simpl; repeat rewrite snd_apply_conts_last; eauto.
Qed.

Lemma star_cred_snd_apply_sate {s1 s2}:
  star cred s1 s2 ->
  snd (apply_state s1) = snd (apply_state s2).
Proof.
  induction 1; eauto.
  rewrite <- IHstar.
  eapply cred_snd_apply_sate; eauto.
Qed. *)

Lemma value_apply_conts {v kappa t}:
  Value v = apply_conts kappa t ->
  (Value v = t) /\ kappa = []
  .
Proof.
  induction kappa as [|k kappa] using List.rev_ind.
  { simpl; eauto. }
  { induction k; rewrite apply_conts_app; simpl; intros; inj. }
Qed.

(* Lemma Forall_CReturn_star_cred {kappa1 env0 result kappa2}:
  List.Forall (fun k => exists sigma, k = CReturn sigma) kappa1 ->
  star cred
    (mode_cont (kappa1 ++ kappa2) env0 result)
    (mode_cont kappa2 (last kappa1 env0) result)
  .
Proof.
  intros. revert env0.
  induction H as [|? kappa1 [env1 Hk]]; subst; simpl; intros.
  { eapply star_refl. }
  { eapply star_step. { econstructor. }
    eapply IHForall.
  }
Qed. *)


Theorem rev_ind_wf {A}:
  forall P: list A -> Prop,
    P [] ->
    (forall (x:A) (l:list A),
      P l ->
      forall (IHlen: forall l', List.length l' < List.length (l ++ [x]) -> P l'),
      P (l ++ [x])) ->
    forall l:list A, P l.
Proof.
  intros P Hnil Hcons l.
  induction l as [l IHl] using (
    well_founded_induction
      (wf_inverse_image _ nat _ (@List.length _)
      PeanoNat.Nat.lt_wf_0)).
  induction l using List.rev_ind.
  { eapply Hnil. }
  { eapply Hcons.
    { eapply IHl.
      rewrite List.last_length; lia.
    }
    { intros.
      eapply IHl.
      rewrite List.last_length in *; lia.
    }
  }
Qed.

Lemma subst_apply_state {t env}:
  t.[subst_of_env env] = apply_state (mode_eval t [] env).
Proof.
  simpl; eauto.
Qed.

Lemma apply_conts_apply_state {t kappa env}:
(apply_conts kappa t.[subst_of_env env]) = apply_state (mode_eval t kappa env).
Proof.
  simpl; eauto.
Qed.

Lemma apply_conts_Value_apply_state {v kappa }:
(apply_conts kappa (Value v)) = apply_state (mode_cont kappa (RValue v)).
Proof.
  simpl; eauto.
Qed.


(* Lemma fst_apply_conts_CReturn {kappa sigma t}:
  fst (apply_conts (kappa ++ [CReturn sigma]) t) = fst (apply_conts kappa t).
Proof.
  rewrite apply_conts_app; simpl; unfold apply_cont; sp; simpl; eauto.
Qed. *)

(* The handling of CReturn is orthogonal to the other continuations, hence we proove it in a different way. *)
(* Lemma induction_case_CReturn
  (sigma: list value)
  (kappa: list cont)
  (IHkappa: forall s1 : state,
            kappa = stack s1 ->
            forall t2 : term,
            sred (fst (apply_state_aux s1)) t2 ->
            exists s2 : state, sim_state s2 t2 /\ star cred s1 s2):

  forall s1 : state,
  kappa ++ [CReturn sigma] = stack s1 ->
  forall t2 : term,
  sred (fst (apply_state_aux s1)) t2 ->
  exists s2 : state, sim_state s2 t2 /\ star cred s1 s2
.
Proof.
  intros.
  assert (Heq: fst (apply_state_aux s1) = fst (apply_state_aux (with_stack s1 kappa))).
  { induction s1; simpl in *; subst; rewrite apply_conts_app; simpl; unfold apply_cont; sp; simpl; eauto. }

  rewrite Heq in *.

  epose proof (IHkappa _ _ _ H0); unpack.
  learn (sim_state_inversion _ _ H1); unpack.
  induction s1; simpl in *; subst.

  all: eapply star_trans_prop; [erewrite append_stack_app; [|solve[simpl; reflexivity]]; eapply star_cred_append_stack; simpl; eauto|].
  all: eapply star_refl_prop; eapply sim_state_from_equiv; simpl.
  all: induction s2; simpl in *; subst; rewrite apply_conts_app; simpl; unfold apply_cont; sp; simpl; eauto.
  all: symmetry; eauto.

  Unshelve.
  induction s1; simpl; eauto.
Qed. *)


Theorem simulation_sred_cred_base:
  forall s1 t2,
    sred (apply_state s1) t2 ->
    exists s2,
      sim_state s2 t2 /\ star cred s1 s2.
Proof.
  intros s1.
  remember (stack s1) as kappa.
  revert s1 Heqkappa.
  induction kappa as [|k kappa] using rev_ind_wf.
  { induction s1; simpl; intro Hkappa; subst; simpl.
    { remember e.[subst_of_env env] as t1.
      intros t2 Ht1t2.
      generalize dependent env.
      generalize dependent e.
      
      induction Ht1t2; intros; repeat subst_of_env.
      all: try repeat (eapply star_step_prop; [econstructor; eauto|]).

      (* Reflexivity cases. *)
      all: try solve [
          eapply star_refl_prop; eapply sim_state_from_equiv; simpl; try reflexivity
      ].

      { eapply star_refl_prop; eapply sim_state_from_equiv.
        asimpl. repeat econstructor.
        rewrite subst_of_env_nil_ids; asimpl; reflexivity. 
      }
      { learn (IHHt1t2 _ _ eq_refl); unpack.
        eapply star_trans_prop.
        rewrite append_stack_all; eapply star_cred_append_stack; simpl; eauto.

        eapply star_refl_prop; eapply sim_state_from_equiv; simpl.
        rewrite apply_state_append_stack; simpl; unfold apply_cont; sp; simpl.
        econstructor; eauto; try reflexivity.
        
        learn (sim_state_inversion _ _ H); unpack; subst; symmetry; eauto.
      }
      { learn (IHHt1t2 _ _ eq_refl); unpack.
        eapply star_trans_prop.
        rewrite append_stack_all; eapply star_cred_append_stack; simpl; eauto.

        eapply star_refl_prop; eapply sim_state_from_equiv; simpl.
        rewrite apply_state_append_stack; simpl; unfold apply_cont; sp; simpl.
        econstructor; eauto; try reflexivity.

        learn (sim_state_inversion _ _ H); unpack; subst; symmetry; eauto.
      }
      { learn (IHHt1t2 _ _ eq_refl); unpack.
        eapply star_trans_prop.
        rewrite append_stack_all; eapply star_cred_append_stack; simpl; eauto.

        eapply star_refl_prop; eapply sim_state_from_equiv; simpl.
        rewrite apply_state_append_stack; simpl; unfold apply_cont; sp; simpl.
        econstructor; eauto; try reflexivity.
        { learn (sim_state_inversion _ _ H); unpack; subst; symmetry; eauto. }
      }
    }
    {
      induction result0; simpl; inversion 1.
    }
  }
  { induction s1; induction k; try match goal with [r: result |- _]=> induction r end; simpl; intro Hkappa; subst; simpl.
    all: rewrite apply_conts_app; simpl; unfold apply_cont; sp; simpl.

    (* { intros t3 Ht2t3.
      match typeof Ht2t3 with sred ?u1 ?u2 => remember u1 as u end.
      induction Ht2t3; intros.
      { inj. }
      { inj.
        repeat match goal with
        [h: Value _ = (apply_conts _ _) |- _] =>
          learn (value_apply_conts h); clear h; unpack; subst
        end.
        repeat subst_of_env.
        { repeat (eapply star_step_prop; [solve[econstructor; eauto]|]).
          eapply star_refl_prop.
          eapply 
          reflexivity.
        }
        Close scope 

      }

    } *)

    all: intros t3 Ht2t3.

    all: match typeof Ht2t3 with sred ?u1 ?u2 => remember u1 as u end.
    all: induction Ht2t3; intros; inj.
    all: repeat match goal with
      [h: Value _ = (apply_conts _ _) |- _] =>
        learn (value_apply_conts h); clear h; unpack; repeat subst_of_env
      end.
    all: injections; subst.
    all: repeat (
      repeat (eapply star_step_prop; [solve[econstructor; eauto]|])
    ).
    all: try solve [
      eapply star_refl_prop; eapply sim_state_from_equiv; simpl; unfold apply_cont; sp; simpl; reflexivity
    ].
    { rewrite subst_apply_state in Ht2t3.
      epose proof (IHlen _ _ _ _ _ Ht2t3); unpack.

      match goal with
      | [h:sim_state _ _ |- _] => learn (sim_state_inversion _ _ h); clear h; unpack; subst
      end.

      eapply star_trans_prop; [rewrite append_stack_all; eapply star_cred_append_stack; eauto|simpl].

      eapply star_refl_prop.
      eapply sim_state_from_equiv; rewrite apply_state_append_stack; simpl; unfold apply_cont; sp; simpl.
      econstructor; first[reflexivity| symmetry; eauto].
    }
    {
      rewrite subst_apply_state in Ht2t3.
      epose proof (IHlen _ _ _ _ _ Ht2t3); unpack.

      match goal with
      | [h:sim_state _ _ |- _] => learn (sim_state_inversion _ _ h); clear h; unpack; subst
      end.

      eapply star_trans_prop; [rewrite append_stack_all; eapply star_cred_append_stack; eauto|simpl].

      eapply star_refl_prop.
      eapply sim_state_from_equiv; rewrite apply_state_append_stack; simpl; unfold apply_cont; sp; simpl.
      econstructor; first[reflexivity| symmetry; eauto].
    }
    {
      rewrite apply_conts_apply_state in Ht2t3.
      epose proof (IHlen _ _ _ _ _ Ht2t3); unpack.

      match goal with
      | [h:sim_state _ _ |- _] => learn (sim_state_inversion _ _ h); clear h; unpack; subst
      end.


      eapply star_trans_prop; [erewrite append_stack_app; [|solve[simpl;eauto]]; eapply star_cred_append_stack; eauto|simpl].

      eapply star_refl_prop.
      eapply sim_state_from_equiv; rewrite apply_state_append_stack; simpl; unfold apply_cont; sp; simpl.
      econstructor; first[reflexivity| symmetry; eauto].

    }
    {
      rewrite apply_conts_apply_state in Ht2t3.
      epose proof (IHlen _ _ _ _ _ Ht2t3); unpack.

      match goal with
      | [h:sim_state _ _ |- _] => learn (sim_state_inversion _ _ h); clear h; unpack; subst
      end.


      eapply star_trans_prop; [erewrite append_stack_app; [|solve[simpl;eauto]]; eapply star_cred_append_stack; eauto|simpl].

      eapply star_refl_prop.
      eapply sim_state_from_equiv; rewrite apply_state_append_stack; simpl; unfold apply_cont; sp; simpl.
      econstructor; first[reflexivity| symmetry; eauto].
    }
    {
      inversion Ht2t3.
    }
    { rewrite subst_apply_state in Ht2t3.
      epose proof (IHlen _ _ _ _ _ Ht2t3); unpack.

      match goal with
      | [h:sim_state _ _ |- _] => learn (sim_state_inversion _ _ h); clear h; unpack; subst
      end.

      eapply star_trans_prop; [rewrite append_stack_all; eapply star_cred_append_stack; eauto|simpl].

      eapply star_refl_prop.
      eapply sim_state_from_equiv; rewrite apply_state_append_stack; simpl; unfold apply_cont; sp; simpl.
      econstructor; first[reflexivity| symmetry; eauto].
    }
    { rewrite apply_conts_Value_apply_state in Ht2t3.
      epose proof (IHlen _ _ _ _ _ Ht2t3); unpack.

      match goal with
      | [h:sim_state _ _ |- _] => learn (sim_state_inversion _ _ h); clear h; unpack; subst
      end.

      eapply star_trans_prop; [erewrite append_stack_app; [|solve[simpl; eauto]]; eapply star_cred_append_stack; eauto|simpl with_stack].
      
      eapply star_refl_prop.
      eapply sim_state_from_equiv; rewrite apply_state_append_stack; simpl; unfold apply_cont; sp; simpl.
      econstructor; [symmetry; eauto|].
      reflexivity.
    }
    { rewrite apply_conts_Value_apply_state in Ht2t3.
      epose proof (IHlen _ _ _ _ _ Ht2t3); unpack.

      match goal with
      | [h:sim_state _ _ |- _] => learn (sim_state_inversion _ _ h); clear h; unpack; subst
      end.

      eapply star_trans_prop; [erewrite append_stack_app; [|solve[simpl; eauto]]; eapply star_cred_append_stack; eauto|simpl with_stack].

      eapply star_refl_prop.
      eapply sim_state_from_equiv; rewrite apply_state_append_stack; simpl; unfold apply_cont; sp; simpl.
      econstructor; first [reflexivity|symmetry; eauto].
    }
    {
      inversion Ht2t3.
    }
  }

  Unshelve.
  all: simpl; try reflexivity.
  all: try rewrite List.length_app; simpl; lia.
Qed.


(* Lifting the result *)

Theorem simulation_sred_cred:
  forall t1 t2,
    sred t1 t2 ->
    forall s1,
      sim_state s1 t1 ->
      exists s2,
        sim_state s2 t2 /\ star cred s1 s2.
Proof.
  intros ? ? Ht1t2 ? Hs1t1.
  learn (sim_state_inversion _ _ Hs1t1); unpack; subst; clear Hs1t1.
  learn (proper_sim_state_sred _ _ Ht1t2 _ H); unpack.
  learn (simulation_sred_cred_base _ _ H3); unpack; subst.
  eexists; split; eauto.
  learn (sim_state_inversion _ _ H4); unpack; subst; clear H2.
  eapply sim_state_from_equiv.
  symmetry.
  etransitivity; eauto.
Qed.

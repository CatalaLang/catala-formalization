Require Export Autosubst.Autosubst.
Require Import String.
Require Import Coq.ZArith.ZArith.
Require Import tactics.
Import List.ListNotations.
Open Scope list.
Require Import common.
Require Import sequences.

Require Import Coq.Classes.SetoidClass.
Require Import Wellfounded.





(*** Definitions of terms and continuations for mini-ml ***)


(* Description of basic lambda calculus. In this file, we choose the use explict value separated from result values from the CEK machine) to express lambda. This decision is to make it possible to write syntactical rules in the reduction rules of the lambda calculus, but has a significant cost because of the presence of mutual induction: Autosubst and induction principles must be shown by hand. *)

Inductive term :=
  (* Lambda calculus part of the language*)
  | Var (x: var)
  | App (t1 t2: term)
  | Value (v: value)
with value :=
  | Lam (t: {bind term}).

(* Autosubst does not sucessfully work when using mutually recursive inductive types. Hence, we define the renaming and substitution by hand, and show the multiple lemmas by hand too. *)

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


(*** Syntax for continuations ***)

(* This is the direct implementation of the CEK machine. *)

Inductive result_value :=
  | Closure (t: {bind term}) (sigma: list result_value).


Inductive cont :=
  | CAppR (t2: term) (sigma: list result_value) (* [\square t2] *)
  | CClosure (t_cl: {bind term}) (sigma_cl: list result_value)
  (* [Clo(x, t_cl, sigma_cl) \square] Since we are using De Bruijn indices,
     there is no variable x. *)
.

Inductive state :=
  | mode_eval (e: term) (kappa: list cont) (env: list result_value)
  | mode_cont (kappa: list cont) (result: result_value)
.


(* We define a notation that take a environement and transform it to an autosubst substitution, represented as functions from nat to result values. We could have defined our environements directly into the states, but as a result, the syntax of term would have contained functions. Using an encoding of lists, we ensure the syntax of states is purely defined using constructors. *)

Notation "'soe' sigma n" := (
match List.nth_error sigma n with
| None => ids (n - List.length sigma)
| Some t => Value t
end)
(at level 69, sigma at level 1, n at level 1, only parsing).

(*** Continuation step semantics ***)


(* This is a direct implementation of the reduction rules for the CEK machine. *)

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


(* Notations to ease the reading of coq goals. *)

Coercion App : term >-> Funclass.
Notation "'λ.' t" := (Lam t) (at level 50).
Notation "'S(' t , kappa , sigma )" := (mode_eval t kappa sigma).
Notation "'C(' v , kappa )" := (mode_cont kappa v).
Notation "'[[[' sigma '.' t ']]]' " := (Closure t sigma) (at level 10).
(* Notation "'λ' sigma '.' t " := (RValue (Closure t sigma)) (at level 10). *)
Notation "'app' ( t , sigma )" := (CAppR t sigma) (at level 50).
Notation "'fun' ( t , sigma )" := (CClosure t sigma) (at level 50).
Notation "s1 ~> s2" := (cred s1 s2) (at level 20).
Definition id_var (n: nat): var := n.
Coercion id_var: nat >-> var.
Coercion Value: value >-> term.
(* Coercion RValue: result_value >-> result. *)
Coercion Var: var >-> term.



(*** small step semantics ***)

(* We encode small-step semanitcs with an explicit syntactic "Value" for values. This permit to encode the sred_beta and sred_app_right reduction rules with explicit "Value". *)
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

Inductive jt_result_value:
   result_value -> type -> Prop :=
  | JTValueClosure:
    forall  tcl sigma_cl Gamma_cl T1 T2,
      List.Forall2 jt_result_value sigma_cl Gamma_cl ->
      jt_value Gamma_cl (Lam tcl) (TFun T1 T2) ->
      jt_result_value (Closure tcl sigma_cl) (TFun T1 T2)
.

(** Expanding the rules of typing to continuation-bases semantics requires to define the typing jugment for continuations. This typing judgement have two additional informations: the "hole" type, and the "environement" in the hole. Both are required with our presentation since the hole is filed when the jt_state judgement is defined. *)


Inductive jt_cont:
  type -> cont -> type -> Prop :=
  | JTCAppR:
    forall {Gamma t2 T1 T2 sigma},
      jt_term Gamma t2 T1 ->
      List.Forall2 jt_result_value sigma Gamma ->
      jt_cont (TFun T1 T2) (CAppR t2 sigma) T2
  | JTCClosure:
    forall {Gamma_cl sigma_cl T1 T2 tcl},
      jt_value Gamma_cl (Lam tcl) (TFun T1 T2) ->
      List.Forall2 (jt_result_value) sigma_cl Gamma_cl ->
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
    List.Forall2 (jt_result_value) sigma Gamma ->
    jt_term Gamma t T1 ->
    jt_conts T1 kappa T2 ->
    jt_state (mode_eval t kappa sigma) T2
| JTmode_cont:
  forall r T1 T2 kappa,
    jt_result_value r T1 ->
    jt_conts T1 kappa T2 ->
    jt_state (mode_cont kappa r) T2
. 


(** Automation of typing judgement: smart inversion **)
Require Import Ltac2.Ltac2.
Set Default Proof Mode "Classic".


(** Specialized tactics to invert typing judgement if one argument is a known constructor. *)
Ltac2 invert_jt () :=
  match! goal with
  | [ h: jt_term _ ?c _ |- _ ] => smart_inversion c h
  | [ h: jt_value _ ?c _ |- _ ] => smart_inversion c h
  | [ h: jt_value _ _ ?c |- _ ] => smart_inversion c h
  | [ h: jt_result_value _ ?c |- _ ] => smart_inversion c h
  | [ h: jt_cont _ ?c _ |- _ ] => smart_inversion c h
  | [ h: jt_conts _ ?c _ |- _ ] => smart_inversion c h
  | [ h: jt_state ?c _ |- _ ] => smart_inversion c h
  | [ h: List.Forall _ ?c |- _ ] => smart_inversion c h
  | [ h: List.Forall2 _ ?c _ |- _ ] => smart_inversion c h
  | [ h: List.Forall2 _ _ ?c |- _ ] => smart_inversion c h
end.

Ltac invert_jt := ltac2:(invert_jt ()).


(** Specialiazed tactic to apply econstructor when possible. *)
Ltac2 econs_jt () :=
  match! goal with
  | [ |- jt_term _ _ _] => econstructor
  | [ |- jt_value _ _ _] => econstructor
  | [ |- jt_result_value _ _] => econstructor
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
  (* Most of the cases are easilly handle by the automation. *)
  all: intros; repeat invert_jt; repeat (econs_jt; eauto).

  (** One case is left. It requires an external lemma about lists. *)
  { pose proof (Forall2_nth_error_Some H4); eauto. }
Qed.


(** To state the progress lemma, we need to represent "final states". It is, as stated in the paper, states in cont mode with an empty stack. *)

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
  all: intros; repeat invert_jt.

  (** Most of the cases are easily handled using the automation *)
  all: try solve [left; eexists; econstructor; eauto].
  all: try solve [right; simpl; eauto].

  (* One case is left that requires an additional lemma on lists. *)
  { pose proof (Forall2_nth_error_Some_right H3 (eq_sym H1)); unpack.
    left; eexists; econstructor; eauto.
  }
Qed.

(*** Typing for tss ***)

(* The progress lemma only holds for closed terms. This is expressed using the fv (free variable) definition. *)
Definition fv k t :=
  t.[upn k (ren (+1))] = t.

Definition fvv k v :=
  subst_value (upn k (ren (+1))) v = v.


Lemma fv_Lam_eq:
  forall k t,
  fvv k (Lam t) <-> fv (S k) t.
Proof.
  unfold fv, fvv. intros. asimpl. split; intros.
  { injections. eauto. }
  { f_equal. unpack. eauto. }
Qed.


Lemma fv_Value_eq:
  forall k v,
  fv k (Value v) <-> fvv k v.
Proof.
  unfold fv, fvv. intros; asimpl; split; intros.
  { injections; eauto. }
  { f_equal; eauto. }
Qed.

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


(** Main progress lemma for continuation-based semantics. *)
Theorem progress_trad t1:
  forall Gamma T,
    jt_term Gamma t1 T ->
    fv 0 t1 ->
    (exists t2, sred t1 t2) \/ (match t1 with |Value _ => True | _ => False end).
Proof.
  induction 1.

  (** Using inversion on each of the cases *)
  all: intros; repeat invert_jt.
  all: unzip; subst.

  (** Less cases than in the cbss case. *)
  all: try solve [left; eexists; econstructor; eauto].
  all: try solve [right; simpl; eauto].
  
  { rewrite fv_Var_eq in *. lia. }

  { (** Manual handling of the proof here. *)
    rewrite fv_App_eq in *; unpack.
    pose proof (IHjt_term1 H1).
    pose proof (IHjt_term2 H2).
    unzip; subst.
    all: intros; repeat invert_jt.
    (* automation here depends on the order of the constructors. *)
    all: try solve [left; eexists; econstructor; eauto].
    { (* The automation does not even work for half the cases *)
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


(* The preservation lemma is a bit hard to show, because we use lists to represent the typing judgements. This mean that we need to show explicit lemma with respect to substitutions. It is technical but the proof are rather classical. *)

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


Lemma upn_k_sigma_x':
  forall k sigma x,
  x >= k ->
  x < List.length sigma + k ->
  upn k (fun n => soe sigma n) x = lift k ((fun n => soe sigma n) (x - k)).
Proof.
  induction k; intros; asimpl.
  { repeat rewrite Nat.sub_0_r. reflexivity. }
  { destruct x; asimpl.
    { lia. }
    { rewrite IHk by lia.
      assert (Hx: x - k < List.length sigma) by lia.
      remember (List.nth_error sigma (x - k)) as o; induction o.
      { rewrite SubstLemmas_term4. autosubst. }
      { exfalso.
        eapply List.nth_error_Some; eauto.
      }
    }
  }
Qed.


(* The weakening lemma is precise. We add new variables in the middle of the typing environement. THis requires to rename the terms, making a space between variables of the first list, and the second list. This lemma is then modified for application when the first list is empty (jt_weakening_0). It is the second version that is used in the proof, but we need to show this version to get all the correct induction hypothesis. *)

Lemma jt_weakening:
  forall Gamma1 Gamma3 t T,
    jt_term (Gamma1 ++ Gamma3) t T ->
    forall Gamma2,
      jt_term (Gamma1 ++ Gamma2 ++ Gamma3) (
        rename_term (
          fun x =>
            if x <? List.length Gamma1 then x
            else x + List.length Gamma2
      )%nat t) T.
Proof.
  intros Gamma1 Gamma3 t T.
  revert t Gamma1 Gamma3 T.
  eapply (term_value_induction_term
    (fun t => forall Gamma1 Gamma3  T,
    jt_term (Gamma1 ++ Gamma3) t T ->
    forall Gamma2,
      jt_term (Gamma1 ++ Gamma2 ++ Gamma3) (rename_term (
          fun x =>
            if x <? List.length Gamma1 then x
            else x + List.length Gamma2
      )%nat t) T)
    (fun v => forall Gamma1 Gamma3  T,
      jt_value (Gamma1 ++ Gamma3) v T ->
      forall Gamma2,
        jt_value (Gamma1 ++ Gamma2 ++ Gamma3) (rename_value (
            fun x =>
              if x <? List.length Gamma1 then x
              else x + List.length Gamma2
        )%nat v) T)).
  all: intros; repeat invert_jt.
  { econstructor.
    rewrite List.nth_error_app in H2.
    destruct (Nat.ltb_spec x (Datatypes.length Gamma1)).
    { rewrite List.nth_error_app1; try lia; eauto. }
    { do 2 (rewrite List.nth_error_app2; try lia); eauto.
      rewrite H2; f_equal; lia.
    }
  }
  { asimpl; econstructor; eauto. }
  { econstructor; eauto. }
  { econstructor. fold rename_term.
    replace (upren
    (fun x : var =>
     if (x <? Datatypes.length Gamma1)%nat then x else x + Datatypes.length Gamma2)) with  (fun x : var =>
     if (x <? Datatypes.length (T1::Gamma1))%nat then x else x + Datatypes.length Gamma2)
    .
    {
      rewrite List.app_comm_cons.
      eapply H; eauto.
    }

    { eapply FunctionalExtensionality.functional_extensionality; intros.
      destruct (Nat.ltb_spec x (Datatypes.length (T1::Gamma1))).
      { induction x; simpl in *; eauto.
        destruct (Nat.ltb_spec x (Datatypes.length (Gamma1))); lia.
      }
      { induction x; simpl in *; eauto; try lia.
        destruct (Nat.ltb_spec x (Datatypes.length (Gamma1))); lia.
      }
    }
  }
Qed.


Lemma jt_weakening_0:
  forall Gamma3 t T,
    jt_value Gamma3 t T ->
    forall Gamma2,
      jt_value (Gamma2 ++ Gamma3) (
        rename_value (
          fun x => x + List.length Gamma2
      )%nat t) T.
Proof.
  induction t; intros; repeat invert_jt; econstructor.
  fold rename_term.
  replace (T1 :: Gamma2 ++ Gamma3) with ([T1] ++ Gamma2 ++ Gamma3) by eauto.
  replace (upren (fun x : var => x + Datatypes.length Gamma2)) with (
      fun x =>
        if x <? @List.length type [T1] then x
        else x + List.length Gamma2
  )%nat.
  { eapply jt_weakening; eauto. }

  { apply FunctionalExtensionality.functional_extensionality; intros; simpl.
    induction x; simpl; eauto.
  }
Qed.


(* Strengthening lemma: we can remove variables that do not appear in the term. *)
Lemma jt_strengthening:
  forall t n,
    fv n t ->
    forall Gamma T,
      jt_term Gamma t T ->
      jt_term (List.firstn n Gamma) t T.
Proof.
  intros t.
  eapply (term_value_induction_term
    (fun t => forall n : nat,
    fv n t ->
    forall (Gamma : list type) (T : type),
    jt_term Gamma t T -> jt_term (List.firstn n Gamma) t T)

    (fun v => forall n : nat,
      fvv n v ->
      forall (Gamma : list type) (T : type),
      jt_value Gamma v T -> jt_value (List.firstn n Gamma) v T)
  ); intros.
  { rewrite fv_Var_eq in H; invert_jt.
    econstructor.
    rewrite List.nth_error_firstn.
    rewrite (Bool.reflect_iff _ _ (Nat.ltb_spec0 _ _)) in H.
    rewrite H; eauto.
  }
  { rewrite fv_App_eq in *; unpack.
    invert_jt; econstructor.
    { eapply H; eauto. }
    { eapply H0; eauto. }
  }
  { invert_jt; econstructor.
    rewrite fv_Value_eq in H0.
    eapply H; eauto.
  }
  { invert_jt; econstructor.
    rewrite fv_Lam_eq in H0.
    rewrite <- List.firstn_cons.
    eapply H; eauto.
  }
Qed.

(* Similarlly to the weakening lemma, we need to show a more general version of the substitution lemma because we are using lists instead of explicit functions. A simpler version that is actually used is available just after. *)

Lemma jt_term_subst_technical:
  forall Gamma t T,
  jt_term Gamma t T
  -> forall Gamma1 Gamma2,
  Gamma1 ++ Gamma2 = Gamma
  -> forall sigma Delta,
  (List.Forall2 (jt_value Delta) sigma Gamma2)
  ->
    jt_term (Gamma1 ++ Delta) t.[upn (List.length Gamma1) (fun n => soe sigma n)] T.
Proof.
  intros Gamma t.
  revert t Gamma.
  eapply (term_value_induction_term
    (fun t =>
      forall Gamma T,
        jt_term Gamma t T ->
        forall Gamma1 Gamma2,
          Gamma1 ++ Gamma2 = Gamma ->
          forall sigma Delta,
            (List.Forall2 (jt_value Delta) sigma Gamma2) ->
            jt_term (Gamma1 ++ Delta) (subst_term (upn (List.length Gamma1) (fun n => soe sigma n)) t) T)
    
    (fun v =>
    forall Gamma T,
      jt_value Gamma v T ->
      forall Gamma1 Gamma2,
        Gamma1 ++ Gamma2 = Gamma ->
        forall sigma Delta,
          (List.Forall2 (jt_value Delta) sigma Gamma2) ->
          jt_value (Gamma1 ++ Delta) (subst_value (upn (List.length Gamma1) (fun n => soe sigma n)) v) T)
  )
  .
  all: asimpl; intros; repeat invert_jt.
  { rewrite List.nth_error_app in H4.
    destruct (Nat.ltb_spec x (Datatypes.length Gamma1)).
    { exploit upn_k_sigma_x; intros.
      { eauto. }
      rewrite H0.
      econstructor.
      rewrite List.nth_error_app1; eauto.
    }
    { learn (Forall2_nth_error_Some_right H1 (eq_sym H4)); unpack.
      learn (Forall2_nth_error_Some H1 _ _ _ H0 (eq_sym H4)).
      
      rewrite <- List.nth_error_app2 in H4; eauto.
      learn (nth_error_Some' (eq_sym H4)).
      learn (List.Forall2_length H1).
      rewrite List.length_app in *.
      rewrite upn_k_sigma_x'; try lia.
      rewrite H0.
      rewrite <- SubstLemmas_term1.
      econstructor.
      fold rename_value.

      replace ((+Datatypes.length Gamma1)) with (fun x : var => x + Datatypes.length Gamma1).

      { eapply jt_weakening_0; eauto. }

      { clear; eapply FunctionalExtensionality.functional_extensionality; induction x; simpl; eauto; lia. }
    }
  }
  { econstructor.
    { eapply H; eauto. }
    { eapply H0; eauto. }
  }
  { econstructor.
    eapply H; eauto.
  }
  { econstructor.
    exploit H; eauto.
    { rewrite List.app_comm_cons.
      reflexivity.
    }
    { intros.
      simpl in *.
      rewrite fold_up_upn.
      eauto.
    }
  }
Qed.

Lemma jt_term_subst:
  forall Gamma t T, jt_term Gamma t T
  -> forall sigma Delta,
  (List.Forall2 (jt_value Delta) sigma Gamma)
  ->
    jt_term Delta t.[fun n => soe sigma n] T.
Proof.
  intros.
  learn (jt_term_subst_technical Gamma t T H [] Gamma).
  exploit H1; simpl; eauto.
Qed.

(* How that we have the substitution lemma, we can show the preservation of traditional small-step semantics. *)

Theorem preservation_trad t1:
  fv 0 t1 ->
  forall t2,
    sred t1 t2 ->
    forall Gamma T,
      jt_term Gamma t1 T ->
      jt_term Gamma t2 T.
Proof.
  intros Hfv.
  induction 1; intros; repeat invert_jt; repeat econs_jt; eauto.
  { unfold subst.
    replace (Value v .: ids) with (fun n => soe [v] n).
    2: {
      eapply FunctionalExtensionality.functional_extensionality.
      induction x; simpl; eauto.
      { rewrite List.nth_error_nil; repeat f_equal; lia. }
    }
    eapply jt_term_subst.
    { exploit jt_strengthening; [|eapply H4|intros].
      { rewrite fv_App_eq in Hfv; unpack.
        rewrite fv_Value_eq in H.
        rewrite fv_Lam_eq in H.
        eauto.
      }
      { simpl in *.
        eapply H.
      }
    }
    { repeat (econstructor; eauto). } 
  }
  { rewrite fv_App_eq in *; unpack. eapply IHsred; eauto. }
  { rewrite fv_App_eq in *; unpack; eapply IHsred; eauto. }
Qed.


(*** Determinism of the relation ***)

Theorem cred_deterministic:
  forall s1 s2, cred s1 s2 -> forall s2', cred s1 s2' -> s2 = s2'.
Proof.
  induction 1; inversion 1; subst; simpl in *; eauto.
  { rewrite H in H5; inj; eauto. }
Qed.


(* Even though we define small-step reduction using an explicit Value, we still have conflict between the different rules. Moreover, if we change the order of the different reduction rule, the proof changes. *)

Theorem sred_deterministic:
  forall t1 t2, sred t1 t2 -> forall t2', sred t1 t2' -> t2 = t2'.
Proof.
  induction 1; inversion 1; subst; simpl in *; eauto.
  { inversion H3; subst; tryfalse. }
  { inversion H3; subst; tryfalse. }
  { inversion H; subst; tryfalse. }
  { repeat f_equal. eapply IHsred. eauto. }
  { inversion H4; subst; tryfalse. }
  { inversion H; subst; tryfalse. }
  { inversion H; subst; tryfalse. }
  { repeat f_equal. eapply IHsred. eauto. }
Qed.


(** Equivalence between tss and cbss **)

(* We first define the reconstruction function to reconstruct the terms from a given state. We then state and show the equivalence between semantics. *)

Fixpoint value_of_result_value v :=
  match v with
  | Closure t sigma =>
    Lam t.[up (fun n => soe (List.map value_of_result_value sigma) n)]
  end.


Definition reconstruct_cont
  (t: term)
  (k: cont)
  : term :=
  match k with
  | CAppR t2 sigma =>
    App t t2.[(fun n => soe (List.map value_of_result_value sigma) n)]
  | CClosure t_cl sigma_cl =>
    App (Value (Lam t_cl.[up (fun n => soe (List.map value_of_result_value sigma_cl) n)])) t
  end.

Definition reconstruct_conts
  (kappa: list cont)
  : term -> term :=
  List.fold_left reconstruct_cont kappa.

Definition reconstruct_state (s: state): term :=
  match s with
  | mode_eval t stack env =>
    reconstruct_conts stack t.[(fun n => soe (List.map value_of_result_value env) n)]
  | mode_cont stack r =>
    reconstruct_conts stack (Value (value_of_result_value r))
  end.

(* This lemma is key in the proof. It permit to decompose the reconstruction of a continution into its different parts. *)
Lemma reconstruct_conts_app:
  forall kappa1 kappa2 p,
    reconstruct_conts (kappa1 ++ kappa2) p
    = reconstruct_conts kappa2 (reconstruct_conts kappa1 p).
Proof.
  intros.
  unfold reconstruct_conts.
  rewrite List.fold_left_app; eauto.
Qed.


(* We first show cred => sred. For that, we use the following contextual reduction lemma. *)

Theorem sred_reconstruct_conts: forall kappa t t',
  sred t t' ->
  sred
    (reconstruct_conts kappa t)
    (reconstruct_conts kappa t')
.
Proof.
  induction kappa as [|k kappa] using List.rev_ind.
  { induction 1; simpl; econstructor; eauto. }
  { induction k; intros t t' Htt'.

    all: pose proof (IHkappa _ _ Htt').
    all: repeat rewrite reconstruct_conts_app;
    simpl; unfold reconstruct_cont;  simpl.
    
    all: try econstructor; eauto.
  }
Qed.


Theorem star_sred_reconstruct_conts: forall kappa t t',
  star sred t t' ->
  star sred
    (reconstruct_conts kappa t)
    (reconstruct_conts kappa t')
.
Proof.
  induction 1; econstructor; eauto using sred_reconstruct_conts.
Qed.

(* We then show a simulation theorem between cred and sred. *)
Theorem simulation_cred_sred:
  forall s1 s2,
    cred s1 s2 ->
    star sred (reconstruct_state s1) (reconstruct_state s2).
Proof.
  intros s1 s2 Hs1s2'.
  pose proof (Hs1s2') as Hs1s2.
  induction Hs1s2'; try induction o.
  all: simpl.
  all: apply star_sred_reconstruct_conts.
  { rewrite List.nth_error_map.
    rewrite H.
    simpl.
    apply star_refl.
  }
  { eapply star_refl. }
  { eapply star_refl. }
  { eapply star_refl. }
  { eapply star_step; [econstructor|].
    eapply star_refl_eq.
    rewrite subst_comp.
    f_equal.
    eapply FunctionalExtensionality.functional_extensionality; clear; induction x; asimpl; eauto.
  }
Qed.


(*** From sred to cred ***)


(* For the other side, we define the append_stack operator, that append a continuation to a state. It correspond to the ++ operator in the paper. *)

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

Lemma reconstruct_state_append_stack {s kappa}:
  reconstruct_state (append_stack s kappa) =
  reconstruct_conts kappa (reconstruct_state s).
Proof.
  induction s; simpl; unfold reconstruct_conts; eapply List.fold_left_app.
Qed.

(* inverison lemmas about reconstruct_conts. We could have define reconstruct_conts an inductive type to get those inversion for free, like we did in the paper when defining the ~ invariant in the if-then-else translation. *)

Lemma inv_reconstruct_cont_eq_app {kappa' t t1 t2}:
  reconstruct_conts kappa' t = App t1 t2 ->
  (kappa' = [] /\ t = App t1 t2) \/
  (exists t' sigma kappa,
    kappa' = kappa ++ [CAppR t' sigma] /\
    t'.[(fun n => soe (List.map value_of_result_value sigma) n)] = t2 /\
    reconstruct_conts kappa t = t1
  ) \/
  (exists t' sigma kappa,
    kappa' = kappa ++ [CClosure t' sigma] /\
    ((Value (Lam t')).[(fun n => soe (List.map value_of_result_value sigma) n)]) = t1 /\
    reconstruct_conts kappa t = t2
  ).
Proof.
  induction kappa' as [|k kappa IHkappa] using List.rev_ind; simpl; intros.
  { left; eauto. }
  { right.
    rewrite reconstruct_conts_app in *.
    induction k; simpl in *; repeat injections; tryfalse.
    { left; repeat eexists; eauto. }
    { right; repeat eexists; eauto. }
  }
Qed.

Lemma inv_reconstruct_cont_eq_var {kappa' t x}:
  reconstruct_conts kappa' t = Var x ->
  (kappa' = [] /\ t = Var x).
Proof.
  induction kappa' as [|k kappa IHkappa] using List.rev_ind; simpl; intros.
  { eauto. }
  { rewrite reconstruct_conts_app in *.
    induction k; simpl in *; repeat injections; tryfalse.
  }
Qed.

Lemma inv_reconstruct_cont_eq_value {kappa' t v}:
  reconstruct_conts kappa' t = Value v ->
  (kappa' = [] /\ t = Value v).
Proof.
  induction kappa' as [|k kappa IHkappa] using List.rev_ind; simpl; intros.
  { eauto. }
  { rewrite reconstruct_conts_app in *.
    induction k; simpl in *; repeat injections; tryfalse.
  }
Qed.

Lemma info_our_subst_value_or_ids sigma:
  (forall x, (exists v, (fun n : var =>
  match List.nth_error (List.map value_of_result_value sigma) n with
  | Some t => Value t
  | None =>
    ids (n - Datatypes.length (List.map value_of_result_value sigma))
  end) x = Value v) \/ exists n, (fun n : var =>
  match List.nth_error (List.map value_of_result_value sigma) n with
  | Some t => Value t
  | None =>
    ids (n - Datatypes.length (List.map value_of_result_value sigma))
  end) x = ids n).
Proof.
  intros.
  learn (@nth_error_alt_def _ (List.map value_of_result_value sigma) x).
  induction (Nat.ltb_spec x (Datatypes.length (List.map value_of_result_value sigma))); unpack.
  { rewrite H; eauto. }
  { rewrite H; eauto. }
Qed.

Lemma inv_subst_term_eq_App { t sigma t1' t2'}:
  (forall x, (exists v, sigma x = Value v) \/ exists n, sigma x = ids n) ->
  subst_term sigma t = App t1' t2' ->
  exists t1 t2,
    t = App t1 t2.
Proof.
  induction t; simpl; intros; injections; tryfalse.
  { exfalso.
    destruct (H x); unpack; unfold ids in *; unfold Ids_term in *; tryfalse.
  }
  { repeat eexists; eauto. }
Qed.

Lemma inv_subst_term_eq_Value { t sigma v'}:
  subst_term sigma t = Value v' ->
  (exists x, t = Var x /\ sigma x = Value v') \/
  (exists v, t = Value v).
Proof.
  induction t; simpl; intros; injections; tryfalse.
  { intros; left; eexists; repeat split; eauto. }
  { right; repeat eexists; eauto. }
Qed.

Lemma inv_subst_value_eq_Lam { v sigma t'}:
  subst_value sigma v = Lam t' ->
  exists t, v = Lam t.
Proof.
  induction v; simpl; intros; injections; tryfalse.
  { repeat eexists; eauto. }
Qed.

Lemma inv_soe_value {sigma v x}:
  soe sigma x = Value v ->
  exists t, List.nth_error sigma x = Some t.
Proof.
  intros.
  induction (List.nth_error sigma x).
  { eauto. }
  { unfold ids, Ids_term in H. tryfalse. }
Qed.

Lemma inv_option_map_Some {A B} {f: A -> B}{o v'}:
  option_map f o = Some v' ->
  exists v, o = Some v.
Proof.
  intro.
  induction o.
  { eauto. }
  { simpl in H; tryfalse. }
Qed.

Lemma inv_option_map_None {A B} {f: A -> B} {o}:
  option_map f o = None ->
  o = None.
Proof.
  intro.
  induction o.
  { simpl in H; tryfalse. }
  { eauto. }
Qed.

Lemma inv_value_of_result_value_Lam {v t'}:
  value_of_result_value v = Lam t' ->
  exists t sigma, v = Closure t sigma.
Proof.
  induction v; simpl; eauto.
Qed.



Lemma inv_tail_eq {A: Type} {t1: A} {l t2} :
  [t1] = l ++ [t2] ->
  l = [] /\ t1 = t2
.
Proof.
  replace ([t1]) with ([] ++ [t1]) by eauto.
  intros.
  learn (List.app_inj_tail _ _ _ _ H); injections; unpack; subst; split; eauto.
Qed.

(* Debug utility. It is possible to use it to write learn (ok "test") to add a new hypothesis in the context. *)
Inductive ok: string -> forall (A: Type), A -> Prop :=
  OK: forall s: string, forall A: Type, forall a: A, ok s A a.

Theorem simulation_sred_cred:
  forall t1 t2,
    sred t1 t2 ->
    forall s1,
      reconstruct_state s1 = t1 ->
      exists s2,
      reconstruct_state s2 = t2 /\ star cred s1 s2.
Proof.
Ltac inversions := 
  (* Try to apply every single inversion define above. *)
  (match goal with
    | [h: reconstruct_state ?s = _ |- _] =>
      induction s; simpl reconstruct_state in h
    | [h: reconstruct_conts _ _ = App _ _ |- _] =>
      learn (inv_reconstruct_cont_eq_app h); unzip; subst; simpl reconstruct_conts in h
    | [h: reconstruct_conts _ _ = Value _ |- _] =>
      learn (inv_reconstruct_cont_eq_value h); unzip; subst; simpl reconstruct_conts in h
    | [h: reconstruct_conts _ _ = Var _ |- _] =>
      learn (inv_reconstruct_cont_eq_var h); unzip; subst; simpl reconstruct_conts in h
    | [h: reconstruct_conts (_ ++ _) _ = _ |- _] =>
      rewrite reconstruct_conts_app in h
    | [h: reconstruct_conts [_] _ = _ |- _] =>
      simpl in h
    | [h: [_] = ?kappa ++ [_] |- _ ] => 
      learn (inv_tail_eq h); unzip; subst
    | [h: _.[_] = _ |- _] =>
      unfold subst in h; unfold Subst_term in h
    | [h: subst_term _ _ = App _ _ |- _] =>
      learn (inv_subst_term_eq_App (info_our_subst_value_or_ids _) h); unzip; subst; simpl in h
    | [h: subst_term _ _ = Value _ |- _] =>
      learn (inv_subst_term_eq_Value h); unzip; subst; simpl in h
    | [h: subst_value _ _ = Lam _ |- _] =>
      learn (inv_subst_value_eq_Lam h); unzip; subst; simpl in h
    | [h: soe _ _ = Value _ |- _] =>
      learn (inv_soe_value h); unzip; subst; simpl in h
    | [h: List.nth_error _ _ = Some _ |- _] =>
      rewrite h in *
    | [h: List.nth_error _ _ = None |- _] =>
      rewrite h in *
    | [h: List.nth_error (List.map _ _) _ = Some _ |- _] =>
      rewrite List.nth_error_map in h;
      learn (inv_option_map_Some h); unzip; subst; simpl in h
    | [h: List.nth_error (List.map _ _) _ = None |- _] =>
      rewrite List.nth_error_map in h;
      learn (inv_option_map_None h); unzip; subst; simpl in h
    | [h: value_of_result_value _ = Lam _ |- _] =>
      learn (inv_value_of_result_value_Lam h); unzip; subst; simpl in h
    end; injections; subst; tryfalse).


  (* This tactic rename states/continuations into the same names. *)
  Ltac rename_all := 
    match goal with
    | [ |- exists _, _ /\ star cred S(?t, [?k0], ?env) _] =>
      pose (s :=S(t, [], env));
      pose (k := k0)
    | [ |- exists _, _ /\ star cred S(?t, ?kappa ++ [?k0], ?env) _] =>
      pose (s :=S(t, kappa, env));
      pose (k := k0)
    | [ |- exists _, _ /\ star cred C(?w, [?k0]) _] =>
      pose (s :=C(w, []));
      pose (k := k0)
    | [ |- exists _, _ /\ star cred C(?w, ?kappa ++ [?k0]) _] =>
      pose (s :=C(w, kappa));
      pose (k := k0)
    end.

  induction 1.
  { (* base case where the computation is happening right here, right now *)
    intros; repeat inversions.
    all:
      repeat (try match goal with
      |  _ => eapply star_step_prop; [solve[repeat econstructor; eauto]|]

      (* If it is not possible to advance, try a few things *)
      | [|- exists _, _ /\ star cred S( Value ?v, _, _) _] =>
        learn (OK "induction on value" _ v);
        induction v
      | [|- exists _, _ /\ star cred C( ?v, _) _] =>
        learn (OK "induction on value" _ v);
        induction v
      end)
      .
    
    all: cleanup.
    all: eapply star_refl_prop.
    all: fold Subst_term; fold (@subst term _).

    all: rewrite subst_comp; simpl.
    all: clear; f_equal; apply FunctionalExtensionality.functional_extensionality; induction x; asimpl; eauto.
  }
  { intros; repeat inversions; cleanup.
    
    all: repeat (eapply star_step_prop; [solve[repeat econstructor; eauto]|]).

    all: rename_all.

    all: exploit (IHsred s); [solve[simpl; fold Subst_term; fold (@subst term _); eauto]|intros; unpack].
    all: repeat match goal with
      [h: star cred _ _ |- _] =>
      learn (@star_cred_append_stack s _ h [k])
    end.
    all: unfold s in *; unfold k in *; simpl append_stack in *.
    all: eapply star_trans_prop; [solve[eauto]|].

    all: eapply star_refl_prop.
    all: rewrite reconstruct_state_append_stack; simpl reconstruct_conts.
    all: repeat f_equal; eauto.
  }

  { intros.
    lock H.
    repeat inversions; cleanup.
   
    all: repeat (eapply star_step_prop; [solve[repeat econstructor; eauto]|]).

    all: rename_all.
    all: try solve [exploit (IHsred s); [solve[simpl; fold Subst_term; fold (@subst term _); eauto]|intros; unpack];
    repeat match goal with
      [h: star cred _ _ |- _] =>
      learn (@star_cred_append_stack s _ h [k])
    end;
    unfold s in *; unfold k in *; simpl append_stack in *;
    eapply star_trans_prop; [solve[eauto]|];
    eapply star_refl_prop;
    rewrite reconstruct_state_append_stack; simpl reconstruct_conts;
    repeat f_equal; eauto].
    { unlock H.
      simpl in H.
      inversion H.
    }
    { unlock H.
      simpl in H.
      inversion H.
    }
  }
Qed.


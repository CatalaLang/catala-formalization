Require Export Autosubst.Autosubst.
Require Import String.
Require Import Coq.ZArith.ZArith.
Require Import tactics.
Import List.ListNotations.
Require Import common.
Require Import sequences.
Require Import FunInd.

Require Import Coq.Classes.SetoidClass.
Require Import Wellfounded.

Require Import Coq.Program.Equality.

From Equations Require Import Equations.

Set Default Goal Selector "!".


(*** Definitions of terms and continuations for mini-ML ***)


Inductive term :=
  (* Lambda calculus part of the language*)
  | Var (x: var)
  | App (t1 t2: term)
  | Lam (t: {bind term})
  | Value (v: value)

  | If (u t1 t2: term)

with value :=
  | Closure (t: {bind term}) (sigma: list value)
  | Bool (b: bool)
.

#[export] Instance Ids_term : Ids term. derive. Defined.
#[export] Instance Rename_term : Rename term. derive. Defined.
#[export] Instance Subst_term : Subst term. derive. Defined.
#[export] Instance SubstLemmas_term : SubstLemmas term. derive. Qed.

Lemma ids_inj:
  forall x y, ids x = ids y -> x = y.
intros; inj; eauto.
Qed.


(*** Strong induction principle for terms ***)

Fixpoint size_term t := 
  match t with
  | Var _ => 0
  | App t1 t2 => S (size_term t1 + size_term t2)
  | Lam t => S (size_term t)
  | Value v => S (size_value v)
  | If u t1 t2 => S (size_term u + size_term t1 + size_term t2)
  end
with size_value v :=
  match v with
  | Closure t env => S (size_term t + (List.list_sum (List.map size_value env)))
  | Bool _ => 0
  end.

Definition size (x : term + value) :=
  match x with
  | inl t => size_term t
  | inr v => size_value v
  end.


Theorem term_value_induction
: forall {P : term -> Prop} {P0 : value -> Prop}
    {HVar: forall x : var, P (Var x)}
    {HApp: forall t1 : term, P t1 -> forall t2 : term, P t2 -> P (App t1 t2)}
    {HLam: forall t : {bind term}, P t -> P (Lam t)}
    {HValue: forall v : value, P0 v -> P (Value v)}
    {HIf: forall u, P u -> forall t1, P t1 -> forall t2, P t2 -> P (If u t1 t2)}
    {HClosure: forall t,
      P t -> forall sigma, (List.Forall P0 sigma) -> P0 (Closure t sigma)}
    {HBool: forall b, P0 (Bool b)},
    (forall x : term + value, match x with | inl t => P t | inr v => P0 v end).
Proof.
  induction x as [x IHx] using (
    well_founded_induction
      (wf_inverse_image _ nat _ size 
      PeanoNat.Nat.lt_wf_0)).
  { destruct x.
    { destruct t; try first [
        eapply HVar|
        eapply HApp|
        eapply HLam|
        eapply HValue|
        eapply HIf
      ].
      1: eapply (IHx (inl t1)).
      2: eapply (IHx (inl t2)).
      3: eapply (IHx (inl t)).
      4: eapply (IHx (inr v)).
      5: eapply (IHx (inl t1)).
      6: eapply (IHx (inl t2)).
      7: eapply (IHx (inl t3)).
      all: simpl; lia.
    }
    { destruct v; try first [
        eapply HClosure
      ].
      { eapply (IHx (inl t)); simpl; lia. }
      {
        induction sigma; econstructor; eauto.
        { eapply (IHx (inr a)); simpl; lia. }

        eapply IHsigma; intros.
        { eapply IHx. simpl in *; lia. }
      }
      eapply HBool.
    }
  }
Qed.

Theorem term_ind'
  : forall (P : term -> Prop) (P0 : value -> Prop),
      (forall x : var, P (Var x)) ->
      (forall t1 : term, P t1 -> forall t2 : term, P t2 -> P (App t1 t2)) ->
      (forall t : {bind term}, P t -> P (Lam t)) ->
      (forall v : value, P0 v -> P (Value v)) ->
      (forall t,
       P t -> forall sigma, (List.Forall P0 sigma) -> P0 (Closure t sigma)) ->
      (forall u, P u -> forall t1, P t1 -> forall t2, P t2 -> P (If u t1 t2)) ->
      (forall b, P0 (Bool b)) ->
      (forall t : term, P t) /\ (forall v : value, P0 v).
Proof.
  split; intros.
  { unshelve eapply (term_value_induction (inl t)); eauto. }
  { unshelve eapply (term_value_induction (inr v)); eauto. }
Qed.


(*** Syntax for continuations ***)

Inductive cont :=
  | CAppR (t2: term) (sigma: list value) (* [\square t2] *)
  | CClosure (t_cl: {bind term}) (sigma_cl: list value)
  (* [Clo(x, t_cl, sigma_cl) \square] Since we are using De Bruijn indices,
     there is no variable x. *)
  | CIf (t1 t2: term) (sigma: list value) (* [if \square then t1 else t2]*)
.

Inductive result :=
  | RValue (v: value)
.


Inductive state :=
  | mode_eval (e: term) (kappa: list cont) (env: list value)
  | mode_cont (kappa: list cont) (result: result)
.


(*** Continuation step semantics ***)

Inductive cred: state -> state -> Prop :=
  (** Rules related to the lambda calculus *)
  | cred_var: info "cred_var" ->
    forall x kappa sigma v,
    List.nth_error sigma x = Some v ->
    cred
      (mode_eval (Var x) kappa sigma)
      (mode_cont kappa (RValue v))

  | cred_app: info "cred_app" ->
    forall t1 t2 kappa sigma,
    cred
      (mode_eval (App t1 t2) kappa sigma)
      (mode_eval t1 ((CAppR t2 sigma) :: kappa) sigma)

  | cred_clo: info "cred_clo" ->
    forall t kappa sigma,
    cred
      (mode_eval (Lam t) kappa sigma)
      (mode_cont kappa (RValue (Closure t sigma)))

  | cred_arg: info "cred_arg" ->
    forall t2 kappa sigma tcl sigmacl,
    cred
      (mode_cont ((CAppR t2 sigma)::kappa) (RValue (Closure tcl sigmacl)))
      (mode_eval t2 ((CClosure tcl sigmacl)::kappa) sigma)

  | cred_value: info "cred_value" ->
    forall v kappa sigma,
    cred
      (mode_eval (Value v) kappa sigma)
      (mode_cont kappa (RValue v))

  | cred_beta: info "cred_beta" ->
    forall t_cl sigma_cl kappa v,
    cred
      (mode_cont ((CClosure t_cl sigma_cl)::kappa) (RValue v))
      (mode_eval t_cl kappa (v :: sigma_cl))

  | cred_if: info "cred_if" ->
    forall u t1 t2 kappa sigma,
    cred
      (mode_eval (If u t1 t2) kappa sigma)
      (mode_eval u ((CIf t1 t2 sigma)::kappa) sigma)
  
  | cred_if_true: info "cred_if_true" ->
    forall t1 t2 kappa sigma,
    cred
      (mode_cont ((CIf t1 t2 sigma):: kappa) (RValue (Bool true)))
      (mode_eval t1 kappa sigma)
  
  | cred_if_false: info "cred_if_false" ->
    forall t1 t2 kappa sigma,
    cred
      (mode_cont ((CIf t1 t2 sigma):: kappa) (RValue (Bool false)))
      (mode_eval t2 kappa sigma)
.

Coercion App : term >-> Funclass.
(* Notation "'λ.' t" := (Lam t) (at level 50).
Notation "'S(' t , kappa , sigma )" := (mode_eval t kappa sigma).
Notation "'C(' v , kappa )" := (mode_cont kappa v).
Notation "'λ' sigma '.' t " := (Value (Closure t sigma)) (at level 10).
Notation "'λ' sigma '.' t " := (RValue (Closure t sigma)) (at level 10).
Notation "'if' u 'then' t1 'else' t2 'end'" := (If u t1 t2) (at level 10).
Notation "'k_app1' ( t )" := (CAppR t) (at level 50).
Notation "'k_app2' ( t , sigma )" := (CClosure t sigma) (at level 50).
(* Notation "'k_ret' ( sigma )" := (CReturn sigma) (at level 50). *)
Notation "s1 ~> s2" := (cred s1 s2) (at level 20). *)
Definition id_var (n: nat): var := n.
Coercion id_var: nat >-> var.
Coercion Value: value >-> term.
Coercion RValue: value >-> result.
Coercion Bool : bool >-> value.
Coercion Var: var >-> term.


Example example_of_reduction t1 t2:
  star cred
    (mode_eval (If (Value (Bool true)) t1 t2) [] [])
    (mode_eval t1 [] []).
Proof.
  eapply star_step;[econstructor; econstructor|].
  eapply star_step;[econstructor; econstructor|].
  eapply star_step;[econstructor; econstructor|].
  eapply star_refl.
Qed.

(*** small step semantics ***)

Import List.ListNotations.
Open Scope list.

Definition subst_of_env sigma :=
  fun n =>
  match List.nth_error sigma n with
  | None => ids (n - List.length sigma)
  | Some t => Value t
  end
.




Inductive sred: term -> term -> Prop :=
  | sred_lam:
    forall t,
      sred
        (Lam t)
        (Value (Closure t []))
  | sred_beta:
    forall t v sigma',
      sred
        (App (Value (Closure t sigma')) (Value v))
        (t.[subst_of_env (v :: sigma')])
  | sred_app_right:
    forall t sigma u1 u2,
      sred (u1) (u2) ->
      sred
        (App (Value (Closure t sigma)) u1)
        (App (Value (Closure t sigma)) u2)
  | sred_app_left:
    forall t1 t2 u,
      sred (t1) (t2) ->
      sred
        (App t1 u)
        (App t2 u)
  | sred_if_true:
    forall t1 t2,
      sred (If (Value (Bool true)) t1 t2) t1
  
  | sred_if_false:
    forall t1 t2,
      sred (If (Value (Bool false)) t1 t2) t2
  
  | sred_if_cond:
    forall u1 u2 t1 t2,
      sred u1 u2 ->
      sred (If u1 t1 t2) (If u2 t1 t2)
.

Lemma star_sred_app_right:
forall t sigma u1 u2,
  star sred (u1) (u2) ->
  star sred
    (App (Value (Closure t sigma)) u1)
    (App (Value (Closure t sigma)) u2).
Proof.
  induction 1.
  { eapply star_refl. }
  { eapply star_step.
    { econstructor; eauto. }
    { eauto. }
  }
Qed.
Lemma star_sred_app_left:
forall t1 t2 u,
  star sred (t1) (t2) ->
  star sred
    (App t1 u)
    (App t2 u).
Proof.
  induction 1.
  { eapply star_refl. }
  { eapply star_step.
    { econstructor; eauto. }
    { eauto. }
  }
Qed.

Lemma star_sred_if_cond:
forall u1 u2 t1 t2,
  star sred u1 u2 ->
  star sred (If u1 t1 t2) (If u2 t1 t2).
Proof.
  induction 1.
  { eapply star_refl. }
  { eapply star_step.
    { econstructor; eauto. }
    { eauto. }
  }
Qed.



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
  | JTLam:
    forall Gamma t T1 T2,
      jt_term (T1::Gamma) t T2 ->
      jt_term Gamma (Lam t) (TFun T1 T2)
  | JTValue:
    forall Gamma v T,
      jt_value v T ->
      jt_term Gamma (Value v) T
  | JTEIf:
    forall Gamma u ta tb T,
      jt_term Gamma u TBool ->
      jt_term Gamma ta T ->
      jt_term Gamma tb T ->
      jt_term Gamma (If u ta tb) T
with jt_value:
   value -> type -> Prop :=
  | JTValueClosure:
    forall  tcl sigma_cl Gamma_cl T1 T2,
      List.Forall2 jt_value sigma_cl Gamma_cl ->
      jt_term Gamma_cl (Lam tcl) (TFun T1 T2) ->
      jt_value (Closure tcl sigma_cl) (TFun T1 T2)
  | JTValueBool:
    forall b,
      jt_value (Bool b) TBool
.

(** Expanding the rules of typing to continuation-bases semantics requires to define the typing jugment for continuations. This typing judgement have two additional informations: the "hole" type, and the "environement" in the hole. Both are required with our presentation since the hole is filed when the jt_state judgement is defined. *)

Inductive jt_result: result -> type -> Prop := 
  | JTRValue:
    forall v T,
    jt_value v T ->
    jt_result (RValue v) T.

Inductive jt_cont:
  type -> cont -> type -> Prop :=
  | JTCAppR:
    forall {Gamma sigma t2 T1 T2},
      jt_term Gamma t2 T1 ->
      List.Forall2 jt_value sigma Gamma ->
      jt_cont (TFun T1 T2) (CAppR t2 sigma) T2
  | JTCClosure:
    forall {Gamma_cl sigma_cl T1 T2 tcl},
      jt_term Gamma_cl (Lam tcl) (TFun T1 T2) ->
      List.Forall2 jt_value sigma_cl Gamma_cl ->
      jt_cont T1 (CClosure tcl sigma_cl) T2
  | JTCIf:
    forall Gamma T sigma ta tb,
      jt_term Gamma ta T ->
      jt_term Gamma tb T ->
      List.Forall2 jt_value sigma Gamma ->
      jt_cont TBool (CIf ta tb sigma) T
.

Inductive jt_conts:  type -> list cont -> type -> Prop :=
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
    List.Forall2 (jt_value) sigma Gamma ->
    jt_term Gamma t T1 ->
    jt_conts T1 kappa T2 ->
    jt_state (mode_eval t kappa sigma) T2
| JTmode_cont:
  forall r T1 T2 kappa,
    jt_result r T1 ->
    jt_conts T1 kappa T2 ->
    jt_state (mode_cont kappa r) T2
. 



Require Import Ltac2.Ltac2.
Set Default Proof Mode "Classic".


Lemma jt_conts_app { kappa1 kappa2 T1 T3 }:
  jt_conts T1 (kappa1 ++ kappa2) T3 ->
  exists T2,
  jt_conts T1 kappa1 T2
  /\ jt_conts T2 kappa2 T3
.
Proof.
  revert kappa2 T1 T3.
  induction kappa1; simpl; intros kappa2 T1 T3.
  { intros; repeat eexists.
    { econstructor. }
    { eauto. }
  }
  { inversion 1; subst.
    learn (IHkappa1 _ _ _ H5); unpack.
    repeat eexists.
    { econstructor; eauto. }
    { eauto. }
  }
Qed.

(** Specialized tactics to invert typing judgement if one argument is a known constructor. *)
Ltac2 inv_jt () :=
  match! goal with
  | [ h: jt_term _ ?c _ |- _ ] => smart_inversion c h
  | [ h: jt_value ?c _ |- _ ] => smart_inversion c h
  | [ h: jt_value _ ?c |- _ ] => smart_inversion c h
  | [ h: jt_cont _ ?c _ |- _ ] => smart_inversion c h
  | [ h: jt_conts _ ?c _ |- _ ] => smart_inversion c h
  | [ h: jt_conts _ (_ ++ _) _ |- _ ] =>
    let p := Control.hyp h in
    let l := Fresh.in_goal @L in
    Std.assert (Std.AssertValue l constr:(jt_conts_app $p));
    Std.clear [h]
  | [ h: jt_state ?c _ |- _ ] => smart_inversion c h
  | [ h: jt_result ?c _ |- _ ] => smart_inversion c h
  | [ h: jt_result _ ?c |- _ ] => smart_inversion c h
  | [ h: List.Forall _ ?c |- _ ] => smart_inversion c h
  | [ h: List.Forall2 _ ?c _ |- _ ] => smart_inversion c h
  | [ h: List.Forall2 _ _ ?c |- _ ] => smart_inversion c h
end.

Ltac2 rename_jt () := 
  let hyps := Control.hyps () in
  let rename h := 
    let ht := Fresh.in_goal @HT0 in
    Std.rename [h, ht]
  in
  List.iter (fun (h, _, t) =>
    match! t with
    | jt_conts _ _ _ _ _ => rename h
    | jt_term _ _ _  => rename h  
    | jt_cont _ _ _ _ _ => rename h  
    | jt_state _ _ _ => rename h 
    | jt_result _ _ => rename h 
    | List.Forall2 jt_value _ _ => rename h  
    | _ => ()
    end
  ) (List.rev hyps)
.

Ltac inv_jt := ltac2:(inv_jt (); rename_jt ()); unpack.

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
  all: intros; repeat inv_jt; repeat econstructor; eauto.

  (** One case is left. It requires an external lemma. *)
  { pose proof (Forall2_nth_error_Some HT0); eauto. }
Qed.

Definition is_mode_cont s :=
  match s with
  | mode_cont _ _ => True
  | _ => False
  end.

Definition stack s :=
  match s with
  | mode_eval _ k _ => k
  | mode_cont k _ => k
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
    (exists s2, cred s1 s2) \/ (is_mode_cont s1 /\ stack s1 = nil).
Proof.
  (* Precise case analysis. *)
  induction s1 as [t kappa env|kappa r]; [induction t|(induction kappa as [|k kappa]; [|induction k]); induction r].

  

  (** Using inversion on each of the cases *)
  all: intros; repeat inv_jt.


  (** To add the boolean case, we need to further do a case analysis on b in the mode_cont case. *)
  all: try induction b.

  (** Most of the cases are easily handled using the automation *)
  all: try solve [left; eexists; econstructor; eauto].
  all: try solve [right; simpl; eauto].

  (* One case is left that requires an additional lemma on lists. *)
  { pose proof (Forall2_nth_error_Some_right HT0 (eq_sym H1)); unpack.
    left; eexists; econstructor; eauto.
  }
Qed.


Definition fv k t :=
  t.[upn k (ren (+1))] = t.

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

Lemma fv_If_eq:
  forall k u t1 t2,
  fv k (If u t1 t2) <-> fv k u /\ fv k t1 /\ fv k t2.
Proof.
  unfold fv. intros. asimpl. split; intros.
  { injections. eauto. }
  { unpack. congruence. }
Qed.

Hint Rewrite fv_Lam_eq fv_App_eq fv_If_eq : fv.


(** Main progress lemma for continuation-based semantics. *)
Theorem progress_trad t1:
  forall Gamma T,
    jt_term Gamma t1 T ->
    Gamma = [] ->
    (exists t2, sred t1 t2) \/ (exists v, t1 = Value v).
Proof.
  induction 1.

  (** Using inversion on each of the cases *)
  all: intros; repeat inv_jt.
  all: unzip; subst.
  
  (** Less cases than in the normal cases. *)
  all: try solve [left; eexists; econstructor; eauto].
  all: try solve [right; simpl; eauto].

  { (* Could be shown in a different lemma. *)
    exfalso.
    induction x; simpl in *; congruence. 
  } 

  { (** Manual handling of the proof here. *)
    pose proof (IHjt_term1 eq_refl).
    pose proof (IHjt_term2 eq_refl).
    unzip; subst.
    all: intros; repeat inv_jt.
    (* automation here depends on the order of the constructors. *)
    all: try solve [left; eexists; econstructor; eauto].
  }
  { (* applying left; eexists, econstructor leads to an unsolvable goal as we are not sure whenever u redices to t2 or is a value. *)
    (* left; eexists; econstructor. *)
    pose proof (IHjt_term1 eq_refl).
    unzip; subst.
    all: intros; repeat inv_jt.

    (* same case analysis as the continutation-based case before *)
    all: try induction b.

    (* the normal proof script can the resume. *)
    all: try solve [left; eexists; econstructor; eauto].
    all: try solve [right; simpl; eauto].
  }
Qed.


(*** Determinism of the relation *)

Theorem cred_deterministic:
  forall s1 s2, cred s1 s2 -> forall s2', cred s1 s2' -> s2 = s2'.
Proof.
  induction 1; inversion 1; subst; simpl in *; eauto.
  { rewrite H0 in H7; inj; eauto. }
Qed.

Theorem sred_deterministic:
  forall t1 t2, sred t1 t2 -> forall t2', sred t1 t2' -> t2 = t2'.
Proof.
  induction 1; inversion 1; subst; simpl in *; eauto.
  { inversion H4. }
  { inversion H3. }
  { inversion H. }
  { repeat f_equal. eapply IHsred. eauto. }
  { inversion H4. }
  { inversion H. }
  { inversion H. }
  { repeat f_equal. eapply IHsred. eauto. }
  { inversion H4. }
  { inversion H4. }
  { inversion H. }
  { inversion H. }
  { repeat f_equal. eapply IHsred. eauto. }
Qed.

(** Simple translation of [if t then ta else tb] into [if (if t then false else true) then tb else ta] *)

Module trans1.
Fixpoint trans_term t :=
  match t with
  | Var x => Var x
  | App t1 t2 => App (trans_term t1) (trans_term t2)
  | Lam t => Lam (trans_term t)
  | Value v => Value (trans_value v)
  | If u t1 t2 =>
    If (If (trans_term u) (Value (Bool false)) (Value (Bool true)))
       (trans_term t2) (trans_term t1)
  end
with trans_value v :=
  match v with
  | Closure t sigma =>
    Closure (trans_term t) (List.map trans_value sigma)
  | Bool b => Bool b
  end
.

Fixpoint trans_conts (kappa: list cont): list cont :=
  match kappa with
  | nil => nil
  | CAppR t2 sigma :: kappa => CAppR (trans_term t2) (List.map trans_value sigma) :: trans_conts kappa
  | CClosure t sigma :: kappa =>
    CClosure (trans_term t) (List.map trans_value sigma) :: trans_conts kappa
  | CIf t1 t2 sigma :: kappa =>
    CIf (Value (Bool false)) (Value (Bool true)) (List.map trans_value sigma)::
    CIf (trans_term t2) (trans_term t1) (List.map trans_value sigma)::
    trans_conts kappa
  end
.

Definition trans_return (r: result): result:=
  match r with
  | RValue v => RValue (trans_value v)
  end.

Definition trans_state (s: state) : state :=
  match s with
  | mode_eval e kappa env =>
    mode_eval (trans_term e) (trans_conts kappa) (List.map trans_value env)
  | mode_cont kappa r =>
    mode_cont (trans_conts kappa) (trans_return r)
  end
.

Theorem correction_continuations:
  forall s1 s2,
  cred s1 s2 ->

  star cred
    (trans_state s1) (trans_state s2).
Proof.
Local Ltac step := (
  try (eapply star_step; [solve
    [ econstructor; simpl; eauto using List.map_nth_error
  ]|]))
.
  induction 1; simpl; repeat step; try eapply star_refl.
Qed.

End trans1.


(*
Module trans2.
Fixpoint trans_term t :=
  match t with
  | Var x => Var x
  | App t1 t2 => App (trans_term t1) (trans_term t2)
  | Lam t => Lam (trans_term t)
  | Value v => Value (trans_value v)
  | If (If u (Value (Bool false)) (Value (Bool true))) t1 t2 =>
    If (trans_term u) (trans_term t2) (trans_term t1)
  | If u t1 t2 =>
    If (trans_term u) (trans_term t1) (trans_term t2)
  end
with trans_value v :=
  match v with
  | Closure t sigma =>
    Closure (trans_term t) (List.map trans_value sigma)
  | Bool b => Bool b
  end
.

(* Where is the fuction eliminator that i want ? Do i need the same thing as below for trans_state ? I belive so. *)

(* Generalized transformation for continuations *)
(* Fixpoint trans_conts (kappa: list cont): list cont :=
  match kappa with
  | nil => nil
  | CAppR t2 :: kappa => CAppR (trans_term t2) :: trans_conts kappa
  | CClosure t sigma :: kappa =>
    CClosure (trans_term t) (List.map trans_value sigma) :: trans_conts kappa
  | CReturn sigma :: kappa =>
    CReturn (List.map trans_value sigma) :: trans_conts kappa
  | CIf (Value (Bool false)) (Value (Bool true)) :: CIf t1 t2 :: kappa =>
    CIf (trans_term t1) (trans_term t2) :: trans_conts kappa
  | CIf t1 t2 :: kappa =>
    CIf (trans_term t1) (trans_term t2) :: trans_conts kappa
  end.

(* Generalized transformation for results *)
Definition trans_return (r: result): result :=
  match r with
  | RValue v => RValue (trans_value v)
  end.

(* Generalized transformation for states with the special If case *)
Definition trans_state (s: state) : state :=
  match s with
  | mode_eval (If b (Value (Bool false)) (Value (Bool true))) (CIf t2 t1::kappa) env =>
    mode_eval (trans_term b) (CIf (trans_term t1) (trans_term t2)::trans_conts kappa) (List.map trans_value env)
  | mode_eval e kappa env =>
    mode_eval (trans_term e) (trans_conts kappa) (List.map trans_value env)
  | mode_cont kappa env r =>
    mode_cont (trans_conts kappa) (List.map trans_value env) (trans_return r)
    end.

End trans2.

(*

Equations f (l : list nat) : list nat :=
f []  := [];
f (cons a (cons b l)) := cons (a+b) (f l);
f (cons a l) := cons a (f l).

*)
*) *)

Module trans3.

Definition with_stack s kappa :=
  match s with
  | mode_cont _ v => mode_cont kappa v
  | mode_eval t _ sigma => mode_eval t kappa sigma
  end.

Definition append_stack s kappa :=
  with_stack s (stack s ++ kappa).
Definition cons_stack s kappa :=
  with_stack s (kappa ++ stack s ).
Definition rev_state (s: state): state :=
  with_stack s (List.rev (stack s))
. 

Set Equations Transparent.

(* we define trans_state to be rev_state \circ trans_state_aux \circ rev_state
to permit more adapted pattern matching. *)

(* Definition total_relation {A : Type} : A -> A -> Prop := fun x y => True.
Axiom wf_total_init : forall {A}, WellFounded (@total_relation A).
#[local]
Remove Hints wf_total_init : typeclass_instances.

#[local]
Instance wf_total_init_compute : forall {A}, WellFounded (@total_relation A).
  exact (fun A => Acc_intro_generator 10 wf_total_init).
Defined. *)

Inductive cong_term: term -> term -> Prop :=
  | cong_if_base {u t1 t2 u' t1' t2'}:
    cong_term u u' ->
    cong_term t1 t1' ->
    cong_term t2 t2' ->
    cong_term
      (If (If u (Value (Bool false)) (Value (Bool true))) t1 t2)
      (If u' t2' t1')
  | cong_Var {x}:
    cong_term (Var x) (Var x)
  | cong_App { t1 t2 t1' t2' }:
    cong_term t1 t1' ->
    cong_term t2 t2' ->
    cong_term (App t1 t2) (t1' t2')
  | cong_Lam { t t' }:
    cong_term t t' ->
    cong_term (Lam t) (Lam t')
  | cong_Value {v v'}:
    cong_value v v' ->
    cong_term (Value v) (Value v')
  | cong_If {u t1 t2 u' t1' t2'}:
    cong_term u u' ->
    cong_term t1 t1' ->
    cong_term t2 t2' ->
    cong_term (If u t1 t2) (If u' t1' t2')
with cong_value: value -> value -> Prop :=
  | cong_Bool {b}:
    cong_value (Bool b) (Bool b)
  | cong_Closure {t sigma t' sigma'}:
    cong_term t t' ->
    List.Forall2 (cong_value) sigma sigma' ->
    cong_value (Closure t sigma) (Closure t' sigma')
.

Function trans_term t :=
  match t with
  | Var x => Var x
  | App t1 t2 => App (trans_term t1) (trans_term t2)
  | Lam t => Lam (trans_term t)
  | Value v => Value (trans_value v)
  | If (If u (Value (Bool false)) (Value (Bool true))) t1 t2 =>
    If (trans_term u) (trans_term t2) (trans_term t1)
  | If u t1 t2 =>
    If (trans_term u) (trans_term t1) (trans_term t2)
  end
with trans_value v :=
  match v with
  | Closure t sigma =>
    Closure (trans_term t) (List.map trans_value sigma)
  | Bool b => Bool b
  end
.

Functional Scheme
  trans_term_ind2 := Induction for trans_term Sort Prop
with
  trans_value_ind2 := Induction for trans_value Sort Prop.


(* Correspondance between trans_term and cong_term*)
Theorem trans_cong_term:
  forall t,
  cong_term t (trans_term t).
Proof.
  intros t.
  eapply trans_term_ind2.
  all: try solve [intros; econstructor; eauto].
  { intros; econstructor; eauto.
    admit "missing case from the induction principle generated by coq, but it is correct".
  }
Abort.

(* Generalization of the equivalence between terms to an equivalence between states. *)


(* In this definition, I choose to not separate the mode_eval and mode_cont when it was possible. I hence used the "append_stack" function. This might pose issues when applying the "econstructor" tactic. *)
Inductive cong_state: state -> state -> Prop :=
  (* Base cases *)
  | cong_mode_eval {t sigma t' sigma'}:
    cong_term t t' ->
    List.Forall2 cong_value sigma sigma' ->
    cong_state
      (mode_eval t [] sigma)
      (mode_eval t' [] sigma')
  
  | cong_mode_cont {v v' }:
    cong_value v v' ->
    cong_state
      (mode_cont [] (RValue v))
      (mode_cont [] (RValue v'))

  (* Normal congruence cases *)
  | cong_CAppR {s s' t t' sigma sigma'}:
    cong_term t t' ->
    cong_state s s' ->
    List.Forall2 cong_value sigma sigma' ->
    cong_state
      (append_stack s [CAppR t sigma])
      (append_stack s' [CAppR t' sigma'])
  | cong_CClosure {s s' t t' sigma sigma'}:
    cong_term t t' ->
    cong_state s s' ->
    List.Forall2 cong_value sigma sigma' ->
    cong_state
      (append_stack s [CClosure t sigma])
      (append_stack s' [CClosure t' sigma'])
  | cong_CIf {s s' t1 t1' t2 t2' sigma sigma'}:
    cong_term t1 t1' ->
    cong_term t2 t2' ->
    cong_state s s' ->
    List.Forall2 cong_value sigma sigma' ->
    cong_state
      (append_stack s [CIf t1 t2 sigma])
      (append_stack s' [CIf t1' t2' sigma'])

  (* Additional cases *)
  | cong_if_stack {s s' t1 t1' t2 t2' sigma0 sigma sigma'} :
    (* Nothing tells me that the environement is the same for both continuations. Hence, i separate them. 
    
    TODO: when the proof is done, change sigma0 into sigma, and check what breaks. *)
    cong_term t1 t1' ->
    cong_term t2 t2' ->
    cong_state s s' ->
    List.Forall2 cong_value sigma sigma' ->
    cong_state
      (append_stack s [CIf false true sigma0; CIf t1 t2 sigma])
      (append_stack s' [CIf t2' t1' sigma'])

  | cong_if_overlap {u u' t1 t1' t2 t2' sigma0 sigma0' sigma sigma'}:
    (* Same comment as above *)
    cong_term u u' ->
    cong_term t1 t1' ->
    cong_term t2 t2' ->
    List.Forall2 cong_value sigma sigma' ->
    List.Forall2 cong_value sigma0 sigma0' ->
    cong_state
      (mode_eval (If u false true) [CIf t1 t2 sigma] sigma0)
      (mode_eval u' [CIf t2' t1' sigma'] sigma0')
.

Lemma mode_eval_cong_state:
  forall { s s'},
    cong_state s s' ->
    forall {t kappa sigma},
    s = mode_eval t kappa sigma ->
    exists t' kappa' sigma', 
      s' = mode_eval t' kappa' sigma'.
Proof.
  induction 1; intros; injections; subst; try solve
  [ repeat econstructor| tryfalse].
  { induction s; simpl in *; tryfalse; injections; subst.
    edestruct IHcong_state; [solve[reflexivity]|]; unpack; subst; simpl.
    repeat econstructor. }
  { induction s; simpl in *; tryfalse; injections; subst.
    edestruct IHcong_state; [solve[reflexivity]|]; unpack; subst; simpl.
    repeat econstructor. }
  { induction s; simpl in *; tryfalse; injections; subst.
    edestruct IHcong_state; [solve[reflexivity]|]; unpack; subst; simpl.
    repeat econstructor. }
  { induction s; simpl in *; tryfalse; injections; subst.
    edestruct IHcong_state; [solve[reflexivity]|]; unpack; subst; simpl.
    repeat econstructor. }
Qed.

(** let's start with the statement we want to show *)


Ltac2 sinv_cong () :=
  match! goal with
  | [ h: cong_term ?c _ |- _ ] => smart_inversion c h
  | [ h: cong_value ?c _ |- _ ] => smart_inversion c h
  | [ h: List.Forall _ ?c |- _ ] => smart_inversion c h
  | [ h: List.Forall2 _ ?c _ |- _ ] => smart_inversion c h
  | [ h: List.Forall2 _ _ ?c |- _ ] => smart_inversion c h
  end.

Ltac sinv_cong := ltac2:(sinv_cong ()).


Lemma append_stack_mode_eval {s k t kappa sigma}:
  append_stack s [k] = mode_eval t kappa sigma ->
  exists kappa',
  kappa = kappa' ++ [k] /\
  s = mode_eval t kappa' sigma
  .
Proof.
  induction kappa using List.rev_ind.
  { intros; exfalso. induction s; simpl in *; tryfalse.
    injections; subst.
    apply (f_equal (@Datatypes.length cont)) in H0; rewrite List.app_length in *; simpl in *.
    lia.
  }
  { intros; induction s; simpl in *; tryfalse.
    repeat injections; subst.
    learn (List.app_inj_tail _ _ _ _ H0); unpack; subst.
    repeat econstructor.
  }
Qed.

Lemma append_stack_mode_cont {s k v kappa}:
  append_stack s [k] = mode_cont kappa v ->
  exists kappa',
  kappa = kappa' ++ [k] /\
  s = mode_cont kappa' v
  .
Proof.
  induction kappa using List.rev_ind.
  { intros; exfalso. induction s; simpl in *; tryfalse.
    injections; subst.
    apply (f_equal (@Datatypes.length cont)) in H0; rewrite List.app_length in *; simpl in *.
    lia.
  }
  { intros; induction s; simpl in *; tryfalse.
    repeat injections; subst.
    learn (List.app_inj_tail _ _ _ _ H0); unpack; subst.
    repeat econstructor.
  }
Qed.

Lemma append_stack_app {s kappa1 kappa2}:
  stack s = kappa1 ++ kappa2 ->
  s = append_stack (with_stack s kappa1) kappa2.
Proof.
  induction s; intros; simpl in *; subst; reflexivity.
Qed.


Lemma app_injective {A: Type} { kappa kappa0 kappa1 kappa2 : list A}:
 Datatypes.length kappa1 = Datatypes.length kappa2 ->
 kappa ++ kappa1 = kappa0 ++ kappa2 ->
 kappa = kappa0 /\ kappa1 = kappa2.
Proof.
Admitted.


Lemma append_stack_inj {kappa1 kappa2}:
  List.length kappa1 = List.length kappa2 ->
  forall {s1 s2},
    append_stack s1 kappa1 = append_stack s2 kappa2 ->
    s1 = s2 /\ kappa1 = kappa2.
Proof.
  induction s1, s2; simpl; intros; tryfalse; injections; subst.
  { split; repeat f_equal; destruct (app_injective H H1); eauto. }
  { split; repeat f_equal; destruct (app_injective H H1); eauto. }
Qed.

Lemma append_stack_all {s}:
  s = append_stack (with_stack s []) (stack s).
Proof.
  induction s; intros; simpl in *; subst; reflexivity.
Qed.


Lemma cong_state_Var {x kappa sigma s'}:
  cong_state (mode_eval (Var x) kappa sigma) s' ->
  exists kappa' sigma',
    List.Forall2 cong_value sigma sigma' /\
    s' = mode_eval (Var x) kappa' sigma'.
Proof.
  induction kappa using List.rev_ind; inversion 1; repeat sinv_cong; subst.
  { repeat eexists; repeat split; eauto. }
  { repeat eexists; repeat split; eauto.
Abort.

Theorem correction_traditional:
  forall s1 s1',
    cong_state s1 s1' ->
    forall s2,
      cred s1 s2 ->  
      exists s2',
        cong_state s2 s2' /\ star cred s1' s2'.
Proof.
  induction 1; inversion 1; subst; try sinv_cong.
  all: repeat (eapply star_step_prop; [solve[econstructor; eauto]|]).
  { learn (Forall2_nth_error_Some_left _ _ _ H0 _ _ H7); unpack.
    eapply star_step_prop; [econstructor; eauto|].
    eapply star_refl_prop; econstructor.
    eapply Forall2_nth_error_Some; eauto.
  }
  { eapply star_refl_prop.
    match goal with [|- cong_state ?s1 ?s2] =>
      rewrite (@append_stack_all s1);
      rewrite (@append_stack_all s2);
      simpl with_stack; simpl stack
    end.
    repeat (econstructor; eauto).
  }
  { eapply star_refl_prop.
    match goal with [|- cong_state ?s1 ?s2] =>
      rewrite (@append_stack_all s1);
      rewrite (@append_stack_all s2);
      simpl with_stack; simpl stack
    end.
    repeat (econstructor; eauto).
  }
  { eapply star_refl_prop.
    match goal with [|- cong_state ?s1 ?s2] =>
      rewrite (@append_stack_all s1);
      rewrite (@append_stack_all s2);
      simpl with_stack; simpl stack
    end.
    repeat (econstructor; eauto).
  }
  { eapply star_refl_prop.
    repeat (econstructor; eauto).
  }
  { eapply star_refl_prop.
    match goal with [|- cong_state ?s1 ?s2] =>
      rewrite (@append_stack_all s1);
      rewrite (@append_stack_all s2);
      simpl with_stack; simpl stack
    end.
    repeat (econstructor; eauto).
  }
  { learn (append_stack_mode_eval (eq_sym H3)); unpack; subst.
    eapply star_refl_prop.
    match goal with [|- cong_state ?s1 ?s2] =>
      try (erewrite (@append_stack_app s1); [|solve[simpl; eauto]]);
      try (erewrite (@append_stack_app s2); [|solve[simpl; eauto]]);
      simpl with_stack; simpl stack
    end.
    repeat (econstructor; eauto).
    admit "use H0 to derive information about s'. For exmeple, the term is the same. and since H1.".
  }
  { eapply star_refl_prop.
    match goal with [|- cong_state ?s1 ?s2] =>
      rewrite (@append_stack_all s1);
      rewrite (@append_stack_all s2);
      simpl with_stack; simpl stack
    end.
    repeat (econstructor; eauto).
    admit.
  }

Abort.


(* Same theorem, but we first do the induction on cred. *)

(** Second tentative *)
Theorem correction_traditional:
  forall s1 s2,
    cred s1 s2 ->  
    forall s1',
      cong_state s1 s1' ->
      exists s2',
        cong_state s2 s2' /\ star cred s1' s2'.
Abort.



(****************************************************************)
(* Third tentative *)

Lemma stack_append_stack {s kappa}:
  stack (append_stack s kappa) = stack s ++ kappa.
Proof.
  induction s; simpl; eauto.
Qed.





Ltac list_simpl_base h := 
  learn (f_equal (@List.rev _) h);
    repeat multimatch goal with
    | [h: _ |- _] =>
      let P := typeof h in
      match P with
      | @Learnt _ =>
        idtac
      | _ =>
        repeat rewrite List.rev_involutive in h;
        repeat rewrite List.rev_app_distr in h;
        simpl in h
      end
    end;
    injections;
    subst;
    try congruence
.

Ltac list_simpl := 
  (try multimatch goal with
  | [h: _ = _ |- _] =>
    list_simpl_base h
  end)
  .

Lemma list_append_decompose: forall {A} {kappa1 kappa2} {k1 k2: A} ,
  k1 :: kappa1 = kappa2 ++ [k2] ->
  (k1 = k2 /\ kappa1 = nil /\ kappa2 = nil)
  \/ (exists kappa, kappa1 = kappa ++ [k2] /\ kappa2 = k1 :: kappa).
Proof.
  induction kappa1 as [|a1 kappa1]; intros.
  { repeat list_simpl.
    left; unzip; eauto.
  }
  {
    induction kappa2 as [|a2 kappa2]; repeat list_simpl.
    destruct IHkappa1 with kappa2 a1 k2; eauto.
  }
Qed.


(* This lemma is not true for the cong_state relation, as expected *)
Lemma cong_term_deterministic:
  forall t t1,
    cong_term t t1 ->
    forall t2,
    cong_term t t2 ->
    t1 = t2.
Proof.
  induction 1; inversion 1; subst.
  all: repeat f_equal; eauto.
Abort.

Theorem cred_append_stack s s':
  (* If you can do a transition, then you can do the same transition with additional informations on the stack. *)
  cred s s' ->
  forall k,
  cred (append_stack s k) (append_stack s' k).
Proof.
  induction 1; intros; asimpl; try econstructor; eauto.
Qed.

Theorem star_cred_append_stack s s':
  star cred s s'
  ->
  forall k,
  star cred (append_stack s k) (append_stack s' k).
Proof.
  induction 1; intros.
  * eauto with sequences.
  * eapply star_step; eauto using cred_append_stack.
Qed.


Lemma append_left_and_right {s1 s2 kappa}:
  (exists tgt, star cred s1 tgt /\ star cred s2 tgt) ->
  (exists tgt,
    star cred (append_stack s1 kappa) tgt
    /\ star cred (append_stack s2 kappa) tgt
  ).
Proof.
  intros; unpack.
  eexists; split; eapply star_cred_append_stack; eauto.
Qed.

Ltac decompose h :=
  let kappa := fresh "kappa" in
  first
    [ destruct (list_append_decompose h) as [?|[kappa ?]]
    | destruct (list_append_decompose (eq_sym h)) as [?|[kappa ?]]
    ];
    unpack;
    repeat list_simpl;
    repeat cleanup
.

Lemma stack_app_append_stack_eval {t kappa1 kappa2 sigma}:
  mode_eval t (kappa1 ++ kappa2) sigma = append_stack (mode_eval t kappa1 sigma) kappa2.
Proof.
  simpl; eauto.
Qed.

Lemma stack_all_append_stack_eval {t kappa sigma}:
  mode_eval t (kappa) sigma = append_stack (mode_eval t [] sigma) kappa.
Proof.
  simpl; eauto.
Qed.


Lemma stack_app_append_stack_cont {kappa1 kappa2 r}:
  mode_cont (kappa1 ++ kappa2) r = append_stack (mode_cont kappa1 r) kappa2.
Proof.
  simpl; eauto.
Qed.

Lemma stack_all_append_stack_cont {kappa r}:
  mode_cont (kappa) r = append_stack (mode_cont [] r) kappa.
Proof.
  simpl; eauto.
Qed.


(* Modifying the induction hypothesis : *)

Lemma modify_WF_IH {n}:
  (forall y : list cont,
  Datatypes.length y < n ->
  forall s1 : state,
    stack s1 = y ->
    forall s2 : state,
      cred s1 s2 ->
      forall s1' : state,
        cong_state s1 s1' ->
        exists s2' : state, cong_state s2 s2' /\ star cred s1' s2'
        )
  ->
  forall s1 s1',
    cong_state s1 s1' ->
    forall s2,
      cred s1 s2 ->
      List.length (stack s1) < n ->
      exists s2', cong_state s2 s2' /\ star cred s1' s2'
  .
Proof.
  intros.
  eapply H; eauto.
Qed.


(* This time, we do the well-founded induction based on kappa. *)
Theorem correction_traditional:
  forall kappa,
  forall s1,
    stack s1 = kappa ->
    forall s2,
      cred s1 s2 ->  
      forall s1',
        cong_state s1 s1' ->
        exists s2',
          cong_state s2 s2' /\ star cred s1' s2'.
Proof.
  induction kappa as [kappa IHkappa] using (
    well_founded_induction
      (wf_inverse_image _ nat _ (@List.length cont) 
      PeanoNat.Nat.lt_wf_0)).
  rename IHkappa into IH; assert (IHkappa:= modify_WF_IH IH); clear IH.
  intros until s2; induction 1.
  { inversion 1; subst; repeat sinv_cong.
    { inversion H2; subst.
      { learn (Forall2_nth_error_Some_left _ _ _ H7 _ _ H1); unpack.
        learn (Forall2_nth_error_Some H7 _ _ _ H1 H).
        eapply star_step_prop. { econstructor; eauto. }
        eapply star_refl_prop.
        econstructor; eauto.
      }
      { learn (f_equal stack H).
        learn (f_equal (@List.length _) H7).
        induction s; simpl in *; list_simpl.
      }
      { learn (f_equal stack H).
        learn (f_equal (@List.length _) H7).
        induction s; simpl in *; list_simpl.
      }
      { learn (f_equal stack H).
        learn (f_equal (@List.length _) H9).
        induction s; simpl in *; list_simpl.
      }
      { learn (f_equal stack H).
        learn (f_equal (@List.length _) H9).
        induction s; simpl in *; list_simpl.
      }
    }
    {
      induction s; simpl in *; injections; tryfalse; subst.
      exploit (IHkappa _ _ H5); [solve[econstructor; eauto]|solve[simpl; rewrite List.app_length; simpl; lia] | intros; unpack ].
      eapply star_trans_prop; [apply star_cred_append_stack; eauto|].
      eapply star_refl_prop.
      repeat rewrite List.app_comm_cons; erewrite append_stack_app; [|solve[reflexivity]].
      econstructor; eauto.
    }
    {
      induction s; simpl in *; injections; tryfalse; subst.
      exploit (IHkappa _ _ H5); [solve[econstructor; eauto]|solve[simpl; rewrite List.app_length; simpl; lia] | intros; unpack ].
      eapply star_trans_prop; [apply star_cred_append_stack; eauto|].
      eapply star_refl_prop.
      repeat rewrite List.app_comm_cons; erewrite append_stack_app; [|solve[reflexivity]].
      econstructor; eauto.
    }
    {
      induction s; simpl in *; injections; tryfalse; subst.
      exploit (IHkappa _ _ H6); [solve[econstructor; eauto]|solve[simpl; rewrite List.app_length; simpl; lia] | intros; unpack ].
      eapply star_trans_prop; [apply star_cred_append_stack; eauto|].
      eapply star_refl_prop.
      repeat rewrite List.app_comm_cons; erewrite append_stack_app; [|solve[reflexivity]].
      econstructor; eauto.
    }
    {
      induction s; simpl in *; injections; tryfalse; subst.
      exploit (IHkappa _ _ H6); [solve[econstructor; eauto]|solve[simpl; rewrite List.app_length; simpl; lia] | intros; unpack ].
      eapply star_trans_prop; [apply star_cred_append_stack; eauto|].
      eapply star_refl_prop.
      repeat rewrite List.app_comm_cons; erewrite append_stack_app; [|solve[reflexivity]].
      econstructor; eauto.
    }
  }
  { inversion 1; subst; repeat sinv_cong.
    { inversion H1; subst.
      {
        eapply star_step_prop. { econstructor; eauto. }
        eapply star_refl_prop.
        (* This requires prices rewriting *)
        match goal with [|- cong_state ?s1 ?s2] =>
          rewrite (@append_stack_all s1);
          rewrite (@append_stack_all s2);
          simpl with_stack; simpl stack
        end.
        repeat (econstructor; eauto).
      }
      { learn (f_equal stack H).
        learn (f_equal (@List.length _) H9).
        induction s; simpl in *; list_simpl.
      }
      { learn (f_equal stack H).
        learn (f_equal (@List.length _) H9).
        induction s; simpl in *; list_simpl.
      }
      { learn (f_equal stack H).
        learn (f_equal (@List.length _) H10).
        induction s; simpl in *; list_simpl.
      }
      { learn (f_equal stack H).
        learn (f_equal (@List.length _) H10).
        induction s; simpl in *; list_simpl.
      }
    }
    {
      induction s; simpl in *; injections; tryfalse; subst.
      exploit (IHkappa _ _ H4); [solve[econstructor; eauto]|solve[simpl; rewrite List.app_length; simpl; lia] | intros; unpack ].
      eapply star_trans_prop; [apply star_cred_append_stack; eauto|].
      eapply star_refl_prop.

      repeat rewrite List.app_comm_cons; erewrite append_stack_app; [|solve[reflexivity]].
      econstructor; eauto.
    }
    {
      induction s; simpl in *; injections; tryfalse; subst.
      exploit (IHkappa _ _ H4); [solve[econstructor; eauto]|solve[simpl; rewrite List.app_length; simpl; lia] | intros; unpack ].
      eapply star_trans_prop; [apply star_cred_append_stack; eauto|].
      eapply star_refl_prop.

      repeat rewrite List.app_comm_cons; erewrite append_stack_app; [|solve[reflexivity]].
      econstructor; eauto.
    }
    {
      induction s; simpl in *; injections; tryfalse; subst.
      exploit (IHkappa _ _ H5); [solve[econstructor; eauto]|solve[simpl; rewrite List.app_length; simpl; lia] | intros; unpack ].
      eapply star_trans_prop; [apply star_cred_append_stack; eauto|].
      eapply star_refl_prop.

      repeat rewrite List.app_comm_cons; erewrite append_stack_app; [|solve[reflexivity]].
      econstructor; eauto.
    }
    {
      induction s; simpl in *; injections; tryfalse; subst.
      exploit (IHkappa _ _ H5); [solve[econstructor; eauto]|solve[simpl; rewrite List.app_length; simpl; lia] | intros; unpack ].
      eapply star_trans_prop; [apply star_cred_append_stack; eauto|].
      eapply star_refl_prop.

      repeat rewrite List.app_comm_cons; erewrite append_stack_app; [|solve[reflexivity]].
      econstructor; eauto.
    }
  }
  { inversion 1; subst; repeat sinv_cong.
    { inversion H1; subst.
      {
        eapply star_step_prop. { econstructor; eauto. }
        eapply star_refl_prop.
        repeat (econstructor; eauto).
      }
      { learn (f_equal stack H).
        learn (f_equal (@List.length _) H8).
        induction s; simpl in *; list_simpl.
      }
      { learn (f_equal stack H).
        learn (f_equal (@List.length _) H8).
        induction s; simpl in *; list_simpl.
      }
      { learn (f_equal stack H).
        learn (f_equal (@List.length _) H9).
        induction s; simpl in *; list_simpl.
      }
      { learn (f_equal stack H).
        learn (f_equal (@List.length _) H9).
        induction s; simpl in *; list_simpl.
      }
    }
    {
      induction s; simpl in *; injections; tryfalse; subst.
      exploit (IHkappa _ _ H4); [solve[econstructor; eauto]|solve[simpl; rewrite List.app_length; simpl; lia] | intros; unpack ].
      eapply star_trans_prop; [apply star_cred_append_stack; eauto|].
      eapply star_refl_prop.

      repeat rewrite List.app_comm_cons; erewrite append_stack_app; [|solve[reflexivity]].
      econstructor; eauto.
    }
    {
      induction s; simpl in *; injections; tryfalse; subst.
      exploit (IHkappa _ _ H4); [solve[econstructor; eauto]|solve[simpl; rewrite List.app_length; simpl; lia] | intros; unpack ].
      eapply star_trans_prop; [apply star_cred_append_stack; eauto|].
      eapply star_refl_prop.

      repeat rewrite List.app_comm_cons; erewrite append_stack_app; [|solve[reflexivity]].
      econstructor; eauto.
    }
    {
      induction s; simpl in *; injections; tryfalse; subst.
      exploit (IHkappa _ _ H5); [solve[econstructor; eauto]|solve[simpl; rewrite List.app_length; simpl; lia] | intros; unpack ].
      eapply star_trans_prop; [apply star_cred_append_stack; eauto|].
      eapply star_refl_prop.

      repeat rewrite List.app_comm_cons; erewrite append_stack_app; [|solve[reflexivity]].
      econstructor; eauto.
    }
    {
      induction s; simpl in *; injections; tryfalse; subst.
      exploit (IHkappa _ _ H5); [solve[econstructor; eauto]|solve[simpl; rewrite List.app_length; simpl; lia] | intros; unpack ].
      eapply star_trans_prop; [apply star_cred_append_stack; eauto|].
      eapply star_refl_prop.

      repeat rewrite List.app_comm_cons; erewrite append_stack_app; [|solve[reflexivity]].
      econstructor; eauto.
    }
  }
  { inversion 1; subst; repeat sinv_cong.
    {
      induction s; simpl in *; injections; tryfalse; subst.
      decompose H2.
      { inversion H4; subst.
        { simpl.
          inversion H2; subst.
          repeat (eapply star_step_prop; [solve[econstructor; eauto]|]).
          eapply star_refl_prop.
          match goal with [|- cong_state ?s1 ?s2] =>
            rewrite (@append_stack_all s1);
            rewrite (@append_stack_all s2);
            simpl with_stack; simpl stack
          end.
          repeat (econstructor; eauto).
        }
        { learn (f_equal stack H).
          learn (f_equal (@List.length _) H11).
          induction s; simpl in *; list_simpl.
        }
        { learn (f_equal stack H).
          learn (f_equal (@List.length _) H11).
          induction s; simpl in *; list_simpl.
        }
        { learn (f_equal stack H).
          learn (f_equal (@List.length _) H12).
          induction s; simpl in *; list_simpl.
        }
        { learn (f_equal stack H).
          learn (f_equal (@List.length _) H12).
          induction s; simpl in *; list_simpl.
        }
      }
      {
        exploit (IHkappa _ _ H4); [solve[econstructor; eauto]|solve[simpl; rewrite List.app_length; simpl; lia] | intros; unpack ].
        eapply star_trans_prop; [apply star_cred_append_stack; eauto|].
        eapply star_refl_prop.

        repeat rewrite List.app_comm_cons; erewrite append_stack_app; [|solve[reflexivity]].
        econstructor; eauto.
      }
    }
    {
      induction s; simpl in *; injections; tryfalse; subst.
      decompose H2.
      exploit (IHkappa _ _ H4); [solve[econstructor; eauto]|solve[simpl; rewrite List.app_length; simpl; lia] | intros; unpack ].
      eapply star_trans_prop; [apply star_cred_append_stack; eauto|].
      eapply star_refl_prop.

      repeat rewrite List.app_comm_cons; erewrite append_stack_app; [|solve[reflexivity]].
      econstructor; eauto.
    }
    {
      induction s; simpl in *; injections; tryfalse; subst.
      decompose H2.
      exploit (IHkappa _ _ H5); [solve[econstructor; eauto]|solve[simpl; rewrite List.app_length; simpl; lia] | intros; unpack ].
      eapply star_trans_prop; [apply star_cred_append_stack; eauto|].
      eapply star_refl_prop.

      repeat rewrite List.app_comm_cons; erewrite append_stack_app; [|solve[reflexivity]].
      econstructor; eauto.
    }
    {
      induction s; simpl in *; injections; tryfalse; subst.
      admit "decompose H2.
      exploit (IHkappa _ _ H5); [solve[econstructor; eauto]|solve[simpl; rewrite List.app_length; simpl; lia] | intros; unpack ].
      eapply star_trans_prop; [apply star_cred_append_stack; eauto|].
      eapply star_refl_prop.

      repeat rewrite List.app_comm_cons; erewrite append_stack_app; [|solve[reflexivity]].
      econstructor; eauto".
    }
  }
  { inversion 1; subst; repeat sinv_cong.
    { eapply star_step_prop. { econstructor; eauto. }
      eapply star_refl_prop.
      econstructor; eauto.
    }
    {
      induction s; simpl in *; injections; tryfalse; subst.
      exploit (IHkappa _ _ H4); [solve[econstructor; eauto]|solve[simpl; rewrite List.app_length; simpl; lia] | intros; unpack ].
      eapply star_trans_prop; [apply star_cred_append_stack; eauto|].
      eapply star_refl_prop.
      repeat rewrite List.app_comm_cons; erewrite append_stack_app; [|solve[reflexivity]].
      econstructor; eauto.
    }
    {
      induction s; simpl in *; injections; tryfalse; subst.
      exploit (IHkappa _ _ H4); [solve[econstructor; eauto]|solve[simpl; rewrite List.app_length; simpl; lia] | intros; unpack ].
      eapply star_trans_prop; [apply star_cred_append_stack; eauto|].
      eapply star_refl_prop.
      repeat rewrite List.app_comm_cons; erewrite append_stack_app; [|solve[reflexivity]].
      econstructor; eauto.
    }
    {
      induction s; simpl in *; injections; tryfalse; subst.
      exploit (IHkappa _ _ H5); [solve[econstructor; eauto]|solve[simpl; rewrite List.app_length; simpl; lia] | intros; unpack ].
      eapply star_trans_prop; [apply star_cred_append_stack; eauto|].
      eapply star_refl_prop.
      repeat rewrite List.app_comm_cons; erewrite append_stack_app; [|solve[reflexivity]].
      econstructor; eauto.
    }
    {
      induction s; simpl in *; injections; tryfalse; subst.
      exploit (IHkappa _ _ H5); [solve[econstructor; eauto]|solve[simpl; rewrite List.app_length; simpl; lia] | intros; unpack ].
      eapply star_trans_prop; [apply star_cred_append_stack; eauto|].
      eapply star_refl_prop.
      repeat rewrite List.app_comm_cons; erewrite append_stack_app; [|solve[reflexivity]].
      econstructor; eauto.
    }
  }
  { inversion 1; subst; repeat sinv_cong.
    {
      induction s; simpl in *; injections; tryfalse; subst.
      decompose H2.
      exploit (IHkappa _ _ H4); [solve[econstructor; eauto]|solve[simpl; rewrite List.app_length; simpl; lia] | intros; unpack ].
      eapply star_trans_prop; [apply star_cred_append_stack; eauto|].
      eapply star_refl_prop.
      repeat rewrite List.app_comm_cons; erewrite append_stack_app; [|solve[reflexivity]].
      econstructor; eauto.
    }
    {
      induction s; simpl in *; injections; tryfalse; subst.
      decompose H2.
      { inversion H4; subst; simpl.
        { repeat (eapply star_step_prop; [solve[econstructor; eauto]|]).
          eapply star_refl_prop.
          repeat (econstructor; eauto).
        }
        { learn (f_equal stack H).
          learn (f_equal (@List.length _) H11).
          induction s; simpl in *; list_simpl.
        }
        { learn (f_equal stack H).
          learn (f_equal (@List.length _) H11).
          induction s; simpl in *; list_simpl.
        }
        { learn (f_equal stack H).
          learn (f_equal (@List.length _) H12).
          induction s; simpl in *; list_simpl.
        }
        { learn (f_equal stack H).
          learn (f_equal (@List.length _) H12).
          induction s; simpl in *; list_simpl.
        }
      }
      {
        exploit (IHkappa _ _ H4); [solve[econstructor; eauto]|solve[simpl; rewrite List.app_length; simpl; lia] | intros; unpack ].
        eapply star_trans_prop; [apply star_cred_append_stack; eauto|].
        eapply star_refl_prop.
        repeat rewrite List.app_comm_cons; erewrite append_stack_app; [|solve[reflexivity]].
        econstructor; eauto.
      }
    }
    {
      induction s; simpl in *; injections; tryfalse; subst.
      decompose H2.
      exploit (IHkappa _ _ H5); [solve[econstructor; eauto]|solve[simpl; rewrite List.app_length; simpl; lia] | intros; unpack ].
      eapply star_trans_prop; [apply star_cred_append_stack; eauto|].
      eapply star_refl_prop.
      repeat rewrite List.app_comm_cons; erewrite append_stack_app; [|solve[reflexivity]].
      econstructor; eauto.
    }
    {
      induction s; simpl in *; injections; tryfalse; subst.
      admit "need a better decomposition tactic".
      (* exploit (IHkappa _ _ H4); [solve[econstructor; eauto]|solve[simpl; rewrite List.app_length; simpl; lia] | intros; unpack ].
      eapply star_trans_prop; [apply star_cred_append_stack; eauto|].
      eapply star_refl_prop.
      repeat rewrite List.app_comm_cons; erewrite append_stack_app; [|solve[reflexivity]].
      econstructor; eauto. *)
    }
  }
  { inversion 1; subst; repeat sinv_cong.
    { (* "Interresting" case *)
      eapply star_step_prop; [solve[econstructor; eauto]|].
      eapply star_refl_prop.
      repeat (econstructor; eauto).
    }
    { eapply star_step_prop; [solve[econstructor; eauto]|].
      eapply star_refl_prop.
      match goal with [|- cong_state ?s1 ?s2] =>
        rewrite (@append_stack_all s1);
        rewrite (@append_stack_all s2);
        simpl with_stack; simpl stack
      end.
      repeat (econstructor; eauto).
    }
    { induction s; simpl in *; injections; tryfalse; subst.
      exploit (IHkappa _ _ H4); [solve[econstructor; eauto]|solve[simpl; rewrite List.app_length; simpl; lia] | intros; unpack ].
      eapply star_trans_prop; [apply star_cred_append_stack; eauto|].
      eapply star_refl_prop.
      repeat rewrite List.app_comm_cons; erewrite append_stack_app; [|solve[reflexivity]].
      econstructor; eauto.
    }
    { induction s; simpl in *; injections; tryfalse; subst.
      exploit (IHkappa _ _ H4); [solve[econstructor; eauto]|solve[simpl; rewrite List.app_length; simpl; lia] | intros; unpack ].
      eapply star_trans_prop; [apply star_cred_append_stack; eauto|].
      eapply star_refl_prop.
      repeat rewrite List.app_comm_cons; erewrite append_stack_app; [|solve[reflexivity]].
      econstructor; eauto.
    }
    { induction s; simpl in *; injections; tryfalse; subst.
      exploit (IHkappa _ _ H5); [solve[econstructor; eauto]|solve[simpl; rewrite List.app_length; simpl; lia] | intros; unpack ].
      eapply star_trans_prop; [apply star_cred_append_stack; eauto|].
      eapply star_refl_prop.
      repeat rewrite List.app_comm_cons; erewrite append_stack_app; [|solve[reflexivity]].
      econstructor; eauto.
    }
    { induction s; simpl in *; injections; tryfalse; subst.
      exploit (IHkappa _ _ H5); [solve[econstructor; eauto]|solve[simpl; rewrite List.app_length; simpl; lia] | intros; unpack ].
      eapply star_trans_prop; [apply star_cred_append_stack; eauto|].
      eapply star_refl_prop.
      repeat rewrite List.app_comm_cons; erewrite append_stack_app; [|solve[reflexivity]].
      econstructor; eauto.
    }
    { eapply star_refl_prop.
      match goal with [|- cong_state ?s1 ?s2] =>
        rewrite (@append_stack_all s1);
        rewrite (@append_stack_all s2);
        simpl with_stack; simpl stack
      end.
      repeat (econstructor; eauto).
    }
  }
  { inversion 1; subst; repeat sinv_cong.
    { induction s; simpl in *; injections; tryfalse; subst.
      decompose H2.
      exploit (IHkappa _ _ H4); [solve[econstructor; eauto]|solve[simpl; rewrite List.app_length; simpl; lia] | intros; unpack ].
      eapply star_trans_prop; [apply star_cred_append_stack; eauto|].
      eapply star_refl_prop.
      repeat rewrite List.app_comm_cons; erewrite append_stack_app; [|solve[reflexivity]].
      econstructor; eauto.
    }
    { induction s; simpl in *; injections; tryfalse; subst.
      decompose H2.
      exploit (IHkappa _ _ H4); [solve[econstructor; eauto]|solve[simpl; rewrite List.app_length; simpl; lia] | intros; unpack ].
      eapply star_trans_prop; [apply star_cred_append_stack; eauto|].
      eapply star_refl_prop.
      repeat rewrite List.app_comm_cons; erewrite append_stack_app; [|solve[reflexivity]].
      econstructor; eauto.
    }
    { induction s; simpl in *; injections; tryfalse; subst.
      decompose H2.
      { inversion H5; subst; repeat sinv_cong.
        { (eapply star_step_prop; [solve[econstructor; eauto]|]).
          eapply star_refl_prop.
          repeat (econstructor; eauto).
        }
        { learn (f_equal stack H).
          learn (f_equal (@List.length _) H12).
          induction s; simpl in *; list_simpl.
        }
        { learn (f_equal stack H).
          learn (f_equal (@List.length _) H12).
          induction s; simpl in *; list_simpl.
        }
        { learn (f_equal stack H).
          learn (f_equal (@List.length _) H13).
          induction s; simpl in *; list_simpl.
        }
        { learn (f_equal stack H).
          learn (f_equal (@List.length _) H13).
          induction s; simpl in *; list_simpl.
        }
      }
      { exploit (IHkappa _ _ H5); [solve[econstructor; eauto]|solve[simpl; rewrite List.app_length; simpl; lia] | intros; unpack ].
        eapply star_trans_prop; [apply star_cred_append_stack; eauto|].
        eapply star_refl_prop.
        repeat rewrite List.app_comm_cons; erewrite append_stack_app; [|solve[reflexivity]].
        econstructor; eauto.
      }
    }
    { induction s; simpl in *; injections; tryfalse; subst.
      admit "decompose H2.
      exploit (IHkappa _ _ H4); [solve[econstructor; eauto]|solve[simpl; rewrite List.app_length; simpl; lia] | intros; unpack ].
      eapply star_trans_prop; [apply star_cred_append_stack; eauto|].
      eapply star_refl_prop.
      repeat rewrite List.app_comm_cons; erewrite append_stack_app; [|solve[reflexivity]].
      econstructor; eauto.".
    }
  }
  { inversion 1; subst; repeat sinv_cong. all: admit. }

Abort. 





Theorem correction_traditional:
  forall s1 s2,
  sred s1 s2 ->

  star sred
    (trans_term s1) (trans_term s2).
Proof.
  Local Ltac step' := (
    try (eapply star_step; [solve
      [ repeat econstructor; simpl; eauto using List.map_nth_error
    ]|]))
  .
  induction 1; simpl; repeat step'; try eapply star_refl.
  { admit "subst lemma". }
  { eapply star_sred_app_right. eauto. }
  { eapply star_sred_app_left. eauto. }
  { admit "Here we don't have the induction hypothesis on a subterm of u1. Hence we cannot continue".
  }
Abort.

End trans3.

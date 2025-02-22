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


Require Import Ltac2.Ltac2.
Set Default Proof Mode "Classic".

Set Default Goal Selector "!".


(* This file demonstrates an proof for compiler correctness using continuation-based semantics. The base language is lambda-calculus + if-then-else.

We define both type of semantics, with adapted lemmas. We then prove type safety for both semantics. Finally, we show why continuation-based semantics is better regarding to the proof some exemples of compilation passes using smulation diagrams. Namely, we show two simulation diagrams two simple compiler optimisations.
*)


(* -------------------------------------------------------------------------- *)
(*** Additions to the Lists library ***)

Theorem Forall2_nth_error_Some_left {A B F l1 l2}:
  List.Forall2 F l1 l2 ->
  forall {k} {x: A},
    List.nth_error l1 k = Some x ->
    exists (y: B), List.nth_error l2 k = Some y.
Proof.
  induction 1, k; simpl; intros; inj; eauto.
Qed.


Theorem Forall2_nth_error_Some_right {A B F l1 l2}:
  List.Forall2 F l1 l2 ->
  forall {k} {y: B},
    List.nth_error l2 k = Some y ->
    exists (x: A), List.nth_error l1 k = Some x.
Proof.
  induction 1, k; simpl; intros; inj; eauto.
Qed.

Theorem Forall2_nth_error_Some {A B F l1 l2}:
  List.Forall2 F l1 l2 ->
  forall {k} {x: A} {y: B},
    List.nth_error l1 k = Some x ->
    List.nth_error l2 k = Some y ->
    F x y.
Proof.
  induction 1, k; simpl; intros; inj; eauto.
Qed.


(* This is a tactic that tries to infer equalities between terms in a list where :: and ++ are used. It uses [List.rev] and the [List.rev_app_distr] lemmas. *)

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
  | [h: @eq (list _) _ _ |- _] =>
    list_simpl_base h
  end)
  .

(* This lemmas precisely decompose an equality in the form: [k1 :: kappa1 = kappa2 ++ [k2]]. *)
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

(* We use it with the decompose tactic *)
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



(* -------------------------------------------------------------------------- *)
(*** Definition of the syntax of our language ***)


Inductive term :=
  (* Lambda calculus part of the language*)
  | Var (x: var)
  | App (t1 t2: term)
  | Lam (t: {bind term})
  | Value (v: value)

  (* The additionnal if-then-else *)
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

(* -------------------------------------------------------------------------- *)

(*** Strong induction principle for terms ***)

(* This proves usefull to show a correct induction principle, because our syntax inductive definition is pretty complex in Coq's terms, hence the gneerated induction principle is not strong enought. Indeed, our syntax is a mutally inductive type defintion, and it contains containers. At the time of this publication, no tool openly available for coq is able to generate a suitable induction principle.


Moreover, we need for one of the transformation to have a deep induction principle because of a rewriting of depth 2.


Hence, we define a metric, and show an induction principle. *)

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

(* To define the induction principle, we use the following trick: we show the induction principle on [term + value]. This permit us to derive the induction principle on both [term] and [value]. *)


Definition size (x : term + value) :=
  match x with
  | inl t => size_term t
  | inr v => size_value v
  end.


Theorem term_value_induction
: forall {P : term -> Prop} {Q : value -> Prop}
    {HVar: forall x : var, P (Var x)}
    {HApp: forall t1 : term, P t1 -> forall t2 : term, P t2 -> P (App t1 t2)}
    {HLam: forall t : {bind term}, P t -> P (Lam t)}
    {HValue: forall v : value, Q v -> P (Value v)}
    {HIf: forall u, P u -> forall t1, P t1 -> forall t2, P t2 -> P (If u t1 t2)}
    {HClosure: forall t,
      P t -> forall sigma, (List.Forall Q sigma) -> Q (Closure t sigma)}
    {HBool: forall b, Q (Bool b)},
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
        eapply HLam|
        eapply HValue|
        eapply HIf
      ].
      all: match goal with
      | [|- _ ?t] => eapply (IHx (inl t))
      | [|- _ ?v] => eapply (IHx (inr v))
      end.
      all: simpl; lia.
    }
    { destruct v; try first [
        eapply HClosure|
        eapply HBool
      ].
      all: try match goal with
      | [|- _ ?t] => eapply (IHx (inl t))
      | [|- _ ?v] => eapply (IHx (inr v))
      end.
      all: try solve [simpl; lia].
      {
        induction sigma; econstructor; eauto.
        { eapply (IHx (inr a)); simpl; lia. }

        eapply IHsigma; intros.
        { eapply IHx. simpl in *; lia. }
      }
    }
  }
Qed.

Theorem term_ind'
  : forall {P : term -> Prop} {Q : value -> Prop}
      {HVar: forall x : var, P (Var x)}
      {HApp: forall t1 : term, P t1 -> forall t2 : term, P t2 -> P (App t1 t2)}
      {HLam: forall t : {bind term}, P t -> P (Lam t)}
      {HValue: forall v : value, Q v -> P (Value v)}
      {HIf: forall u, P u -> forall t1, P t1 -> forall t2, P t2 -> P (If u t1 t2)}
      {HClosure: forall t,
        P t -> forall sigma, (List.Forall Q sigma) -> Q (Closure t sigma)}
      {HBool: forall b, Q (Bool b)},
      (forall t, P t) /\ (forall v, Q v).
Proof.
  split; intros.
  { unshelve eapply (term_value_induction (inl t)); eauto. }
  { unshelve eapply (term_value_induction (inr v)); eauto. }
Qed.


(* -------------------------------------------------------------------------- *)

(* We can now define the continuation-based semantics for our language. We first to define what are the control units and what is a state. *)

Inductive cont :=
  | CAppR (t2: term) (sigma: list value) (* [\square t2] *)
  | CClosure (t_cl: {bind term}) (sigma_cl: list value)
  (* [Clo(x, t_cl, sigma_cl) \square] Since we are using De Bruijn indices,
     there is no variable x. *)
  | CIf (t1 t2: term) (sigma: list value) (* [if \square then t1 else t2]*)
.

(* In this example, results can only be values, but in larger languages it can hold also exceptions. *)
Inductive result :=
  | RValue (v: value)
.


Inductive state :=
  | mode_eval (e: term) (kappa: list cont) (env: list value)
  | mode_cont (kappa: list cont) (result: result)
.

(* -------------------------------------------------------------------------- *)

(*** Continuation-based small-step semantics ***)

(* We define the continuation-based small-step semantics as defined in the paper. The syntax is a bit more verbose that in the paper, but we define notations to get closer to the paper's notation next.

We use an additional implementation trick: each case have an [info "rule_name"] hypothesis. This is used to know in what case using the `check "rule_name"` tactic we are to be able to debugger proof script more easily.

Contrary to the paper, we use de Bruijn indices to represent variables. No substitution is needed to define this reduction as environement are passed in the computation. *)

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

(* Some notations to get closer to the paper. Those are disabled except for the coercions that provide a lot more clarity. Uncomment and [Check cred] to get a pretty-printed version of the cred reduction predicate. *)


(* Notation "'λ.' t" := (Lam t) (at level 50).
Notation "'S(' t , kappa , sigma )" := (mode_eval t kappa sigma).
Notation "'C(' v , kappa )" := (mode_cont kappa v).
Notation "'λ' sigma '.' t " := ((Closure t sigma)) (at level 10).
Notation "'if' u 'then' t1 'else' t2 'end'" := (If u t1 t2) (at level 10).
Notation "'k_app1' ( t, sigma )" := (CAppR t sigma) (at level 50).
Notation "'k_app2' ( t , sigma )" := (CClosure t sigma) (at level 50).
Notation "'k_if' ( t1 , t2 , sigma )" := (CIf t1 t2 sigma) (at level 50).
Notation "s1 ~> s2" := (cred s1 s2) (at level 20).
Notation "s1 ~>* s2" := (star cred s1 s2) (at level 20). *)
Coercion App : term >-> Funclass.
Definition id_var (n: nat): var := n.
Coercion id_var: nat >-> var.
Coercion Value: value >-> term.
Coercion RValue: value >-> result.
Coercion Bool : bool >-> value.
Coercion Var: var >-> term.

(* Here is an exemple of reduction with continuation-based small-step semantics. As you can see, we can simply implement an interpreter in ltac for continuation based semantics directly in ltac. *)

Example example_of_reduction t1 t2:
  star cred
    (mode_eval (If (Value (Bool true)) t1 t2) [] [])
    (mode_eval t1 [] []).
Proof.
  eapply star_step; [solve[econstructor; eauto]|].
  eapply star_step; [solve[econstructor; eauto]|].
  eapply star_step; [solve[econstructor; eauto]|].
  eapply star_refl.
Qed.

(* -------------------------------------------------------------------------- *)
(*** Some definitions and property of CBSS ***)

(* Returns [True] if the state is in cont mode. *)
Definition is_mode_cont s :=
  match s with
  | mode_cont _ _ => True
  | _ => False
  end.

(* Returns the continuation stack of a state. *)
Definition stack s :=
  match s with
  | mode_eval _ k _ => k
  | mode_cont k _ => k
  end.

(* Replaces the continuation stack with a new one *)
Definition with_stack s kappa :=
  match s with
  | mode_cont _ v => mode_cont kappa v
  | mode_eval t _ sigma => mode_eval t kappa sigma
  end.

(* Adds a continuation to an existing state *)
Definition append_stack s kappa :=
  with_stack s (stack s ++ kappa).

(* The function [append_stack] is central to the understanding of continuation-based small-step semantics. This is due to the following theorem: *)

(* This theorem states that if you can do a reduction, then you can do the same reduction while having a larger continuation. *)
Theorem cred_append_stack s s':
  cred s s' ->
  forall k,
  cred (append_stack s k) (append_stack s' k).
Proof.
  induction 1; intros; asimpl; try econstructor; eauto.
Qed.

(* The same is true for any number of reductions. *)
Theorem star_cred_append_stack s s':
  star cred s s'
  ->
  forall k,
  star cred (append_stack s k) (append_stack s' k).
Proof.
  induction 1; intros.
  { eauto with sequences. }
  { eapply star_step; eauto using cred_append_stack. }
Qed.


(* The following lemmas are rewriting lemmas to get more information from equality in the current context. *)

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
    apply (f_equal (@Datatypes.length cont)) in H0; rewrite List.length_app in *; simpl in *.
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
    apply (f_equal (@Datatypes.length cont)) in H0; rewrite List.length_app in *; simpl in *.
    lia.
  }
  { intros; induction s; simpl in *; tryfalse.
    repeat injections; subst.
    learn (List.app_inj_tail _ _ _ _ H0); unpack; subst.
    repeat econstructor.
  }
Qed.

(* The following lemmas are rewriting lemmas to get the continuation stack in a certain shape before applying functions. *)

Lemma append_stack_app {s kappa1 kappa2}:
  stack s = kappa1 ++ kappa2 ->
  s = append_stack (with_stack s kappa1) kappa2.
Proof.
  induction s; intros; simpl in *; subst; reflexivity.
Qed.

Lemma append_stack_all {s}:
  s = append_stack (with_stack s []) (stack s).
Proof.
  induction s; intros; simpl in *; subst; reflexivity.
Qed.

Lemma stack_append_stack {s kappa}:
  stack (append_stack s kappa) = stack s ++ kappa.
Proof.
  induction s; simpl; eauto.
Qed.

(* -------------------------------------------------------------------------- *)
(*** Traditional small-step semanitcs ***)

(* We also define traditional small-step semantics for our language. *)

Import List.ListNotations.
Open Scope list.


(* Because autosubst uses functions [nat -> term] and we use lists in the syntax, we need a way to get from one version to the other. *)

Definition subst_of_env sigma :=
  fun n =>
  match List.nth_error sigma n with
  | None => ids (n - List.length sigma)
  | Some t => Value t
  end
.

(* To stay coherent with our over language, we have both closures and lambda in this language. When a lambda is created, we define a closure with an empty environement.

We don't show in this file the equivalence between both style of semantics. But we show it for the lambda calculus fragment in `miniml.v` file, and for the full catala language in the `simulation_cred_to_sred.v` and `simulation_sred_to_cred.v` files. In both cases, a diagram is shown and the equivalence relation states that two closures are equivalent if the terms are the same after substitution. *)

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

(* In traditional small-step semantics, we need to extend each contextual rules to the star of the reduction. *)

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


(* -------------------------------------------------------------------------- *)
(*** Typing ***)


(* Our typing syntax is pretty basic. *)

Inductive type :=
  | TBool
  | TFun (T1 T2: type)
.

(* Standard typing rules for lambda calculus. Those are classical. We use a list of type as typing environement. This is because we uses de Bruijn indices. *)

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

(* Because the shape of the typing judgment, we can usually derive what rule have been applied by looking at the head term. Hence, inversion is non-ambiguious when the head-term is known. Because of this we can define a smart-inversion tactic for typing judgement. 


We extend a little bit this statement for cases where we have an concatenation of two continuations. [TODO: what is the name of such a property ?] This simplify induction using the [List.rev_ind] induction principle of lists. *)

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

(* We also define a tactic to automatically rename typing judgements to HT. This trick permit to add to an existing proof new hypothesis regarding typing, without having to change other's hypothesis naming. *)

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

(* To be used as [repeat inv_jt]. *)
Ltac inv_jt := ltac2:(inv_jt (); rename_jt ()); unpack.



(* -------------------------------------------------------------------------- *)
(*** Type safety for continuation-based semantics. ***)


(* we show type safety using preservation and progress lemmas.*)

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
  { eapply (Forall2_nth_error_Some HT0); eauto. }
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

(* -------------------------------------------------------------------------- *)
(*** Type safety for Traditional small-step semantics. ***)


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

(* -------------------------------------------------------------------------- *)
(*** Determinism of the reductions. ***)

(* Because of the syntactix nature of continuation-based small step semantics, no cases are left. *)
Theorem cred_deterministic:
  forall s1 s2, cred s1 s2 -> forall s2', cred s1 s2' -> s2 = s2'.
Proof.
  induction 1; inversion 1; subst; simpl in *; eauto.
  { congruence. }
Qed.

(* This is not the case for traditional small-step semantics. *)
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

(* -------------------------------------------------------------------------- *)
(** Translation of [if t then ta else tb] into [if (if t then false else true) then tb else ta] *)

Module trans1.

(* Let use define the translation on terms. *)
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

(* To define it to states, we need to extend the definition. *)
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

(* After defining the extension of the translation to states, the proof of the following diagram is immediate. *)

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


(* -------------------------------------------------------------------------- *)
(*** Translating [if (if t then false else true) then tb else ta] into [if t then ta else tb] ***)

(* Inverse of the previous translation. This is significantly harder to show because of de-synchronization issues, as explained below. *)

Module trans2.

(* Definition of the translation on terms. *)
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

(** Inside the diagrams, we use an invariant and not this translation function. This is due to a desynchronization between the translation of terms after a reduction:

Indeed, the term `t1`

[ t1 = if (if true then if t then false else true else u) then a else b]

is translated into `t1'`

[t1' = if (if true then (trans_term (if t then false else true)) else (trans_term u)) then (trans_term a) else (trans_term b)]

Which reduces to 

[t2' = if (trans_term (if t then false else true)) then (trans_term a) else (trans_term b)]

while after one step of reduction, the term ` becomes the term `t2`

[t2 = if if t then false else true then a else b]

which translates to `t2'`

[t2'' = if (trans_term t) then (trans_term b) else (trans_term a)]

You can observe that the terms `t2'` and `t2''` are not the same as the translation applies either to the outer if or to the condition. 

Hence, we need to define an invariant between terms that is more general than the above function, in the sense that we can decide to apply the translation or not, non-deterministicly. This fixes the desynchronization issue but requires more work to find an show the correct diagram.

*)

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

(* -------------------------------------------------------------------------- *)
(** The goal of this paragraph is to show that the [trans_term] function is a subcase of the [cong_term] relation : *)

Theorem trans_cong_term :
  forall t, 
    cong_term t (trans_term t)
.
Abort.


(** For that, we need to show the result for both values and terms. Because we have deep-sub-terms, we need to use well-founded induction (or reprove a induction principle for our needs). We reuse the trick to show our theorem that we already presented in the section about inductions principles on terms: we show our property on objects [x] of type [term + values]. This permit to, after the use of the `econstructor` tactic apply the induction principle on both terms and values of smaller size. 


This is an obligation beacause the induction principle generated by Functional Scheme [trans_term_ind2] is lacking an hypothesis in the case of the [List.Forall2].

*)

Functional Scheme trans_term_ind2 := Induction for trans_term Sort Prop
with trans_value_ind2 := Induction for trans_value Sort Prop.

(* Missing induction hypothesis related to List.Forall2 sigma _ _. Uncomment to show. *)
(* Check trans_term_ind2. *)


Lemma trans_cong_technical:
  forall x,
  match x with
  | inl t => cong_term t (trans_term t)
  | inr v => cong_value v (trans_value v)
  end
.
Proof.
  induction x as [x IHx] using (
    well_founded_induction
      (wf_inverse_image _ nat _ size 
      PeanoNat.Nat.lt_wf_0)).
  induction x; [induction a|induction b].
  all: simpl.
  all: repeat unzip_match.
  all: repeat econstructor; fold trans_term; fold trans_value.
  all: try match goal with
    | [ |- cong_term ?e _ ] => solve [eapply (IHx (inl e)); simpl; lia]
    | [ |- cong_value ?e _ ] => solve [eapply (IHx (inr e)); simpl; lia]
  end.

  (* One case is left, corresponding to where we have a List.Forall2. We do the induction on the first list to derive the result. *)
  { induction sigma; econstructor.
    { eapply (IHx (inr a)).
      simpl; lia.
    }
    { eapply IHsigma.
      intros.
      eapply IHx.
      simpl in *; lia.
    }
  }
Qed.

(** The wanted theorem can be derived by a simple application. of the above result. *)
Theorem trans_cong_term :
  forall t, 
    cong_term t (trans_term t)
.
Proof.
  intros.
  eapply (trans_cong_technical (inl t)).
Qed.

(* -------------------------------------------------------------------------- *)
(*** Extending [cong_term] into [cong_states] ***)

(* To be able to state the theorem on continuation based small-step semantics reductions, we first need to extend our invariant to states.
*)


(* In this definition, we choose to not separate the mode_eval and mode_cont when it was possible. we hence used the "append_stack" function. This might pose issues when applying the "econstructor" tactic. In those case, we use the rewriting lemmas present in the section about continuation-based small-step semantics. *)

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
    (* Nothing tells us that the environement is the same for both continuations. Hence, we separate them. *)
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

(* We define a smart-inversion tactic for this invariant. This comes handy when deconstructing hypothesis of type cong_term. Sadly, we cannot have such an tactic with [cong_state] because we are using [append_stack] and not a coq constructor. *)
Ltac2 sinv_cong () :=
  match! goal with
  | [ h: cong_term ?c _ |- _ ] => smart_inversion c h
  | [ h: cong_value ?c _ |- _ ] => smart_inversion c h
  | [ h: List.Forall2 cong_value ?c _ |- _ ] => smart_inversion c h
  | [ h: List.Forall2 cong_value _ ?c |- _ ] => smart_inversion c h
  | [ h: List.Forall2 cong_term ?c _ |- _ ] => smart_inversion c h
  | [ h: List.Forall2 cong_term _ ?c |- _ ] => smart_inversion c h
  end.

Ltac sinv_cong := ltac2: (sinv_cong ()).

Lemma cong_term_ren:
  forall t1 t2,
    cong_term t1 t2 ->
    forall sigma,
    cong_term t1.[ren sigma] t2.[ren sigma].
Proof.
  induction 1; asimpl; intros; repeat econstructor; eauto.
  { asimpl; eauto. }
Qed.

Lemma cong_term_subst_tech:
  forall t1 t2,
    cong_term t1 t2 ->
    forall sigma1 sigma2,
      List.Forall2 cong_value sigma1 sigma2 ->
      forall k,
        cong_term t1.[upn k (subst_of_env sigma1)] t2.[upn k (subst_of_env sigma2)].
Proof.
  induction 1; asimpl; intros; repeat econstructor; eauto.
  { admit. }
  { repeat rewrite fold_up_upn.
    eapply IHcong_term; eauto.
  }
Admitted.

Lemma cong_term_subst:
  forall t1 t2,
    cong_term t1 t2 ->
    forall sigma1 sigma2,
      List.Forall2 cong_value sigma1 sigma2 ->
      cong_term t1.[subst_of_env sigma1] t2.[subst_of_env sigma2].
Proof.
  intros ? ? H ? ? H'.
  learn (cong_term_subst_tech _ _ H _ _ H' 0).
  unfold upn in *.
  eauto.
Qed.


Theorem cong_term_correctness:
  forall t1 t2,
    sred t1 t2 ->
    forall t1',
      cong_term t1 t1' ->
      exists t2',
        cong_term t2 t2'
        /\ star sred t1' t2'.
Proof.
  induction 1; inversion 1; subst.
  { eapply star_step_prop. { solve[repeat (econstructor; eauto)]. }
    eapply star_refl_prop.
    repeat (econstructor; eauto). 
  }
  { repeat sinv_cong.
    eapply star_step_prop. { solve[repeat (econstructor; eauto)]. }
    eapply star_refl_prop.
    repeat (econstructor; eauto).
    eapply cong_term_subst; eauto.
  }
  { repeat sinv_cong.
    eapply IHsred in H5; unpack.
    eapply star_trans_prop. { eapply star_sred_app_right; eauto. }
    eapply star_refl_prop.
    repeat (econstructor; eauto).
  }
  { repeat sinv_cong.
    eapply IHsred in H3; unpack.
    eapply star_trans_prop. { eapply star_sred_app_left; eauto. }
    eapply star_refl_prop.
    repeat (econstructor; eauto).
  }
  { repeat sinv_cong.
    eapply star_step_prop. { solve[repeat (econstructor; eauto)]. }
    eapply star_refl_prop.
    eauto.
  }
  { repeat sinv_cong.
    eapply star_step_prop. { solve[repeat (econstructor; eauto)]. }
    eapply star_refl_prop.
    eauto.
  }
  {
    exploit IHsred.
    { repeat (econstructor; eauto). }
    intros; unpack.
    inversion H; subst.
    { inversion H4; subst; inversion H5; subst.
      inversion H1; inversion H8; subst.
      eapply star_step_prop. { solve[repeat (econstructor; eauto)]. }
      eapply star_refl_prop. admit "diagram is wrong". (* diagram *)
    }
    { inversion H4; subst; inversion H5; subst.
      inversion H1; inversion H8; subst.
      eapply star_step_prop. { solve[repeat (econstructor; eauto)]. }
      eapply star_refl_prop. admit "diagram is wrong". (* diagram *)
    }
    { admit.
    }
  }
  { eapply IHsred in H4; unpack.
    eapply star_trans_prop. { eapply star_sred_if_cond; eauto. }
    eapply star_refl_prop.
    repeat (econstructor; eauto).
  }
Abort.


Lemma external_lemma:
  forall b t,
    star sred (If b false true) t ->
    (exists b', star sred b b' /\ t = (If b' false true))
      \/ (t = false /\ star sred b true)
      \/ (t = true /\ star sred b false).
Proof.
  induction 1 using star_ind_n1.
  { left; repeat econstructor. }
  { unzip; subst.
    { inversion H; subst; eauto.
      { left.
        eexists; split; [|eauto].
        eapply star_step_n1; eauto.
      }
    }
    { inversion H. }
    { inversion H. }
  }
Qed.

Theorem cong_term_correctness:
  forall t1 t2,
    sred t1 t2 ->
    forall t1',
      cong_term t1 t1' ->
      exists t3 t3',
        star sred t2 t3 /\
        star sred t1' t3' /\
        cong_term t3 t3'.
Proof.
  induction 1; inversion 1; subst.

  { eapply confluent_prop_star_step_right. { solve[repeat (econstructor; eauto)]. }
    eapply confluent_prop_star_refl.
    repeat (econstructor; eauto). 
  }
  { repeat sinv_cong.
    eapply confluent_prop_star_step_right. { solve[repeat (econstructor; eauto)]. }
    eapply confluent_prop_star_refl.
    repeat (econstructor; eauto).
    eapply cong_term_subst; eauto.
  }
  { repeat sinv_cong.
    eapply IHsred in H5; unpack.
    eapply confluent_prop_star_trans_left. { eapply star_sred_app_right; eauto. }
    eapply confluent_prop_star_trans_right. { eapply star_sred_app_right; eauto. }
    eapply confluent_prop_star_refl.
    repeat (econstructor; eauto).
  }
  { repeat sinv_cong.
    eapply IHsred in H3; unpack.
    eapply confluent_prop_star_trans_left. { eapply star_sred_app_left; eauto. }
    eapply confluent_prop_star_trans_right. { eapply star_sred_app_left; eauto. }
    eapply confluent_prop_star_refl.
    repeat (econstructor; eauto).
  }
  { repeat sinv_cong.
    eapply confluent_prop_star_step_right. { solve[repeat (econstructor; eauto)]. }
    eapply confluent_prop_star_refl.
    eauto.
  }
  { repeat sinv_cong.
    eapply confluent_prop_star_step_right. { solve[repeat (econstructor; eauto)]. }
    eapply confluent_prop_star_refl.
    eauto.
  }
  {
    exploit IHsred.
    { repeat (econstructor; eauto). }
    intros; unpack.

    inversion H; subst.
    { inversion H4; subst.
      inversion H8; subst.
      inversion H1; subst. 2:{ inversion H5. }
      inversion H3; inversion H9; subst.
      eapply confluent_prop_star_step_right. { solve[repeat (econstructor; eauto)]. }
      eapply confluent_prop_star_step_left. { solve[repeat (econstructor; eauto)]. }

      eapply confluent_prop_star_refl; eauto.
    }

    { inversion H4; subst.
      inversion H8; subst.
      inversion H1; subst. 2:{ inversion H5. }
      inversion H3; inversion H9; subst.
      eapply confluent_prop_star_step_right. { solve[repeat (econstructor; eauto)]. }
      eapply confluent_prop_star_step_left. { solve[repeat (econstructor; eauto)]. }

      eapply confluent_prop_star_refl; eauto.
    }
    { clear H0.
      repeat sinv_cong.
      learn (external_lemma _ _ H1).
      learn (external_lemma _ _ H2).
      unzip; subst; repeat sinv_cong.
      {
        eapply confluent_prop_star_trans_left.
        { do 2 eapply star_sred_if_cond. eauto. }

        eapply confluent_prop_star_trans_right.
        { eapply star_sred_if_cond. eauto. }
        
        eapply confluent_prop_star_refl.
        econstructor; eauto.
      }
      {
        eapply confluent_prop_star_trans_left.
        { do 2 eapply star_sred_if_cond. eauto. }

        eapply confluent_prop_star_trans_right.
        { eapply star_sred_if_cond. eauto. }

        eapply confluent_prop_star_step_left.
        { eapply sred_if_cond.
          econstructor.
        }
        eapply confluent_prop_star_step_left.
        { econstructor. }

        eapply confluent_prop_star_step_right.
        { econstructor. }

        eapply confluent_prop_star_refl.
        eauto.
      }
      {
        eapply confluent_prop_star_trans_left.
        { do 2 eapply star_sred_if_cond. eauto. }

        eapply confluent_prop_star_trans_right.
        { eapply star_sred_if_cond. eauto. }

        eapply confluent_prop_star_step_left.
        { eapply sred_if_cond.
          econstructor.
        }
        eapply confluent_prop_star_step_left.
        { econstructor. }

        eapply confluent_prop_star_step_right.
        { econstructor. }

        eapply confluent_prop_star_refl.
        eauto.
      }
    }
  }
  { eapply IHsred in H4; unpack.
    eapply confluent_prop_star_trans_left. { eapply star_sred_if_cond; eauto. }
    eapply confluent_prop_star_trans_right. { eapply star_sred_if_cond; eauto. }
    eapply confluent_prop_star_refl.
    repeat (econstructor; eauto).
  }
Qed.

Print Assumptions cong_term_correctness.

(* This strategy works *)
Theorem cong_term_correctness:
  forall t1 t1',
    cong_term t1 t1' ->
    forall t2,
      sred t1 t2 ->
      exists t3 t3',
        star sred t2 t3 /\
        star sred t1' t3' /\
        cong_term t3 t3'.
Proof.
  induction 1; inversion 1; subst.
  { (* This strategy is ok for the if-then-else *)
    inversion H7; subst.
    { repeat sinv_cong.
      eapply confluent_prop_star_step_left; [solve[repeat (econstructor; eauto)]|].
      eapply confluent_prop_star_step_right; [solve[repeat (econstructor; eauto)]|].
      eapply confluent_prop_star_refl; eauto.
    }
    { repeat sinv_cong.
      eapply confluent_prop_star_step_left; [solve[repeat (econstructor; eauto)]|].
      eapply confluent_prop_star_step_right; [solve[repeat (econstructor; eauto)]|].
      eapply confluent_prop_star_refl; eauto.
    }
    { repeat sinv_cong.
      eapply IHcong_term1 in H8; unpack.
      eapply confluent_prop_star_trans_left.
        { eapply star_sred_if_cond.
          eapply star_sred_if_cond.
          eauto.
        }
      eapply confluent_prop_star_trans_right.
        { eapply star_sred_if_cond.
          eauto.
        }
      eapply confluent_prop_star_refl.
      repeat (econstructor; eauto).
    }
  }
  { repeat sinv_cong.
    eapply confluent_prop_star_step_right. { econstructor. }
    eapply confluent_prop_star_refl.
    eapply cong_term_subst; eauto.
  }
  { repeat sinv_cong.
    eapply IHcong_term2 in H5; unpack.
    eapply confluent_prop_star_trans_right. {
      eapply star_sred_app_right; eauto.
    }
    eapply confluent_prop_star_trans_left. {
      eapply star_sred_app_right; eauto.
    }
    eapply confluent_prop_star_refl.
    repeat (econstructor; eauto).
  }
  { repeat sinv_cong.
    eapply IHcong_term1 in H5; unpack.
    eapply confluent_prop_star_trans_right. {
      eapply star_sred_app_left; eauto.
    }
    eapply confluent_prop_star_trans_left. {
      eapply star_sred_app_left; eauto.
    }
    eapply confluent_prop_star_refl.
    repeat (econstructor; eauto).
  }
  { repeat sinv_cong.
    eapply confluent_prop_star_step_right. { econstructor. }
    eapply confluent_prop_star_refl.
    repeat (econstructor; eauto).
  }
  { repeat sinv_cong.
    eapply confluent_prop_star_step_right. { econstructor. }
    eapply confluent_prop_star_refl.
    eauto.
  }
  { repeat sinv_cong.
    eapply confluent_prop_star_step_right. { econstructor. }
    eapply confluent_prop_star_refl.
    eauto.
  }
  { eapply IHcong_term1 in H7; unpack.
    eapply confluent_prop_star_trans_right. {
      eapply star_sred_if_cond.
      eauto.
    }
    eapply confluent_prop_star_trans_left. {
      eapply star_sred_if_cond.
      eauto.
    }
    eapply confluent_prop_star_refl.
    eauto.
    repeat (econstructor; eauto).
  }
Qed.


(* -------------------------------------------------------------------------- *)
(** Some properties about cong_term and cong_value. *)


(* [cong_term] is not deterministic. *)
Lemma cong_term_deterministic:
  forall t t1,
    cong_term t t1 ->
    forall t2,
    cong_term t t2 ->
    t1 = t2.
Proof.
  induction 1; inversion 1; subst.
  all: repeat f_equal; eauto.
  (* All of the remaning cases are linked to the non-determinism of the translation of the if, and are unsolvable *)
Abort.

Lemma cong_term_non_deterministic:
  exists t t1,
    cong_term t t1 /\
    exists t2,
    cong_term t t2 /\
    t1 <> t2.
Proof.
  exists (If (If true false true) true false).
  repeat eexists.
  { eapply cong_if_base; repeat econstructor. }
  { eapply cong_If; repeat econstructor. }
  { intros; congruence. }
Qed.

(* -------------------------------------------------------------------------- *)
(*** Naive simulation diagram. ***)

(* We first try to show a simulation diagram. by induction on cong_state. *)

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
  { learn (Forall2_nth_error_Some_left H0 H7); unpack.
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

(* -------------------------------------------------------------------------- *)
(* Same theorem, but we first do the induction on cred. *)

(** Second tentative: doing an induction on cred *)
Theorem correction_traditional:
  forall s1 s2,
    cred s1 s2 ->  
    forall s1',
      cong_state s1 s1' ->
      exists s2',
        cong_state s2 s2' /\ star cred s1' s2'.
Abort.

(* -------------------------------------------------------------------------- *)
(*** Doing a well-founded induction on the continuation stack. ***)

(* 
  We prove the lemma using a well-formed induction on the length of the stack.  However, this statement is not directly usable in Coq because we lack certain hypotheses when applying (such as the stack length and its proof of being less than n). To address this, we reorganize the induction hypothesis so that these requirements are introduced properly.

  Usage:
    Once you have an instance [H] of [cong_state s1 s1'], use the following tactic to apply the induction hypothesis.

      exploit (IHkappa _ _ H);
        [ solve [econstructor; eauto]   (* solves [cred s1 s2] *)
        | solve [simpl; repeat (rewrite List.length_app; simpl); lia] 
          (* handles the proof that the stack length is smaller than n *)
        | intros; unpack ].   (* introduces and unpacks the new hypotheses *)
*)

Lemma modify_WF_IH {P n}:
  (forall y : list cont,
  Datatypes.length y < n ->
  forall s1 : state,
    stack s1 = y ->
    forall s2 : state,
      cred s1 s2 ->
      forall s1' : state,
        cong_state s1 s1' ->
        P s1 s2 s1')
  ->
  forall s1 s1',
    cong_state s1 s1' ->
    forall s2,
      cred s1 s2 ->
      List.length (stack s1) < n ->
      P s1 s2 s1'
  .
Proof.
  intros X ? ? ? ? ? ?; eapply X; eauto.
Qed.

(* This time, we do the well-founded induction based on kappa. *)

(* The diagram does not work, but we can find why: the diagram is incorrect. I first try to automatize the proof.*)
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

  (* 43 cases. But two cases are not working because the diagram is incorrect with this precise invariant.

  The cases are those related to if-then-else when the argument is true (resp. false).

  Namely, we cannot show [cred s1 s2 -> cong_state s1 s1' -> exists s2', cong_state s2 s2' /\ star cred s1' s2'] when [s2] is [mode_eval false [CIf t1 t1' sigma1] sigma1'] and [s1'] is [mode_cont [CIf t2 t1' sigma'] true].

  *)
  { inversion 1; subst; repeat sinv_cong.
    { inversion H2; subst.
      { learn (Forall2_nth_error_Some_left H7  H1); unpack.
        learn (Forall2_nth_error_Some H7 H1 H).
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
      exploit (IHkappa _ _ H5); [solve[econstructor; eauto]|solve[simpl; repeat (rewrite List.length_app; simpl); lia] | intros; unpack ].
      eapply star_trans_prop; [apply star_cred_append_stack; eauto|].
      repeat rewrite List.app_comm_cons; erewrite append_stack_app; [|solve[reflexivity]].
      eapply star_refl_prop.
      
      econstructor; eauto.
    }
    {
      induction s; simpl in *; injections; tryfalse; subst.
      exploit (IHkappa _ _ H5); [solve[econstructor; eauto]|solve[simpl; repeat (rewrite List.length_app; simpl); lia] | intros; unpack ].
      eapply star_trans_prop; [apply star_cred_append_stack; eauto|].
      eapply star_refl_prop.
      repeat rewrite List.app_comm_cons; erewrite append_stack_app; [|solve[reflexivity]].
      econstructor; eauto.
    }
    {
      induction s; simpl in *; injections; tryfalse; subst.
      exploit (IHkappa _ _ H6); [solve[econstructor; eauto]|solve[simpl; repeat (rewrite List.length_app; simpl); lia] | intros; unpack ].
      eapply star_trans_prop; [apply star_cred_append_stack; eauto|].
      eapply star_refl_prop.
      repeat rewrite List.app_comm_cons; erewrite append_stack_app; [|solve[reflexivity]].
      econstructor; eauto.
    }
    {
      induction s; simpl in *; injections; tryfalse; subst.
      exploit (IHkappa _ _ H6); [solve[econstructor; eauto]|solve[simpl; repeat (rewrite List.length_app; simpl); lia] | intros; unpack ].
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
      exploit (IHkappa _ _ H4); [solve[econstructor; eauto]|solve[simpl; repeat (rewrite List.length_app; simpl); lia] | intros; unpack ].
      eapply star_trans_prop; [apply star_cred_append_stack; eauto|].
      eapply star_refl_prop.

      repeat rewrite List.app_comm_cons; erewrite append_stack_app; [|solve[reflexivity]].
      econstructor; eauto.
    }
    {
      induction s; simpl in *; injections; tryfalse; subst.
      exploit (IHkappa _ _ H4); [solve[econstructor; eauto]|solve[simpl; repeat (rewrite List.length_app; simpl); lia] | intros; unpack ].
      eapply star_trans_prop; [apply star_cred_append_stack; eauto|].
      eapply star_refl_prop.

      repeat rewrite List.app_comm_cons; erewrite append_stack_app; [|solve[reflexivity]].
      econstructor; eauto.
    }
    {
      induction s; simpl in *; injections; tryfalse; subst.
      exploit (IHkappa _ _ H5); [solve[econstructor; eauto]|solve[simpl; repeat (rewrite List.length_app; simpl); lia] | intros; unpack ].
      eapply star_trans_prop; [apply star_cred_append_stack; eauto|].
      eapply star_refl_prop.

      repeat rewrite List.app_comm_cons; erewrite append_stack_app; [|solve[reflexivity]].
      econstructor; eauto.
    }
    {
      induction s; simpl in *; injections; tryfalse; subst.
      exploit (IHkappa _ _ H5); [solve[econstructor; eauto]|solve[simpl; repeat (rewrite List.length_app; simpl); lia] | intros; unpack ].
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
      exploit (IHkappa _ _ H4); [solve[econstructor; eauto]|solve[simpl; repeat (rewrite List.length_app; simpl); lia] | intros; unpack ].
      eapply star_trans_prop; [apply star_cred_append_stack; eauto|].
      eapply star_refl_prop.

      repeat rewrite List.app_comm_cons; erewrite append_stack_app; [|solve[reflexivity]].
      econstructor; eauto.
    }
    {
      induction s; simpl in *; injections; tryfalse; subst.
      exploit (IHkappa _ _ H4); [solve[econstructor; eauto]|solve[simpl; repeat (rewrite List.length_app; simpl); lia] | intros; unpack ].
      eapply star_trans_prop; [apply star_cred_append_stack; eauto|].
      eapply star_refl_prop.

      repeat rewrite List.app_comm_cons; erewrite append_stack_app; [|solve[reflexivity]].
      econstructor; eauto.
    }
    {
      induction s; simpl in *; injections; tryfalse; subst.
      exploit (IHkappa _ _ H5); [solve[econstructor; eauto]|solve[simpl; repeat (rewrite List.length_app; simpl); lia] | intros; unpack ].
      eapply star_trans_prop; [apply star_cred_append_stack; eauto|].
      eapply star_refl_prop.

      repeat rewrite List.app_comm_cons; erewrite append_stack_app; [|solve[reflexivity]].
      econstructor; eauto.
    }
    {
      induction s; simpl in *; injections; tryfalse; subst.
      exploit (IHkappa _ _ H5); [solve[econstructor; eauto]|solve[simpl; repeat (rewrite List.length_app; simpl); lia] | intros; unpack ].
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
        { cleanup. simpl.
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
        exploit (IHkappa _ _ H4); [solve[econstructor; eauto]|solve[simpl; repeat (rewrite List.length_app; simpl); lia] | intros; unpack ].
        eapply star_trans_prop; [apply star_cred_append_stack; eauto|].
        eapply star_refl_prop.

        repeat rewrite List.app_comm_cons; erewrite append_stack_app; [|solve[reflexivity]].
        econstructor; eauto.
      }
    }
    {
      induction s; simpl in *; injections; tryfalse; subst.
      decompose H2.
      exploit (IHkappa _ _ H4); [solve[econstructor; eauto]|solve[simpl; repeat (rewrite List.length_app; simpl); lia] | intros; unpack ].
      eapply star_trans_prop; [apply star_cred_append_stack; eauto|].
      eapply star_refl_prop.

      repeat rewrite List.app_comm_cons; erewrite append_stack_app; [|solve[reflexivity]].
      econstructor; eauto.
    }
    {
      induction s; simpl in *; injections; tryfalse; subst.
      decompose H2.
      exploit (IHkappa _ _ H5); [solve[econstructor; eauto]|solve[simpl; repeat (rewrite List.length_app; simpl); lia] | intros; unpack ].
      eapply star_trans_prop; [apply star_cred_append_stack; eauto|].
      eapply star_refl_prop.

      repeat rewrite List.app_comm_cons; erewrite append_stack_app; [|solve[reflexivity]].
      econstructor; eauto.
    }
    {
      induction s; simpl in *; injections; tryfalse; subst.
      list_simpl.
      decompose H.
      decompose H13.
      exploit (IHkappa _ _ H5); [solve[econstructor; eauto]|solve[simpl; repeat (rewrite List.length_app; simpl); lia] | intros; unpack ].
      eapply star_trans_prop; [apply star_cred_append_stack; eauto|].
      eapply star_refl_prop.

      repeat rewrite List.app_comm_cons; erewrite append_stack_app; [|solve[reflexivity]].
      simpl.
      repeat rewrite List.app_comm_cons.
      rewrite <- List.app_assoc.
      simpl.
      simpl.
      rewrite List.app_comm_cons.
      erewrite append_stack_app; [|solve[reflexivity]].
      econstructor; eauto.
    }
  }
  { inversion 1; subst; repeat sinv_cong.
    { eapply star_step_prop. { econstructor; eauto. }
      eapply star_refl_prop.
      econstructor; eauto.
    }
    {
      induction s; simpl in *; injections; tryfalse; subst.
      exploit (IHkappa _ _ H4); [solve[econstructor; eauto]|solve[simpl; repeat (rewrite List.length_app; simpl); lia] | intros; unpack ].
      eapply star_trans_prop; [apply star_cred_append_stack; eauto|].
      eapply star_refl_prop.
      repeat rewrite List.app_comm_cons; erewrite append_stack_app; [|solve[reflexivity]].
      econstructor; eauto.
    }
    {
      induction s; simpl in *; injections; tryfalse; subst.
      exploit (IHkappa _ _ H4); [solve[econstructor; eauto]|solve[simpl; repeat (rewrite List.length_app; simpl); lia] | intros; unpack ].
      eapply star_trans_prop; [apply star_cred_append_stack; eauto|].
      eapply star_refl_prop.
      repeat rewrite List.app_comm_cons; erewrite append_stack_app; [|solve[reflexivity]].
      econstructor; eauto.
    }
    {
      induction s; simpl in *; injections; tryfalse; subst.
      exploit (IHkappa _ _ H5); [solve[econstructor; eauto]|solve[simpl; repeat (rewrite List.length_app; simpl); lia] | intros; unpack ].
      eapply star_trans_prop; [apply star_cred_append_stack; eauto|].
      eapply star_refl_prop.
      repeat rewrite List.app_comm_cons; erewrite append_stack_app; [|solve[reflexivity]].
      econstructor; eauto.
    }
    {
      induction s; simpl in *; injections; tryfalse; subst.
      exploit (IHkappa _ _ H5); [solve[econstructor; eauto]|solve[simpl; repeat (rewrite List.length_app; simpl); lia] | intros; unpack ].
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
      exploit (IHkappa _ _ H4); [solve[econstructor; eauto]|solve[simpl; repeat (rewrite List.length_app; simpl); lia] | intros; unpack ].
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
        exploit (IHkappa _ _ H4); [solve[econstructor; eauto]|solve[simpl; repeat (rewrite List.length_app; simpl); lia] | intros; unpack ].
        eapply star_trans_prop; [apply star_cred_append_stack; eauto|].
        eapply star_refl_prop.
        repeat rewrite List.app_comm_cons; erewrite append_stack_app; [|solve[reflexivity]].
        econstructor; eauto.
      }
    }
    {
      induction s; simpl in *; injections; tryfalse; subst.
      decompose H2.
      exploit (IHkappa _ _ H5); [solve[econstructor; eauto]|solve[simpl; repeat (rewrite List.length_app; simpl); lia] | intros; unpack ].
      eapply star_trans_prop; [apply star_cred_append_stack; eauto|].
      eapply star_refl_prop.
      repeat rewrite List.app_comm_cons; erewrite append_stack_app; [|solve[reflexivity]].
      econstructor; eauto.
    }
    {
      induction s; simpl in *; injections; tryfalse; subst.
      list_simpl.
      decompose H.
      decompose H8.
      exploit (IHkappa _ _ H5); [solve[econstructor; eauto]|solve[simpl; repeat (rewrite List.length_app; simpl); lia] | intros; unpack ].
      eapply star_trans_prop; [apply star_cred_append_stack; eauto|].
      eapply star_refl_prop.
      repeat rewrite List.app_comm_cons; erewrite append_stack_app; [|solve[reflexivity]]; simpl; repeat rewrite List.rev_involutive.

      rewrite <- List.app_assoc; simpl.
      erewrite append_stack_app; [|solve[reflexivity]].
      econstructor; eauto.
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
      exploit (IHkappa _ _ H4); [solve[econstructor; eauto]|solve[simpl; repeat (rewrite List.length_app; simpl); lia] | intros; unpack ].
      eapply star_trans_prop; [apply star_cred_append_stack; eauto|].
      eapply star_refl_prop.
      repeat rewrite List.app_comm_cons; erewrite append_stack_app; [|solve[reflexivity]].
      econstructor; eauto.
    }
    { induction s; simpl in *; injections; tryfalse; subst.
      exploit (IHkappa _ _ H4); [solve[econstructor; eauto]|solve[simpl; repeat (rewrite List.length_app; simpl); lia] | intros; unpack ].
      eapply star_trans_prop; [apply star_cred_append_stack; eauto|].
      eapply star_refl_prop.
      repeat rewrite List.app_comm_cons; erewrite append_stack_app; [|solve[reflexivity]].
      econstructor; eauto.
    }
    { induction s; simpl in *; injections; tryfalse; subst.
      exploit (IHkappa _ _ H5); [solve[econstructor; eauto]|solve[simpl; repeat (rewrite List.length_app; simpl); lia] | intros; unpack ].
      eapply star_trans_prop; [apply star_cred_append_stack; eauto|].
      eapply star_refl_prop.
      repeat rewrite List.app_comm_cons; erewrite append_stack_app; [|solve[reflexivity]].
      econstructor; eauto.
    }
    { induction s; simpl in *; injections; tryfalse; subst.
      exploit (IHkappa _ _ H5); [solve[econstructor; eauto]|solve[simpl; repeat (rewrite List.length_app; simpl); lia] | intros; unpack ].
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
      exploit (IHkappa _ _ H4); [solve[econstructor; eauto]|solve[simpl; repeat (rewrite List.length_app; simpl); lia] | intros; unpack ].
      eapply star_trans_prop; [apply star_cred_append_stack; eauto|].
      eapply star_refl_prop.
      repeat rewrite List.app_comm_cons; erewrite append_stack_app; [|solve[reflexivity]].
      econstructor; eauto.
    }
    { induction s; simpl in *; injections; tryfalse; subst.
      decompose H2.
      exploit (IHkappa _ _ H4); [solve[econstructor; eauto]|solve[simpl; repeat (rewrite List.length_app; simpl); lia] | intros; unpack ].
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
      { exploit (IHkappa _ _ H5); [solve[econstructor; eauto]|solve[simpl; repeat (rewrite List.length_app; simpl); lia] | intros; unpack ].
        eapply star_trans_prop; [apply star_cred_append_stack; eauto|].
        eapply star_refl_prop.
        repeat rewrite List.app_comm_cons; erewrite append_stack_app; [|solve[reflexivity]].
        econstructor; eauto.
      }
    }
    { induction s; simpl in *; injections; tryfalse; subst.
      list_simpl.
      decompose H.
      decompose H10.
      { inversion H5; subst; repeat sinv_cong.
        { simpl.

          admit "The diagram is not working because of this reason". }
        { learn (f_equal stack H).
          learn (f_equal (@List.length _) H10).
          induction s; simpl in *; list_simpl.
        }
        { learn (f_equal stack H).
          learn (f_equal (@List.length _) H10).
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
      {
        exploit (IHkappa _ _ H5); [solve[econstructor; eauto]|solve[simpl; repeat (rewrite List.length_app; simpl); lia] | intros; unpack ].
        eapply star_trans_prop; [apply star_cred_append_stack; eauto|].
        eapply star_refl_prop.
        repeat rewrite List.app_comm_cons; erewrite append_stack_app; [|solve[reflexivity]].
        simpl.
        rewrite List.rev_involutive.
        rewrite <- List.app_assoc.
        simpl.
        erewrite append_stack_app; [|solve[reflexivity]].
        econstructor; eauto.
      }
    }
  }
  { inversion 1; subst; repeat sinv_cong.
    { induction s; simpl in *; injections; tryfalse; subst.
      decompose H2.
      exploit (IHkappa _ _ H4); [solve[econstructor; eauto]|solve[simpl; repeat (rewrite List.length_app; simpl); lia] | intros; unpack ].
      eapply star_trans_prop; [apply star_cred_append_stack; eauto|].
      eapply star_refl_prop.
      repeat rewrite List.app_comm_cons; erewrite append_stack_app; [|solve[reflexivity]].
      econstructor; eauto.
    }
    { induction s; simpl in *; injections; tryfalse; subst.
      decompose H2.
      exploit (IHkappa _ _ H4); [solve[econstructor; eauto]|solve[simpl; repeat (rewrite List.length_app; simpl); lia] | intros; unpack ].
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
      {
        exploit (IHkappa _ _ H5); [solve[econstructor; eauto]|solve[simpl; repeat (rewrite List.length_app; simpl); lia] | intros; unpack ].
        eapply star_trans_prop; [apply star_cred_append_stack; eauto|].
        eapply star_refl_prop.
        repeat rewrite List.app_comm_cons; erewrite append_stack_app; [|solve[reflexivity]].
        econstructor; eauto.
      }
    }
    { induction s; simpl in *; injections; tryfalse; subst.
      list_simpl; decompose H.
      decompose H10.
      { (* intersting case *)
        inversion H5; subst; repeat sinv_cong.
        { simpl.
          (* The diagram is not working for this case. *)
          (eapply star_step_prop; [solve[econstructor; eauto]|]).
          admit "not working here.".
        }
        { learn (f_equal stack H).
          learn (f_equal (@List.length _) H10).
          induction s; simpl in *; list_simpl.
        }
        { learn (f_equal stack H).
          learn (f_equal (@List.length _) H10).
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
      {
        exploit (IHkappa _ _ H5); [solve[econstructor; eauto]|solve[simpl; repeat (rewrite List.length_app; simpl); lia] | intros; unpack ].
        eapply star_trans_prop; [apply star_cred_append_stack; eauto|].
        eapply star_refl_prop.
        repeat rewrite List.app_comm_cons; erewrite append_stack_app; [|solve[reflexivity]].
        simpl.
        rewrite List.rev_involutive.
        rewrite <- List.app_assoc.
        simpl.
        erewrite append_stack_app; [|solve[reflexivity]].
        repeat (econstructor; eauto).
      }
    }
  }
Abort.

(* -------------------------------------------------------------------------- *)
(*** Refined diagram ***)

(* As stated above, the naive diagram does not work. This is due to the cred_if_true reduction: two reduction are needed in the source, while only one reduction is possible in the target. To solve this issue, we modify slightly the diagram, permitting multiple reduction in the source as well as in the target.

More precisely, we show the following:
*)


Theorem correction_diagram:
  forall s1 s1' s2,
    cong_state s1 s1' ->
    cred s1 s2 ->
    exists s3 s3',
      star cred s2 s3 /\
      star cred s1' s3' /\
      cong_state s3 s3'
.
Abort.

(* The main point of using continution-based semantics and our reduction lemmas [star_refl_prop, star_step_prop, star_trans_prop] is that we can reuse the above proof with minimal modifications.

Indeed, the structure is globally the same. We need to change each [star_step_prop] with a similar application of [confluent_prop_star_step_right], and every cases that worked previously works again. There is no issues with the application of the induction principle as it is solved automatically using lia. 

This means we can focus on the remaning.
*)

Theorem correction_diagram_aux:
  forall kappa,
  forall s1,
    stack s1 = kappa ->
    forall s2,
      cred s1 s2 ->
      forall s1',
        cong_state s1 s1' ->
      exists s3 s3',
        star cred s2 s3 /\
        star cred s1' s3' /\
        cong_state s3 s3'
.

Ltac mytryfalse :=
  tryfalse;
  try solve [repeat match goal with 
  | [h: @eq state _ _ |- _ ] => learn (f_equal stack h)
  | [h: @eq (list _) _ _ |- _ ] => learn (f_equal (@List.length _) h)
  | [h: context[append_stack ?s _] |- _] => learn (eq_refl s); destruct s
  end; simpl in *; repeat list_simpl]
  .

induction kappa as [kappa IHkappa] using (
  well_founded_induction
    (wf_inverse_image _ nat _ (@List.length cont) 
    PeanoNat.Nat.lt_wf_0)).
rename IHkappa into IH; assert (IHkappa:= modify_WF_IH IH); clear IH.
intros until s2; induction 1; inversion 1; subst; repeat sinv_cong.

  (* Handling induction hypothesis and base cases.*)
  all: try (induction s; simpl in *; injections; tryfalse; subst).
  (* decompose equalities *)
  all: list_simpl;
  repeat match goal with
  | [h: _ ++ [_] = _ :: _ |- _] => decompose h
  | [h: _ ++ [_; _] = _ :: _ |- _] => decompose h
  | [h: _ :: _ = _ ++ [_] |- _] => decompose h
  | [h: _ :: _ = _ ++ [_; _] |- _] => decompose h
  end.
  all: try match goal with
  | [h: cong_state (mode_eval _ [] _) _ |- _] => inversion h; subst; mytryfalse
  | [h: cong_state (mode_cont [] _) _ |- _ ] => inversion h; subst; mytryfalse
  | [h: cong_state _ _ |- _] =>
    exploit (IHkappa _ _ h); [solve[econstructor; eauto]|solve[simpl; repeat (rewrite List.length_app; simpl); lia] | intros; unpack ]
  end.

  (* efficient stepping. *)
  all: try (repeat rewrite List.app_comm_cons; erewrite append_stack_app; [|solve[reflexivity]]).
  all: try (rewrite List.rev_involutive; simpl;
    rewrite <- List.app_assoc; simpl List.app;
    repeat rewrite List.app_comm_cons; erewrite append_stack_app; [|solve[reflexivity]];
    simpl stack; simpl with_stack)
  .
  all: repeat first[
    progress (eapply confluent_prop_star_trans_right; [solve[apply star_cred_append_stack; eauto]|])|
    progress (eapply confluent_prop_star_trans_left; [solve[apply star_cred_append_stack; eauto]|])|
    progress (repeat (simpl; try sinv_cong; eapply confluent_prop_star_step_right; [solve[ econstructor; eauto]|]))|
    progress (repeat (simpl; try sinv_cong; eapply confluent_prop_star_step_left; [solve[ econstructor; eauto]|]))|
    progress (repeat (simpl; eapply confluent_prop_star_step_right; [solve[ econstructor; eauto]|]))|
    progress (repeat (simpl; eapply confluent_prop_star_step_left; [solve[ econstructor; eauto]|]))
  ].

  (* Finishing up the proof*)
  all: try solve
    [ eapply confluent_prop_star_refl; repeat (econstructor; eauto)
    | eapply confluent_prop_star_refl;
      match goal with [|- cong_state ?s1 ?s2] =>
        rewrite (@append_stack_all s1);
        rewrite (@append_stack_all s2);
        simpl with_stack; simpl stack
      end;
      repeat (econstructor; eauto)
    ].
  { inversion H2; subst; mytryfalse.
    learn (Forall2_nth_error_Some_left H7 H1); unpack.
    learn (Forall2_nth_error_Some H7 H1 H).
    eapply confluent_prop_star_step_right; [solve[econstructor; eauto]|].
    eapply confluent_prop_star_refl.
    repeat (econstructor; eauto).
  }
  { simpl.
    rewrite <- List.app_assoc; simpl List.app;
    repeat rewrite List.app_comm_cons; erewrite append_stack_app; [|solve[reflexivity]];
    simpl stack; simpl with_stack;
    rewrite List.rev_involutive.
    repeat first[
      eapply confluent_prop_star_trans_right; [solve[apply star_cred_append_stack; eauto]|]|
      eapply confluent_prop_star_trans_left; [solve[apply star_cred_append_stack; eauto]|]|
      repeat (simpl; sinv_cong; eapply confluent_prop_star_step_right; [solve[ econstructor; eauto]|])|
      repeat (simpl; sinv_cong; eapply confluent_prop_star_step_left; [solve[ econstructor; eauto]|])
    ].

    all: try solve
    [ eapply confluent_prop_star_refl; repeat (econstructor; eauto)
    | eapply confluent_prop_star_refl;
      match goal with [|- cong_state ?s1 ?s2] =>
        rewrite (@append_stack_all s1);
        rewrite (@append_stack_all s2);
        simpl with_stack; simpl stack
      end;
      repeat (econstructor; eauto)
    ].
  }
  { simpl.
    rewrite <- List.app_assoc; simpl List.app;
    repeat rewrite List.app_comm_cons; erewrite append_stack_app; [|solve[reflexivity]];
    simpl stack; simpl with_stack;
    rewrite List.rev_involutive.
    repeat first[
      eapply confluent_prop_star_trans_right; [solve[apply star_cred_append_stack; eauto]|]|
      eapply confluent_prop_star_trans_left; [solve[apply star_cred_append_stack; eauto]|]|
      repeat (simpl; sinv_cong; eapply confluent_prop_star_step_right; [solve[ econstructor; eauto]|])|
      repeat (simpl; sinv_cong; eapply confluent_prop_star_step_left; [solve[ econstructor; eauto]|])
    ].

    all: try solve
    [ eapply confluent_prop_star_refl; repeat (econstructor; eauto)
    | eapply confluent_prop_star_refl;
      match goal with [|- cong_state ?s1 ?s2] =>
        rewrite (@append_stack_all s1);
        rewrite (@append_stack_all s2);
        simpl with_stack; simpl stack
      end;
      repeat (econstructor; eauto)
    ].
  }
  {
    simpl.
    rewrite <- List.app_assoc; simpl List.app;
    repeat rewrite List.app_comm_cons; erewrite append_stack_app; [|solve[reflexivity]];
    simpl stack; simpl with_stack;
    rewrite List.rev_involutive.
    repeat first[
      eapply confluent_prop_star_trans_right; [solve[apply star_cred_append_stack; eauto]|]|
      eapply confluent_prop_star_trans_left; [solve[apply star_cred_append_stack; eauto]|]|
      repeat (simpl; try sinv_cong; eapply confluent_prop_star_step_right; [solve[ econstructor; eauto]|])|
      repeat (simpl; try sinv_cong; eapply confluent_prop_star_step_left; [solve[ econstructor; eauto]|])
    ].

    all: try solve
    [ eapply confluent_prop_star_refl; repeat (econstructor; eauto)
    | eapply confluent_prop_star_refl;
      match goal with [|- cong_state ?s1 ?s2] =>
        rewrite (@append_stack_all s1);
        rewrite (@append_stack_all s2);
        simpl with_stack; simpl stack
      end;
      repeat (econstructor; eauto)
    ].
  }
  {
    simpl.
    rewrite <- List.app_assoc; simpl List.app;
    repeat rewrite List.app_comm_cons; erewrite append_stack_app; [|solve[reflexivity]];
    simpl stack; simpl with_stack;
    rewrite List.rev_involutive.
    repeat first[
      eapply confluent_prop_star_trans_right; [solve[apply star_cred_append_stack; eauto]|]|
      eapply confluent_prop_star_trans_left; [solve[apply star_cred_append_stack; eauto]|]|
      repeat (simpl; sinv_cong; eapply confluent_prop_star_step_right; [solve[ econstructor; eauto]|])|
      repeat (simpl; sinv_cong; eapply confluent_prop_star_step_left; [solve[ econstructor; eauto]|])
    ].

    all: try solve
    [ eapply confluent_prop_star_refl; repeat (econstructor; eauto)
    | eapply confluent_prop_star_refl;
      match goal with [|- cong_state ?s1 ?s2] =>
        rewrite (@append_stack_all s1);
        rewrite (@append_stack_all s2);
        simpl with_stack; simpl stack
      end;
      repeat (econstructor; eauto)
    ].
  }
Qed.

Theorem correction_diagram:
  forall s1 s1' s2,
    cong_state s1 s1' ->
    cred s1 s2 ->
    exists s3 s3',
      star cred s2 s3 /\
      star cred s1' s3' /\
      cong_state s3 s3'
.
Proof.
  intros.
  eapply (correction_diagram_aux (stack s1) _ eq_refl _ H0 _ H).
Qed.

End trans2.

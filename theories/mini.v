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
  | Lam (t: {bind term})
  | Value (v: value)

with value :=
  | Closure (t: {bind term}) (sigma: list value)
.

#[export] Instance Ids_term : Ids term. derive. Defined.
#[export] Instance Rename_term : Rename term. derive. Defined.
#[export] Instance Subst_term : Subst term. derive. Defined.
#[export] Instance SubstLemmas_term : SubstLemmas term. derive. Qed.

Lemma ids_inj:
  forall x y, ids x = ids y -> x = y.
intros; inj; eauto.
Qed.


(* Strong induction principle for terms *)

Fixpoint size_term t := 
  match t with
  | Var _ => 0
  | App t1 t2 => S (size_term t1 + size_term t2)
  | Lam t => S (size_term t)
  | Value v => S (size_value v)
  end
with size_value v :=
  match v with
  | Closure t env => S (size_term t + (List.list_sum (List.map size_value env)))
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
    {HClosure: forall t,
      P t -> forall sigma, (List.Forall P0 sigma) -> P0 (Closure t sigma)},
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
        eapply HValue
      ].
      1: eapply (IHx (inl t1)).
      2: eapply (IHx (inl t2)).
      3: eapply (IHx (inl t)).
      4: eapply (IHx (inr v)).
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
      (forall t : term, P t) /\ (forall v : value, P0 v).
Proof.
  split; intros.
  unshelve eapply (term_value_induction (inl t)); eauto.
  unshelve eapply (term_value_induction (inr v)); eauto.
Qed.


Inductive cont :=
  | CAppR (t2: term) (* [\square t2] *)
  | CClosure (t_cl: {bind term}) (sigma_cl: list value)
  (* [Clo(x, t_cl, sigma_cl) \square] Since we are using De Bruijn indices,
     there is no variable x. *)
  | CReturn (sigma: list value) (* call return *)
.

Inductive result :=
  | RValue (v: value)
.


Inductive state :=
  | mode_eval (e: term) (kappa: list cont) (env: list value)
  | mode_cont (kappa: list cont) (env: list value) (result: result)
.


(*** continuation step semantics ***)

Inductive cred: state -> state -> Prop :=


  (** Rules related to the lambda calculus *)
  | cred_var:
    forall x kappa sigma v,
    List.nth_error sigma x = Some v ->
    cred
      (mode_eval (Var x) kappa sigma)
      (mode_cont kappa sigma (RValue v))

  | cred_app:
    forall t1 t2 kappa sigma,
    cred
      (mode_eval (App t1 t2) kappa sigma)
      (mode_eval t1 ((CAppR t2) :: kappa) sigma)

  | cred_clo:
    forall t kappa sigma,
    cred
      (mode_eval (Lam t) kappa sigma)
      (mode_cont kappa sigma (RValue (Closure t sigma)))

  | cred_arg:
    forall t2 kappa sigma tcl sigmacl,
    cred
      (mode_cont ((CAppR t2)::kappa) sigma (RValue (Closure tcl sigmacl)))
      (mode_eval t2 ((CClosure tcl sigmacl)::kappa) sigma)
  
  | cred_value:
    forall v kappa sigma,
    cred
      (mode_eval (Value v) kappa sigma)
      (mode_cont kappa sigma (RValue v))
      

  | cred_beta:
    forall t_cl sigma_cl kappa sigma v,
    cred
      (mode_cont ((CClosure t_cl sigma_cl)::kappa) sigma (RValue v))
      (mode_eval t_cl (CReturn sigma::kappa)  (v :: sigma_cl))

  | cred_return:
    forall sigma_cl kappa sigma r,
    cred
      (mode_cont (CReturn sigma::kappa) sigma_cl r)
      (mode_cont kappa sigma r)
.

Import List.ListNotations.
Open Scope list.

Definition subst_of_env sigma :=
  fun n =>
  match List.nth_error sigma n with
  | None => ids (n - List.length sigma)
  | Some t => Value t
  end
.


(*** small step semantics ***)

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
    forall t u1 u2 sigma,
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
.


(*** Equivalence relation definition ***)

Inductive sim_term: term -> term -> Prop :=
  | sim_term_1: forall x y, x = y -> sim_term (Var x) (Var y)
  | sim_term_2: forall t1 t2 u1 u2,
    sim_term t1 u1 ->
    sim_term t2 u2 ->
    sim_term (App t1 t2) (App u1 u2)
  | sim_term_3: forall t1 u1,
    sim_term t1 u1 ->
    sim_term (Lam t1) (Lam u1)
  | sim_term_4: forall v1 w1,
    sim_value v1 w1 ->
    sim_term (Value v1) (Value w1)
with sim_value: value -> value -> Prop :=
  | sim_value_1: forall t1 t2 sigma1 sigma2,
    sim_term t1.[up (subst_of_env sigma1)] t2.[up (subst_of_env sigma2)] ->
    sim_value (Closure t1 sigma1) (Closure t2 sigma2)
.

(* "ca ne me choque pas, mais je trouve ça dommage" parce que en small steps, je fais de la subst. C'est artificiel d'utiliser des subtitution et pas un lambda calcul small steps. *)


(* We prove three main properties on this simulation property : *)

(* It is an equivalence class *)

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
  (param1: term * list value)
  (k: cont)
  : term * list value :=
  let '(t, sigma) := param1 in
  match k with
  | CAppR t2 =>
    (App t t2.[subst_of_env sigma], sigma)
  | CClosure t_cl sigma_cl =>
    (App (Value (Closure t_cl sigma_cl)) t, sigma)
  | CReturn sigma' => (t, sigma')
  end.

Definition apply_conts
  (kappa: list cont)
  : term * list value -> term * list value :=
  List.fold_left apply_cont kappa.

Definition apply_return (r: result) :=
  match r with
  | RValue v => Value v
  end.

Definition apply_state_aux (s: state): term * list value :=
  match s with
  | mode_eval t stack env =>
    (apply_conts stack (t.[subst_of_env env], env))
  | mode_cont stack env r =>
    (apply_conts stack ((apply_return r),env))
  end.
  
(* We use an notation to be apple to simplify this definition. *)
Notation "'apply_state' s" := (fst (apply_state_aux s)) (at level 50, only parsing).



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


Fixpoint last (l: list cont) (env0: list value) : list value :=
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
Qed.

Theorem sred_apply_conts: forall kappa t t' sigma,
  sred t t' ->
  sred
    (fst (apply_conts kappa (t, sigma)))
    (fst (apply_conts kappa (t', sigma)))
.
Proof.
  induction kappa as [|k kappa] using List.rev_ind.
  { induction 1; simpl; econstructor; eauto. }
  { induction k; intros t t' env Htt'.

    all: pose proof (IHkappa _ _ env Htt').
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


Theorem star_sred_apply_conts: forall kappa t t' sigma,
  star sred t t' ->
  star sred
    (fst (apply_conts kappa (t, sigma)))
    (fst (apply_conts kappa (t', sigma)))
.
Proof.
  induction 1; econstructor; eauto using sred_apply_conts.
Qed.

Lemma sim_state_apply_conts {kappa t1 t2 sigma}:
  sim_term t1 t2 ->
  sim_term
    (fst (apply_conts kappa (t1, sigma)))
    (fst (apply_conts kappa (t2, sigma))).
Proof.
  revert sigma t1 t2.
  induction kappa as [|k kappa] using List.rev_ind; simpl; eauto.
  induction k; intros; repeat rewrite apply_conts_app; simpl; unfold apply_cont; sp; simpl.
  { econstructor. eapply IHkappa; eauto.
    repeat rewrite snd_apply_conts_last.
    reflexivity.
  }
  { econstructor.
    { reflexivity. }
    { eapply IHkappa; eauto. }
  }
  { eapply IHkappa; eauto. }
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

Definition stack s :=
  match s with
  | mode_cont kappa _ _ => kappa
  | mode_eval _ kappa _ => kappa
  end.

Definition with_stack s kappa :=
  match s with
  | mode_cont _ sigma r => mode_cont kappa sigma r
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
  apply_state_aux (append_stack s kappa) =
  apply_conts kappa (apply_state_aux s).
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

Lemma cred_snd_apply_sate {s1 s2}:
  cred s1 s2 ->
  snd (apply_state_aux s1) = snd (apply_state_aux s2).
Proof.
  induction 1; simpl; repeat rewrite snd_apply_conts_last; eauto.
Qed.

Lemma star_cred_snd_apply_sate {s1 s2}:
  star cred s1 s2 ->
  snd (apply_state_aux s1) = snd (apply_state_aux s2).
Proof.
  induction 1; eauto.
  rewrite <- IHstar.
  eapply cred_snd_apply_sate; eauto.
Qed.

Lemma value_apply_conts {v kappa t env0}:
  Value v = fst (apply_conts kappa (t, env0)) ->
  List.Forall (fun k => exists sigma, k = CReturn sigma) kappa /\ (
  (Value v = t))
  .
Proof.
  split; revert v kappa t env0 H.
  { induction kappa as [|k kappa] using List.rev_ind.
    { econstructor. }
    { induction k.
      all: intros.
      all: try rewrite apply_conts_app in *; simpl in *; unfold apply_cont in *; sp; simpl in *; inj.
      { learn (IHkappa _ _ H); eapply List.Forall_app; eauto. }
    }
  }
  { induction kappa as [|k kappa] using List.rev_ind.
    { induction t; asimpl; intros; inj; subst; eauto. }
    { destruct t; induction k.
      all: intros.
      all: try rewrite apply_conts_app in *; simpl in *; unfold apply_cont in *; sp; simpl in *; inj.
      { destruct (IHkappa (Var x) _ H); inj; unpack; injections; subst; eauto. }
      all: try match goal with
      | [h: Value _ = fst (apply_conts _ (?t, ?env)) |- _] =>
        destruct (IHkappa t env); simpl; eauto
      end.
    }
  }
Qed.

Lemma Forall_CReturn_star_cred {kappa1 env0 result kappa2}:
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
Qed.


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
(fst (apply_conts kappa (t.[subst_of_env env], env))) = apply_state (mode_eval t kappa env).
Proof.
  simpl; eauto.
Qed.

Lemma apply_conts_Value_apply_state {v kappa env}:
(fst (apply_conts kappa (Value v, env))) = apply_state (mode_cont kappa env (RValue v)).
Proof.
  simpl; eauto.
Qed.


Lemma fst_apply_conts_CReturn {kappa sigma t}:
  fst (apply_conts (kappa ++ [CReturn sigma]) t) = fst (apply_conts kappa t).
Proof.
  rewrite apply_conts_app; simpl; unfold apply_cont; sp; simpl; eauto.
Qed.

(* The handling of CReturn is orthogonal to the other continuations, hence we proove it in a different way. *)
Lemma induction_case_CReturn
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
Qed.


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
        { learn (star_cred_snd_apply_sate H2); simpl in *; subst.
          reflexivity.
        }
      }
    }
    {
      induction result0; simpl; inversion 1.
    }
  }
  { induction s1; induction k; try match goal with [r: result |- _]=> induction r end; simpl; intro Hkappa; subst; simpl.
    all: rewrite apply_conts_app; simpl; unfold apply_cont; sp; simpl.
    all: intros t3 Ht2t3.

    all: try match goal with [|-context [CReturn ]] =>
    eapply induction_case_CReturn; eauto; simpl;
    try rewrite fst_apply_conts_CReturn; eauto end.

    all: match typeof Ht2t3 with sred ?u1 ?u2 => remember u1 as u end.
    generalize dependent env; generalize dependent e.
    all: induction Ht2t3; intros; inj; tryfalse.
    all: repeat match goal with
      [h: Value _ = fst (apply_conts _ _) |- _] =>
        learn (value_apply_conts h); clear h; unpack; repeat subst_of_env
      end.
    all: repeat rewrite snd_apply_conts_last in *.
    all: injections; subst.
    all: repeat (
      repeat (eapply star_step_prop; [solve[econstructor; eauto]|]);
      repeat (eapply star_trans_prop; [solve[eapply Forall_CReturn_star_cred; eauto]|])
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

      rewrite <- (star_cred_snd_apply_sate H0).
      simpl; rewrite snd_apply_conts_last.
      reflexivity.
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
      pose proof (star_cred_snd_apply_sate H0); simpl in *; rewrite snd_apply_conts_last in *; rewrite H1.
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
  all: try rewrite List.app_length; simpl; lia.
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

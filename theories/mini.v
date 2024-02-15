Require Export Autosubst.Autosubst.
Require Export AutosubstExtra.
Require Import Autosubst_FreeVars.
Require Import String.
Require Import Coq.ZArith.ZArith.
Require Import tactics.
Import List.ListNotations.

Require Import Coq.Classes.SetoidClass.


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
#[export] Instance Idslemmas_term : IdsLemmas term.
  econstructor.
  unfold ids, Ids_term.
  intros; inj; eauto.
Defined.
#[export] Instance Rename_term : Rename term. derive. Defined.
#[export] Instance Subst_term : Subst term. derive. Defined.
#[export] Instance SubstLemmas_term : SubstLemmas term. derive. Qed.

Lemma ids_inj:
  forall x y, ids x = ids y -> x = y.
intros; inj; eauto.
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
Require Import Autosubst_FreeVars.
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

Scheme term_value_ind := Induction for term Sort Prop
  with value_term_ind := Induction for value Sort Prop.

Scheme sim_term_sim_value_ind := Induction for sim_term Sort Prop
with sim_value_sim_term_ind := Induction for sim_value Sort Prop.

Theorem term_indudction
	 : forall (P : term -> Prop) (P0 : value -> Prop),
       (forall x : var, P (Var x)) ->
       (forall t1 : term, P t1 -> forall t2 : term, P t2 -> P (App t1 t2)) ->
       (forall t : {bind term}, P t -> P (Lam t)) ->
       (forall v : value, P0 v -> P (Value v)) ->
       (forall t : {bind term},
        P t -> forall sigma : list value, P0 (Closure t sigma)) ->
       (forall t : term, P t) /\ forall v : value, P0 v.
Proof.
  split.
  eapply term_value_ind; eauto.
  eapply value_term_ind; eauto.
Qed.



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
split.
eapply sim_term_sim_value_ind; eauto.
eapply sim_value_sim_term_ind; eauto.
Qed.


(* this is obviously an equivalence relation, and substitution is an morphism. *)

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

Lemma sim_term_reflexive: Reflexive sim_term /\ Reflexive sim_value.
  (*** This proof is false. We need to have a stronger induction principle to prove this. ***)
  eapply term_indudction.
  { econstructor; eauto. }
  { econstructor; eauto. }
  { econstructor; eauto. }
  { econstructor; eauto. }
  { econstructor; eauto. admit. }
Abort.

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

Instance Reflexive_sim_term : Reflexive sim_term. Admitted.
Instance Symmetric_sim_term : Symmetric sim_term. destruct sim_symmetric; eauto. Qed.
Instance Transtive_sim_term : Transitive sim_term. destruct sim_transitive; eauto. Qed.


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


Inductive inv_state: state -> term -> Prop :=
  | InvBase: forall s,
    inv_state s (apply_state s)
  | InvStep: forall s t1,
    inv_state s t1 ->
    forall t2,
    sim_term t1 t2 ->
    inv_state s t2
.

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

Lemma last_snd_apply_conts :
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

    all: repeat rewrite last_snd_apply_conts.
    
    all: try econstructor; eauto.
  }
Qed.

Require Import sequences.

Theorem star_sred_apply_conts: forall kappa t t' sigma,
  star sred t t' ->
  star sred
    (fst (apply_conts kappa (t, sigma)))
    (fst (apply_conts kappa (t', sigma)))
.
Proof.
  induction 1; econstructor; eauto using sred_apply_conts.
Qed.

Lemma inversion_inv_state:
  forall s t1,
  inv_state s t1 ->
  exists t,
    sim_term t1 t /\ apply_state s = t.
Proof.
  induction 1.
  { eexists; split; eauto. reflexivity. }
  { intros; inj; subst.
    edestruct IHinv_state; eauto; unpack.
    eexists; split; eauto.
    symmetry.
    etransitivity.
    symmetry.
    eauto.
    eauto.
  }
Qed.


Lemma inv_state_from_equiv {t2 s}:
  sim_term (apply_state s) t2 ->
  inv_state s t2.
Proof.
  repeat econstructor; eauto.
Qed.

Lemma inv_state_apply_conts {kappa t1 t2 sigma}:
  sim_term t1 t2 ->
  sim_term
    (fst (apply_conts kappa (t1, sigma)))
    (fst (apply_conts kappa (t2, sigma))).
Proof.
  revert sigma t1 t2.
  induction kappa as [|k kappa] using List.rev_ind; simpl; eauto.
  induction k; intros; repeat rewrite apply_conts_app; simpl; unfold apply_cont; sp; simpl.
  { econstructor. eapply IHkappa; eauto.
    repeat rewrite last_snd_apply_conts.
    reflexivity.
  }
  { econstructor.
    { reflexivity. }
    { eapply IHkappa; eauto. }
  }
  { eapply IHkappa; eauto. }
Qed.

Lemma lift_inj_EVar:
  forall t x,
  lift 1 t = Var (S x) <-> t = Var x.
Proof.
  split; intros.
  { eauto using lift_inj. }
  { subst. eauto. }
Qed.


Lemma fv_Var_eq:
  forall k x,
  fv k (Var x) <-> x < k.
Proof.
  unfold fv. asimpl. induction k; intros.
  { asimpl. split; intros; exfalso.
    { unfold ids, Ids_term in *. injections.
      eapply Nat.neq_succ_diag_l. eauto. }
    { lia. }
  }
  (* Step. *)
  { destruct x; asimpl.
    { split; intros. { lia. } { reflexivity. }
  }
    rewrite lift_inj_EVar. rewrite IHk. lia. }
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


#[export]
Hint Rewrite
  fv_Var_eq
  fv_Lam_eq
  fv_App_eq
  : fv.

Lemma fv_1_subst_upn { t k sigma }:
  fv k t ->
    t.[upn k sigma] = t.
Proof.
  revert k sigma.
  induction t; simpl; intros.
  { rewrite fv_Var_eq in *. 
    eapply upn_k_sigma_x; eauto.
    eapply SubstLemmas_term.
  }
  { rewrite IHt1, IHt2; fv; unpack; eauto. }
  { rewrite fold_up_upn, IHt; fv; eauto. }
  { eauto. }
Qed.

Lemma iterate_1: forall {A : Type} (f : A -> A) (a : A), iterate f 1 a = f a.
Proof.
  intros.
  rewrite iterate_S, iterate_0; eauto.
Qed.

Lemma fv_1_subst_up { t sigma }:
  fv 1 t ->
    t.[up sigma] = t.
Proof.
  replace (up sigma) with (upn 1 sigma) by eapply iterate_1.
  eapply fv_1_subst_upn.
Qed.

Lemma subst_of_env_nil_ids:
  subst_of_env [] = ids.
Proof.
  eapply FunctionalExtensionality.functional_extensionality.
  induction x; unfold subst_of_env; simpl; eauto.
Qed.

Theorem simulation_cred_sred:
  forall s1 s2,
    cred s1 s2 ->
    exists t,
      inv_state s2 t /\
      star sred (apply_state s1) t.
Proof.
  induction 1; try induction o.
  all: simpl.
  all: try solve [eexists; split; [eapply InvBase|]; eapply star_refl].
  { eexists; split; [eapply InvBase|].
    simpl; unfold subst_of_env; rewrite H; eauto with sequences. }
  {
    eexists; split.
    2:{ eapply star_sred_apply_conts. eapply star_one. econstructor. }
    eapply inv_state_from_equiv.
    eapply inv_state_apply_conts.
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



Lemma subst_env_cons v sigma:
  subst_of_env (v :: sigma) = (Value v) .: subst_of_env sigma.
Proof.
  eapply FunctionalExtensionality.functional_extensionality.
  induction x; asimpl; eauto.
Qed.


Lemma proper_inv_state_sred:
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
    replace (t.[subst_of_env (v :: sigma')]) with t.[up (subst_of_env sigma')].[Value v/] by (rewrite subst_env_cons; asimpl; eauto).
    replace (t2.[subst_of_env (w0 :: sigma2)]) with t2.[up (subst_of_env sigma2)].[Value w0/] by (rewrite subst_env_cons; asimpl; eauto).
    eapply sim_term_subst; eauto.
    { induction x; simpl; econstructor; eauto. }
    
  }
  { learn (IHsred _ H5); unpack.
    inversion H3; subst.
    inversion H6; subst.
    repeat econstructor; eauto.
  }
  {
    learn (IHsred _ H3); unpack.
    repeat econstructor; eauto.
  }
Qed.


Lemma proper_inv_state_star_sred:
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
    learn (proper_inv_state_sred _ _ H _ H1); unpack.
    eexists; split; eauto.
    eapply star_step_n1; eauto.
  }
Qed.

Theorem simulation_cred_sred_inv:
  forall s1 s2,
    cred s1 s2 ->
    forall t1,
      inv_state s1 t1 ->
      exists t2,
        inv_state s2 t2 /\ star sred t1 t2.
Proof.
  intros ? ? Hs1s2 ? Hs1t1.
  learn (simulation_cred_sred _ _ Hs1s2); unpack; subst.
  repeat match goal with
  | [h: inv_state  _ _ |- _] =>
    learn (inversion_inv_state _ _ h); unpack; subst
  end.
  learn (proper_inv_state_star_sred _ _ H0 _ (symmetry H2)); unpack.
  eexists; split; [|eauto].
  eapply inv_state_from_equiv.
  etransitivity; [symmetry|]; eauto.
Qed.

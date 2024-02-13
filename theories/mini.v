Require Export Autosubst.Autosubst.
Require Export AutosubstExtra.
Require Import Autosubst_FreeVars.
Require Import String.
Require Import Coq.ZArith.ZArith.
Require Import tactics.

From Equations Require Import Equations.
Import List.ListNotations.

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

(* this is obviously an equivalence relation. *)

Require Import Coq.Classes.SetoidClass.

Instance Reflexive_sim_term : Reflexive sim_term. Admitted.
Instance Transtive_sim_term : Transitive sim_term. Admitted.
Instance Symmetric_sim_term : Symmetric sim_term. Admitted.
Instance Equivalence_sim_term : Equivalence sim_term. Admitted.

Instance Setoid_term: @Setoid term := {
  equiv := sim_term;
  setoid_equiv := Equivalence_sim_term
}.

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
  | InvValue: forall s t1,
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

Lemma inv_state_value_aux:
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

Lemma fv_1_subst_upn { t k sigma }:
  fv k t ->
    t.[upn k sigma] = t.
Proof.
  revert k sigma.
  induction t; simpl; intros.
  { admit.
    (* fv k (Var x) <-> x < k
    upn k sigma x = Var x <-> x < k *)
  }
  { rewrite IHt1. rewrite IHt2. eauto. all: admit "ok". }
  { rewrite fold_up_upn. rewrite IHt; eauto. all: admit "ok". }
  { eauto. }
Admitted.

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
    (* require the invariant that terms inside closures are closed. *)
    assert (fv 1 (t.[up (subst_of_env sigma)])). { admit. }
    replace (t.[up (subst_of_env sigma)].[up (subst_of_env [])]) with (t.[up (subst_of_env sigma)]).
    reflexivity.
    symmetry.
    eapply fv_1_subst_up.
    eauto.
  }
  { eexists; split; [eapply InvBase|]; simpl.
    eapply star_sred_apply_conts.
    repeat econstructor.
  }
Admitted.


Lemma value_apply_conts_inversion_eval {v kappa t env0}:
  Value v = fst (apply_conts kappa (t, env0)) ->
  List.Forall (fun k => exists sigma, k = CReturn sigma) kappa /\ (
  (Value v = t))
  .
Proof.
  (* imported from cred_to_sred *)
Admitted.

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




Theorem simulation_cred_sred_inv:
  forall s1 s2,
    cred s1 s2 ->
    forall t1,
    inv_state s1 t1 ->
    exists t2,
    inv_state s2 t2 /\ star sred t1 t2.
Proof.
  intros s1 s2 Hs1s2.
  pose proof (Hs1s2) as Hs1s2'.
  induction Hs1s2'.
  all: intros tt1 IHt1.
  all: inversion IHt1; subst; clear IHt1.
  all: simpl.
  all: try solve [pose proof (simulation_cred_sred _ _ Hs1s2);
  eexists; split; eauto; econstructor].
  
  {
    admit.
    pose proof (inv_state_value H); unpack. simpl in *.
    symmetry in H3.
    pose proof (value_apply_conts_inversion_eval H3); unpack.
    pose proof (nth_error_subst_of_env H).
    rewrite <- H5 in H6; inj. (* could be automatized if only coq used egraphs... *)

    eexists; split; [|eapply star_refl].
    pose proof (simulation_cred_sred _ _ Hs1s2).
    simpl apply_state_aux at 1 in H6.
    rewrite <- H3 in H6. (* here to... *)
    pose proof (star_sred_Value H6).
    eapply inv_state_from_equiv; eauto with sequences.
  }

  {
    pose proof (inv_state_value H); unpack. simpl in *.
    symmetry in H2.
    pose proof (value_apply_conts_inversion_eval H2); unpack.
    congruence.
  }

  {
    pose proof (inv_state_value H); unpack. simpl in *.
    symmetry in H2.
    pose proof (value_apply_conts_inversion_eval H2); unpack.
    congruence.
  }

  {
    pose proof (inv_state_value H); unpack. simpl in *.
    symmetry in H2.
    pose proof (value_apply_conts_inversion_eval H2); unpack.
    congruence.
  }

  {
    pose proof (inv_state_value H); unpack. simpl in *.
    symmetry in H2.
    pose proof (value_apply_conts_inversion_eval H2); unpack.
    congruence.
  }

  {
    pose proof (inv_state_value H); unpack. simpl in *.
    symmetry in H2.
    pose proof (value_apply_conts_inversion_eval H2); unpack.
    induction r; simpl in *; inj.

    eexists; split; [|eapply star_refl].
    pose proof (simulation_cred_sred _ _ Hs1s2).
    simpl apply_state_aux at 1 in H4.
    rewrite <- H2 in H4. (* here to... *)
    pose proof (star_sred_Value H4).
    eapply inv_state_from_equiv; eauto with sequences.
  }
Qed.

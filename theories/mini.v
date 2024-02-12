Require Export Autosubst.Autosubst.
Require Export AutosubstExtra.
Require Import Autosubst_FreeVars.
Require Import String.
Require Import Coq.ZArith.ZArith.
Require Import tactics.
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

Require Import sequences.


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

Inductive inv_value: value -> value -> Prop :=
.

Inductive inv_state: state -> term -> Prop :=
  | InvBase: forall s,
    inv_state s (apply_state s)
  | InvValue: forall s v v',
    inv_state s (Value v) ->
    inv_value v v' ->
    inv_state s (Value v')
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

Theorem star_sred_apply_conts: forall kappa t t' sigma,
  star sred t t' ->
  star sred
    (fst (apply_conts kappa (t, sigma)))
    (fst (apply_conts kappa (t', sigma)))
.
Proof.
  induction 1; econstructor; eauto using sred_apply_conts.
Qed.

Lemma inv_state_value:
  forall s t,
  inv_state s t ->
  forall v, t = Value v ->
  exists v',
    star inv_value v' v /\ apply_state s = Value v'.
Proof.
  induction 1.
  { eexists; split; eauto. econstructor. }
  { intros; inj; subst.
    edestruct IHinv_state; eauto; unpack.
    eexists; split; eauto.
    eauto with sequences.
  }
Qed.

Definition sym {T} R (x y:T) := R x y \/ R y x.

Lemma inv_state_nvalue_aux:
  forall s t,
  inv_state s t ->
  forall v1, t = Value v1 ->
  forall t2, inv_state s t2 ->
  exists v2, t2  = Value v2 /\ star (sym inv_value) v1 v2.
Proof.
  unfold sym.
  induction 1.
  { intros v1 Hv1.
    induction 1.
    { eexists; split; eauto with sequences. }
    { destruct IHinv_state as [v0 ?]; eauto; unpack.
      inj; subst.
      eexists; split; eauto.
      eapply star_step_n1; eauto.
    }
  }
  {
    intros; inj; subst.
    edestruct IHinv_state as [v2 ?]; eauto; unpack; subst.
    eexists; split; eauto.
    eapply star_step; eauto.
  }
Qed.

Lemma 

Theorem simulation_cred_sred:
  forall s1 s2,
    cred s1 s2 ->
    forall t1,
    inv_state s1 t1 ->
    exists t2,
    inv_state s2 t2 /\ star sred t1 t2.
Proof.
  induction 1.
  all: intros tt1 IHt1.
  all: inversion IHt1; subst; clear IHt1.
  all: simpl.
  
  2: { eexists; split; [|eapply star_refl].
    pose proof (inv_state_nvalue _ _ H0).

  }
Qed.

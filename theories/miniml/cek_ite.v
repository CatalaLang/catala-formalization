Require Export Autosubst.Autosubst.
Require Import String.
Require Import Coq.ZArith.ZArith.
Require Import tactics.
Import List.ListNotations.
Require Import common.
Require Import sequences.

Require Import Coq.Classes.SetoidClass.
Require Import Wellfounded.


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
  | mode_eval (e: term) (kappa: list cont) (sigma: list value)
  | mode_cont (kappa: list cont) (result: result)
.



Inductive cred: state -> state -> Prop :=
  (** Rules related to the lambda calculus *)
  | cred_var:
    forall x kappa sigma v,
    List.nth_error sigma x = Some v ->
    cred
      (mode_eval (Var x) kappa sigma)
      (mode_cont kappa (RValue v))

  | cred_app:
    forall t1 t2 kappa sigma,
    cred
      (mode_eval (App t1 t2) kappa sigma)
      (mode_eval t1 ((CAppR t2 sigma) :: kappa) sigma)

  | cred_clo:
    forall t kappa sigma,
    cred
      (mode_eval (Lam t) kappa sigma)
      (mode_cont kappa (RValue (Closure t sigma)))

  | cred_arg:
    forall t2 kappa sigma tcl sigmacl,
    cred
      (mode_cont ((CAppR t2 sigma)::kappa) (RValue (Closure tcl sigmacl)))
      (mode_eval t2 ((CClosure tcl sigmacl)::kappa) sigma)

  | cred_value:
    forall v kappa sigma,
    cred
      (mode_eval (Value v) kappa sigma)
      (mode_cont kappa (RValue v))

  | cred_beta:
    forall t_cl sigma_cl kappa v,
    cred
      (mode_cont ((CClosure t_cl sigma_cl)::kappa) (RValue v))
      (mode_eval t_cl kappa (v :: sigma_cl))

  | cred_if:
  forall u t1 t2 kappa sigma,
  cred
    (mode_eval (If u t1 t2) kappa sigma)
    (mode_eval u ((CIf t1 t2 sigma)::kappa) sigma)

  | cred_if_true:
    forall t1 t2 kappa sigma,
    cred
      (mode_cont ((CIf t1 t2 sigma):: kappa) (RValue (Bool true)))
      (mode_eval t1 kappa sigma)

  | cred_if_false:
    forall t1 t2 kappa sigma,
    cred
      (mode_cont ((CIf t1 t2 sigma):: kappa)  (RValue (Bool false)))
      (mode_eval t2 kappa sigma)
.

Goal star cred
  (mode_eval (App (Lam (If (App (Var 0) (Value (Bool true))) (Value (Bool true)) (Value (Bool false))) ) (Lam (Var 0))) [] []) (mode_cont [] (RValue (Bool true))).
Proof.
  eapply star_step; [solve[econstructor; simpl; eauto]|].
  eapply star_step; [solve[econstructor; simpl; eauto]|].
  eapply star_step; [solve[econstructor; simpl; eauto]|].
  eapply star_step; [solve[econstructor; simpl; eauto]|].
  eapply star_step; [solve[econstructor; simpl; eauto]|].
  eapply star_step; [solve[econstructor; simpl; eauto]|].
  eapply star_step; [solve[econstructor; simpl; eauto]|].
  eapply star_step; [solve[econstructor; simpl; eauto]|].
  eapply star_step; [solve[econstructor; simpl; eauto]|].
  eapply star_step; [solve[econstructor; simpl; eauto]|].
  eapply star_step; [solve[econstructor; simpl; eauto]|].
  eapply star_step; [solve[econstructor; simpl; eauto]|].
  eapply star_step; [solve[econstructor; simpl; eauto]|].
  eapply star_step; [solve[econstructor; simpl; eauto]|].
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

Definition stack s :=
  match s with
  | mode_eval _ k _ => k
  | mode_cont k _ => k
  end.


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

Require Import FunInd.

Function apply_cont
  (t: term)
  (k: cont)
  : term :=
  match k with
  | CAppR t2 sigma =>
    (App t t2.[subst_of_env sigma])
  | CClosure t_cl sigma_cl =>
    App (Value (Closure t_cl sigma_cl)) t
  | CIf t1 t2 sigma =>
    If t (t1.[subst_of_env sigma]) (t2.[subst_of_env sigma])
  end.

Function apply_conts kappa t :=
  match kappa with
    | [] => t
    | k::kappa => apply_conts kappa (apply_cont t k)
  end.

Function apply_return (r: result) :=
  match r with
  | RValue v => Value v
  end.

Function apply_state (s: state): term :=
  match s with
  | mode_eval t kappa sigma =>
    (apply_conts kappa t.[subst_of_env sigma])
  | mode_cont stack r =>
    (apply_conts stack (apply_return r))
  end.

Lemma apply_state_append_stack {s kappa}:
  apply_state (append_stack s kappa) =
  apply_conts kappa (apply_state s).
Proof.
  (* Increadible that this is working *)
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


Lemma apply_conts_app {kappa1 kappa2 t}:
  apply_conts (kappa1 ++ kappa2) t = 
  apply_conts kappa2 (apply_conts kappa1 t).
Proof.
  apply List.fold_left_app.
Qed.

Lemma value_apply_conts {v kappa t}:
  Value v = (apply_conts kappa t) ->
  kappa = [] /\ t = Value v.
Proof.
  induction kappa using List.rev_ind.
  { simpl; intros; split; eauto. }
  { induction x; rewrite apply_conts_app; simpl; intros; congruence. }
Qed.


Theorem simulation_sred_cred_base:
  forall t1 t2,
    sred t1 t2 ->
    forall s1, t1 = apply_state s1 ->
    exists s2,
      t2 = apply_state s2  /\ star cred s1 s2.
Proof.
  induction 1.
  { intros.
    functional induction (apply_state s1).
    { revert t0 t sigma H.
      induction kappa using List.rev_ind.
      { simpl in *; intros.
        subst_of_env.
        eapply star_step_prop; [solve[econstructor; simpl; eauto]|].
        eapply star_refl_prop.
        simpl.
        admit "does not remove the other difficulity linked to the handling of up sigma and sigma.".
      }
      { intros; rewrite apply_conts_app in *; induction x; simpl in H; congruence.
      }
    }
    { induction stack0 using List.rev_ind; try clear IHstack0.
      { induction r; induction v; simpl in *; congruence. }
      { intros; rewrite apply_conts_app in *; induction x; simpl in H; congruence. }
    }
  }
  2:{
    intros; functional induction (apply_state s1).
    { revert t sigma u1 u2 H IHsred t0 sigma0 H0.
      induction kappa using List.rev_ind; intros.
      { simpl in *; intros.
        repeat subst_of_env.
        { repeat (eapply star_step_prop; [solve[econstructor; simpl; eauto]|]).
          exploit (IHsred (mode_eval t2' [] sigma0)); [simpl; eauto|]; intros; unpack.
          eapply star_trans_prop; [rewrite append_stack_all; eapply star_cred_append_stack; simpl; eauto|simpl].
          eapply star_refl_prop.
          rewrite apply_state_append_stack; simpl; repeat f_equal; eauto.
        }
        { admit "basically the same thing". }
      }
      { induction x; try solve [rewrite apply_conts_app in *; simpl in *; try congruence].
        { rewrite apply_conts_app in *; simpl in *; injections; subst.
          exploit (IHsred (mode_eval t2 [] sigma1)); [simpl; eauto|]; intros; unpack.

          learn (value_apply_conts H1); unpack; subst; simpl.
          learn (subst_of_env_Value (eq_sym H5)); unzip; subst; simpl in *; injections.
          { repeat (eapply star_step_prop; [solve[econstructor; simpl; eauto]|]).
            eapply star_trans_prop; [rewrite append_stack_all; eapply star_cred_append_stack; simpl; eauto|simpl].
            eapply star_refl_prop.
            rewrite apply_state_append_stack.
            simpl; eauto.
          }
          { repeat (eapply star_step_prop; [solve[econstructor; simpl; eauto]|]).
            eapply star_trans_prop; [rewrite append_stack_all; eapply star_cred_append_stack; simpl; eauto|simpl].
            eapply star_refl_prop.
            rewrite apply_state_append_stack; simpl; eauto.
          }
        }
        { exploit (IHsred (mode_eval t0 kappa sigma0)); [simpl; eauto|].
          { rewrite apply_conts_app in *; simpl in *; injections; subst; eauto. }

            intros; unpack; subst.

            eapply star_trans_prop; [erewrite append_stack_app;[|solve[simpl; eauto]]; eapply star_cred_append_stack; simpl; eauto|simpl].
            eapply star_refl_prop.

            rewrite apply_conts_app in *; simpl in *; injections; subst.
            rewrite apply_state_append_stack in *; simpl in *; eauto.
        }
      }
    }
    { admit "same case". }
  }

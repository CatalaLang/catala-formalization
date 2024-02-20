Require Import syntax continuations small_step sequences tactics.
Require Import Coq.ZArith.ZArith.
Import List.ListNotations.
Import Learn.


(* -------------------------------------------------------------------------- *)

(* Translating a state into a term *)

Lemma EmptyOrNotEmpty:
  forall t, (t = Empty) \/ (t <> Empty).
Proof.
  induction t; try solve [right; repeat intro; congruence|left; eauto].
Qed.


Definition apply_CDefault o ts tj tc t sigma : term :=
  match (o, t) with
  | (Some v, Empty) =>
      Default ((Value (VPure v)).[subst_of_env sigma]::ts..[subst_of_env sigma]) tj.[subst_of_env sigma] tc.[subst_of_env sigma]
  | (Some v, _) =>
      Default ((Value (VPure v)).[subst_of_env sigma]::t::ts..[subst_of_env sigma]) tj.[subst_of_env sigma] tc.[subst_of_env sigma]
  | (None, Empty) =>
      Default ((ts)..[subst_of_env sigma]) tj.[subst_of_env sigma] tc.[subst_of_env sigma]
  | (None, _) =>
      Default (t::(ts)..[subst_of_env sigma]) tj.[subst_of_env sigma] tc.[subst_of_env sigma]
  end.

(* This permits to simplify apply defaults using the EmptyOrNotEmpty lemma in an automatic fashon *)

Lemma apply_CDefault_NT: forall {t ts tj tc sigma},
  t <> Empty ->
  apply_CDefault None ts tj tc t sigma =
    Default (t::(ts)..[subst_of_env sigma]) tj.[subst_of_env sigma] tc.[subst_of_env sigma].
Proof.
induction t; intros; tryfalse; eauto.
Qed.

Lemma apply_CDefault_ST: forall {v t ts tj tc sigma},
  t <> Empty ->
  apply_CDefault (Some v) ts tj tc t sigma =
    Default ((Value (VPure v)).[subst_of_env sigma]::t::ts..[subst_of_env sigma]) tj.[subst_of_env sigma] tc.[subst_of_env sigma]
.
Proof.
induction t; intros; tryfalse; injections; subst; eauto.
Qed.

Lemma apply_CDefault_NE: forall {t ts tj tc sigma},
  t = Empty ->
  apply_CDefault None ts tj tc t sigma =
    Default ((ts)..[subst_of_env sigma]) tj.[subst_of_env sigma] tc.[subst_of_env sigma].
Proof.
induction t; intros; tryfalse; eauto.
Qed.

Lemma apply_CDefault_SE: forall {v t ts tj tc sigma},
  t = Empty ->
  apply_CDefault (Some v) ts tj tc t sigma =
    Default ((Value (VPure v)).[subst_of_env sigma]::ts..[subst_of_env sigma]) tj.[subst_of_env sigma] tc.[subst_of_env sigma].
Proof.
induction t; intros; tryfalse; injections; subst; eauto.
Qed.

Definition apply_cont
  (param1: term * list value)
  (k: cont)
  : term * list value :=
  let '(t, sigma) := param1 in
  match k with
  | CAppR t2 =>
    (App t t2.[subst_of_env sigma], sigma)
  | CBinopL op v1 =>
    (Binop op (Value v1) t, sigma)
  | CBinopR op t2 =>
    (Binop op t t2.[subst_of_env sigma], sigma)
  | CClosure t_cl sigma_cl =>
    (App (Value (Closure t_cl sigma_cl)) t, sigma)
  | CReturn sigma' => (t, sigma')
  | CDefault h o ts tj tc =>
    (apply_CDefault o ts tj tc t sigma, sigma)
  | CDefaultBase tc =>
    (Default nil t tc.[subst_of_env sigma], sigma)
  | CMatch t1 t2 =>
    (Match_ t t1.[subst_of_env sigma] t2.[up (subst_of_env sigma)], sigma)
  | CSome =>
    (ESome t, sigma)
  | CIf ta tb =>
    (If t ta.[subst_of_env sigma] tb.[subst_of_env sigma], sigma)
  | CErrorOnEmpty =>
    (ErrorOnEmpty t, sigma)
  | CDefaultPure =>
    (DefaultPure t, sigma)
  | CFold f ts =>
    (Fold f.[subst_of_env sigma] ts..[subst_of_env sigma] t, sigma)
  end.

Definition apply_conts
  (kappa: list cont)
  : term * list value -> term * list value :=
  List.fold_left apply_cont kappa.

Definition apply_return (r: result) :=
  match r with
  | RValue v => Value v
  | REmpty => Empty
  | RConflict => Conflict
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


Lemma NEmpty_subst_of_env_NEmpty {t} sigma:
  t <> Empty -> t.[subst_of_env sigma] <> Empty.
Proof.
  induction t; simpl; repeat intro; try congruence.
  unfold subst_of_env in *.
  induction (List.nth_error sigma x).
  all: unfold ids, Ids_term in *; try congruence.
Qed.


Lemma Empty_eq_Empty : Empty = Empty.
Proof.
  reflexivity.
Qed.

Ltac dsimpl :=
  repeat match goal with
  | [h: ?t = Empty |- context [apply_CDefault (Some _) _ _ _ ?t _]] =>
    rewrite (apply_CDefault_SE h)
  | [h: ?t = Empty |- context [apply_CDefault None _ _ _ ?t _]] =>
    rewrite (apply_CDefault_NE h)
  | [h: ?t <> Empty |- context [apply_CDefault (Some _) _ _ _ ?t _]] =>
    rewrite (apply_CDefault_ST h)
  | [h: ?t <> Empty |- context [apply_CDefault None _ _ _ ?t _]] =>
    rewrite (apply_CDefault_NT h)
  | [h1: ?t = Empty, h2: context [apply_CDefault (Some _) _ _ _ ?t _] |- _] =>
    rewrite (apply_CDefault_SE h1) in h2
  | [h1: ?t = Empty, h2: context [apply_CDefault None _ _ _ ?t _] |- _] =>
    rewrite (apply_CDefault_NE h1) in h2
  | [h1: ?t <> Empty, h2: context [apply_CDefault (Some _) _ _ _ ?t _] |- _] =>
    rewrite (apply_CDefault_ST h1) in h2
  | [h1: ?t <> Empty, h2: context [apply_CDefault None _ _ _ ?t _] |- _] =>
    rewrite (apply_CDefault_NT h1) in h2

  | [h: ?t <> Empty |- context [?t.[subst_of_env ?sigma]]] =>
    learn (NEmpty_subst_of_env_NEmpty sigma h)
  | [h: _ /\ _ |- _] =>
    destruct h
  | [h: exists _, _ |- _] =>
    destruct h

  | _ => learn (Empty_eq_Empty) (* so the first two cases trigger*)
  | _ => progress subst
  | _ => progress simpl
  end.

(* -------------------------------------------------------------------------- *)


(* Second side of the implication. *)

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

Lemma last_last:
  forall l env0 env1,
    last (l ++ [CReturn env0]) env1 = env0.
Proof.
  induction l.
  { intros; reflexivity. }
  { intros; simpl.
    case a; intros; rewrite IHl; eauto.
  }
Qed.

Lemma snd_apply_conts_last :
  forall kappa env0 t, (snd (apply_conts kappa (t, env0))) = (last kappa env0).
Proof.
  induction kappa.
  { simpl; eauto. }
  { induction a; simpl; intros; try induction o.

    all: repeat match goal with
    | [ |- context [match ?t with Empty => _ | _ => _ end]] =>
      induction t
    | [h: _ \/ _ |- _] =>
      destruct h
    | _ => progress subst
    end.
    all: try eapply IHkappa.
  }
Qed.


(* -------------------------------------------------------------------------- *)


(*
  We are now ready to demonstrate the simulation theorem between continuation-style semantics (`cred`) and small-step semantics (`sred`). This demonstration hinges the following lemma that ensures compositionality when applying a continuation stack.
*)


Lemma star_sred_default_E_zero:
    forall ti ti' ts2 tj tc,
      star sred ti ti' ->
      star sred (Default (ti::ts2) tj tc) (Default (ti'::ts2) tj tc).
Proof.
  eauto with sred.
Qed.

Hint Resolve
  star_refl
: sred.

Theorem star_sred_apply_conts: forall kappa t t' sigma,
  star sred t t' ->
  star sred
    (fst (apply_conts kappa (t, sigma)))
    (fst (apply_conts kappa (t', sigma)))
.
Proof.
  induction kappa as [|k kappa] using List.rev_ind.
  { simpl; eauto with sequences. }
  { induction k;
    intros t t' env Htt'.
    all: pose proof (IHkappa _ _ env Htt') as Hred_kappa.

    all:
      setoid_rewrite apply_conts_app;
      simpl; unfold apply_cont;
        repeat match goal with
      | [ |- context [let '(_, _) := ?p in _]] =>
        rewrite (surjective_pairing p)
      | [h: context [let '(_, _) := ?p in _] |- _] =>
        rewrite (surjective_pairing p) in h
      end; simpl.

    all: repeat rewrite snd_apply_conts_last.

    all: try solve [eauto with sred].
    { induction o.
      all: repeat match goal with
      | [|- context [apply_CDefault ?o _ _ _ ?t _] ] =>
        learn (EmptyOrNotEmpty t)
      | [h: _ \/ _ |- _] =>
        destruct h
      | [h: ?t = Empty|- context [apply_CDefault (Some _) _ _ _ ?t _]] =>
        rewrite (apply_CDefault_SE h)
      | [h: ?t = Empty|- context [apply_CDefault None _ _ _ ?t _]] =>
        rewrite (apply_CDefault_NE h)
      | [h: ?t <> Empty|- context [apply_CDefault (Some _) _ _ _ ?t _]] =>
        rewrite (apply_CDefault_ST h)
      | [h: ?t <> Empty|- context [apply_CDefault None _ _ _ ?t _]] =>
        rewrite (apply_CDefault_NT h)
      | [h1: ?t = Empty, h2: context [?t] |- _] =>
        rewrite h1 in h2
      | [h1: ?t = Empty |- context [?t]] =>
        rewrite h1
      | [h: sred Empty _ |- _] =>
        inversion h
      | [h: star sred Empty _ |- _] =>
        learn (star_sred_empty_empty _ h)
      | _ =>
        progress try congruence
      | _ =>
        solve [eauto with sred]
      end.
      { (* t' is empty, o has a value *)
        eapply star_trans. { eapply star_sred_default_E_one. eauto. }
        eapply star_one. { econstructor. }
      }
      { (* t' is not empty, o has a value *)
        eapply star_trans. { eapply star_sred_default_E_one. eauto. }
        eapply star_refl.
      }
      { eapply star_trans. { eapply star_sred_default_E_zero. eauto. }
        eapply star_one. { econstructor. }
      }
    }
  }
Qed.


(* In particular, this apply too on single transition step *)

Theorem sred_apply_conts: forall kappa t t' sigma,
  sred t t' ->
  star sred
    (fst (apply_conts kappa (t, sigma)))
    (fst (apply_conts kappa (t', sigma)))
.
  intros.
  eapply star_sred_apply_conts.
  eauto with sequences.
Qed.

Lemma sim_term_apply_conts {kappa t1 t2 sigma}:
  sim_term t1 t2 ->
  sim_term
    (fst (apply_conts kappa (t1, sigma)))
    (fst (apply_conts kappa (t2, sigma))).
Proof.
  revert sigma t1 t2.
  induction kappa as [|k kappa] using List.rev_ind; simpl; eauto.
  induction k; intros; repeat rewrite apply_conts_app; simpl; unfold apply_cont; sp; simpl.
  all: repeat econstructor.
  all: try eapply IHkappa; eauto.
  all: repeat rewrite snd_apply_conts_last.
  all: try reflexivity.
  { admit "need to show that sim_term Empty v => sim_term Empty". }
  { induction ts; asimpl; econstructor; try reflexivity; eauto. }
Admitted.


Lemma impli_under_exists {X: Type} {P Q R: X -> Prop}:
  (forall x, P x -> Q x) ->
  (exists x, P x /\ R x) ->
  (exists x, Q x /\ R x).
Proof.
  intros; unpack.
  eexists; eauto.
Qed.

Lemma sim_term_star_sred_apply_counts {t1 t2' kappa sigma}: 
(exists t2,
  sim_term t2' t2 /\
  star sred t1 t2
) ->
(exists t2 : term,
  sim_term (fst (apply_conts kappa (t2', sigma))) t2 /\
  star sred (fst (apply_conts kappa (t1, sigma))) t2).
Proof.
  intros; unpack; eexists; split.
  { eapply sim_term_apply_conts. eauto. }
  { eapply star_sred_apply_conts. eauto. }
Qed.

Theorem simulation_cred_sred_base:
  forall s1 s2,
  cred s1 s2 ->
  exists t,
    sim_state s2 t /\
    star sred (apply_state s1) t.
Proof.
  Local Ltac step := eapply star_step_prop;[solve[econstructor; eauto]|].
  intros s1 s2 Hs1s2'.
  pose proof Hs1s2' as Hs1s2.
  eapply (impli_under_exists).
  intros.
  eapply sim_state_from_equiv.
  eapply H.
  induction Hs1s2'; try induction o; try induction phi.
  all: try destruct (EmptyOrNotEmpty th).
  all: dsimpl; try eapply sim_term_star_sred_apply_counts.
  all: repeat step.
  all: try solve [
    eapply star_refl_prop;
    simpl; reflexivity].
  { eapply star_refl_prop.
    unfold subst_of_env; rewrite H.
    reflexivity.
  }
  { eapply star_refl_prop.
    repeat econstructor.
    rewrite soe_nil; asimpl.
    reflexivity.
  }
  { admit "one too may steps". }
  { exfalso.
    eapply H; eauto.
  }
  { admit "this one as well". }
  { eapply star_refl_prop.
    asimpl.
    rewrite soe_cons.
    reflexivity.
  }
Admitted.


(*** Lifting of this result ***)



Lemma proper_sim_state_sred:
  forall t1 t2,
    sred t1 t2 ->
    forall u1,
      sim_term t1 u1 ->
      exists u2,
        sim_term t2 u2 /\ sred u1 u2.
Proof.
  induction 1; intros; repeat sinv_sim_term; subst.
  (* induction hypothesis *)
  all: repeat match goal with
    | [ih: forall x, ?P x -> _, h: ?P _ |- _] => 
      learn (ih _ h); unpack; subst end.

  (* Most cases are trivial. *)
  all: try solve[repeat econstructor; eauto].

  { repeat econstructor.
    rewrite soe_nil.
    asimpl.
    eauto.
  }
  { repeat econstructor.
    admit "need to replace the substitution into two substitutions". 
  }
  { admit "binop". }
  { repeat econstructor.
    eapply sim_term_subst; eauto.
    induction x; simpl; repeat econstructor; eauto.
  }
Admitted.

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
  symmetry in H4.
  learn (proper_sim_state_star_sred _ _ H1 _ H4); unpack.
  eexists; split; [|eauto].
  eapply sim_state_from_equiv.
  etransitivity; [symmetry|]; eauto.
Qed.

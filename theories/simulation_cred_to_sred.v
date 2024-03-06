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

Definition if_is_empty {A} (th: term) (x y: A) :=
    match th with | Empty => x | _ => y end.

Lemma match_nempty {A} {th: term} {x y: A}:
  th <> Empty ->
  if_is_empty th x y = y.
Proof.
  induction th; intros; try reflexivity; tryfalse.
Qed.

Definition apply_CDefault o ts tj tc t sigma : term :=
  Default
  match o with
  | Some v =>
    if_is_empty t 
      ((Value (VPure v)).[subst_of_env sigma]::ts..[subst_of_env sigma])
      ((Value (VPure v)).[subst_of_env sigma]::t::ts..[subst_of_env sigma])
  | None =>
    if_is_empty t 
      ((ts)..[subst_of_env sigma])
      (t::(ts)..[subst_of_env sigma])
  end
  tj.[subst_of_env sigma] tc.[subst_of_env sigma].

(* This permits to simplify apply defaults using the EmptyOrNotEmpty lemma in an automatic fashon *)


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

(* -------------------------------------------------------------------------- *)


(* From cred to sred. *)

Lemma apply_conts_app:
  forall kappa1 kappa2 p,
    apply_conts (kappa1 ++ kappa2) p
    = apply_conts kappa2 (apply_conts kappa1 p).
Proof.
  intros.
  unfold apply_conts.
  rewrite List.fold_left_app; eauto.
Qed.

Fixpoint last_env (l: list cont) (env0: list value) : list value :=
  match l with
  | [] => env0
  | CReturn env1 :: l =>
    last_env l env1
  | _ :: l =>
    last_env l env0
  end.

Lemma snd_apply_conts_last_env :
  forall kappa env0 t, (snd (apply_conts kappa (t, env0))) = (last_env kappa env0).
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

Theorem sred_apply_conts: forall kappa t t' sigma,
  sred t t' ->
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
      simpl; unfold apply_cont; sp; simpl.

    all: repeat rewrite snd_apply_conts_last_env.

    all: try solve [eauto with sred].
    { (* Default case *)
      induction o; unfold apply_CDefault.
      all:
      repeat match goal with
        | [|- context [if_is_empty ?t]] =>
          learn (EmptyOrNotEmpty t); unzip
        | [h: ?t = Empty |- context [if_is_empty ?t]] =>
          rewrite h in *; simpl in *
        | [h: ?t <> Empty |- context [if_is_empty ?t]] =>
          rewrite (match_nempty h); simpl in *
        | [h: star sred Empty _ |- _] =>
        learn (star_sred_empty_empty _ h)
      end.
      all: try eapply star_refl.
      all: try congruence.
      all: repeat first
        [ eapply star_trans; [solve [ eapply star_sred_default_E_one; eauto]|]
        | eapply star_trans; [solve [ eapply star_sred_default_E_zero; eauto]|]
        | eapply star_step; [solve[econstructor; eauto]|]
      ].
      all: eapply star_refl.
    }
  }
Qed.

Theorem star_sred_apply_conts: forall kappa t t' sigma,
  star sred t t' ->
  star sred
    (fst (apply_conts kappa (t, sigma)))
    (fst (apply_conts kappa (t', sigma)))
.
  induction 1; [eapply star_refl|eapply star_trans]; eauto.
  eapply sred_apply_conts; eauto.
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
  all: repeat rewrite snd_apply_conts_last_env.
  all: try reflexivity.
  { learn (IHkappa sigma _ _ H).
    assert (fst (apply_conts kappa (t1, sigma)) = Empty <-> fst (apply_conts kappa (t2, sigma)) = Empty).
    { split; intros; rewrite H2 in *; inversion H0; eauto. }
    destruct (EmptyOrNotEmpty (fst (apply_conts kappa (t1, sigma)))).
    { rewrite H3 in *; destruct H2; rewrite H2; eauto.
      induction o; simpl; reflexivity.
    }
    {
      learn ((proj1 (not_iff_compat H2)) H3).
      induction o; repeat rewrite (hole_none_nempty _); repeat rewrite (hole_some_nempty _).
      all: repeat match goal with
      | [h: _ <> Empty |- _] => rewrite (match_nempty h)
      end.
      all: repeat econstructor; first [eauto; reflexivity].
    }
  }
Qed.


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
  all: try solve [
    eapply star_refl_prop;
    simpl; reflexivity; eauto].
  all: repeat step.
  all: try solve [
    eapply star_refl_prop;
    simpl; reflexivity; eauto].
  { eapply star_refl_prop.
    unfold subst_of_env; rewrite H.
    reflexivity.
  }
  { eapply star_refl_prop.
    repeat econstructor.
    rewrite soe_nil; asimpl.
    reflexivity.
  }
  { exfalso; eapply H; eauto. } 
  { induction o; simpl; repeat step; eapply star_refl_prop; reflexivity. }
  { eapply star_refl_prop.
    asimpl.
    rewrite soe_cons.
    reflexivity.
  }
Qed.


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
    repeat rewrite subst_of_env_decompose.
    eapply sim_term_subst; eauto.
    { induction x; asimpl; repeat econstructor; eauto. }
  }
  { induction op2, v1, v2; simpl in *; tryfalse; inj; repeat sinv_sim_term.
    all: repeat econstructor.
  }
  { repeat econstructor.
    eapply sim_term_subst; eauto.
    induction x; simpl; repeat econstructor; eauto.
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
  symmetry in H4.
  learn (proper_sim_state_star_sred _ _ H1 _ H4); unpack.
  eexists; split; [|eauto].
  eapply sim_state_from_equiv.
  etransitivity; [symmetry|]; eauto.
Qed.

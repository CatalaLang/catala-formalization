Require Import syntax continuations small_step sequences tactics.
Require Import Coq.ZArith.ZArith.
Import List.ListNotations.



(* -------------------------------------------------------------------------- *)

(* Translating an term into an *)

Lemma EmptyOrNotEmpty:
  forall t, (t = Empty) \/ (t <> Empty).
Proof.
  induction t; try solve [right; repeat intro; congruence|left; eauto].
Qed.


Definition apply_CDefault o ts tj tc t sigma : term :=
  match (o, t) with
  | (Some v, Empty) =>
      Default ((Value v).[subst_of_env sigma]::ts..[subst_of_env sigma]) tj.[subst_of_env sigma] tc.[subst_of_env sigma]
  | (Some v, _) =>
      Default ((Value v).[subst_of_env sigma]::t::ts..[subst_of_env sigma]) tj.[subst_of_env sigma] tc.[subst_of_env sigma]
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
    Default ((Value v).[subst_of_env sigma]::t::ts..[subst_of_env sigma]) tj.[subst_of_env sigma] tc.[subst_of_env sigma]
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
    Default ((Value v).[subst_of_env sigma]::ts..[subst_of_env sigma]) tj.[subst_of_env sigma] tc.[subst_of_env sigma].
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
  | CDefault o ts tj tc =>
    (apply_CDefault o ts tj tc t sigma, sigma)
  | CDefaultBase tc =>
    (Default nil t tc.[subst_of_env sigma], sigma)
  | CMatch t1 t2 =>
    (Match_ t t1.[subst_of_env sigma] t2.[up (subst_of_env sigma)], sigma)
  | CSome =>
    (ESome t, sigma)
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

Import Learn.

Ltac dsimpl :=
  repeat match goal with
  | [ |- context [match ?t with Empty => _ | _ => _ end]] =>
    induction t using EmptyOrNotEmpty
  | [h: _ /\ _ |- _] =>
    destruct h
  | [h: exists _, _ |- _] =>
    destruct h
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

(* Idea: subtil lemma *)

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

Lemma cred_process_return {kappa1 env0 result}: forall kappa2,
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

Import Learn.

Lemma last_snd_apply_conts :
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



Theorem sred_apply_conts: forall kappa t t' sigma,
  sred t t' ->
  sred
    (fst (apply_conts kappa (t, sigma)))
    (fst (apply_conts kappa (t', sigma)))
.
Proof.
  induction kappa as [|k kappa] using List.rev_ind.
  { simpl; eauto. }
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

    all: repeat rewrite last_snd_apply_conts.


    all: try solve [econstructor; eauto].
    { eapply IHkappa; eauto. }
    { repeat match goal with
      | [|- context [apply_CDefault ?o _ _ _ ?t _] ] =>
        induction o; learn (EmptyOrNotEmpty t)
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
      end.
      all: asimpl.
      all: try solve [econstructor; eauto].
      3:{  }
      asimpl.
      2: { econstructor; eauto. }
      eapply sred_DefaultE_one.
    }
  }
Qed.



Theorem sreds_apply_conts: forall kappa t t' sigma,
  star sred t t' ->
  star sred
    (fst (apply_conts kappa (t, sigma)))
    (fst (apply_conts kappa (t', sigma)))
.
Proof.
  induction 1; eauto using sred_apply_conts with sequences.
Qed.


Theorem simulation_cred_sred:
  forall s1 s2,
    cred s1 s2 ->
    star sred (apply_state s1) (apply_state s2).
Proof.
  induction 1; try induction o.
  all: simpl; try solve [eapply star_refl| eapply sreds_apply_conts; eapply star_one; econstructor; eauto].
  { simpl; unfold subst_of_env; rewrite H; eauto with sequences. }
  { simpl. eapply sreds_apply_conts.
    eapply star_one.
    admit "lambda related issue".
  }
  { eapply sreds_apply_conts.
    eapply star_one.
    admit "issue related to Empty in right position".
  }
  { eapply sreds_apply_conts.
    eapply star_one.
    admit "same: the reduction append an empty on the right hand side".
  }
  { eapply sreds_apply_conts.
    eapply star_one.
    admit "same: the reduction append an empty on the right hand side".
  }
  { eapply sreds_apply_conts.
    eapply star_one.
    admit "same: the reduction append an empty on the right hand side".
  }
  { eapply sreds_apply_conts.
    eapply star_one.
    admit "same: the reduction append an empty on the right hand side".
  }
  { eapply sreds_apply_conts.
    eapply star_one.
    admit "same: the reduction append an empty on the right hand side".
  }
  { induction phi; try induction o.
    all: try solve[eapply sreds_apply_conts; eapply star_one; econstructor; eauto].
    { exfalso.
      eapply H0; eauto.
    }
    { exfalso; eapply H; eauto. }
    { exfalso; eapply H; eauto. }
  }
  { induction phi; try induction o.
    all: try solve[eapply sreds_apply_conts; eapply star_one; econstructor; eauto].
    { exfalso.
      eapply H; eauto.
    }
  }
  { eapply sreds_apply_conts.
    eapply star_one.
    rewrite subst_env_cons.
    replace t2.[Value v .: subst_of_env sigma] with t2.[up (subst_of_env sigma)].[Value v/] by autosubst.
    econstructor.
  }
Admitted.

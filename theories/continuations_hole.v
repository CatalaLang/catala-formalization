Require Import syntax.
Require Import Sorting.Permutation.
Import List.ListNotations.
Open Scope list_scope.
Require Import sequences common.
Require Import Coq.Arith.Arith.
Require Import Coq.ZArith.ZArith.
Require Import Bool.

Require Import String.


(* Proof automation. ZifyBool is needed for operators such as [_ <=? _] *)
Require Import Lia ZifyBool.

From Catala Require Import tactics.


(* Definition of continuaton semantics for the catala programming language. *)

Inductive result :=
  | RValue (v: value)
  | REmpty
  | RConflict
.

Inductive is_hole :=
  | Hole
  | NoHole
.

(* App (Var 0) (up t2) *)

Inductive cont :=
  | CAppR (t2: term) (* [\square t2] *)
  | CClosure (t_cl: {bind term}) (sigma_cl: list value)
  (* [Clo(x, t_cl, sigma_cl) \square] Since we are using De Bruijn indices,
     there is no variable x. *)

  | CBinopL (op: op) (v1: value) (* [op t1 \square] *)
  | CBinopR (op: op) (t2: term) (* [op \square t2] *)
  | CReturn (sigma: list value) (* call return *)
  | CDefault (b: is_hole) (o: option value) (ts: list term) (tj: term) (tc: term)
    (* [Def(o, ts, tj, tc)] *)
  | CDefaultBase (tc: term)
    (* [ <| \square :- tc >] *)
  | CMatch (t1: term) (t2: {bind term})
    (* [ match \square with None -> t1 | Some -> t2 end ] *)
  | CSome
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


  (** Rules related to the defaults *)

  | cred_default:
    forall ts tj tc kappa sigma,
    cred
      (mode_eval (Default ts tj tc) kappa sigma)
      (mode_cont ((CDefault Hole None ts tj tc)::kappa) sigma REmpty)

  | cred_default_unpack:
    forall o th ts tj tc kappa sigma,
    cred
      (mode_cont ((CDefault Hole o (th::ts) tj tc)::kappa) sigma REmpty)
      (mode_eval th ((CDefault NoHole o ts tj tc)::kappa) sigma)

  (* Possible results :
  
  value *)

  | cred_default_value:
    forall o ts tj tc kappa sigma v,
    cred
      (mode_cont ((CDefault NoHole o ts tj tc)::kappa) sigma (RValue v))
      (mode_cont ((CDefault Hole o ts tj tc)::kappa) sigma (RValue v))

  | cred_default_value_none_to_some:
    forall ts tj tc kappa sigma v,
    cred
      (mode_cont ((CDefault Hole None ts tj tc)::kappa) sigma (RValue v))
      (mode_cont ((CDefault Hole (Some v) ts tj tc)::kappa) sigma REmpty)

  | cred_default_value_conflict:
    forall ts tj tc kappa sigma v v',
    cred
      (mode_cont ((CDefault Hole (Some v) ts tj tc)::kappa) sigma (RValue v'))
      (mode_cont kappa sigma RConflict)

  | cred_default_value_return:
    forall v tj tc kappa sigma,
    cred
      (mode_cont ((CDefault Hole (Some v) [] tj tc)::kappa) sigma REmpty)
      (mode_cont kappa sigma (RValue v))

  (* empty *)
  | cred_default_empty:
    forall o ts tj tc kappa sigma,
    cred
      (mode_cont ((CDefault NoHole o ts tj tc)::kappa) sigma REmpty)
      (mode_cont ((CDefault Hole o ts tj tc)::kappa) sigma REmpty)

  | cred_defaultbase:
    forall tj tc kappa sigma,
    cred
      (mode_cont ((CDefault Hole None [] tj tc)::kappa) sigma REmpty)
      (mode_eval tj ((CDefaultBase tc)::kappa) sigma)

  | cred_defaultbasetrue:
    forall tc kappa sigma,
    cred
      (mode_cont ((CDefaultBase tc)::kappa) sigma (RValue (Bool true)))
      (mode_eval tc kappa sigma)

  | cred_defaultbasefalse:
    forall tc kappa sigma,
    cred
      (mode_cont ((CDefaultBase tc)::kappa) sigma (RValue (Bool false)))
      (mode_cont kappa sigma REmpty)

  (* REmpty is catched by CDefault in the rule cdefaultbase. *)
  | cred_empty:
    forall phi kappa sigma,
    (forall b o ts tj tc, phi <> CDefault b o ts tj tc) ->
    (forall sigma', phi <> CReturn sigma') ->
    cred
      (mode_cont (phi::kappa) sigma REmpty)
      (mode_cont kappa sigma REmpty)

  (* Conflict panics and stop the execution of the program.
     We only pop the stack one at the time to ensure the size of kappa
     is changed by one at most. *)
  | cred_conflict:
    forall phi kappa sigma,
    (forall sigma', phi <> CReturn sigma') ->
    cred
      (mode_cont (phi::kappa) sigma RConflict)
      (mode_cont kappa sigma RConflict)

  | cred_confict_intro:
    forall kappa sigma,
    cred
      (mode_eval Conflict kappa sigma)
      (mode_cont kappa sigma RConflict)

  | cred_empty_intro:
    forall kappa sigma,
    cred
      (mode_eval Empty kappa sigma)
      (mode_cont kappa sigma REmpty)

  | cred_value_intro:
    forall v kappa sigma,
    cred
      (mode_eval (Value v) kappa sigma)
      (mode_cont kappa sigma (RValue v))

  | cred_op_intro:
    forall op e1 e2 kappa sigma,
    cred
      (mode_eval (Binop op e1 e2) kappa sigma)
      (mode_eval e1 (CBinopR op e2::kappa) sigma)

  | cred_op_mid:
    forall op e2 kappa sigma v,
    cred
      (mode_cont (CBinopR op e2 :: kappa) sigma (RValue v))
      (mode_eval e2 (CBinopL op v :: kappa) sigma)

  | cred_op_final:
    forall op v v1 v2 kappa sigma,
    Some v = get_op op v1 v2 ->
    cred
      (mode_cont (CBinopL op v1 :: kappa) sigma (RValue v2))
      (mode_cont kappa sigma (RValue v))

  | cred_match:
    forall u t1 t2 kappa sigma,
    cred
      (mode_eval (Match_ u t1 t2) kappa sigma)
      (mode_eval u ((CMatch t1 t2)::kappa) sigma)
  | cred_match_none:
    forall t1 t2 kappa sigma,
    cred
      (mode_cont ((CMatch t1 t2)::kappa) sigma (RValue VNone))
      (mode_eval t1 kappa sigma)
  | cred_match_some:
    forall t1 t2 kappa sigma v,
    cred
      (mode_cont ((CMatch t1 t2) :: kappa) sigma (RValue (VSome (v))))
      (mode_eval t2 (CReturn sigma :: kappa) (v::sigma))
  | cred_enone:
    forall kappa sigma,
    cred
      (mode_eval ENone kappa sigma)
      (mode_cont kappa sigma (RValue VNone))
  | cred_esome_intro:
    forall t kappa sigma,
    cred
      (mode_eval (ESome t) kappa sigma)
      (mode_eval t (CSome::kappa) sigma)
  | cred_esome_elim:
    forall v kappa sigma,
    cred
      (mode_cont (CSome::kappa) sigma (RValue v))
      (mode_cont kappa sigma (RValue (VSome v)))
.

Notation "'cred' t1 t2" :=
  (cred t1 t2) (
  at level 50,
  t1 at level 3,
  t2 at level 3,
  only printing,
  format "'cred'  '[hv' t1  '/' t2 ']'"
).
Notation "'star' 'cred' t1 t2" :=
  (star cred t1 t2) (
  at level 50,
  t1 at level 3,
  t2 at level 3,
  only printing,
  format "'star'  'cred'  '[hv' t1  '/' t2 ']'"
).
Notation "'plus' 'cred' t1 t2" :=
  (plus cred t1 t2) (
  at level 50,
  t1 at level 3,
  t2 at level 3,
  only printing,
  format "'plus'  'cred'  '[hv' t1  '/' t2 ']'"
).


(** STACK MANIPULATION *)

Definition stack s :=
  match s with
  | mode_eval _ k _ => k
  | mode_cont k _ _ => k
  end.

Definition with_stack s kappa :=
  match s with
  | mode_eval t _ sigma => mode_eval t kappa sigma
  | mode_cont _ sigma v => mode_cont kappa sigma v
  end.

Definition is_mode_eval s :=
  match s with
  | mode_eval _ _ _ => true
  | _ => false
  end.

Definition is_mode_cont s :=
  match s with
  | mode_cont _ _ _ => true
  | _ => false
  end.

Definition append_stack s kappa2 :=
  match s with
  | mode_eval t kappa1 sigma =>
    mode_eval t (kappa1++kappa2) sigma
  | mode_cont kappa1 sigma v =>
    mode_cont (kappa1++kappa2) sigma v
  end
.

Definition append_env s sigma2 :=
  match s with
  | mode_eval t kappa sigma1 =>
    mode_eval t kappa (sigma1 ++ sigma2)
  | mode_cont kappa sigma1 v =>
    mode_cont kappa (sigma1 ++ sigma2) v
  end
.

Lemma append_stack_def s kappa:
  append_stack s kappa = with_stack s (stack s ++ kappa).
Proof.
  induction s; simpl; eauto.
Qed.


(** Reductions are stable if stack is append. *)

Theorem append_stack_stable s s':
  (* If you can do a transition, then you can do the same transition with additional informations on the stack. *)
  cred s s' ->
  forall k,
  cred (append_stack s k) (append_stack s' k).
Proof.
  induction 1; intros; asimpl; try econstructor; eauto.
Qed.

Theorem append_stack_stable_star s s':
  star cred s s'
  ->
  forall k,
  star cred (append_stack s k) (append_stack s' k).
Proof.
  induction 1; intros.
  * eauto with sequences.
  * eapply star_step; eauto using append_stack_stable.
Qed.

Theorem append_stack_stable_plus s s':
  plus cred s s'
  ->
  forall k,
  plus cred (append_stack s k) (append_stack s' k).
Proof.
  induction 1; intros.
  econstructor; try eapply append_stack_stable; try eapply append_stack_stable_star; eauto.
Qed.

Theorem append_stack_cont kappa1 kappa2 sigma r:
  mode_cont (kappa1++kappa2) sigma r
  = append_stack (mode_cont kappa1 sigma r) kappa2.
Proof.
  simpl; eauto.
Qed.

Theorem append_stack_eval t kappa1 kappa2 sigma:
  mode_eval t (kappa1++kappa2) sigma
  = append_stack (mode_eval t kappa1 sigma) kappa2.
Proof.
  simpl; eauto.
Qed.

(* PROPERTIES OF CRED *)

Theorem cred_deterministic (s s1' s2': state):
  cred s s1' -> cred s s2' -> s1' = s2'.
Proof.
  induction 1; inversion 1; subst; try solve [eauto|congruence].
  (* What is left is cases involving the [cred_empty] and [cred_conflict] rules. Since congrugence don't go inside the forall, it does not handle those cases correctly. *)
  all: try match goal with
    [h: context [CReturn _ <> CReturn _] |- _ ] =>
      epose proof h _ as tmp; exfalso; apply tmp; eauto
    end.
  all: try match goal with
    [h: context [CDefault _ _ _ _ _ <> CDefault _ _ _ _ _] |- _ ] =>
    epose proof h _ _ _ _ _ as tmp; exfalso; apply tmp; eauto
    end.
Qed.

Require continuations.

Definition apply_cont c :=
  match c with
  | CAppR t => continuations.CAppR t
  | CClosure t s => continuations.CClosure t s
  | CBinopL op v => continuations.CBinopL op v
  | CBinopR op t => continuations.CBinopR op t
  | CReturn s => continuations.CReturn s
  | CDefault b o ts tj tc => continuations.CDefault o ts tj tc
  | CDefaultBase tc => continuations.CDefaultBase tc
  | CMatch t1 t2 => continuations.CMatch t1 t2
  | CSome => continuations.CSome
  end.

Definition apply_return r :=
  match r with
  | RValue v => continuations.RValue v
  | REmpty => continuations.REmpty
  | RConflict => continuations.RConflict
  end.

Definition apply s :=
  match s with
  | mode_eval t kappa sigma =>
    continuations.mode_eval t (List.map apply_cont kappa) sigma
  | mode_cont kappa sigma r =>
    continuations.mode_cont (List.map apply_cont kappa) sigma (apply_return r)
  end.

Theorem simulation_cred_cred':
  forall s1 s2,
    cred s1 s2 ->
    star continuations.cred (apply s1) (apply s2).
Proof.
  induction 1; simpl; intros; subst.
  all: try solve [eapply star_refl|eapply star_one; econstructor; eauto].
  { induction phi; simpl.
    all: eapply star_one; econstructor; repeat intro; tryfalse.
    { edestruct H0; eauto. }
    { edestruct H; eauto. }
  }
  { induction phi; simpl.
    all: eapply star_one; econstructor; repeat intro; tryfalse.
    { edestruct H; eauto. }
  }
Qed.

Lemma apply_cont_inj:
  forall k1 k2,
    apply_cont k1 = apply_cont k2 -> k1 = k2.
Proof.
  induction k1, k2; simpl in *; intros; injections; subst; tryfalse; eauto.
  { f_equal. (* this is not anymore true *) admit. }
Admitted.

Lemma map_apply_cont_inj:
  forall kappa1 kappa2,
  List.map apply_cont kappa1 = List.map apply_cont kappa2 ->
    kappa1 = kappa2.
Proof.
Admitted.

Lemma map_apply_cont_left:
  forall k1 kappa1 kappa2,
  k1 :: List.map apply_cont kappa1 = List.map apply_cont kappa2 ->
  exists k2, kappa2 = k2 :: kappa1 /\ k1 = apply_cont k2.
Proof.
  intros.
  induction kappa2; simpl in *; tryfalse.
  injections; eexists; split; eauto.
  f_equal. eapply map_apply_cont_inj; eauto.
Qed.

Lemma map_apply_cont_left':
  forall k1 kappa1 kappa2,
  k1 :: kappa1 = List.map apply_cont kappa2 ->
  exists k2 kappa1', kappa2 = k2 :: kappa1'.
Proof.
  intros.
  induction kappa2; simpl in *; tryfalse.
  { injections; subst.
    repeat eexists.
  }
Qed.


(** Our reduction sequences should have the folowing shape:

the head of kappa, if it exists can have any possible shape.

Each member of the tail should however no contain "Hole" inside their default terms.

This is explained by the following invariant on state :

*)

Inductive inv_kappa_no_hole: cont -> Prop :=
.


Definition inv_state (s: state): Prop :=
  let kappa := (stack s) in
  match kappa with
  | [] => True
  | h::t =>  List.Forall inv_kappa_no_hole t
  end
.

(* This property is indeed conserved by the cred relation. *)

Theorem cred_inv_state_stable:
  forall s1,
    inv_state s1 ->
    forall s2,
      cred s1 s2 ->
      inv_state s2.
Proof.
  induction 2.
  all: try solve [unfold inv_state in *; simpl in *; eauto].
Abort.


Import Learn.

Theorem simulation_cred'_cred:
  forall s1 s2,
    continuations.cred s1 s2 ->
    forall s1',
      s1 = apply s1' ->
      exists s2',
        star cred s1' s2' /\ s2 = apply s2'.
Proof.
  intros s1 s2.
  induction 1; simpl; intros; subst.
  all: repeat ((repeat match goal with
  | [h: continuations.mode_eval _ _ _ = apply ?s1 |- _] =>
    induction s1; simpl in h; injections; tryfalse; subst
  | [h: continuations.mode_cont _ _ _ = apply ?s1 |- _] =>
    induction s1; simpl in h; injections; tryfalse; subst

  | [h: continuations.RValue _ = apply_return ?r |- _] =>
    induction r; simpl in h; injections; tryfalse; subst
  | [h: continuations.REmpty = apply_return ?r |- _] =>
    induction r; simpl in h; injections; tryfalse; subst
  | [h: continuations.RConflict = apply_return ?r |- _] =>
    induction r; simpl in h; injections; tryfalse; subst

  (* | [h: List.map apply_cont _ = List.map apply_cont _ |- _] =>
    learn (map_apply_cont_inj _ _ h) *)
  | [h: _ :: List.map apply_cont _ = List.map apply_cont _ |- _] =>
    learn (map_apply_cont_left _ _ _ h)

  | [h: _ :: _ = List.map apply_cont _ |- _] =>
    learn (map_apply_cont_left' _ _ _ h)

  | [h: continuations.CAppR _ = apply_cont ?k |- _ ] =>
    induction k; simpl in h; injections; tryfalse; subst
  | [h: continuations.CClosure _ _ = apply_cont ?k |- _ ] =>
    induction k; simpl in h; injections; tryfalse; subst
  | [h: continuations.CBinopL _ _ = apply_cont ?k |- _ ] =>
    induction k; simpl in h; injections; tryfalse; subst
  | [h: continuations.CBinopR _ _ = apply_cont ?k |- _ ] =>
    induction k; simpl in h; injections; tryfalse; subst
  | [h: continuations.CReturn _ = apply_cont ?k |- _ ] =>
    induction k; simpl in h; injections; tryfalse; subst
  | [h: continuations.CDefault _ _ _ _ = apply_cont ?k |- _ ] =>
    induction k; simpl in h; injections; tryfalse; subst
  | [h: continuations.CDefaultBase _ = apply_cont ?k |- _ ] =>
    induction k; simpl in h; injections; tryfalse; subst
  | [h: continuations.CMatch _ _ = apply_cont ?k |- _ ] =>
    induction k; simpl in h; injections; tryfalse; subst
  | [h: continuations.CSome = apply_cont ?k |- _ ] =>
    induction k; simpl in h; injections; tryfalse; subst

  | [h: _ /\ _ |- _ ] =>
    destruct h
  | [h: exists _, _ |- _] =>
    destruct h
  
  end); repeat (simpl in *; injections; subst)).

  all: try solve [eexists;split;[
      solve [repeat (eapply star_step; [econstructor; eauto|]); eapply star_refl]|simpl; eauto]].
  { eexists; split.
    { eapply star_one; econstructor. }
    { simpl; eauto. }
  }
  { induction b; eexists; split.
    { eapply star_one; econstructor. }
    { simpl; eauto. }
    { eapply star_step; [econstructor; eauto|].
      eapply star_one; econstructor.
    }
    { simpl; eauto. }
  }
  { induction b; eexists; split.
    { eapply star_one; econstructor. }
    { simpl; eauto. }
    { eapply star_step; [econstructor; eauto|].
      eapply star_one; econstructor.
    }
    { simpl; eauto. }
  }
  { induction b; eexists; split.
    { eapply star_one; econstructor. }
    { simpl; eauto. }
    { eapply star_step; [econstructor|].
      eapply star_one; econstructor.
    }
    { simpl; eauto. }
  }
  { induction b; eexists; split.
    { eapply star_step; [econstructor; eauto|].
      eapply star_refl.
    }
    { simpl; eauto. }
    { eapply star_step; [econstructor; eauto|].
      eapply star_step; [econstructor; eauto|].
      eapply star_refl.
    }
    { simpl; eauto. }
  }
  { induction b; eexists; split.
    { eapply star_step; [econstructor; eauto|].
      eapply star_refl.
    }
    { simpl; eauto. }
    { eapply star_step; [econstructor; eauto|].
      eapply star_step; [econstructor; eauto|].
      eapply star_refl.
    }
    { simpl; eauto. }
  }
  { induction x; simpl in *.
    all: eexists; split; [eapply star_one; econstructor; repeat intro; tryfalse; eauto|simpl; eauto].
    { edestruct H0; eauto. }
    { edestruct H; eauto. }
  }
  { induction x; simpl in *.
    all: eexists; split; [eapply star_one; econstructor; repeat intro; tryfalse; eauto|simpl; eauto].
    { edestruct H; eauto. }
  }
Qed.

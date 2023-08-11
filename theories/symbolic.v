From Coq Require Import List String ZArith FunctionalExtensionality.
From Autosubst Require Import Autosubst.
From Catala Require Import syntax continuations sequences tactics.
Import ListNotations.

(** Symbolic expressions *)
Inductive sym_expr :=
  | Sbool (b: bool)
  | Sint (i: Z)
  | Svar (s : string)
  | Sop (o : op) (e1 e2 : sym_expr)
  | Sclo (t: term) (sigma: var -> sym_expr)
  .

Inductive sym_result :=
  | SRexpr (e : sym_expr)
  | SRempty
  | SRconflict.

Fixpoint eval_sym_expr (e : sym_expr) (env : string -> value) : value :=
  match e with
  | Sbool b => Bool b
  | Sint i => Int i
  | Svar s => env s
  | Sop Add e1 e2 =>
      match eval_sym_expr e1 env, eval_sym_expr e2 env with
      | Int i1, Int i2 => Int (i1 + i2)%Z
      | _, _ => Int 0%Z (* unreachable *)
      end
  | Sop Eq e1 e2 =>
      match eval_sym_expr e1 env, eval_sym_expr e2 env with
      | Int i1, Int i2 => Bool (i1 =? i2)%Z
      | _, _ => Bool false (* unreachable *)
      end
  | Sclo t s => Closure t (fun x => eval_sym_expr (s x) env)
  end.

(** Symbolic continuations *)
Inductive sym_cont :=
  (* | SCAppL (t1 : term) (* [ t1 \square ] *) *)
  | SCAppR (t2 : term) (* [ \square t2 ] *)
  | SCClosure (t_cl: {bind term}) (sigma_cl: var -> sym_expr)
  | SCDefault (o : option sym_expr) (ts: list term) (tj: term) (tc: term)
  | SCDefaultBase (tc: term)
  .

(** Symbolic constraints *)
Inductive sym_constraint :=
  | Eq (e1 e2 : sym_expr)
  | IsTrue (e : sym_expr)
  | And (c1 c2 : sym_constraint)
  | Or (c1 c2 : sym_constraint)
  | Not (c : sym_constraint)
  .

(** Symbolic paths *)
Definition sym_path := list sym_constraint.

(** Symbolic stores *)
Definition sym_store := var -> sym_expr.

Fixpoint eval_sym_constraint (env : string -> value) (c : sym_constraint) :=
  match c with
  | Eq e1 e2 => value_eqb (eval_sym_expr e1 env) (eval_sym_expr e1 env)
  | IsTrue e =>
      match eval_sym_expr e env with
      | Bool b => b
      | _ => false
      end
  | And c1 c2 =>
      (eval_sym_constraint env c1 && eval_sym_constraint env c2)%bool
  | Or c1 c2 =>
      (eval_sym_constraint env c1 || eval_sym_constraint env c2)%bool
  | Not c =>
      negb (eval_sym_constraint env c)
  end.

Definition eval_sym_path (env : string -> value) (p : sym_path) :=
  forallb (eval_sym_constraint env) p.

(** Symbolic states *)
Inductive sym_state :=
  (* Symbolic evaluation mode *)
  | sym_mode_eval (e : term) (stack : list sym_cont) (path : sym_path) (env : sym_store)
  (* Symbolic continuation mode *)
  | sym_mode_cont (stack : list sym_cont) (path : sym_path) (env : sym_store) (r : sym_result).


Inductive sym_cred: sym_state -> sym_state -> Prop :=
  | sym_cred_var:
      forall x kappa phi sigma,
      sym_cred
          (sym_mode_eval (Var x) kappa phi sigma)
          (sym_mode_cont kappa phi sigma (SRexpr (sigma x)))

  | sym_cred_app:
      forall t1 t2 kappa phi sigma,
      sym_cred
          (sym_mode_eval (App t1 t2) kappa phi sigma)
          (sym_mode_eval t1 ((SCAppR t2) :: kappa) phi sigma)
  
  | sym_cred_clo:
      forall t kappa phi sigma,
      sym_cred
          (sym_mode_eval (Lam t) kappa phi sigma)
          (sym_mode_cont kappa phi sigma (SRexpr (Sclo t sigma)))

  | sym_cred_arg:
      forall t2 kappa phi sigma tcl sigmacl,
      sym_cred
          (sym_mode_cont ((SCAppR t2)::kappa) phi sigma (SRexpr (Sclo tcl sigmacl)))
          (sym_mode_eval t2 ((SCClosure tcl sigmacl)::kappa) phi sigma)

  | sym_cred_beta:
      forall tcl sigmacl kappa phi sigma v,
      sym_cred
          (sym_mode_cont ((SCClosure tcl sigmacl)::kappa) phi sigma (SRexpr v))
          (sym_mode_eval tcl kappa phi (v .: sigmacl))


  | sym_cred_default:
      forall ts tj tc kappa phi sigma,
      sym_cred
          (sym_mode_eval (Default ts tj tc) kappa phi sigma)
          (sym_mode_cont ((SCDefault None ts tj tc)::kappa) phi sigma SRempty)

  | sym_cred_defaultunpack:
      forall o th ts tj tc kappa phi sigma,
      sym_cred
          (sym_mode_cont ((SCDefault o (th::ts) tj tc)::kappa) phi sigma SRempty)
          (sym_mode_eval th ((SCDefault o ts tj tc)::kappa) phi sigma)

  | sym_cred_defaultnone:
      forall ts tj tc kappa phi sigma v,
      sym_cred
          (sym_mode_cont ((SCDefault None ts tj tc)::kappa) phi sigma (SRexpr v))
          (sym_mode_cont ((SCDefault (Some v) ts tj tc)::kappa) phi sigma SRempty)

  | sym_cred_defaultconflict:
      forall ts tj tc kappa phi sigma v v',
      sym_cred
          (sym_mode_cont ((SCDefault (Some v) ts tj tc)::kappa) phi sigma (SRexpr v'))
          (sym_mode_cont kappa phi sigma SRconflict)

  | sym_cred_defaultvalue:
      forall v tj tc kappa phi sigma,
      sym_cred
          (sym_mode_cont ((SCDefault (Some v) [] tj tc)::kappa) phi sigma SRempty)
          (sym_mode_cont kappa phi sigma (SRexpr v))

  (* | cred_defaultnonefinal: (* not needed *)
      (* $\lcont \mathtt{Def}(\synnone, [], e_j, e_c) \cons \kappa, \sigma, v \rcont \leadsto \lcont \kappa, \sigma, v \rcont$ \hfill $v \neq \synempty, \synconflict$ *)
      todo *)

  | sym_cred_defaultbase:
      forall tj tc kappa phi sigma,
      sym_cred
          (sym_mode_cont ((SCDefault None [] tj tc)::kappa) phi sigma SRempty)
          (sym_mode_eval tj ((SCDefaultBase tc)::kappa) phi sigma)

  | sym_cred_defaultbasetrue:
      forall tc kappa phi sigma v,
      sym_cred
          (sym_mode_cont ((SCDefaultBase tc)::kappa) phi sigma (SRexpr v))
          (sym_mode_eval tc kappa (IsTrue v :: phi) sigma)

  | sym_cred_defaultbasefalse:
      forall tc kappa phi sigma v,
      sym_cred
          (sym_mode_cont ((SCDefaultBase tc)::kappa) phi sigma (SRexpr v))
          (sym_mode_cont kappa (Not (IsTrue v) :: phi) sigma SRempty)

  | sym_cred_empty:
      forall k kappa phi sigma,
      (forall o ts tj tc, k <> SCDefault o ts tj tc) ->
      sym_cred
          (sym_mode_cont (k::kappa) phi sigma SRempty)
          (sym_mode_cont kappa phi sigma SRempty)

  | sym_cred_conflict:
      forall k kappa phi sigma,
      sym_cred
          (sym_mode_cont (k::kappa) phi sigma SRconflict)
          (sym_mode_cont kappa phi sigma SRconflict)

  (* | sym_cred_confict_intro:
      forall kappa phi sigma,
      sym_cred
          (sym_mode_eval Conflict kappa phi sigma)
          (sym_mode_cont kappa phi sigma SRconflict)

  | sym_cred_empty_intro:
      forall kappa phi sigma,
      sym_cred
          (sym_mode_eval Empty kappa phi sigma)
          (sym_mode_cont kappa phi sigma SRempty) *)
  .

Definition concretize_env (env : string -> value) (ctx : var -> sym_expr) :=
  fun x => eval_sym_expr (ctx x) env.

Notation "env • ctx" := (concretize_env env ctx) (at level 80).

Definition concretize_cont (env : string -> value) (k : sym_cont) :=
  match k with
  (* | SCAppL t => CAppL t *)
  | SCAppR t => CAppR t
  | SCClosure t ctx => CClosure t (env • ctx)
  | SCDefault None l t1 t2 => CDefault None l t1 t2
  | SCDefault (Some e) l t1 t2 => CDefault (Some (eval_sym_expr e env)) l t1 t2
  | SCDefaultBase t => CDefaultBase t
  end.

Definition concretize_result (env : string -> value) (r : sym_result) :=
  match r with
  | SRexpr e => RValue (eval_sym_expr e env)
  | SRempty => REmpty
  | SRconflict => RConflict
  end.

Definition concretize_state (env : string -> value) (s : sym_state) :=
  match s with
  | sym_mode_eval t l p s => mode_eval t (map (concretize_cont env) l) (env • s)
  | sym_mode_cont l p s r => mode_cont (map (concretize_cont env) l) (env • s) (concretize_result env r)
  end.

Definition satisfy (env : string -> value) (s : sym_state) :=
  match s with
  | sym_mode_eval _ _ p _ => eval_sym_path env p = true
  | sym_mode_cont _ p _ _ => eval_sym_path env p = true
  end.

Notation "x ⊨ s" := (satisfy x s) (at level 80).

(**
    What it means for a concrete and a symbolic value
    to be related with respect to an assignement of free variables
*)

Definition similar_value (env : string -> value) (v : value) (sym_v : sym_expr) :=
    v = eval_sym_expr sym_v env.

(**
    What it means for a concrete and a symbolic result
    to be related with respect to an assignement of free variables
*)
Inductive similar_result (env : string -> value) : result -> sym_result -> Prop :=
    | similar_result_value v sym_v :
        similar_value env v sym_v ->
        similar_result env (RValue v) (SRexpr sym_v)
    | similar_result_empty :
        similar_result env REmpty SRempty
    | similar_result_conflict :
        similar_result env RConflict SRconflict.

(**
    What it means for a concrete and a symbolic environement
    to be related with respect to an assignement of free variables
*)
Definition similar_env (env0 : string -> value) (env1 : var -> value) (env2 : var -> sym_expr) :=
    forall x, similar_value env0 (env1 x) (env2 x).

(**
    What it means for a concrete and a symbolic continuation to be related
    with respect to an assignement of free variables
*)
Inductive similar_cont (env : string -> value) : cont -> sym_cont -> Prop :=
    (* | similar_cont_CAppL t :
        similar_cont env (CAppL t) (SCAppL t) *)

    | similar_cont_CAppR t :
        similar_cont env (CAppR t) (SCAppR t)
    
    | similar_cont_CClosure (x : {bind term}) ctx sym_ctx :
        similar_env env ctx sym_ctx ->
        similar_cont env (CClosure x ctx) (SCClosure x sym_ctx)
    
    | similar_cont_CDefault_none l t1 t2 :
        similar_cont env (CDefault None l t1 t2) (SCDefault None l t1 t2)

    | similar_cont_CDefault_some v sym_v l t1 t2 :
        similar_value env v sym_v ->
        similar_cont env (CDefault (Some v) l t1 t2) (SCDefault (Some sym_v) l t1 t2)
    
    | similar_cont_CDefault_base t :
        similar_cont env (CDefaultBase t) (SCDefaultBase t).

(**
    What it means for a concrete and a symbolic state to be related
    with respect to an assignement of free variables
*)
Inductive similar (env : string -> value) : state -> sym_state -> Prop :=
    | similar_mode_eval t kappa sym_kappa sigma sym_sigma phi :
        Forall2 (similar_cont env) kappa sym_kappa ->
        eval_sym_path env phi = true ->
        similar_env env sigma sym_sigma ->
        similar env (mode_eval t kappa sigma) (sym_mode_eval t sym_kappa phi sym_sigma)
    
    | similar_mode_cont kappa sym_kappa sigma sym_sigma phi r sym_r :
        Forall2 (similar_cont env) kappa sym_kappa ->
        eval_sym_path env phi = true ->
        similar_result env r sym_r ->
        similar_env env sigma sym_sigma ->
        similar env (mode_cont kappa sigma r) (sym_mode_cont sym_kappa phi sym_sigma sym_r)
    .

(* Lemma eval_sym_expr_closure:
    forall tcl sigmacl e env,
        Closure tcl sigmacl = eval_sym_expr e env ->
        exists sym_sigmacl,
            e = Sclo tcl sym_sigmacl /\
            similar_env env sigmacl sym_sigmacl.
Proof.
    intros.
    induction e; try easy; simpl in *.
    - eexists. *)

Definition no_closure (env : string -> value) :=
    forall x tcl sigmacl, env x = Closure tcl sigmacl -> False.

Theorem boring_lemma:
  forall env sigma sym_sigma v sym_v,
    similar_value env v sym_v ->
    similar_env env sigma sym_sigma ->
    similar_env env (v .: sigma) (sym_v .: sym_sigma).
Proof.
  intros * Hsim_v Hsim_env x.
  unfold similar_value in *; subst.
  destruct x; simpl; try easy.
  apply Hsim_env.
Qed.

(**
    Every concrete transition can be simulated
    by a symbolic one
*)
Theorem sym_cred_complete:
  forall env s1 s2 sym_s1,
    no_closure env ->
    similar env s1 sym_s1 ->
    cred s1 s2 ->
    exists sym_s2,
      similar env s2 sym_s2 /\ sym_cred sym_s1 sym_s2.
Proof.
  intros * Hclo Hsim1 Hred.
  induction Hred.
  { inversion Hsim1; subst.
    now repeat econstructor.
  }
  { inversion Hsim1; subst.
    now repeat econstructor.
  }
  - inversion Hsim1; subst.
    repeat econstructor; eauto.
    unfold similar_value. simpl.
    f_equal. now apply functional_extensionality.
  - inversion Hsim1; subst.
    inversion H2; subst.
    inversion H5; subst.
    inversion H1; subst.
    inversion H0; subst.
    destruct sym_v; try easy.
    + simpl in H4. exfalso. eapply Hclo; eauto.
    + simpl in H4. destruct o; try easy.
      destruct (eval_sym_expr sym_v1); try easy.
      destruct (eval_sym_expr sym_v2); try easy.
      destruct (eval_sym_expr sym_v1); try easy.
      destruct (eval_sym_expr sym_v2); try easy.
    + simpl in H4. injection H4 as -> ->.
      repeat econstructor; eauto.
  - inversion Hsim1; subst.
    inversion H5; subst.
    inversion H2; subst.
    inversion H4; subst.
    repeat econstructor; eauto.
    now apply boring_lemma.
  - inversion Hsim1; subst.
    now repeat econstructor.
  - inversion Hsim1; subst.
    inversion H2; subst.
    inversion H5; subst.
    inversion H1; subst.
    + now repeat econstructor.
    + now repeat econstructor.
  - inversion Hsim1; subst.
    inversion H2; subst.
    inversion H1; subst.
    inversion H5; subst.
    now repeat econstructor.
  - inversion Hsim1; subst.
    inversion H2; subst.
    inversion H1; subst.
    inversion H5; subst.
    now repeat econstructor.
  - inversion Hsim1; subst.
    inversion H2; subst.
    inversion H1; subst.
    inversion H5; subst.
    now repeat econstructor.
  - inversion Hsim1; subst.
    inversion H2; subst.
    inversion H1; subst.
    inversion H5; subst.
    now repeat econstructor.
  - inversion Hsim1; subst.
    inversion H2; subst.
    inversion H1; subst.
    inversion H5; subst.
    inversion H0.
    repeat econstructor; eauto.
    simpl. now rewrite <- H4.
  - inversion Hsim1; subst.
    inversion H2; subst.
    inversion H1; subst.
    inversion H5; subst.
    inversion H0.
    repeat econstructor; eauto.
    simpl. now rewrite <- H4.
  - inversion Hsim1; subst.
    inversion H6; subst.
    inversion H3; subst.
    repeat econstructor; auto.
    inversion H2; subst; try easy.
    + intros * [=<-<-<-<-].
      now eapply H.
    + intros * [=<-<-<-<-].
      now eapply H.
  - inversion Hsim1; subst.
    inversion H2; subst.
    inversion H5; subst.
    now repeat econstructor.
  - admit arthur "todo : fix".
  - admit arthur "todo : fix".
  - admit arthur "todo : fix".
  - admit arthur "todo : fix".
Admitted.


Theorem sym_creds_complete:
  forall s1 s2,
    star cred s1 s2 ->
    forall env sym_s1,
      no_closure env ->
      similar env s1 sym_s1 ->
      exists sym_s2,
        similar env s2 sym_s2 /\ star sym_cred sym_s1 sym_s2.
Proof.
  intros s1 s2 H.
  induction H using star_ind_n1; intros.
  - eauto with sequences.
  - specialize (IHstar _ _ H1 H2) as [sym_s2 [Hs2_1 Hs2_2]].
    epose proof (sym_cred_complete _ _ _ _ H1 Hs2_1 H) as [sym_s3 [Hs3_1 Hs3_2]].
    eexists. split; cycle 1.
    eapply star_trans; eauto.
    eapply star_one; eauto.
    auto.
Qed.

(* Theorem boring_2: *)
Theorem boring_2:
  forall env sigma1 sigma2,
    similar_env env sigma1 sigma2 -> (fun x => eval_sym_expr (sigma2 x) env) = sigma1.
Proof.
  intros.
  apply functional_extensionality.
  intros. simpl.
  now rewrite H.
Qed.

Theorem boring_3:
  forall (env : string -> value) v ctx,
    (env • v .: ctx) = ((eval_sym_expr v env) .: (env • ctx)).
Proof.
  intros.
  apply functional_extensionality.
  now intros [].
Qed.

Theorem sym_cred_sound:
  forall sym_s1 sym_s2,
    sym_cred sym_s1 sym_s2 ->
    forall env,
      no_closure env ->
      env ⊨ sym_s2 ->
      cred (concretize_state env sym_s1) (concretize_state env sym_s2).
Proof.
  intros * Hred * Hclo Hsat.
  inversion Hred; subst; try (econstructor; fail).
  - simpl. rewrite boring_3.
    econstructor.
  - simpl. destruct o; econstructor.
  - simpl in *.
    destruct eval_sym_expr; try easy.
    destruct b; simpl in *; try easy.
    econstructor.
  - simpl in *.
    assert (exists b, eval_sym_expr v env = Bool b) as [b Hb] by admit arthur.
    rewrite Hb in *.
    destruct b; simpl in *; try easy.
    econstructor.
  - simpl in *.
    econstructor.
    intros.
    destruct k; try easy.
    simpl. destruct o0.
    + specialize (H (Some s) ts tj tc).
      now intros [=<-<-<-<-].
    + specialize (H None ts tj tc).
      now intros [=<-<-<-<-].
Abort.

(* Theorem sym_cred_sound:
  forall sym_s1 sym_s2,
    sym_cred sym_s1 sym_s2 ->
    forall env s1 s2,
      no_closure env ->
      similar env s1 sym_s1 ->
      similar env s2 sym_s2 ->
      cred s1 s2.
Proof.
  intros * Hred * Hclo Hsim1 Hsim2.
  inversion Hred; subst.
  - inversion Hsim1; subst.
    inversion Hsim2; subst.
    inversion H9; subst.
    rewrite H1. 
    
    <- (boring_2 _ _ _ H10), <- (boring_2 _ _ _ H6).
    repeat econstructor; eauto.
    econstructor.
  - inversion Hsim1; subst.
    repeat econstructor; eauto.
    rewrite <- (boring_2 _ _ _ H6).
    econstructor.
  - inversion Hsim1; subst.
    repeat econstructor; eauto.
    rewrite <- (boring_2 _ _ _ H6).
    econstructor.
  - inversion Hsim1; subst.
    inversion H4; subst.
    inversion H2; subst.
    inversion H6; subst.
    inversion H1; subst.
    repeat econstructor; eauto.
    rewrite <- (boring_2 _ _ _ H7).
    econstructor.
  - inversion Hsim1; subst.
    inversion H4; subst.
    inversion H2; subst.
    inversion H6; subst.
    repeat econstructor; eauto.
    rewrite <- (boring_2 _ _ _ H7).
    pose proof (boring_lemma _ _ _ _ _ H8 H1).
    rewrite (boring_2 _ _ _ H).
    econstructor.
  - inversion Hsim1; subst.
    repeat econstructor; eauto.
    rewrite <- (boring_2 _ _ _ H6).
    econstructor.
  - inversion Hsim1; subst.
    inversion H4; subst.
    inversion H6; subst.
    inversion H2; subst.
    + repeat econstructor; eauto.
      rewrite <- (boring_2 _ _ _ H7).
      econstructor.
    + repeat econstructor; eauto.
      rewrite H1, <- (boring_2 _ _ _ H7).
      econstructor.
  - inversion Hsim1; subst.
    inversion H4; subst.
    inversion H6; subst.
    inversion H2; subst.
    repeat econstructor; eauto.
    rewrite H1, <- (boring_2 _ _ _ H7).
    econstructor.
  - inversion Hsim1; subst.
    inversion H4; subst.
    inversion H6; subst.
    inversion H2; subst.
    rewrite H1, H8, <- (boring_2 _ _ _ H7).
    repeat econstructor; eauto.
  - inversion Hsim1; subst.
    inversion H4; subst.
    inversion H6; subst.
    inversion H2; subst.
    rewrite H1, <- (boring_2 _ _ _ H7).
    repeat econstructor; eauto.
  - inversion Hsim1; subst.
    inversion H4; subst.
    inversion H6; subst.
    inversion H2; subst.
    rewrite <- (boring_2 _ _ _ H7).
    repeat econstructor; eauto.
  - inversion Hsim1; subst.
    inversion H4; subst.
    inversion H6; subst.
    inversion H2; subst.
    rewrite <- (boring_2 _ _ _ H7).
    repeat econstructor; eauto.
    simpl. admit.
    econstructor.
  - admit "Arthur".
  - admit "Arthur".
  - admit "Arthur".
  - admit "Arthur".
  - admit "Arthur".
Admitted. *)

Require Import DCSyntax.
Require Import LCSyntax.
Require Import DCFreeVars.
Require Import DCValuesRes.

Require Import DCValues.
Require Import STLCDefinition.

Require Import MyTactics.

Tactic Notation "admit" := admit.
Tactic Notation "admit" string(x):= admit.


Notation "'is_nerror' t" :=
  (match t with
  | Conflict | Empty => False
  | _ => True
  end) (at level 70).

Notation "'is_error' t" :=
  (match t with
  | Conflict | Empty => True
  | _ => False
  end) (at level 70).

Module D := DCSyntax.
Module L := LCSyntax.

Import List.ListNotations.
Open Scope list_scope.


(** Some parts of the code could be *)


Definition trans_op : D.operator -> L.operator.
Admitted.

Lemma assert_lift_do_lift : (lift 1 (D.Var 0)) = D.Var 1.
Proof. autosubst. Qed.


(** Definition of the translation as a program fixpoint. *)

Inductive purity := pure | impure.

Definition trans_ctx := var -> purity.

Definition is_pure (Delta: trans_ctx) t :=
  match t with
  | D.Var x => Delta x
  | D.Lam _ => pure
  | D.App _e1 _e2 => impure
  | D.Default _es _ej _ec => impure
  | D.Const _ => pure
  | D.Empty => impure
  | D.Conflict => impure
  end.

(* begin snippet dc2lc_trans *)
Fixpoint trans (Delta: trans_ctx) t { struct t } :=
  match t with
  | D.Var x =>
    if is_pure Delta t 
    then monad_return (L.EVar x)
    else L.EVar x
  
  | D.Lam t =>
    (L.ELam (trans (pure .: Delta) t))

  | D.App f arg =>
    let f' := trans Delta f in
    let arg' := trans Delta arg in
    match (is_pure Delta f, is_pure Delta arg) with
    | (pure, pure) => (L.EApp f' arg')
    | (impure, pure) => monad_bind f' (L.EApp (L.EVar 0) (lift 1 arg'))
    | (pure, impure) => monad_bind arg' (L.EApp (lift 1 f') (L.EVar 0))
    | (impure, impure) => monad_bind f' (monad_bind (lift 1 arg') (L.EApp (lift 1 (L.EVar 0)) (L.EVar 0)))
    end

  | D.Default es ej ec =>
    monad_handle
      (List.map (fun ei => if is_pure Delta ei then monad_return (trans Delta ei) else trans Delta ei) es)
      (if is_pure Delta ej then monad_return (trans Delta ej) else trans Delta ej)
      (if is_pure Delta ec then monad_return (trans Delta ec) else trans Delta ec)

  | D.Const b =>
    L.OConst b

  | Empty =>
    monad_empty
  | Conflict => L.EPanic EConflict
  end.
(* end snippet dc2lc_trans *)

(* optimisation is optional result. *)
(* Fixpoint cutting Delta t {struct t} : D.term * list D.term := . *)

Require Import MySequences.
Require Import DCReduction.


Theorem safe_optimization:
  forall t Delta,
  is_pure (pure .: Delta) t = pure ->
  forall s v,
  is_value_res v ->
  star cbv (D.App (D.Lam t) s) v <->
  star cbv t.[s/] v.
Proof.
  admit "This theorem is not true at all. Counter example :
    [ (Lam x)[x |-> Empty] ] vs [ let x = Empty in Lam y. x ]

  The first reduces to [Lam y. Empty], while the second one reduces to [Empty]. Both terms are terminals.
  ".
Abort.



Section Correctness.

  Require Import DCReduction.
  Require Import LCReduction.

  Definition dcbv := DCReduction.cbv.
  Definition lcbv := LCReduction.cbv.

  Reserved Notation "'nce' t" (at level 80).
  Print L.term.
  Print L.except.

  Inductive no_compile_error: L.term -> Prop :=
  | NCE_App: forall t1 t2,
    nce t1 -> nce t2 -> nce (EApp t1 t2)
  | NCE_Var: forall x,
    nce (EVar x)
  | NCE_Lam: forall t,
    nce t -> nce (ELam t)
  | NCE_Op: forall op,
    nce (EOp op)
  | NCE_Match: forall arg tnone tsome,
    nce arg ->
    nce tnone ->
    nce tsome ->
    nce (EMatch arg tnone tsome)
  | NCE_None:
    nce EVariantNone
  | Nce_Some: forall t,
    nce t ->
    nce EVariantSome t
  | Nce_Panic_Conflict:
    nce (EPanic EConflict)
  | Nce_Panic_NoValueProvided:
    nce (EPanic ENoValueProvided)

  where "'nce' t" := (no_compile_error t)
  .

Require Import MySequences.
Require Import MyRelations.

Lemma bind_ret_star_cbv v t:
  LCValues.is_value v ->
  star cbv
    (monad_bind (monad_return v) t)
    t.[v/].
Proof.
  intros.
  eapply star_one.
  unfold monad_bind, monad_return.
  eapply RedEMatchSomeV; asimpl; try eauto.
Qed.


Tactic Notation "consider" uconstr(E) :=
  match goal with
    [_:  context [E] |- _ ] =>
    idtac end.



Tactic Notation "pick" uconstr(R) ltac(k) :=
  match goal with
  |[h : context [R] |-_ ] => k h
  end.

Tactic Notation "save" uconstr(E) "as" ident(x) :=
  match goal with [ h: context [E] |- _ ] => rename h into x end.


Require Import STDCDefinition.

Lemma trans_is_value Delta v:
  is_value v -> LCValues.is_value (trans Delta v).
Admitted.

Lemma trans_subst_pure Delta t v:
  pure = is_pure Delta v ->
  exists target,
    star lcbv (trans (pure .: Delta) t).[trans Delta v/] target /\
    star lcbv (trans Delta t.[v/]) target.
Admitted.

Lemma trans_is_value_impure Delta v:
  is_value v ->
  impure = is_pure Delta v ->
  (exists u,
    trans Delta v = EVariantSome u /\
    LCValues.is_value u /\
    exists vv, trans Delta vv = u /\ pure = is_pure Delta vv)
  \/ trans Delta v = EVariantNone.
Admitted.

Lemma trans_impure_None Delta t v:
  trans Delta v = EVariantNone ->
  star lcbv (trans Delta t.[v/]) EVariantNone.
(* Alain to Denis: This is the "lemma" we discussed last time for the optimization property. We need to add hypothesis on trans to make sure this is indeed true, as it is not true in general. 

One candidate should be that free variables must make a difference to the computed term.

One other candidate is that terms must be fully applied in some sense.

In both cases, this propertie is not trivial.
*)
Admitted.

Definition diagram t1 t2 :=
  exists target, star lcbv t1 target /\ star lcbv t2 target.


Lemma diagram_match_branch_some t2 t2':
  diagram t2 t2' ->
  forall u t1,
  diagram (EMatch u t1 t2) (EMatch u t1 t2').
Admitted.

Lemma diagram_match_cond u u':
  diagram u u' ->
  forall t1 t2,
  diagram (EMatch u t1 t2) (EMatch u' t1 t2).
Admitted.

Lemma diagram_app t1 t1':
  diagram t1 t1' ->
  forall t2,
  diagram (EApp t1 t2) (EApp t1' t2).
Admitted.

Lemma diagram_lift t1 t2:
  diagram t1 t2 ->
  forall n,
  diagram (lift n t1) (lift n t2).
Admitted.

Lemma is_pure_stable t t':
  dcbv t t' ->
  forall Delta,
  is_pure Delta t = is_pure Delta t'.
Proof.
  induction 1; tryfalse; intros; try solve [simpl; eauto].
  { admit "not true: first we don't have any hypothesis on whenever t or v are pure or not. Moreother, if [t = Lam x], then it is pure. hence u is pure. Disproving the lemma.". }
  { admit "always true, but we don't have the correct lemma here.". }
  { admit "always true, but we don't have the correct lemma here.". }
Abort.



Lemma trans_correct t1 t2 Gamma T:
  jt Gamma t1 T ->
  forall Delta,
  dcbv t1 t2 ->

  exists target,
    star lcbv (trans Delta t1) target /\
    star lcbv (trans Delta t2) target.  
Proof.
  intros Hjt Delta Hdcbv.
  revert Hdcbv Gamma T Hjt Delta.

  induction 1; tryfalse.
  * (* Beta-reduction with [v] a value *)
    intros.
    simpl; remember (is_pure Delta v) as p; induction p.
    { (* [v] is [pure] *)
      destruct trans_subst_pure with Delta t v as
        [target [Htarget1 Htarget2]]; eauto.
      exists target; split.
      { eapply star_step.
        { eapply RedBetaV; eauto using trans_is_value. }
        eauto.
      } {
        subst. eauto.
      }
    }
    { (* [v] is [impure] *)
      unfold monad_bind.
      destruct trans_is_value_impure with Delta v
        as [[v' [Hv [Hv'1 [vv [Hv'2 Hv'3]]]]]| Hv]; eauto; rewrite Hv.
      { (* [v] is [Some v'] *)
        destruct trans_subst_pure with Delta t vv as
          [target [Htarget1 Htarget2]]; eauto.
        exists target; split.
        { eapply star_step. { eapply RedEMatchSomeV; eauto. }
          eapply star_step. { eapply RedBetaV; eauto. }
          asimpl.
          rewrite <- Hv'2; eauto.
        }
        { subst.
          admit "this i don't really know how to do for now".
        }
      }
      { (* [v] is [None] *)
        eexists; split.
        { eapply star_one. { eapply RedEMatchNone; eauto. } }
        { subst; eapply trans_impure_None; eauto. }
      }
    }
  * (* AppL *)
    intros.
    inverts Hjt.
    edestruct IHHdcbv as [target [Htarget1 Htarget2]]; eauto.
    simpl.
    (* 8 cases to consider. *)
    remember (is_pure Delta t1) as p1.
    remember (is_pure Delta t2) as p2.
    remember (is_pure Delta u) as p3.
    induction p1, p2, p3; unfold monad_bind; asimpl.
    { (* pure, pure, pure *)
      exists (EApp target (trans Delta u)); split;
      eapply LCReduction.star_cbv_EAppL; eauto.
    }
    { (* pure, pure, impure *)
      eapply diagram_match_branch_some.
      eapply diagram_app.
      eapply diagram_lift.
      unfold diagram; eauto.
    }
    { (* pure, impure, pure *)
      admit "induction hypothesis is not sufficent to derive this property. Indeed, in the case where [t1 = t2 = App x y], the induction hypothesis indicate [star lcbv (trans Delta t1) (trans Delta t1)]. In this case, we don't have any relationship between [L.EApp (trans Delta t1) (trans Delta u)] and [EMatch (trans Delta t2) EVariantNone (L.EApp (L.EVar 0) (lift 1 (trans Delta u)))].
      
      
      One way to fix this could be to have is_pure is stable relative to dcbv. But this lemma is not true. see above for a tenative of proof".
    }
    { (* pure, impure, impure *)
      admit "same as previous case.".
    }
    { (* impure, pure, pure *)
      admit "same as previous case.".
    }
    { (* impure, pure, impure *)
      admit "same as previous case.".
    }
    { (* impure, impure, pure *)
      eapply diagram_match_cond.
      unfold diagram; eauto.
    }
    { (* impure, impure, impure *)
      eapply diagram_match_cond.
      unfold diagram; eauto.
    }
  * admit "This should be around the same thing as the previous case.".
  * simpl.
    admit "error: if the term is impure, and [trans Delta t] is None, then the left hand side reduces to None while the right hand side reduces to Conflict.".
  * simpl; intros. 
    remember (is_pure Delta t) as p; induction p; unfold monad_bind; eexists; split.
    all: try solve [ eapply star_refl ].
    eapply star_one.
    eapply RedEMatchConflict. 
    all: try solve [ eapply star_one]



Admitted.


Require Import DCSyntax.
Require Import MCSyntax.
Require Import DCFreeVars.

Require Import STMCDefinition.

Require Import MyTactics.


Module D := DCSyntax.
Module M := MCSyntax.

Import List.ListNotations.
Open Scope list_scope.


(** Some parts of the code could be *)


Definition trans_op : D.operator -> M.operator.
Admitted.

Lemma assert_lift_do_lift : (lift 1 (D.Var 0)) = D.Var 1.
Proof. autosubst. Qed.


Definition thunk: term -> term := fun t => Lam (lift 1 t).
Definition unthunk: term -> term := fun t => App t (Const true).



(** Definition of the translation as a coq inductive. 

To handle environements, we use lists.

*)

Definition trans_ctx := list bool.
Definition trans_ctx := var -> bool.

(* todo : utiliser nouvelle fonction. *)
Inductive trans : trans_ctx -> DCSyntax.term -> MCSyntax.term -> Prop :=
  | TVarPure: forall Delta x,
    List.nth_error Delta x = Some true ->
    trans Delta (D.Var x) (MReturn (M.Var x))
  | TVarUnpure: forall Delta x,
    List.nth_error Delta x = Some false ->
    trans Delta (D.Var x) (M.Var x)
  | TLam: forall Delta t t',
    trans (true .: Delta) t t' ->
    trans Delta (D.Lam t) (MReturn (M.Lam t'))
  | TAppLam: forall Delta arg arg' body body',
    trans Delta arg arg' ->
    trans (true .: Delta) body body' ->
    trans Delta (D.App (D.Lam body) arg) (MBind arg' body')
  | TAppOp: forall Delta t1 t2 t1' t2' op,
    trans Delta t1 t1' ->
    trans Delta t2 t2' ->
    trans Delta
      (D.BinOp op t1 t2)
      (MBind t1'
        (MBind (lift 1 t2')
          (MReturn (M.BinOp (trans_op op) (M.Var 0) (M.Var 1)))
        )
      )
  | TAppVarPure: forall Delta x arg arg',
  List.nth_error Delta x = Some true ->
    trans Delta arg arg' ->
    trans Delta
      (D.App (D.Var x) arg)
      (MBind arg'
        (M.App (lift 1 (M.Var x)) (M.Var 0))
      )
  | TAppVarUnpure: forall Delta x arg arg',
  List.nth_error Delta x = Some false ->
    trans Delta arg arg' ->
    trans Delta
      (D.App (D.Var x) arg)
      (MBind (M.Var x)
        (MBind arg'
          (M.App (lift 1 (M.Var 0)) (M.Var 0))
        ) 
      )
  | TDefault: forall Delta es es' ej ej' ec ec',
    List.Forall2 (trans Delta) es es' ->
    trans Delta ej ej' ->
    trans Delta ec ec' ->
    trans Delta (Default es ej ec) (MHandle es' (thunk ej') (thunk ec'))
  | TLit: forall Delta b, 
    trans Delta (D.Const b) (MReturn (M.Const b))
  | TEmpty: forall Delta,
    trans Delta Empty MEmpty
  | TConflict: forall Delta,
    trans Delta D.Conflict (MRaise EConflict)
.


(** First we need to prove that when we are applying the nth_error function, the result is always in bounds. To do so, we need to check the length of the list is always greater than largest free variable. This is not trivial since we are introducing thunks in the term. *)

Lemma option_Some_neq_None {A} {x: A} o:
  o = Some x -> o <> None.
Proof.
  intros; subst; congruence.
Qed.

Lemma nth_error_Some' {A} l n (x: A) : List.nth_error l n = Some x -> n < List.length l.
Proof.
  intros Hx.
  apply List.nth_error_Some.
  rewrite Hx; congruence.
Qed.


(* The other abence of overflow is on t', and require infrastructure about free variables on the terms. *)

Lemma trans_ctx_no_overflow Delta t t':
    trans Delta t t' -> fv (List.length Delta) t.
Proof.
  induction 1; fv; repeat split; try eapply (nth_error_Some'); eauto.
  { (* missing case because the induction predicate generated automaticly by coq is not strong enought. Assumed for the moment. *)
    admit.
  }
Admitted.


(** translation correction *)

Require Import STDCDefinition.
Module DT := STDCDefinition.
Module MT := STMCDefinition.

Inductive trans_ty: bool -> DT.ty -> MT.ty -> Prop :=
| TTVar: forall x, trans_ty true (DT.TyVar x) (MT.TyVar x)
| TTFun: forall A B A' B',
  trans_ty true A A' ->
  trans_ty true B B' ->
  trans_ty true (DT.TyFun A B) (MT.TyFun A' (MT.TyOption B'))
| TTBool: trans_ty true DT.TyBool MT.TyBool
| TTUnpure: forall tau tau',
  trans_ty true tau tau' ->
  trans_ty false tau (MT.TyOption tau') 
.


(* Propreties on trans_ty: trans_ty is a functionnal. This means there is a function such that trans_ty tau [tau] for all tau. Moreover, if trans_ty tau tau', then tau' = [tau]. *)

Lemma trans_ty_unique: forall b tau tau1',
  trans_ty b tau tau1' -> forall tau2', trans_ty b tau tau2' -> tau1' = tau2'.
Proof.
  induction 1; intros tau2' Htrans; inverts Htrans.
  * eauto.
  * replace A'0 with A'; eauto.
    replace B'0 with B'; eauto.
  * eauto.
  * replace tau'0 with tau'; eauto.
Qed.

Lemma trans_ty_exists: forall b tau, exists tau',
  trans_ty b tau tau'.
Proof.
  assert (forall (tau : DT.ty), exists tau' : MT.ty, trans_ty true tau tau').
  { induction tau; unpack; eexists; econstructor; eauto. }
  intros.
  case b; eauto.
  destruct (H tau) as [tau' Htau'].
  eexists; econstructor; eauto.
Qed.

Lemma trans_correct_type Delta  t1 t1':
  trans Delta t1 t1' ->  
  forall Gamma Gamma' tau tau',
  jt Gamma t1 tau ->
  trans_ty true tau tau' ->
  (forall n, trans_ty (true (* TODO *)) (Gamma n) (Gamma' n)) ->
  MT.jt Gamma' t1' tau'.
Proof.
  (*
  induction 1; intros.
  * inverts H0.
    repeat econstructor.
    eapply trans_ty_unique.
    apply H2.
    apply H1.
  * inverts H0. 
    repeat econstructor.
    eapply trans_ty_unique.
    apply H2.
    apply H1.
  * inverts H0. *)
Admitted.

Require Import DCReduction.

Require Import MySequences.
Require Import MyRelations.

Require Import Procrastination.

Check star.

Lemma trans_correct Delta t1 t2 t1' t2':
  exists rel: M.term -> M.term -> Prop,
  trans Delta t1 t1' ->
  cbv t1 t2 ->
  trans Delta t2 t2' ->
  rel t1' t2'.
Proof.
  begin defer assuming rel.
   exists rel.
   intros Htrans Hred Htrans'.
   gen Htrans Htrans'.
   induction Hred;
    tryfalse.
  * admit.
  * intros Htrans Htrans'.

  * admit.
  * admit.
  * admit.
  * admit.
  * admit.
  * admit.
  * admit.
  * admit.
  * admit.
  * admit.
  * admit.
  * admit.
  * admit.
  * admit. 

  

  



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


Definition thunk: M.term -> M.term := fun t => Lam (lift 1 t).
Definition unthunk: term -> term := fun t => App t (Const true).



(** Definition of the translation as a program fixpoint. *)


Definition trans_ctx := var -> bool.

(* Defintion mmap t f := MBind arg (f (D.Var 0)) *)

Fixpoint trans (Delta: trans_ctx) t { struct t } :=
  match t with
  | D.Var x =>
    if Delta x
    then MReturn (M.Var x)
    else M.Var x
  
  | D.Lam t =>
    MReturn (M.Lam (trans (true .: Delta) t))
  
  | D.App (D.Lam body) arg => (* let arg in body *)
    MBind (trans Delta arg) (trans (true .: Delta) body)
  (* | D.App () =>
    MBind (trans Delta arg) (MReturn (M.Op op) ) *)
  | D.App (D.Var f) arg =>
    if Delta f
    then (MBind (trans Delta arg)
      (M.App (lift 1 (M.Var f)) (M.Var 0))
    )
    else (MBind (M.Var f)
      (MBind (trans Delta arg)
        (M.App (lift 1 (M.Var 0)) (M.Var 0))
      ) 
    )
  | D.Default es ej ec =>
    MHandle
      (List.map (trans Delta) es)
      (thunk (trans Delta ej))
      (thunk (trans Delta ec))
  | D.Const b =>
    M.Const b
  | Empty =>
    MEmpty
  | Conflict => MRaise EConflict

  | D.BinOp op t1 t2 => MRaise M.ECompile
  | D.App _ _ => MRaise M.ECompile
  end.

(** translation correction *)

Require Import STDCDefinition.
Module DT := STDCDefinition.
Module MT := STMCDefinition.

Require Import Program.


Fixpoint trans_ty_aux ty := 
  match ty with
  | DT.TyVar x => MT.TyVar x 
  | DT.TyFun A B => MT.TyFun (trans_ty_aux A) (MT.TyOption (trans_ty_aux B))
  | DT.TyBool => MT.TyBool
  end.

Definition trans_ty (b: bool) ty := if b then trans_ty_aux ty else MT.TyOption (trans_ty_aux ty).

Lemma jt_te_thunk Gamma t tau:
  MT.jt Gamma t tau ->
  forall u,
  MT.jt Gamma (thunk t) (MT.TyFun u tau).
Proof.
  unfold thunk.
  intros.
  econstructor.
  now eapply jt_te_renaming_0.
Qed.


Lemma trans_correct_type Gamma t1 tau:
  jt Gamma t1 tau ->
  forall Delta,
  MT.jt (fun x => trans_ty (Delta x) (Gamma x)) (trans Delta t1) (trans_ty false tau).
Proof.
  induction 1 using jt_ind'; intros.
  * remember (Delta x) as b.
    induction b; simpl; symmetry in Heqb; rewrite Heqb.
    - repeat econstructor; rewrite Heqb, H; eauto.
    - repeat econstructor; rewrite Heqb, H; eauto.
  * simpl.
    repeat econstructor.
    replace (trans_ty_aux T .: (fun x : var => trans_ty (Delta x) (Gamma x))) with (fun x : var => trans_ty ((true .: Delta) x) ((T .: Gamma) x)).
    eapply IHjt.
    { unfold ".:".
      eapply functional_extensionality.
      intros; induction x; simpl; eauto.
    }
  * simpl.
    induction t1; repeat econstructor.
    - remember (Delta x) as b.
      induction b; symmetry in Heqb.
      + econstructor.
        { apply IHjt2. }
        { inverts H. repeat econstructor. simpl; rewrite Heqb, H3; simpl. eauto. } 
      + econstructor.
        { simpl in IHjt1.
          specialize IHjt1 with Delta.
          rewrite Heqb in IHjt1.
          apply IHjt1.
        }
        { econstructor. simpl in IHjt2.
          replace (MT.TyFun (trans_ty_aux T) (MT.TyOption (trans_ty_aux U))
          .: (fun x0 : var => trans_ty (Delta x0) (Gamma x0))) with 
            (fun x => trans_ty ((true .: Delta) x) (((DT.TyFun T U) .: Gamma) x))
          .
          { inverts H. specialize IHjt2 with (true .: Delta). simpl in IHjt2. admit. }
          { unfold ".:".
            eapply functional_extensionality.
            induction x0; simpl; eauto.
          }
          repeat econstructor. }
    - admit.
    - admit.
  * simpl.
    rename H0 into IHjts.
    econstructor.
    - admit.
    - simpl in *. eapply jt_te_thunk. eapply IHjt1.
    - simpl in *. eapply jt_te_thunk. eapply IHjt2.
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

  

  


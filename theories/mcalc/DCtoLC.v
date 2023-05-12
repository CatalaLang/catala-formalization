
Require Import DCSyntax.
Require Import LCSyntax.
Require Import DCFreeVars.

Require Import STLCDefinition.

Require Import MyTactics.


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


Definition trans_ctx := var -> bool.

(* Defintion mmap t f := MBind arg (f (D.Var 0)) *)

Fixpoint trans (Delta: trans_ctx) t { struct t } :=
  match t with
  | D.Var x =>
    if Delta x
    then monad_return (L.EVar x)
    else L.EVar x
  
  | D.Lam t =>
    monad_return (L.ELam (trans (true .: Delta) t))
  
  | D.App (D.Lam body) arg => (* let arg in body *)
    monad_bind (trans Delta arg) (trans (true .: Delta) body)
  (* | D.App () =>
    MBind (trans Delta arg) (monad_return (L.EOp op) ) *)
  | D.App (D.Var f) arg =>
    if Delta f
    then (monad_bind (trans Delta arg)
      (L.EApp (lift 1 (L.EVar f)) (L.EVar 0))
    )
    else (monad_bind (L.EVar f)
      (monad_bind (lift 1 (trans Delta arg))
        (L.EApp (lift 1 (L.EVar 0)) (L.EVar 0))
      ) 
    )
  | D.Default es ej ec =>
    monad_handle
      (List.map (trans Delta) es)
      (trans Delta ej)
      (trans Delta ec)
  | D.Const b =>
    monad_return (L.OConst b)
  | Empty =>
    monad_empty
  | Conflict => L.EPanic EConflict

  | D.BinOp op t1 t2 => L.EPanic L.ECompile
  | D.App _ _ => L.EPanic L.ECompile
  end.

(** translation correction *)

Require Import STDCDefinition.
Module DT := STDCDefinition.
Module LT := STLCDefinition.

Require Import Program.


Fixpoint trans_ty_aux ty := 
  match ty with
  | DT.TyVar x => LT.TyVar x 
  | DT.TyFun A B => LT.TyFun (trans_ty_aux A) (LT.TyOption (trans_ty_aux B))
  | DT.TyBool => LT.TyBool
  end.

Definition trans_ty (b: bool) ty := if b then trans_ty_aux ty else LT.TyOption (trans_ty_aux ty).
(* 
Lemma jt_te_thunk Gamma t tau:
  LT.jt Gamma t tau ->
  forall u,
  LT.jt Gamma (thunk t) (LT.TyFun u tau).
Proof.
  unfold thunk.
  intros.
  econstructor.
  now eapply jt_te_renaming_0.
Qed. *)


Lemma trans_correct_type Gamma t1 tau:
  jt Gamma t1 tau ->
  forall Delta,
  LT.jt (fun x => trans_ty (Delta x) (Gamma x)) (trans Delta t1) (trans_ty false tau).
Proof.
  induction 1 using jt_ind'; intros; try solve [simpl; eauto with jt].
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
  * simpl trans.
    induction t1; try solve [repeat econstructor].
    (* We consider all the cases for App. *)
    - (* First case : App (Var x) _. Either Delta x is true or false. *)
      remember (Delta x) as b.
      induction b; symmetry in Heqb.
      + (* If Delta x is true, *)
        eapply JTmonad_bind.
        { apply IHjt2. }
        { inverts H. repeat econstructor. asimpl.
          rewrite Heqb, H3. now asimpl. } 
      + (* If Delta x is false *)
        eapply JTmonad_bind.
        { simpl in IHjt1.
          specialize IHjt1 with Delta.
          rewrite Heqb in IHjt1.
          apply IHjt1.
        }
        { eapply JTmonad_bind; repeat econstructor.
          { simpl in IHjt2.
            eapply jt_te_renaming_0.
            eapply IHjt2. }
        }
    - (* Second case: [App (Lam body) arg] represents an [let arg in body] statement. *)
      eapply JTmonad_bind.
      { eapply IHjt2. }
      { 
        inverts H.
        specialize IHjt1 with ((* true .: *) Delta).
        simpl in IHjt1.
        inverts IHjt1.
        inverts H3.
        eapply H5.
      }
  * simpl. 
    rename H0 into IHjts.
    eapply JTmonad_handle.
    - induction ts. { econstructor. }
      simpl.
      inverts_Forall.
      econstructor; eauto.
    - simpl in *. eapply IHjt1.
    - simpl in *. eapply IHjt2.
Qed.

(* TODO : look at the trans definition when App does not have multiple arguments. *)

Require Import FunInd.


(* does not work because of List.map in translate. *)
Fail Generate graph for trans.

Fail Functional Scheme trans_ind := Induction for trans Sort Prop.
Fail Check trans_ind.


Lemma trans_te_renaming:
  forall Delta t u,
  trans Delta t = u ->
  forall Delta' xi,
  Delta = xi >>> Delta' ->
  trans Delta' t.[ren xi] = u.[ren xi].
Proof.
  intros Delta t u Hu.
  subst.
  gen Delta.
  induction t using term_ind'; intros; subst; try solve [asimpl; unfold_monad;
  eauto with autosubst].
  * (* Case [Var x]. We just need to look at [Delta x]. *)
    simpl; unfold_monad.
    case (Delta' (xi x)); eauto with autosubst.
  * (* Case [Lam _] nothing particular. *)
    asimpl; unfold_monad; repeat f_equal; eauto with autosubst.
  * (* Case [App _ _] *)
    
    remember t1; induction t1; subst; try eauto with autosubst.
    - (* Case [App (Var f) _ ]*)
      intros; subst.
      simpl trans.
      case (Delta' (xi x)).
      + unfold_monad.
        rewrite
          subst_match,
          subst_variant_none,
          subst_app,
          subst_var.
        repeat f_equal.
        eapply IHt2; reflexivity.
      + unfold_monad. 
        repeat rewrite
          subst_match,
          subst_match,
          subst_app,
          subst_variant_none,
          subst_var.
        do 2 f_equal.
        erewrite IHt2; try reflexivity.
        rewrite lift_up; tc.
    - (* Case [App (Lam _) _]*)
      intros; clear IHt0.
      Opaque trans. asimpl. Transparent trans.
      simpl trans.
      unfold_monad.
      asimpl.
      unfold monad_return in IHt1.
      f_equal.
      + eapply IHt2; eauto.
      + simpl trans in IHt1.
        assert (trans Delta' (Lam t0).[ren xi] = (trans (xi >>> Delta') (Lam t0)).[ren xi]).
        { unfold monad_return in IHt1. forwards: IHt1 (xi >>> Delta') Delta' xi; eauto. }
        injections. eauto with autosubst.
  * asimpl.
    rewrite subst_monad_handle.
    f_equal; eauto.
    { induction ts; asimpl; inverts_Forall; repeat f_equal; eauto. }
Qed.


Lemma trans_te_renaming_0:
  forall Gamma t T u,
  trans Gamma t = u ->
  trans (T .: Gamma) (lift 1 t) = (lift 1 u).
Proof.
  intros.
  eapply trans_te_renaming; eauto.
Qed.

Require Import DCReduction.

Require Import MySequences.
Require Import MyRelations.

Definition transs Delta sigma1 sigma2 :=
  forall x : var,
  trans Delta (sigma1 x) = (sigma2 x).

Lemma trans_ids:
  forall Delta,
  transs Delta ids (fun x => (if Delta x then monad_return (L.EVar x) else L.EVar x)).
Proof.
  unfold transs.
  induction x; eauto.
Qed.

Lemma trans_cons:
  forall Delta t u sigma1 sigma2,
  trans Delta t = u ->
  transs Delta sigma1 sigma2 ->
  transs Delta (t .: sigma1) (u .: sigma2).
Proof.
  intros. intros [|x]; asimpl; eauto.
Qed.


Lemma trans_up_true:
  forall Delta sigma1 sigma2,
  transs Delta sigma1 sigma2 ->
  transs (Delta) (ids 0 .: sigma1) ((if Delta 0 then monad_return (ids 0) else (ids 0)) .: sigma2).
Proof.
  intros. eapply trans_cons; eauto.
Qed.


Lemma trans_te_substitution:
  forall Delta t u,
  trans Delta t = u ->
  forall sigma1 sigma2,
  transs Delta sigma1 sigma2 ->
  trans Delta t.[sigma1] = u.[sigma2].
Proof.
  induction 1; intros; subst; asimpl; eauto using js_up with jt.
  * 
  intros.
  induction t; try solve [
    simpl trans in *;
    subst;
    unfold_monad;
    asimpl; 
    eauto
  ].
  * simpl trans in *.
    subst.
    case (Delta x); asimpl.



Lemma trans_te_substitution_0:
  forall Delta t1 t2 u1 u2,
  trans Delta t1 = u1 ->
  trans Delta t2 = u2 ->
  trans Delta t1.[t2/] = u1.[u2/].
Proof.
  


Require Import LCReduction.

Definition dcbv := DCReduction.cbv.
Definition lcbv := LCReduction.cbv.

Lemma trans_correct t1 t2:
  dcbv t1 t2 ->
  forall Delta,
  exists target,
    star lcbv (trans Delta t1) target /\
    star lcbv (trans Delta t2) target.
Proof.
  induction 1; tryfalse; intros; unpack.
  * subst; eexists; split.
    2:{ eapply star_refl. }
    simpl.



Admitted.


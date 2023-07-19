
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


Definition trans_ctx := var -> bool.

(* Defintion mmap t f := MBind arg (f (D.Var 0)) *)

(* begin snippet dc2lc_trans *)
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
  (* | D.App f arg =>
    monad_bind (trans Delta f) (monad_bind (lift 1 (trans Delta arg)) (L.EApp (lift 1 (L.EVar 0)) (L.EVar 0))) *)
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
  | D.App _ _ => L.EPanic ECompile
  (* | D.BinOp op t1 t2 => L.EPanic L.ECompile*)
  end.
(* end snippet dc2lc_trans *)


(** translation correction *)

Require Import STDCDefinition.
Module DT := STDCDefinition.
Module LT := STLCDefinition.

Module DVR := DCValuesRes.

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
    induction t1; try solve [repeat econstructor|
    (* general case *)
    repeat eapply JTmonad_bind;
    solve
      [ eapply IHjt1
      | eapply jt_te_renaming_0;eapply IHjt2
      | repeat econstructor ]
    ].
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


(******************************************************************************)


(* The goal of this part is to prove a substitution lemma for trans *)

Hypothesis iota_equality: forall t1 t2,
  EMatch (EVariantSome t1) EVariantNone t2 = t2.[t1/].

Hypothesis eta_equality: forall t1 t2,
  EApp (ELam t1) t2 = t1.[t2/].

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
  induction t using term_ind'; intros; subst;
  try solve [asimpl; unfold_monad;
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

Theorem trans_te_substitution:
  forall t Delta,
  forall sigma1 sigma2,
  (exists Gamma T, jt Gamma t T) ->
  (exists Gamma T, jt Gamma t.[sigma1] T) ->
  (forall x, is_value_res (sigma1 x)) ->
  (forall x, is_nerror (sigma1 x)) ->
  (forall x, Delta x = true -> (trans Delta (sigma1 x)) = EVariantSome (sigma2 x)) ->
  (forall x, Delta x = false -> (trans Delta (sigma1 x)) = sigma2 x) ->
  trans Delta t.[sigma1] = (trans Delta t).[sigma2].
Proof.
  induction t using term_ind'; try eauto.
  3: {
    introv [Gamma [T Hty]] [Gamma' [T' Hty']] Hval Hnerr HsigmaT HsigmaF.
    induction t1; try solve [asimpl; eauto].
    - (* Case [App (Var x) _] *) 
      assert (Hvalx: is_value_res (sigma1 x)) by eapply Hval.
      assert (Hnerrx: is_nerror (sigma1 x)) by eapply Hnerr.
      asimpl; remember (sigma1 x); induction t; try clear IHt; tryfalse.
      2:{ (* Then x has type bool, and this is not possible since it must have type TyArrow.*)
          false.
          inverts Hty'.
          rewrite <- Heqt in H2.
          inverts H2.
        }
      1:{
        asimpl.
        remember (Delta x).
        induction b; asimpl; unfold_monad.
        - (* First case: (Delta x) is true. Hence, x is pure.
             In this case, *)
          erewrite IHt2; eauto.
            2:{ inverts Hty; eauto. }
            2:{ inverts Hty'; eauto. }
          
          replace (sigma2 x) with (L.ELam (trans (true .: Delta) t)).
          { asimpl; repeat f_equal.
            rewrite eta_equality; asimpl; eauto.
          }
          {
            symmetry in Heqb.
            assert (Hsigma: trans Delta (sigma1 x) = EVariantSome (sigma2 x)) by eauto.
            rewrite <- Heqt in Hsigma. simpl in Hsigma. unfold monad_return in Hsigma.
            injections; eauto.
          }
        - erewrite IHt2; eauto.
          2:{ inverts Hty; eauto. }
          2:{ inverts Hty'; eauto. }

          erewrite <- HsigmaF; eauto. rewrite <- Heqt. asimpl; unfold_monad.
          rewrite iota_equality; asimpl.
          rewrite eta_equality; asimpl.
          repeat f_equal.
      }
    - (* Case [App (Lam t) _ ] *)
      asimpl; unfold_monad.
      
      repeat f_equal.
      * (* by IHt2, [trans Delta t2.[sigma1] = (trans Delta t2).[sigma2]] *)
        erewrite IHt2; eauto.
        { inverts Hty. inverts Hty'. exists Gamma T0. eauto. }
        { inverts Hty. inverts Hty'. exists Gamma' T1. eauto. }
      * (* by IHt1, [trans Delta (Lam t).[sigma1] = (trans Delta (Lam t)).[sigma2]]. *)
        assert (trans Delta (Lam t).[sigma1] = (trans Delta (Lam t)).[sigma2]).
        { eapply IHt1; eauto; inverts Hty; inverts Hty'.
          { exists Gamma (TyFun T0 T); eauto. }
          { exists Gamma' (TyFun T1 T'); eauto. }
        }
        asimpl in H.
        injections; eauto.
  }
  3: {
    introv [Gamma [T Hty]] [Gamma' [T' Hty']] Hval Hnerr HsigmaT HsigmaF.
    assert (Hts: List.map (trans Delta) ts..[sigma1] = (List.map (trans Delta) ts)..[sigma2]).
    { induction ts; asimpl; repeat f_equal.
      - inverts Hty; inverts Hty'. inverts_Forall.
        eapply H4; eauto.
      - inverts Hty; inverts Hty'. inverts_Forall.
        eapply IHts; eauto using jt. 
    }
    assert (Ht1: trans Delta t1.[sigma1] = (trans Delta t1).[sigma2]).
    { 
      eapply IHt1; eauto.
      inverts Hty; exists Gamma TyBool; eauto.
      inverts Hty'; exists Gamma' TyBool; eauto.
    }
    assert (Ht2: trans Delta t2.[sigma1] = (trans Delta t2).[sigma2]).
    { eapply IHt2; eauto.
      inverts Hty; exists Gamma T; eauto.
      inverts Hty'; exists Gamma' T'; eauto.
    }

    asimpl.
    rewrite Hts, Ht1, Ht2.
    rewrite subst_monad_handle.
    eauto.
  }
  2: {
    (* Case [Lam _] *)
    introv [Gamma [T Hty]] [Gamma' [T' Hty']] Hval Hnerr HsigmaT HsigmaF.
    asimpl.
    unfold_monad. repeat fequal.
    inverts Hty; inverts Hty'.
    eapply IHt; eauto.
    - match goal with [ |- forall x, is_value_res (up sigma1 x) ] => idtac end.

      
      admit "[forall x, is_value_res (up sigma1 x)] is false since [up sigma1 0] is [ids 0] hence a variable.".
    - clear -Hnerr.
      induction x; asimpl.
      { unfold ids, D.Ids_term; eauto. }
      { specialize Hnerr with x.
        remember (sigma1 x) as t.
        induction t; asimpl; eauto.
      }
    - clear -HsigmaT.
      induction x; intros.
      { unfold ids, D.Ids_term; asimpl; eauto. }
      { asimpl.
        replace (EVariantSome (lift 1 (sigma2 x))) with (lift 1 (EVariantSome (sigma2 x))); eauto using trans_te_renaming_0. }
    - clear -HsigmaF.
      induction x; asimpl; intros.
      { tryfalse. }
      { eapply trans_te_renaming_0; eauto. }
  }
  { (* case [Var _] *)
    introv [Gamma [T Hty]] [Gamma' [T' Hty']] Hval Hnerr HsigmaT HsigmaF.
    asimpl.
    remember (Delta x) as b.
    specialize HsigmaT with x.
    specialize HsigmaF with x.
    induction b; eauto.
  }
Admitted. 

Lemma trans_te_substitution_0:
  forall Delta t1 t2 u1 u2,
  trans Delta t1 = u1 ->
  trans Delta t2 = u2 ->
  trans Delta t1.[t2/] = u1.[u2/].
  (* this is not true. *)
Proof.
  admit.
Abort.


Require Import LCReduction.

Definition dcbv := DCReduction.cbv.
Definition lcbv := LCReduction.cbv.

Inductive no_compile_error: term -> Prop :=
.


Declare Scope latex_scope.

Notation "'\left\llbracket' t '\right\rrbracket^{' Delta '}'" := (trans Delta t) : latex_scope.

Notation "'\mathtt{true}'" := (true): latex_scope.
Notation "'\mathtt{false}'" := (false): latex_scope.
Notation "t '.\left[' sigma '\right]'" := (t.[sigma]) (at level 100, no associativity): latex_scope.

Notation "a '\to' b" := (lcbv a b) (at level 100, no associativity): latex_scope.
Notation "a '\to^*' b" := (star lcbv a b) (at level 100, no associativity): latex_scope.

Notation "'\synreturn' t" := (monad_return t) (at level 100): latex_scope.

Open Scope latex_scope.

Print Scopes.


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

Lemma trans_te_substitution_0_true (t v: DCSyntax.term) v' Delta:

  trans (fun i => true) v = EVariantSome v' ->
  (trans (true .: Delta) t).[v'/] = trans Delta t.[v/].
  (* This is an instance of the more general substitution lemma *)
Proof.
  intros.
  asimpl.
  rewrite trans_te_substitution.
Admitted.

Lemma trans_te_substitution_0_false (t v: DCSyntax.term) Delta:
  (trans (false .: Delta) t).[(trans (fun i => true) v)/] = trans Delta (t.[v/]).
  (* This is an instance of the more general *)
Proof.
  intros.
  asimpl.
Admitted.




Lemma trans_correct_bind_const Delta b t:
  (monad_bind (monad_return (L.OConst b)) (trans (true .: Delta) t)) = (trans Delta t).[EOp (L.OConst b)/].
Proof.
  unfold monad_bind, monad_return.
  
Admitted.



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


Lemma trans_correct t1 t2 Gamma T:
  jt Gamma t1 T ->
  forall Delta,
  no_compile_error (trans Delta t1) ->
  dcbv t1 t2 ->

  exists target,
    star lcbv (trans Delta t1) target /\
    star lcbv (trans Delta t2) target.
Proof.
  intros Hjt Delta Hcompil Hdcbv.
  revert Hdcbv Gamma T Hjt Delta Hcompil.

  induction 1; tryfalse; intros; unpack.
  * subst; eexists; split.
    2:{ eapply star_refl. }
    simpl.
    induction v; tryfalse.
    - admit "Variable should not be values. Hence this case should not arise.".
    - admit "More complicated version of the next case.".
    - asimpl.
      eapply star_one.
      unfold monad_bind, monad_return, monad_empty.
      eapply RedEMatchSomeV.
      + trivial.
      + reflexivity.
      + unfold LCValues.is_value, LCValues.if_value; simpl.
        admit "Error: OConst should be a value in LCValues.".
      + eapply trans_te_substitution_0_true.
        asimpl; eauto. 
  * inv jt.
    assert (no_compile_error (trans Delta t1)). { admit. }

    destruct (IHHdcbv _ _ H5 _ H2) as [target [Htarget1 Htarget2]].
    exists (EApp target (trans Delta u)).
    split; eapply star_one; asimpl.
    all: admit.
  * destruct (IHHdcbv Delta) as [target [Htarget1 Htarget2]].
    exists (EApp (trans Delta v) target).
    induction v; simpl in H0; tryfalse.
    (* v is a value. *)
Admitted.


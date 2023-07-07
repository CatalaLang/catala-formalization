
Require Import DCSyntax.
Require Import LCSyntax.
Require Import DCFreeVars.
Require Import DCValuesRes.

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
  | D.App f arg =>
    monad_bind (trans Delta f) (monad_bind (lift 1 (trans Delta arg)) (L.EApp (lift 1 (L.EVar 0)) (L.EVar 0)))
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

Theorem trans_te_substitution:
  forall Delta t,
  forall sigma1 sigma2,
  (forall x,  trans Delta (sigma1 x) = sigma2 x) ->
  trans Delta t.[sigma1] = (trans Delta t).[sigma2].
Proof.
  induction t using term_ind'; intros; asimpl.
  3: { (* Here, if t1 is a variable, then the right hand side reduces to [if Delta f then ...] while the left hand side might reduce to something like an application. In this case, the translation would be a an compilation error. 
  
  Hence this theorem does not hold in general. But do we need it in all generality?
  
  This theorem is used in the simulation diagram in the case of beta-reduction. And since we are in call by value, substitution must happend on values only. Hence, for all x, [sigma1 x] is a value. This reduces greatly the difficulties.
  *)
  admit.
  }
Abort.

Theorem trans_te_substitution:
  forall t Delta,
  forall sigma1 sigma2,
  (exists Gamma T, jt Gamma t T) ->
  (forall x, is_value_res (sigma1 x)) ->
  (forall x, trans Delta (sigma1 x) = sigma2 x) ->
  trans Delta t.[sigma1] = (trans Delta t).[sigma2].
Proof.
  induction t using term_ind'.
  3: {
    introv [Gamma [T Hty]] Hval Hsigma.
    asimpl.
    induction t1; asimpl; eauto.
    - specialize Hval with x; remember (sigma1 x); induction t; tryfalse.
      4:{ }

    - unfold_monad. (* this is basicly the same thing as IHt1 and IHt2. But requires a little more work, since IHt1 is specialized on Lambda *)
      erewrite IHt2; eauto. repeat f_equal.
      admit.
  }

(* The proof is as follows: by induction on t, we take a look into each of the cases. *)


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

Require Import DCReduction.

Require Import MySequences.
Require Import MyRelations.

(* This propertie des not seems to hold correctly. Indeed, *)

Definition transs Delta sigma1 sigma2 :=
  forall x : var,
  trans Delta (sigma1 x) = sigma2 x
  (* if Delta x then monad_return (sigma2 x) else (sigma2 x) *)
  .


Lemma trans_ids:
  forall Delta,
  transs Delta ids (fun x => trans Delta (ids x)).
Proof.
  unfold transs.
  induction x; eauto; asimpl.
Qed.

Lemma trans_cons:
  forall Delta t u sigma1 sigma2,
  trans Delta t = u ->
  transs Delta sigma1 sigma2 ->
  transs Delta (t .: sigma1) (u .: sigma2).
Proof.
  intros.
  intros [|x]; asimpl; eauto.
Qed.

(* this lemma does not hold. *)
Lemma trans_up:
  forall Delta sigma1 sigma2,
  transs Delta sigma1 sigma2 ->
  transs Delta (up sigma1) (up sigma2).
Proof.
  intros; eapply trans_cons; eauto.
  2: {
    unfold transs; intros; asimpl; eapply trans_te_renaming.
Abort.


(* First the propertie on transs should satisfy this : *)

Lemma rewrite_subst_ite:
  forall (b: bool) sigma (x y: L.term),
    (if b then x else y).[sigma] = (if b then x.[sigma] else y.[sigma]).
Proof.
  induction b; intros; asimpl; eauto.
Qed.

Lemma trans_te_subst_var:
  forall Delta sigma1 sigma2, 
  transs Delta sigma1 sigma2 ->
  forall x, 
  trans Delta (sigma1 x) = (if Delta x then monad_return (L.EVar x) else L.EVar x).[sigma2].
Proof.
  unfold monad_return.
  (* I dont really understand this one as it seems. Maybe it is that if we replace x with something else, then it must have a certain shape. For example, let's assume for now that x is a value. *)


  admit.
Abort.



(* 
let translate_var_to_exp (s: D.var_to_exp) : Tot L.var_to_exp =
  fun x -> translate_exp (s x)

let rec substitution_correctness (s: D.var_to_exp) (e: D.exp)
    : Lemma (ensures (
      translate_exp (D.subst s e) ==
        L.subst (translate_var_to_exp s) (translate_exp e)))
      (decreases %[D.is_var_size e; D.is_renaming_size s; 1; e])


    trans (e.[s]) = trans e.[trans_sigma s]
  = *)


(*
Definition transs Delta sigma1 sigma2 :=
  forall x : var,
  trans Delta (sigma1 x) =
    sigma2 x
    (* if Delta x then monad_return (sigma2 x) else (sigma2 x) *)
  .
*)

(* trans x.[x |-> Empty] = trans Empty = None
(trans x).[x |-> None] = x.[x -> None] = None

Delta x = true

trans x.[x |-> 3] = trans 3 = Some 3
(trans x).[x |-> Some 3] = x.[x -> Some 3] = Some 3 *)

Definition transs' Delta sigma1 sigma2 :=
  forall x : var,
  trans Delta (sigma1 x) =
  if Delta x then monad_return (sigma2 x) else (sigma2 x)
  .


Lemma trans'_cons:
  forall Delta t u sigma1 sigma2,
  trans Delta t = u ->
  transs' Delta sigma1 sigma2 ->
  transs' Delta (t .: sigma1) (u .: sigma2).
Proof.
Admitted.


Lemma trans_te_substitution:
  forall Delta t,
  forall sigma1 sigma2,
  transs' Delta sigma1 sigma2 ->
  trans Delta t.[sigma1] = (trans Delta t).[sigma2].
Proof.
  intros Delta t. gen Delta.
  induction t using term_ind'; intros; subst; asimpl; eauto using trans_cons with jt.
  * rewrite H.
    remember (Delta x) as b; induction b; subst; asimpl; eauto.
  * unfold_monad.
    asimpl.
    repeat fequal.
    eapply IHt; eauto.
    eapply trans'_cons.
    (* this does not hold since we don't have trans'_cons. *)
    admit. admit.
  * admit.
  * induction ts; asimpl; admit.
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

(* Open Scope latex_scope. *)

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

Lemma trans_te_substitution_0_true (t v: DCSyntax.term) Delta:
  (trans (true .: Delta) t).[(trans (fun i => true) v)/] = trans Delta (t.[v/]).
  (* This is an instance of the more general *)
Proof.
  intros.
  asimpl.
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

Tactic Notation "admit" := admit.
Tactic Notation "admit" string(x):= admit.


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
        admit "Error in the definition of what is a value in LCValues.".
      + symmetry. eapply trans_te_substitution.
        admit "This is an instance of trans_te_substitution_0 for both relations with the ite ".
  * inv jt.
    assert (no_compile_error (trans Delta t1)). { admit. }

    destruct (IHred ) as [target [Htarget1 Htarget2]].
    exists (EApp target (trans Delta u)).
    split; eapply star_one; asimpl.
    all: admit.
  * destruct (IHred Delta) as [target [Htarget1 Htarget2]].
    exists (EApp (trans Delta v) target).
    induction v; simpl in H0; tryfalse.
    (* v is a value. *)



Admitted.


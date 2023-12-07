Require Import String.
Require Import List.
Require Import syntax continuations_hole tactics sequences.
Import List.ListNotations.


(* The primary challenge was to accurately determine the correct typing judgment for the states of the abstract machine. I chose an approach that specifies the required typing judgment for each continuation. The tricky part is that, within the continuation stack, there can be environmental changes, especially during a function return. These changes must then be propagated throughout the remainder of the continuation stack. As a result, I decided on a method involving two typing environments: an input and an output. Furthermore, an input type (corresponding to the "hole") and an output type are needed. *)

Inductive type :=
| TBool
| TInteger
| TFun (T1 T2: type)
| TOption (T: type)
| TUnit
| TDefault (T: type)
.

Inductive inv_no_default: type -> Prop :=
  | invTBool : inv_no_default TBool
  | invTInteger : inv_no_default TInteger
  | invTUnit : inv_no_default TUnit
  | invTFun : forall T1 T2,
    inv_no_default T1 ->
    inv_no_default T2 ->
    inv_no_default (TFun T1 T2)
  | invTOption: forall T1,
    inv_no_default T1 ->
    inv_no_default (TOption T1)
.

Inductive inv_thunk_or_no_default : type -> Prop :=
  | inv_nodef: forall T, inv_no_default T -> inv_thunk_or_no_default T
  | inv_thunk: forall T1 T2,
    inv_no_default T1 ->
    inv_no_default T2 ->
    inv_thunk_or_no_default (TFun T1 (TDefault T2))
.

Inductive inv_ty: type -> Prop :=
  | inv_base: forall T, inv_thunk_or_no_default T -> inv_ty T
  | inv_root_default: forall T, inv_no_default T -> inv_ty (TDefault T)
.

Definition jt_op (o: op) :=
  match o with
  | Eq => (TInteger, TInteger, TBool)
  | Add => (TInteger, TInteger, TInteger)
  end.


(** [jt_term Delta Gamma t T] signifies that the term [t], within the local environment [Gamma] and the global environment [Delta], is of type [T]. *)
Inductive jt_term:
  (string -> option type) -> list type -> term -> type -> Prop :=
  | JTVar:
    forall Delta Gamma x T,
      Some T = List.nth_error Gamma x ->
      jt_term Delta Gamma (Var x) T
  (* | JTFreeVar:
    forall Delta Gamma x T,
      Some T = Delta x ->
      jt_term Delta Gamma (FreeVar x) T *)
  | JTApp:
    forall Delta Gamma t1 t2 T1 T2,
      jt_term Delta Gamma t1 (TFun T1 T2) ->
      jt_term Delta Gamma t2 T1 ->
      jt_term Delta Gamma (App t1 t2) T2
  | JTLam:
    forall Delta Gamma t T1 T2,
      jt_term Delta (T1::Gamma) t T2 ->
      jt_term Delta Gamma (Lam t) (TFun T1 T2)
  | JTDefault:
    forall Delta Gamma ts tj tc T,
      List.Forall (fun ti => jt_term Delta Gamma ti (TDefault T)) ts ->
      jt_term Delta Gamma tj TBool ->
      jt_term Delta Gamma tc (TDefault T) ->
      jt_term Delta Gamma (Default ts tj tc) (TDefault T)
  | JTDefaultPure:
    forall Delta Gamma t T,
      jt_term Delta Gamma t T ->
      jt_term Delta Gamma (DefaultPure t) (TDefault T)
  | JTErrorOnEmpty:
    forall Delta Gamma t T,
      jt_term Delta Gamma t (TDefault T) ->
      jt_term Delta Gamma (ErrorOnEmpty t) T
  | JTBinop:
    forall Delta Gamma t1 t2 op T1 T2 T3,
      (T1, T2, T3) = jt_op op ->
      jt_term Delta Gamma t1 T1 ->
      jt_term Delta Gamma t2 T2 ->
      jt_term Delta Gamma (Binop op t1 t2) T3
  | JTValue:
    forall Delta Gamma v T,
      jt_value Delta v T ->
      jt_term Delta Gamma (Value v) T
  | JTMatch:
    forall Delta Gamma u U t1 t2 T,
      jt_term Delta Gamma u (TOption U) ->
      jt_term Delta Gamma t1 T ->
      jt_term Delta (U :: Gamma) t2 T ->
      jt_term Delta Gamma (Match_ u t1 t2) T
  | JTESome:
    forall Delta Gamma t T,
      jt_term Delta Gamma t T ->
      jt_term Delta Gamma (ESome t) (TOption T)
  | JTENone:
    forall Delta Gamma T,
      jt_term Delta Gamma ENone (TOption T)
  | JTEEmpty:
    forall Delta Gamma T,
      jt_term Delta Gamma Empty (TDefault T)
  | JTEIf:
    forall Delta Gamma u ta tb T,
      jt_term Delta Gamma u TBool ->
      jt_term Delta Gamma ta T ->
      jt_term Delta Gamma tb T ->
      jt_term Delta Gamma (If u ta tb) T
with jt_value:
  (string -> option type) -> value -> type -> Prop :=
  | JTValueBool:
    forall Delta b,
      jt_value Delta (Bool b) TBool
  | JTValueInt:
    forall Delta i,
      jt_value Delta (Int i) TInteger
  | JTValueClosure:
    forall Delta tcl sigma_cl Gamma_cl T1 T2,
      List.Forall2 (jt_value Delta) sigma_cl Gamma_cl ->
      jt_term Delta (T1 :: Gamma_cl) tcl T2 ->
      jt_value Delta (Closure tcl sigma_cl) (TFun T1 T2)
  | JTValueVNone:
    forall Delta T,
      jt_value Delta VNone (TOption T)
  | JTValueVSome:
    forall Delta v T,
      jt_value Delta v T ->
      jt_value Delta (VSome v) (TOption T)
  | JTValueUnit:
    forall Delta,
      jt_value Delta VUnit TUnit
  | JTValueVPure:
    forall Delta v T,
      jt_value Delta v T ->
      jt_value Delta (VPure v) (TDefault T)
.


Inductive jt_result: (string -> option type) -> result -> type -> Prop := 
  | JTRValue:
    forall Delta v T,
    jt_value Delta v T ->
    jt_result Delta (RValue v) T
  | JTREmpty:
    forall Delta T,
    jt_result Delta REmpty (TDefault T)
  | JTRConflict:
    forall Delta T,
    jt_result Delta RConflict T
.

Inductive jt_cont: (string -> option type) -> list type -> list type -> cont -> type -> type -> Prop :=
  | JTCAppR:
    forall Delta Gamma t2 T1 T2,
      jt_term Delta Gamma t2 T1 ->
      jt_cont Delta Gamma Gamma (CAppR t2) (TFun T1 T2) T2
  | JTCClosure:
    forall Delta Gamma Gamma_cl sigma_cl T1 T2 tcl,
      jt_term Delta (T1 :: Gamma_cl) tcl T2 ->
      List.Forall2 (jt_value Delta) sigma_cl Gamma_cl ->
      jt_cont Delta Gamma Gamma (CClosure tcl sigma_cl) T1 T2
  | JTCBinopL:
    forall T1 T2 T3 op Delta v1 Gamma,
      (T1, T2, T3) = jt_op op ->
      jt_value Delta v1 T1 ->
      jt_cont Delta Gamma Gamma (CBinopL op v1) T2 T3
  | JTCBinopR:
    forall T1 T2 T3 op Delta t2 Gamma,
      (T1, T2, T3) = jt_op op ->
      jt_term Delta Gamma t2 T2 ->
      jt_cont Delta Gamma Gamma (CBinopR op t2) T1 T3
  | JTCDefault:
    forall Delta Gamma h o ts tj tc T,
      List.Forall (fun ti => jt_term Delta Gamma ti (TDefault T)) ts ->
      match o with None => True | Some o => jt_value Delta o T end ->
      jt_term Delta Gamma tj TBool ->
      jt_term Delta Gamma tc (TDefault T) ->
      jt_cont Delta Gamma Gamma (CDefault h o ts tj tc) (TDefault T) (TDefault T)
  | JTCDefaultBase:
    forall Delta Gamma tc T,
      jt_term Delta Gamma tc (TDefault T) ->
      jt_cont Delta Gamma Gamma (CDefaultBase tc) TBool (TDefault T)
  | JTCDefaultPure:
    forall Delta Gamma T,
      jt_cont Delta Gamma Gamma (CDefaultPure) T (TDefault T)
  | JTCErrorOnEmpty:
    forall Delta Gamma T,
      jt_cont Delta Gamma Gamma (CErrorOnEmpty) (TDefault T) T
  | JTCMatch:
    forall Delta Gamma t1 t2 U T,
      jt_term Delta Gamma t1 T ->
      jt_term Delta (U::Gamma) t2 T ->
      jt_cont Delta Gamma Gamma (CMatch t1 t2) (TOption U) T
  | JTCSome:
    forall Delta Gamma T,
      jt_cont Delta Gamma Gamma CSome T (TOption T)
  | JTCIf:
    forall Delta Gamma T ta tb,
      jt_term Delta Gamma ta T ->
      jt_term Delta Gamma tb T ->
      jt_cont Delta Gamma Gamma (CIf ta tb) (TBool) T

  | JTCReturn:
    forall Delta sigma Gamma1 Gamma2 T,
      (List.Forall2 (jt_value Delta) sigma Gamma2) ->
      jt_cont Delta Gamma1 Gamma2 (CReturn sigma) T T
.

Definition inv (Gamma: list type) (T: type) : Prop :=
  inv_ty (List.fold_left TFun Gamma T).

Inductive jt_conts: (string -> option type) -> list type -> list type -> list cont -> type -> type -> Prop :=
  | JTNil:
    forall Delta Gamma T,
      inv Gamma T ->
      jt_conts Delta Gamma Gamma nil T T
  | JTCons:
    forall Delta Gamma1 Gamma2 Gamma3 cont kappa T1 T2 T3,
      inv Gamma1 T1 ->
      jt_cont Delta Gamma1 Gamma2 cont T1 T2 ->
      jt_conts Delta Gamma2 Gamma3 kappa T2 T3 ->
      jt_conts Delta Gamma1 Gamma3 (cont :: kappa) T1 T3
.

Lemma JTConcat:
  forall Delta Gamma1 Gamma2 Gamma3 kappa1 kappa2 T1 T2 T3,
    jt_conts Delta Gamma1 Gamma2 kappa1 T1 T2 ->
    jt_conts Delta Gamma2 Gamma3 kappa2 T2 T3 ->
    jt_conts Delta Gamma1 Gamma3 (kappa1 ++ kappa2) T1 T3.
Proof.
  intros until kappa1.
  revert Delta Gamma1 Gamma2 Gamma3.
  induction kappa1.
  { simpl. intros. inversion H; subst. repeat econstructor; eauto. }
  { simpl. intros. inversion H; subst.
    eapply JTCons; eauto.
  }
Qed.

Lemma JTConcat_inversion:
  forall Delta Gamma1 Gamma3 kappa1 kappa2 T1 T3,
    jt_conts Delta Gamma1 Gamma3 (kappa1 ++ kappa2) T1 T3 ->
    exists Gamma2 T2,
      inv Gamma2 T2 /\
      jt_conts Delta Gamma1 Gamma2 kappa1 T1 T2 /\
      jt_conts Delta Gamma2 Gamma3 kappa2 T2 T3.
Proof.
  intros until kappa1.
  revert Delta Gamma1 Gamma3.
  induction kappa1.
  { simpl; intros.
    assert (inv Gamma1 T1). { inversion H; subst; eauto. }
    exists Gamma1, T1; repeat split; eauto; try solve [econstructor; eauto].
  }
  { simpl; intros.
    inversion H; subst.
    assert (inv Gamma2 T2). { inversion H9; subst; eauto. }
    destruct (IHkappa1 _ _ _ _ _ _ H9) as (Gamma4 & T4 & H24 & H43).
    unpack.
    exists Gamma4, T4; repeat split; eauto; econstructor; eauto.
  }
Qed.


Inductive jt_state: (string -> option type) -> list type -> state -> type -> Prop :=
  | JTmode_eval:
    forall Delta Gamma1 Gamma2 t T1 T2 kappa sigma,
      List.Forall2 (jt_value Delta) sigma Gamma1 ->
      jt_term Delta Gamma1 t T1 ->
      jt_conts Delta Gamma1 Gamma2 kappa T1 T2 ->
      jt_state Delta Gamma2 (mode_eval t kappa sigma) T2
  | JTmode_cont:
    forall Delta Gamma1 Gamma2 r T1 T2 kappa sigma,
      List.Forall2 (jt_value Delta) sigma Gamma1 ->
      jt_result Delta r T1 ->
      jt_conts Delta Gamma1 Gamma2 kappa T1 T2 ->
      jt_state Delta Gamma2 (mode_cont kappa sigma r) T2
.

(* This tactic is used to automaticaly break down judgements types in smaller 
   elements, without .
*)

Ltac inv_jt :=
  match goal with
  | [h: jt_term _ _ (Var _) _ |- _] =>
    inversion h; clear h; subst
  | [h: jt_term _ _ (FreeVar _) _ |- _] =>
    inversion h; clear h; subst
  | [h: jt_term _ _ (App _ _) _ |- _] =>
    inversion h; clear h; subst
  | [h: jt_term _ _ (Lam _) _ |- _] =>
    inversion h; clear h; subst
  | [h: jt_term _ _ (Default _ _ _) _ |- _] =>
    inversion h; clear h; subst
  | [h: jt_term _ _ (ErrorOnEmpty _) _ |- _ ] =>
    inversion h; clear h; subst
  | [h: jt_term _ _ (DefaultPure _) _ |- _ ] =>
    inversion h; clear h; subst
  | [h: jt_term _ _ (Value _) _ |- _] =>
    inversion h; clear h; subst
  | [h: jt_term _ _ Empty _ |- _] =>
    inversion h; clear h; subst
  | [h: jt_term _ _ (Binop _ _ _) _ |- _] =>
    inversion h; clear h; subst
  | [h: jt_term _ _ ENone _ |- _ ] =>
    inversion h; clear h; subst
  | [h: jt_term _ _ (ESome _) _ |- _ ] =>
    inversion h; clear h; subst
  | [h: jt_term _ _ (Match_ _ _ _) _ |- _ ] =>
    inversion h; clear h; subst
  | [h: jt_term _ _ (If _ _ _) _ |- _ ] =>
    inversion h; clear h; subst

  | [h: jt_value _ (Bool _) _ |- _] =>
    inversion h; clear h; subst
  | [h: jt_value _ (Int _) _ |- _] =>
    inversion h; clear h; subst
  | [h: jt_value _ (Closure _ _) _ |- _] =>
    inversion h; clear h; subst
  | [h: jt_value _ (VSome _) _ |- _] =>
    inversion h; clear h; subst
  | [h: jt_value _ VNone _ |- _] =>
    inversion h; clear h; subst
  | [h: jt_value _ VPure _ |- _] =>
    inversion h; clear h; subst
  | [h: jt_value _ _ TUnit |- _] =>
    inversion h; clear h; subst
  | [h: jt_value _ _ (TOption _) |- _] =>
    inversion h; clear h; subst
  | [h: jt_value _ _ (TFun _ _) |- _] =>
    inversion h; clear h; subst
  | [h: jt_value _ _ (TBool) |- _] =>
    inversion h; clear h; subst
  | [h: jt_value _ _ (TInteger) |- _] =>
    inversion h; clear h; subst
  | [h: jt_value _ _ (TUnit) |- _] =>
    inversion h; clear h; subst
  | [h: jt_value _ _ (TDefault _) |- _] =>
    inversion h; clear h; subst

  | [h: jt_cont _ _ _ (CAppR _) _ _ |- _] =>
    inversion h; clear h; subst
  | [h: jt_cont _ _ _ (CClosure _ _) _ _ |- _] =>
    inversion h; clear h; subst
  | [h: jt_cont _ _ _ (CBinopL _ _) _ _ |- _] =>
    inversion h; clear h; subst
  | [h: jt_cont _ _ _ (CBinopR _ _) _ _ |- _] =>
    inversion h; clear h; subst
  | [h: jt_cont _ _ _ (CDefault _ _ _ _ _) _ _ |- _] =>
    inversion h; clear h; subst
  | [h: jt_cont _ _ _ (CDefaultBase _) _ _ |- _] =>
    inversion h; clear h; subst
  | [h: jt_cont _ _ _ CErrorOnEmpty _ _ |- _] =>
    inversion h; clear h; subst
  | [h: jt_cont _ _ _ CDefaultPure _ _ |- _] =>
    inversion h; clear h; subst
  | [h: jt_cont _ _ _ (CReturn _) _ _ |- _] =>
    inversion h; clear h; subst
  | [h: jt_cont _ _ _ CSome _ _ |- _] =>
    inversion h; clear h; subst
  | [h: jt_cont _ _ _ (CMatch _ _) _ _ |- _] =>
    inversion h; clear h; subst
  | [h: jt_cont _ _ _ (CIf _ _) _ _ |- _] =>
    inversion h; clear h; subst

  | [h: jt_state _ _ (mode_eval _ _ _) _ |- _] =>
    inversion h; clear h; subst
  | [h: jt_state _ _ (mode_cont _ _ _) _ |- _] =>
    inversion h; clear h; subst

  | [h: jt_conts _ _ _ nil _ _ |- _] =>
    inversion h; clear h; subst
  | [h: jt_conts _ _ _ (cons _ _) _ _ |- _] =>
    inversion h; clear h; subst
  | [h: jt_conts _ _ _ (app _ _) _ _ |- _] =>
    let G := fresh "Gamma" in
    let T := fresh "T" in
    let H1 := fresh "H" in
    let H2 := fresh "H" in
    destruct (JTConcat_inversion _ _ _ _ _ _ _ h) as (G & T & H1 & H2); clear h; subst

  | [h: jt_result _ (RValue _) _ |- _] =>
    inversion h; clear h; subst
  | [h: jt_result _ REmpty _ |- _] =>
    inversion h; clear h; subst
  | [h: jt_result _ RConflict _ |- _] =>
    inversion h; clear h; subst

  | [h: List.Forall _ (cons _ _) |- _] =>
    inversion h; clear h; subst

  | [h: List.Forall2 _ (cons _ _) (cons _ _) |- _] =>
    inversion h; clear h; subst
  end.

Lemma jt_term_inv:
  forall Delta Gamma t T,
    jt_term Delta Gamma t T ->
    inv Gamma T.
Proof.
  induction 1.
  * admit "require strict nodefault on this one, or maybe not it depends on the thing we know about Gamma".
  * admit "ok".
  * admit "ok".
  * eauto.
  * admit "Require strict nodefault on this one".
  * admit "ok".
  * induction op; simpl in *; injections; subst.
    all: admit "ok".
  * admit "ok".
  * eauto.
  * admit "require strict nodefault on this one".
  * admit "require strict nodefault on this one".
  * admit "require strict nodefault on this one".
  * eauto.
Admitted.

Lemma jt_cont_inv:
  forall Delta Gamma1 Gamma2 cont T1 T2,
    jt_cont Delta Gamma1 Gamma2 cont T1 T2 ->
    inv Gamma1 T1.
Proof.
  induction 1.
  * admit "require information".
  * admit "require information".
  * admit "trivial".
  * admit "trivial".
  * admit "trivial".
  * admit "trivial".
  * admit "require information".
  * admit "require information".
  * admit "require information".
  * admit "require information".
  * admit "trivial".
  * admit "require information".
Admitted.


Lemma jt_conts_inv:
  forall Delta Gamma1 Gamma2 kappa T1 T2,
    jt_conts Delta Gamma1 Gamma2 kappa T1 T2 ->
    inv Gamma1 T1.
Proof.
  induction 1; eauto.
Qed.

Require Import tactics.
Import Learn.

Ltac learn_inv :=
  repeat match goal with
  | [h: jt_term _ _ _ _ |- _] => learn (jt_term_inv _ _ _ _ h)
  end.

Theorem preservation s1 s2:
  cred s1 s2 ->
  forall Delta Gamma T,
  jt_state Delta Gamma s1 T ->
  jt_state Delta Gamma s2 T.
Proof.
  induction 1; intros; try solve [
    repeat inv_jt; learn_inv;
    repeat match goal with
    | [|- inv _ _ ] => idtac
    | _ => econstructor
    end; eauto].
  * match goal with [_: context[Var _]|- context[RValue _] ] => idtac end.
    repeat inv_jt; repeat econstructor; eauto.
    eapply common.Forall2_nth_error_Some; eauto.
  * (* Returning an Conflict *)
    induction phi; try solve [repeat inv_jt; repeat econstructor; eauto].
    { now pose proof H sigma0. }
  * (* Operator case. We just need to consider all the cases. *)
    match goal with [_: context[CBinopL _ _]|- context[RValue _] ] => idtac end.
    repeat inv_jt.
    induction v1; induction v2; induction op; simpl in *; inj; tryfalse;
    eauto; repeat econstructor; eauto.
Qed.


Theorem progress s1:
  forall Delta Gamma T,
    jt_state Delta Gamma s1 T ->
    inv_ty T ->
    (exists s2, cred s1 s2) \/ (is_mode_cont s1 = true /\ stack s1 = nil).
Proof.
  induction s1 as [t kappa env|kappa env r]; intros.
  { repeat inv_jt.
    left.
    clear H0.
    induction t.
    all: repeat inv_jt.
    all: try solve [eexists; econstructor].
    { symmetry in H2.
      destruct (common.Forall2_nth_error_Some_right _ _ _ H6 _ _ H2).
      eexists; econstructor; eauto.
    }
  }
  { induction kappa as [|cont kappa].
    { right; simpl; eauto. }
    { left; induction cont; induction r.
      all: try match goal with [o: option value |- _ ] => induction o end.
      all: try match goal with [ts: list term |- _ ] => induction ts end.
      all: try match goal with [h: is_hole |- _ ] => induction h end.
      all: repeat inv_jt.
      all: learn_inv.
      all: try match goal with [b: bool |- _ ] => induction b end.
      all: try solve [repeat inv_jt; eexists; econstructor; repeat intro; inj].
      3: { induction op; simpl in *; inj; repeat inv_jt. }

      3: { induction op; simpl in *; inj; repeat inv_jt. }
      2: { induction op; simpl in *; inj; repeat inv_jt.
           all: eexists; econstructor; simpl; eauto.
      }
      { exfalso.
        clear -H.
        admit " this is obviously false".
      }
      { admit. }
      { admit. }
      { repeat inv_jt. }
    }
  }
Admitted.

Lemma well_typed_finish:
  forall Delta Gamma s1 T,
    (forall s2, ~ cred s1 s2) ->
    jt_state Delta Gamma s1 T ->
    is_mode_cont s1 = true /\ stack s1 = nil.
Proof.
  intros.
  destruct (progress s1 Delta Gamma T); eauto.
  { unpack; exfalso.
    eapply H; eauto.
  }
Qed.

Module correctness.
  Parameter measure: state -> nat.
  Parameter measure_decrease: forall s1 s2, cred s1 s2 -> measure s2 < measure s1.

  Theorem correctness_technical s1:
    forall Delta Gamma T,
      jt_state Delta Gamma s1 T ->
      exists s2,
        star cred s1 s2 /\
        is_mode_cont s2 = true /\
        stack s2 = nil /\
        jt_state Delta Gamma s2 T
      .
  Proof.
    induction s1 using (Wf_nat.induction_ltof1 _ measure).
    unfold Wf_nat.ltof in H.
    intros ? ? ? HT.
    destruct (progress _ _ _ _ HT).
    * unpack.
      edestruct (H x).
      { eapply measure_decrease; eauto. }
      { eapply preservation; eauto. }
      { unpack. eexists; eauto with sequences. }
    * unpack; eexists; repeat split; try eapply star_refl; eauto.
  Qed.


  Theorem correctness:
    forall Delta t T,
      jt_term Delta [] t T ->
      exists r sigma,
        star cred
          (mode_eval t [] [])
          (mode_cont [] sigma r)
  .
  Proof.
    intros.
    destruct correctness_technical with
      (mode_eval t [] [])
      Delta
      ([]: list type)
      T
    as (s2 & H1 & H2 & H3 & H4).
    { repeat econstructor; eauto. }
    induction s2; simpl in *; subst; inj.
    repeat eexists; eauto.
  Qed.

End correctness.

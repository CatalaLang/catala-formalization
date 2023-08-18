Require Import String.
Require Import List.

Require Import syntax continuations tactics.

Inductive type :=
| TBool
| TInteger
| TFun (T1 T2: type)
| TOption (T: type)
.

Definition jt_op (o: op) :=
  match o with
  | Eq => (TInteger, TInteger, TBool)
  | Add => (TInteger, TInteger, TInteger)
  end.

Inductive jt_term:
  (string -> option type) -> list type -> term -> type -> Prop :=
  | JTVar:
    forall Delta Gamma x T,
      Some T = List.nth_error Gamma x ->
      jt_term Delta Gamma (Var x) T
  | JTFreeVar:
    forall Delta Gamma x T,
      Some T = Delta x ->
      jt_term Delta Gamma (FreeVar x) T
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
      List.Forall (fun ti => jt_term Delta Gamma ti T) ts ->
      jt_term Delta Gamma tj TBool ->
      jt_term Delta Gamma tc T ->
      jt_term Delta Gamma (Default ts tj tc) T
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
.


Inductive jt_result: (string -> option type) -> result -> type -> Prop := 
  | JTRValue:
    forall Delta v T,
    jt_value Delta v T ->
    jt_result Delta (RValue v) T
  | JTREmpty:
    forall Delta T,
    jt_result Delta REmpty T
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
    forall Delta Gamma o ts tj tc T,
      List.Forall (fun ti => jt_term Delta Gamma ti T) ts ->
      match o with None => True | Some o => jt_value Delta o T end ->
      jt_term Delta Gamma tj TBool ->
      jt_term Delta Gamma tc T ->
      jt_cont Delta Gamma Gamma (CDefault o ts tj tc) T T
  | JTCDefaultBase:
    forall Delta Gamma tc T,
      jt_term Delta Gamma tc T->
      jt_cont Delta Gamma Gamma (CDefaultBase tc) TBool T
  | JTCMatch:
    forall Delta Gamma t1 t2 U T,
      jt_term Delta Gamma t1 T ->
      jt_term Delta (U::Gamma) t2 T ->
      jt_cont Delta Gamma Gamma (CMatch t1 t2) (TOption U) T
  | JTCSome:
    forall Delta Gamma T,
      jt_cont Delta Gamma Gamma CSome T (TOption T)

  | JTCReturn:
    forall Delta sigma Gamma1 Gamma2 T,
      (List.Forall2 (jt_value Delta) sigma Gamma2) ->
      jt_cont Delta Gamma1 Gamma2 (CReturn sigma) T T
.

Inductive jt_conts: (string -> option type) -> list type -> list type -> list cont -> type -> type -> Prop :=
  | JTNil:
    forall Delta Gamma T1,
      jt_conts Delta Gamma Gamma nil T1 T1
  | JTCons:
    forall Delta Gamma1 Gamma2 Gamma3 cont kappa T1 T2 T3,
      jt_cont Delta Gamma1 Gamma2 cont T1 T2 ->
      jt_conts Delta Gamma2 Gamma3 kappa T2 T3 ->
      jt_conts Delta Gamma1 Gamma3 (cont :: kappa) T1 T3
.


Inductive jt_state: (string -> option type) -> state -> type -> Prop :=
  | JTmode_eval:
    forall Delta Gamma1 Gamma2 t T1 T2 kappa sigma,
      List.Forall2 (jt_value Delta) sigma Gamma1 ->
      jt_term Delta Gamma1 t T1 ->
      jt_conts Delta Gamma1 Gamma2 kappa T1 T2 ->
      jt_state Delta (mode_eval t kappa sigma) T2
  | JTmode_cont:
    forall Delta Gamma1 Gamma2 r T1 T2 kappa sigma,
      List.Forall2 (jt_value Delta) sigma Gamma1 ->
      jt_result Delta r T1 ->
      jt_conts Delta Gamma1 Gamma2 kappa T1 T2 ->
      jt_state Delta (mode_cont kappa sigma r) T2
.

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
  | [h: jt_term _ _ (Value _) _ |- _] =>
    inversion h; clear h; subst
  | [h: jt_term _ _ (Binop _ _ _) _ |- _] =>
    inversion h; clear h; subst
  | [h: jt_term _ _ ENone _ |- _ ] =>
    inversion h; clear h; subst
  | [h: jt_term _ _ (ESome _) _ |- _ ] =>
    inversion h; clear h; subst
  | [h: jt_term _ _ (Match_ _ _ _) _ |- _ ] =>
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

  | [h: jt_cont _ _ _ (CAppR _) _ _ |- _] =>
    inversion h; clear h; subst
  | [h: jt_cont _ _ _ (CClosure _ _) _ _ |- _] =>
    inversion h; clear h; subst
  | [h: jt_cont _ _ _ (CBinopL _ _) _ _ |- _] =>
    inversion h; clear h; subst
  | [h: jt_cont _ _ _ (CBinopR _ _) _ _ |- _] =>
    inversion h; clear h; subst
  | [h: jt_cont _ _ _ (CDefault _ _ _ _) _ _ |- _] =>
    inversion h; clear h; subst
  | [h: jt_cont _ _ _ (CDefaultBase _) _ _ |- _] =>
    inversion h; clear h; subst
  | [h: jt_cont _ _ _ (CReturn _) _ _ |- _] =>
    inversion h; clear h; subst
  | [h: jt_cont _ _ _ CSome _ _ |- _] =>
    inversion h; clear h; subst
  | [h: jt_cont _ _ _ (CMatch _ _) _ _ |- _] =>
    inversion h; clear h; subst

  | [h: jt_state _ (mode_eval _ _ _) _ |- _] =>
    inversion h; clear h; subst
  | [h: jt_state _ (mode_cont _ _ _) _ |- _] =>
    inversion h; clear h; subst

  | [h: jt_conts _ _ _ nil _ _ |- _] =>
    inversion h; clear h; subst
  | [h: jt_conts _ _ _ (cons _ _) _ _ |- _] =>
    inversion h; clear h; subst

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

Lemma nth_error_Some_nonempty {A}:
  forall l x (v: A), nth_error l x = Some v -> l <> nil.
Proof.
  intros; induction l; induction x; eauto; repeat intro; tryfalse.
Qed.

Theorem preservation s1 s2:
  cred s1 s2 ->
  forall Delta T,
  jt_state Delta s1 T ->
  jt_state Delta s2 T.
Proof.
  induction 1; intros; try solve [repeat inv_jt; repeat econstructor; eauto].
  * match goal with [_: context[Var _]|- context[RValue _] ] => idtac end.
    repeat inv_jt; repeat econstructor; eauto.
    eapply common.Forall2_nth_error_Some; eauto.
  * (* Returning an REmpty: this cause a problem with CReturn. *)
    induction phi; try solve [repeat inv_jt; repeat econstructor; eauto].
    { now pose proof H0 sigma0.  }
  * (* Returning an Conflict *)
    induction phi; try solve [repeat inv_jt; repeat econstructor; eauto].
    { now pose proof H sigma0. }
  * (* Operator case. We just need to consider all the cases. *)
    match goal with [_: context[CBinopL _ _]|- context[RValue _] ] => idtac end.
    repeat inv_jt.
    induction v1; induction v2; induction op; simpl in *; inj; tryfalse;
    eauto; repeat econstructor; eauto.
Qed.


Require Import String.
Require Import List.
Require Import syntax continuations tactics sequences.
Import List.ListNotations.
Require Import Coq.ZArith.ZArith.


Require Import tactics.

Require Import Ltac2.Ltac2.
Set Default Proof Mode "Classic".



(* The primary challenge was to accurately determine the correct typing judgment for the states of the abstract machine. I chose an approach that specifies the required typing judgment for each continuation. The tricky part is that, within the continuation stack, there can be environmental changes, especially during a function return. These changes must then be propagated throughout the remainder of the continuation stack. As a result, I decided on a method involving two typing environments: an input and an output. Furthermore, an input type (corresponding to the "hole") and an output type are needed. *)

Inductive type :=
  | TBool
  | TInteger
  | TFun (T1 T2: type)
  | TOption (T: type)
  | TUnit
  | TDefault (T: type)
.

Inductive inv_base: type -> Prop :=
  | Inv1TBool : inv_base TBool
  | Inv1TInteger : inv_base TInteger
  | Inv1TUnit : inv_base TUnit
  | Inv1TFun : forall T1 T2,
    inv_no_immediate_default T1 ->
    inv_base T2 ->
    inv_base (TFun T1 T2)
  | Inv1TOption: forall T1,
    inv_no_immediate_default T1 ->
    inv_base (TOption T1)
  | Inv1TDefault: forall T1,
    inv_no_immediate_default T1 ->
    inv_base (TDefault T1)
with inv_no_immediate_default: type -> Prop :=
  | Inv2TBool : inv_no_immediate_default TBool
  | Inv2TInteger : inv_no_immediate_default TInteger
  | Inv2TUnit : inv_no_immediate_default TUnit
  | Inv2TFun : forall T1 T2,
    inv_no_immediate_default T1 ->
    inv_base T2 ->
    inv_no_immediate_default (TFun T1 T2)
  | Inv2TOption: forall T1,
    inv_base T1 ->
    inv_no_immediate_default (TOption T1)
.


Ltac2 sinv_inv () :=
  match! goal with
  | [ h : inv_base ?c |- _ ] => smart_inversion c h
  | [ h : inv_no_immediate_default ?c |- _ ] => smart_inversion c h
  end.

Ltac2 econs_inv () :=
  match! goal with
  | [ |- inv_base _ ] => econstructor
  | [ |- inv_no_immediate_default _ ] => econstructor
  end.


Ltac sinv_inv := ltac2: (sinv_inv ()).
Ltac econs_inv := ltac2: (econs_inv ()).

Module Invariant_Examples.
  (* For instance, the following types do follow the invariant:

  int; bool; int -> bool; <bool>; <int -> bool>; int -> <bool>; (int ->
  <bool>) -> bool

  While the following types does not follow the invariant:

  <<int>>;
  <int -> <bool>>;
  <bool> -> int;
  S_in {x: int -> <bool>} -> S {y: <bool>}
  *)

  Example positive_1: inv_base TBool. repeat econs_inv. Qed.
  Example positive_2: inv_base TInteger. repeat econs_inv. Qed.
  Example positive_3: inv_base (TFun TInteger TBool). repeat econs_inv. Qed.
  Example positive_4: inv_base (TDefault TBool). repeat econs_inv. Qed.
  Example positive_5: inv_base (TDefault (TFun TInteger TBool)). repeat econs_inv. Qed.
  Example positive_6: inv_base (TFun TInteger (TDefault TBool)). repeat econs_inv. Qed.
  Example positive_7: inv_base (TFun (TFun TInteger (TDefault TBool)) TBool). repeat econs_inv. Qed.
  Example positive_8: inv_base (TDefault (TFun TBool (TDefault TInteger))). repeat econs_inv. Qed.
  Example positive_9: inv_base (TFun (TFun TInteger (TDefault TBool)) (TDefault TBool)).
  repeat econs_inv. Qed.

  Example negative_1: not (inv_base (TDefault (TDefault TInteger))). intro. repeat sinv_inv. Qed.
  Example negative_2: not (inv_base (TFun (TDefault TBool) TInteger)). intro. repeat sinv_inv. Qed.

End Invariant_Examples.

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
      inv_base T ->
      jt_term Delta Gamma (Var x) T
  | JTApp:
    forall Delta Gamma t1 t2 T1 T2,
      jt_term Delta Gamma t1 (TFun T1 T2) ->
      jt_term Delta Gamma t2 T1 ->
      inv_base T2 ->
      jt_term Delta Gamma (App t1 t2) T2
  | JTLam:
    forall Delta Gamma t T1 T2,
      jt_term Delta (T1::Gamma) t T2 ->
      inv_base (TFun T1 T2) ->
      jt_term Delta Gamma (Lam t) (TFun T1 T2)
  | JTDefault:
    forall Delta Gamma ts tj tc T,
      List.Forall (fun ti => jt_term Delta Gamma ti (TDefault T)) ts ->
      jt_term Delta Gamma tj TBool ->
      jt_term Delta Gamma tc (TDefault T) ->
      inv_base (TDefault T) ->
      jt_term Delta Gamma (Default ts tj tc) (TDefault T)
  | JTDefaultPure:
    forall Delta Gamma t T,
      jt_term Delta Gamma t T ->
      inv_base (TDefault T) ->
      jt_term Delta Gamma (DefaultPure t) (TDefault T)
  | JTErrorOnEmpty:
    forall Delta Gamma t T,
      jt_term Delta Gamma t (TDefault T) ->
      inv_base T ->
      jt_term Delta Gamma (ErrorOnEmpty t) T
  | JTBinop:
    forall Delta Gamma t1 t2 op T1 T2 T3,
      (T1, T2, T3) = jt_op op ->
      jt_term Delta Gamma t1 T1 ->
      jt_term Delta Gamma t2 T2 ->
      inv_base T3 ->
      jt_term Delta Gamma (Binop op t1 t2) T3
  | JTValue:
    forall Delta Gamma v T,
      jt_value Delta v T ->
      inv_base T ->
      jt_term Delta Gamma (Value v) T
  | JTMatch:
    forall Delta Gamma u U t1 t2 T,
      jt_term Delta Gamma u (TOption U) ->
      jt_term Delta Gamma t1 T ->
      jt_term Delta (U :: Gamma) t2 T ->
      inv_base T ->
      jt_term Delta Gamma (Match_ u t1 t2) T
  | JTEFold:
    forall Delta Gamma A B f ts init,
      jt_term Delta Gamma f (TFun A (TFun B B)) ->
      inv_no_immediate_default A ->
      inv_no_immediate_default B ->
      List.Forall (fun ti => jt_term Delta Gamma ti A) ts ->
      jt_term Delta Gamma init B ->
      jt_term Delta Gamma (Fold f ts init) B
  | JTESome:
    forall Delta Gamma t T,
      jt_term Delta Gamma t T ->
      inv_base (TOption T) ->
      jt_term Delta Gamma (ESome t) (TOption T)
  | JTENone:
    forall Delta Gamma T,
      inv_base (TOption T) ->
      jt_term Delta Gamma ENone (TOption T)
  | JTEEmpty:
    forall Delta Gamma T,
      inv_base (TDefault T) ->
      jt_term Delta Gamma Empty (TDefault T)
  | JTEConflict:
    forall Delta Gamma T,
      inv_base T ->
      jt_term Delta Gamma Conflict T
  | JTEIf:
    forall Delta Gamma u ta tb T,
      jt_term Delta Gamma u TBool ->
      jt_term Delta Gamma ta T ->
      jt_term Delta Gamma tb T ->
      inv_base T ->
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
      jt_term Delta Gamma_cl (Lam tcl) (TFun T1 T2) ->
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

Inductive jt_cont: (string -> option type) -> type -> cont -> type -> Prop :=
  | JTCAppR:
    forall Delta sigma Gamma t2 T1 T2,
      jt_term Delta Gamma t2 T1 ->
      List.Forall2 (jt_value Delta) sigma Gamma ->
      jt_cont Delta (TFun T1 T2) (CAppR t2 sigma) T2
  | JTCClosure:
    forall Delta Gamma_cl sigma_cl T1 T2 tcl,
      jt_term Delta Gamma_cl (Lam tcl) (TFun T1 T2) ->
      List.Forall2 (jt_value Delta) sigma_cl Gamma_cl ->
      jt_cont Delta T1 (CClosure tcl sigma_cl) T2
  | JTCBinopL:
    forall T1 T2 T3 op Delta v1,
      (T1, T2, T3) = jt_op op ->
      jt_value Delta v1 T1 ->
      jt_cont Delta T2 (CBinopL op v1) T3
  | JTCBinopR:
    forall T1 T2 T3 op Delta t2 sigma Gamma,
      (T1, T2, T3) = jt_op op ->
      jt_term Delta Gamma t2 T2 ->
      List.Forall2 (jt_value Delta) sigma Gamma ->
      jt_cont Delta T1 (CBinopR op t2 sigma) T3
  | JTCDefault:
    forall Delta Gamma h o ts tj tc T sigma,
      List.Forall (fun ti => jt_term Delta Gamma ti (TDefault T)) ts ->
      match o with None => True | Some o => jt_value Delta o T end ->
      jt_term Delta Gamma tj TBool ->
      jt_term Delta Gamma tc (TDefault T) ->
      List.Forall2 (jt_value Delta) sigma Gamma ->
      jt_cont Delta (TDefault T) (CDefault h o ts tj tc sigma) (TDefault T)
  | JTCDefaultBase:
    forall Delta sigma Gamma tc T,
      jt_term Delta Gamma tc (TDefault T) ->
      List.Forall2 (jt_value Delta) sigma Gamma ->
      jt_cont Delta TBool (CDefaultBase tc sigma) (TDefault T)
  | JTCDefaultPure:
    forall Delta sigma Gamma T,
      inv_no_immediate_default T ->
      List.Forall2 (jt_value Delta) sigma Gamma ->
      jt_cont Delta T (CDefaultPure sigma) (TDefault T)
  | JTCErrorOnEmpty:
    forall Delta T sigma Gamma,
      List.Forall2 (jt_value Delta) sigma Gamma ->
      jt_cont Delta (TDefault T) (CErrorOnEmpty sigma) T
  | JTCMatch:
    forall Delta sigma Gamma t1 t2 U T,
      jt_term Delta Gamma t1 T ->
      jt_term Delta (U::Gamma) t2 T ->
      List.Forall2 (jt_value Delta) sigma Gamma ->
      jt_cont Delta (TOption U) (CMatch t1 t2 sigma) T
  | JTCFold:
    forall Delta sigma Gamma f ts A B,
      jt_term Delta Gamma f (TFun A (TFun B B)) ->
      inv_no_immediate_default A ->
      inv_no_immediate_default B ->
      List.Forall (fun ti => jt_term Delta Gamma ti A) ts ->
      List.Forall2 (jt_value Delta) sigma Gamma ->
      jt_cont Delta B (CFold f ts sigma) B
  | JTCSome:
    forall Delta T sigma Gamma,
      inv_no_immediate_default T ->
      List.Forall2 (jt_value Delta) sigma Gamma ->
      jt_cont Delta T (CSome sigma) (TOption T)
  | JTCIf:
    forall Delta sigma Gamma T ta tb,
      jt_term Delta Gamma ta T ->
      jt_term Delta Gamma tb T ->
      List.Forall2 (jt_value Delta) sigma Gamma ->
      jt_cont Delta TBool (CIf ta tb sigma) T
.

Inductive jt_conts: (string -> option type) -> type -> list cont -> type -> Prop :=
  | JTNil:
    forall Delta T,
      inv_base T ->
      jt_conts Delta T nil T
  | JTCons:
    forall Delta cont kappa T1 T2 T3,
      jt_cont Delta T1 cont T2 ->
      jt_conts Delta T2 kappa T3 ->
      jt_conts Delta T1 (cont :: kappa) T3
.

Inductive jt_state: (string -> option type) -> state -> type -> Prop :=
| JTmode_eval:
  forall Delta Gamma t T1 T2 kappa sigma,
    List.Forall2 (jt_value Delta) sigma Gamma ->
    jt_term Delta Gamma t T1 ->
    jt_conts Delta T1 kappa T2 ->
    jt_state Delta (mode_eval t kappa sigma) T2
| JTmode_cont:
  forall Delta r T1 T2 kappa,
    jt_result Delta r T1 ->
    jt_conts Delta T1 kappa T2 ->
    jt_state Delta (mode_cont kappa r) T2
. 

(*
Lemma jt_state_correct:
  "forall s, jt_state s -> jt_term (apply_state s)."
*)

Ltac2 sinv_jt () :=
  match! goal with
  | [ h: jt_term _ _ ?c _ |- _ ] => smart_inversion c h
  | [ h: jt_value _ ?c _ |- _ ] => smart_inversion c h
  | [ h: jt_value _ _ ?c |- _ ] => smart_inversion c h
  | [ h: jt_cont _ _ ?c _ |- _ ] => smart_inversion c h
  | [ h: jt_conts _ _ ?c _ |- _ ] => smart_inversion c h
  | [ h: jt_state _ ?c _ |- _ ] => smart_inversion c h
  | [ h: jt_result _ ?c _ |- _ ] => smart_inversion c h
  | [ h: List.Forall _ ?c |- _ ] => smart_inversion c h
  | [ h: List.Forall2 _ ?c _ |- _ ] => smart_inversion c h
  | [ h: List.Forall2 _ _ ?c |- _ ] => smart_inversion c h
  end.

Ltac2 econs_jt () :=
  match! goal with
  | [ |- jt_term _ _ _ _] => econstructor
  | [ |- jt_value _ _ _] => econstructor
  | [ |- jt_cont _ _ _ _ ] => econstructor
  | [ |- jt_conts _ _ _ _] => econstructor
  | [ |- jt_state _ _ _] => econstructor
  | [ |- jt_result _ _ _] => econstructor
  | [ |- List.Forall _ _] => econstructor
  | [ |- List.Forall2 _ _ _] => econstructor
  end.


Ltac sinv_jt := ltac2:(sinv_jt ()).
Ltac econs_jt := ltac2:(econs_jt ()).

Module Typing_Examples.
  (* (λ t. eoe < t () | true :- pure 5>) (λ x. Ø) *)
  Example positive_1: jt_term (fun _ => None) [] (App (Lam (ErrorOnEmpty (Default [App (Var 0) (Value (VUnit))] (Value (Bool true)) (DefaultPure (Value (Int 5)))))) (Lam Empty)) TInteger.
  all: repeat econs_jt.
  all: try solve [repeat econstructor].
  Qed.

  Notation "'Let' e1 'In' e2" := (App (Lam e2) e1) 
    ( at level 80
    , right associativity
    , format "'[hv' 'Let'  e1  'In'  '/' e2 ']'"
    ).

  (*
  let Toto : (unit → ⟨integer⟩) → integer =
    λ (Toto_in: unit → ⟨integer⟩) →
    let bar : unit → ⟨integer⟩ = Toto_in in
    let bar1 : integer =
      error_empty
        ⟨ bar () | true ⊢ ⟨error_empty ⟨ ⟨true ⊢ ⟨1⟩⟩ | false ⊢ ∅ ⟩⟩ ⟩
    in
    let foo : integer = error_empty ⟨ ⟨true ⊢ ⟨1212 + bar1⟩⟩ | false ⊢ ∅ ⟩ in
    foo
  *)
  Example positive_2: jt_term (fun _ => None) [] 
  (
    Lam (
      Let (Var 0) In
      Let ErrorOnEmpty
        (Default [(App (Var 0 (* bar_ *)) (Value (VUnit)))]
          (Value (Bool true))
          (DefaultPure
              (ErrorOnEmpty
                (Default
                    [(Default [] (Value (Bool true))
                        (DefaultPure (Value (Int 1))))]
                    (Value (Bool false)) (Empty))))) In
      Let ErrorOnEmpty
        (Default
          [(Default [] (Value (Bool true))
              (DefaultPure
                  (Binop Add (Value (Int 1212)) (Var 0
                    (* bar_ *)))))] (Value (Bool false))
          (Empty)) In
      (Var 0)))
  (TFun (TFun TUnit (TDefault TInteger)) TInteger).
  Proof.
    repeat econs_jt.
    (* Handling nth_error fetching *)
    all: simpl; eauto.
    all: try solve [repeat econs_inv | eapply invThunkedOrNoDefault; repeat econs_inv].
  Qed.


  (* (λ t. < t () | true :- pure 5>) (λ x. Ø) *)
  (* Example negative_1: ~ jt_term (fun _ => None) [] (App (Lam ((Default [App (Var 0) (Value (VUnit))] (Value (Bool true)) (DefaultPure (Value (Int 5)))))) (Lam Empty)) (TDefault TInteger).
    intro.
    repeat sinv_jt.
    clear -H10.
    repeat sinv_inv.
  Qed. *)
End Typing_Examples.

Lemma jt_term_inv:
  forall Delta Gamma t T,
    jt_term Delta Gamma t T ->
    inv_base T.
Proof.
  induction 1; eauto.
Qed.

Ltac learn_inv :=
  repeat match goal with
  | [h: jt_term _ _ _ _ |- _] => learn (jt_term_inv _ _ _ _ h)
  end.

Theorem preservation s1 s2:
  cred s1 s2 ->
  forall Delta T,
  jt_state Delta s1 T ->
  jt_state Delta s2 T.
Proof.
  intro Hred'.
  assert (Hred: cred s1 s2) by eauto.
  revert Hred'.
  induction 1; intros; try solve [
    repeat sinv_jt; learn_inv;
    repeat match goal with
    | [|- inv_base _ ] => idtac
    | _ => econstructor
    end; eauto].
  all: repeat sinv_jt.
  all: learn_inv.
  all: repeat sinv_inv.
  all: try solve [repeat (econstructor; eauto)].
  (* Operator handling *)
  { repeat (econstructor; eauto).
    eapply common.Forall2_nth_error_Some; eauto.
  }
  { induction op, v1, v2; simpl in *; inj; repeat (econstructor; eauto). }
Qed.

Theorem progress s1:
  forall Delta T,
    jt_state Delta s1 T ->
    (exists s2, cred s1 s2) \/ (is_mode_cont s1 = true /\ stack s1 = nil).
Proof.
  induction s1 as [t kappa env|kappa r]; intros.
  { repeat sinv_jt.
    left.
    induction t.
    all: repeat sinv_jt.
    all: try solve [eexists; econstructor].
    { symmetry in H0.
      destruct (common.Forall2_nth_error_Some_right _ _ _ H4 _ _ H0).
      eexists; econstructor; eauto.
    }
  }
  { induction kappa as [|cont kappa].
    { right; simpl; eauto. }
    { left; induction cont; induction r.
      all: repeat sinv_jt. (* need to infer information about values that are boolean *)
      all: try match goal with [o: option value |- _ ] => induction o end.
      all: try match goal with [ts: list term |- _ ] => induction ts end.
      all: try match goal with [h: is_hole |- _ ] => induction h end.
      all: try match goal with [op: op |- _ ] => induction op end.
      all: repeat match goal with [b: bool |- _ ] => induction b end.
      all: repeat (
        try learn_inv;
        try sinv_inv;
        try sinv_jt;
        try simpl in *; inj
      ).
      all: try solve [idtac
        |eexists; econstructor; repeat intro; inj
        |eexists; econstructor; simpl; eauto].
    }
  }
Qed.

Lemma well_typed_finish:
  forall Delta s1 T,
    (forall s2, ~ cred s1 s2) ->
    jt_state Delta s1 T ->
    is_mode_cont s1 = true /\ stack s1 = nil.
Proof.
  intros.
  destruct (progress s1 Delta T); eauto.
  { unpack; exfalso.
    eapply H; eauto.
  }
Qed.

Module correctness.
  Parameter measure: state -> nat.
  Parameter measure_decrease: forall s1 s2, cred s1 s2 -> measure s2 < measure s1.

  Theorem correctness_technical_aux s1:
    forall Delta T,
      jt_state Delta s1 T ->
      exists s2,
        star cred s1 s2 /\
        is_mode_cont s2 = true /\
        stack s2 = nil /\
        jt_state Delta s2 T
      .
  Proof.
    induction s1 using (Wf_nat.induction_ltof1 _ measure).
    unfold Wf_nat.ltof in H.
    intros ? ? HT.
    destruct (progress _ _ _ HT).
    { unpack.
      edestruct (H s2).
      { eapply measure_decrease; eauto. }
      { eapply preservation; eauto. }
      { unpack. eexists; eauto with sequences. }
    }
    { unpack; eexists; repeat split; try eapply star_refl; eauto. }
  Qed.

  Theorem correctness:
    forall Delta t T,
      inv_base T ->
      jt_term Delta [] t T ->
      exists r,
        star cred
          (mode_eval t [] [])
          (mode_cont [] r)
  .
  Proof.
    intros.
    destruct correctness_technical_aux with
      (mode_eval t [] [])
      Delta
      T
    as (s2 & H1 & H2 & H3 & H4).
    { repeat (econstructor; eauto). }
    induction s2; simpl in *; subst; inj.
    repeat eexists; eauto.
  Qed.

End correctness.

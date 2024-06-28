Require Import String.
Require Import List.
Require Import syntax continuations tactics sequences.
Require Import small_step.
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
  | TArray (T: type)
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
  | Inv1TArray: forall T1,
    inv_no_immediate_default T1 ->
    inv_base (TArray T1)
with inv_no_immediate_default: type -> Prop :=
  | Inv2TBool : inv_no_immediate_default TBool
  | Inv2TInteger : inv_no_immediate_default TInteger
  | Inv2TUnit : inv_no_immediate_default TUnit
  | Inv2TFun : forall T1 T2,
    inv_no_immediate_default T1 ->
    inv_base T2 ->
    inv_no_immediate_default (TFun T1 T2)
  | Inv2TOption: forall T1,
    inv_no_immediate_default T1 ->
    inv_no_immediate_default (TOption T1)
  | Inv2TArray: forall T1,
    inv_no_immediate_default T1 ->
    inv_no_immediate_default (TArray T1)
.


Lemma inv_no_immediate_is_inv_base:
  forall A, inv_no_immediate_default A -> inv_base A.
Proof.
  induction 1.
  all: try solve [econstructor; eauto].
Qed.


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
  | JTEArray:
    forall Delta Gamma A ts,
    List.Forall (fun t => jt_term Delta Gamma t A) ts ->
    inv_no_immediate_default A ->
    jt_term Delta Gamma (EArray ts) (TArray A)
  | JTEFold:
    forall Delta Gamma A B f ts init,
      jt_term Delta Gamma f (TFun A (TFun B B)) ->
      inv_no_immediate_default A ->
      inv_no_immediate_default B ->
      jt_term Delta Gamma ts (TArray A) ->
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
      inv_no_immediate_default T ->
      jt_value Delta VNone (TOption T)
  | JTValueVSome:
    forall Delta v T,
      jt_value Delta v T ->
      inv_no_immediate_default T ->
      jt_value Delta (VSome v) (TOption T)
  | JTValueUnit:
    forall Delta,
      jt_value Delta VUnit TUnit
  | JTValueVPure:
    forall Delta v T,
      jt_value Delta v T ->
      inv_no_immediate_default T ->
      jt_value Delta (VPure v) (TDefault T)
  | JTVArray:
    forall Delta A vs,
      inv_no_immediate_default A ->
      List.Forall (fun v => jt_value Delta v A) vs ->
      jt_value Delta (VArray vs) (TArray A)
.

Definition jt_term_ind' :=
fun
  (P : forall (o : string -> option type) (l : list type) 
	     (t : term) (t0 : type), Prop)
  (P0 : forall (o : string -> option type) (v : value) (t : type), Prop)
  (f : forall (Delta : string -> option type) (Gamma : list type) 
         (x : nat) (T : type) (e : Some T = nth_error Gamma x)
         (i : inv_base T),
       P Delta Gamma (Var x) T)
  (f0 : forall (Delta : string -> option type) (Gamma : list type)
          (t1 t2 : term) (T1 T2 : type)
          (j : jt_term Delta Gamma t1 (TFun T1 T2)),
        P Delta Gamma t1 (TFun T1 T2) ->
        forall j0 : jt_term Delta Gamma t2 T1,
        P Delta Gamma t2 T1 ->
        forall i : inv_base T2,
        P Delta Gamma (App t1 t2) T2)
  (f1 : forall (Delta : string -> option type) (Gamma : list type) 
          (t : term) (T1 T2 : type) (j : jt_term Delta (T1 :: Gamma) t T2),
        P Delta (T1 :: Gamma) t T2 ->
        forall i : inv_base (TFun T1 T2),
        P Delta Gamma (Lam t) (TFun T1 T2))
  (f2 : forall (Delta : string -> option type) (Gamma : list type)
          (ts : list term) (tj tc : term) (T : type)
          (f2 : Forall (fun ti : term => jt_term Delta Gamma ti (TDefault T))
                  ts)
          (f2' : Forall (fun ti : term => P Delta Gamma ti (TDefault T))
          ts) (j : jt_term Delta Gamma tj TBool),
        P Delta Gamma tj TBool ->
        forall j0 : jt_term Delta Gamma tc (TDefault T),
        P Delta Gamma tc (TDefault T) ->
        forall i : inv_base (TDefault T),
        P Delta Gamma (Default ts tj tc) (TDefault T))
  (f3 : forall (Delta : string -> option type) (Gamma : list type) 
          (t : term) (T : type) (j : jt_term Delta Gamma t T),
        P Delta Gamma t T ->
        forall i : inv_base (TDefault T),
        P Delta Gamma (DefaultPure t) (TDefault T))
  (f4 : forall (Delta : string -> option type) (Gamma : list type) 
          (t : term) (T : type) (j : jt_term Delta Gamma t (TDefault T)),
        P Delta Gamma t (TDefault T) ->
        forall i : inv_base T,
        P Delta Gamma (ErrorOnEmpty t) T)
  (f5 : forall (Delta : string -> option type) (Gamma : list type)
          (t1 t2 : term) (op : op) (T1 T2 T3 : type)
          (e : (T1, T2, T3) = jt_op op) (j : jt_term Delta Gamma t1 T1),
        P Delta Gamma t1 T1 ->
        forall j0 : jt_term Delta Gamma t2 T2,
        P Delta Gamma t2 T2 ->
        forall i : inv_base T3,
        P Delta Gamma (Binop op t1 t2) T3)
  (f6 : forall (Delta : string -> option type) (Gamma : list type)
          (v : value) (T : type) (j : jt_value Delta v T),
        P0 Delta v T ->
        forall i : inv_base T,
        P Delta Gamma (Value v) T)
  (f7 : forall (Delta : string -> option type) (Gamma : list type) 
          (u : term) (U : type) (t1 t2 : term) (T : type)
          (j : jt_term Delta Gamma u (TOption U)),
        P Delta Gamma u (TOption U) ->
        forall j0 : jt_term Delta Gamma t1 T,
        P Delta Gamma t1 T ->
        forall j1 : jt_term Delta (U :: Gamma) t2 T,
        P Delta (U :: Gamma) t2 T ->
        forall i : inv_base T,
        P Delta Gamma (Match_ u t1 t2) T)
  (f8 : forall (Delta : string -> option type) (Gamma : list type) 
          (A : type) (ts : list term)
          (f8 : Forall (fun t : term => jt_term Delta Gamma t A) ts)
          (f8' : Forall (fun t : term => P Delta Gamma t A) ts)
          (i : inv_no_immediate_default A),
        P Delta Gamma (EArray ts) (TArray A))
  (f9 : forall (Delta : string -> option type) (Gamma : list type)
          (A B : type) (f9 ts init : term)
          (j : jt_term Delta Gamma f9 (TFun A (TFun B B))),
        P Delta Gamma f9 (TFun A (TFun B B)) ->
        forall (i : inv_no_immediate_default A)
          (i0 : inv_no_immediate_default B)
          (j0 : jt_term Delta Gamma ts (TArray A)),
        P Delta Gamma ts (TArray A) ->
        forall j1 : jt_term Delta Gamma init B,
        P Delta Gamma init B ->
        P Delta Gamma (Fold f9 ts init) B)
  (f10 : forall (Delta : string -> option type) (Gamma : list type)
           (t : term) (T : type) (j : jt_term Delta Gamma t T),
         P Delta Gamma t T ->
         forall i : inv_base (TOption T),
         P Delta Gamma (ESome t) (TOption T))
  (f11 : forall (Delta : string -> option type) (Gamma : list type)
           (T : type) (i : inv_base (TOption T)),
         P Delta Gamma ENone (TOption T))
  (f12 : forall (Delta : string -> option type) (Gamma : list type)
           (T : type) (i : inv_base (TDefault T)),
         P Delta Gamma Empty (TDefault T))
  (f13 : forall (Delta : string -> option type) (Gamma : list type)
           (T : type) (i : inv_base T),
         P Delta Gamma Conflict T)
  (f14 : forall (Delta : string -> option type) (Gamma : list type)
           (u ta tb : term) (T : type) (j : jt_term Delta Gamma u TBool),
         P Delta Gamma u TBool ->
         forall j0 : jt_term Delta Gamma ta T,
         P Delta Gamma ta T ->
         forall j1 : jt_term Delta Gamma tb T,
         P Delta Gamma tb T ->
         forall i : inv_base T,
         P Delta Gamma (If u ta tb) T)
  (f15 : forall (Delta : string -> option type) (b : bool),
         P0 Delta (Bool b) TBool)
  (f16 : forall (Delta : string -> option type) (i : Z),
         P0 Delta (Int i) TInteger)
  (f17 : forall (Delta : string -> option type) (tcl : {bind term})
           (sigma_cl : list value) (Gamma_cl : list type) 
           (T1 T2 : type) (f17 : Forall2 (jt_value Delta) sigma_cl Gamma_cl)
           (f17' : Forall2 (P0 Delta) sigma_cl Gamma_cl)
           (j : jt_term Delta Gamma_cl (Lam tcl) (TFun T1 T2)),
         P Delta Gamma_cl (Lam tcl) (TFun T1 T2) ->
         P0 Delta (Closure tcl sigma_cl) (TFun T1 T2))
  (f18 : forall (Delta : string -> option type) (T : type)
           (i : inv_no_immediate_default T),
         P0 Delta VNone (TOption T))
  (f19 : forall (Delta : string -> option type) (v : value) 
           (T : type) (j : jt_value Delta v T),
         P0 Delta v T ->
         forall i : inv_no_immediate_default T,
         P0 Delta (VSome v) (TOption T))
  (f20 : forall Delta : string -> option type,
         P0 Delta VUnit TUnit)
  (f21 : forall (Delta : string -> option type) (v : value) 
           (T : type) (j : jt_value Delta v T),
         P0 Delta v T ->
         forall i : inv_no_immediate_default T,
         P0 Delta (VPure v) (TDefault T))
  (f22 : forall (Delta : string -> option type) (A : type) 
           (vs : list value) (i : inv_no_immediate_default A)
           (f22 : Forall (fun v : value => jt_value Delta v A) vs)
           (f22' : Forall (fun v : value => P0 Delta v A) vs),
         P0 Delta (VArray vs) (TArray A)) =>
fix F
  (o : string -> option type) (l : list type) (t : term) 
  (t0 : type) (j : jt_term o l t t0) {struct j} : 
P o l t t0 :=
  match j as j0 in (jt_term o0 l0 t1 t2) return (P o0 l0 t1 t2) with
  | JTVar Delta Gamma x T e i => f Delta Gamma x T e i
  | JTApp Delta Gamma t1 t2 T1 T2 j0 j1 i =>
      f0 Delta Gamma t1 t2 T1 T2 j0 (F Delta Gamma t1 (TFun T1 T2) j0) j1
        (F Delta Gamma t2 T1 j1) i
  | JTLam Delta Gamma t1 T1 T2 j0 i =>
      f1 Delta Gamma t1 T1 T2 j0 (F Delta (T1 :: Gamma) t1 T2 j0) i
  | JTDefault Delta Gamma ts tj tc T f23 j0 j1 i =>
      f2 Delta Gamma ts tj tc T f23 (Forall_ind
      (Forall (fun ti => P Delta Gamma ti (TDefault T)))
      (Forall_nil (fun ti => P Delta Gamma ti (TDefault T)))
      (fun x l H _ IHB => Forall_cons x (F Delta Gamma x (TDefault T) H) IHB) f23) j0 (F Delta Gamma tj TBool j0) j1
        (F Delta Gamma tc (TDefault T) j1) i
  | JTDefaultPure Delta Gamma t1 T j0 i =>
      f3 Delta Gamma t1 T j0 (F Delta Gamma t1 T j0) i
  | JTErrorOnEmpty Delta Gamma t1 T j0 i =>
      f4 Delta Gamma t1 T j0 (F Delta Gamma t1 (TDefault T) j0) i
  | JTBinop Delta Gamma t1 t2 op T1 T2 T3 e j0 j1 i =>
      f5 Delta Gamma t1 t2 op T1 T2 T3 e j0 (F Delta Gamma t1 T1 j0) j1
        (F Delta Gamma t2 T2 j1) i
  | JTValue Delta Gamma v T j0 i => f6 Delta Gamma v T j0 (F0 Delta v T j0) i
  | JTMatch Delta Gamma u U t1 t2 T j0 j1 j2 i =>
      f7 Delta Gamma u U t1 t2 T j0 (F Delta Gamma u (TOption U) j0) j1
        (F Delta Gamma t1 T j1) j2 (F Delta (U :: Gamma) t2 T j2) i
  | JTEArray Delta Gamma A ts f23 i => f8 Delta Gamma A ts f23 (Forall_ind
  (Forall (fun ti => P Delta Gamma ti A))
  (Forall_nil (fun ti => P Delta Gamma ti A))
  (fun x l H _ IHB => Forall_cons x (F Delta Gamma x A H) IHB) f23) i
  | JTEFold Delta Gamma A B f23 ts init j0 i i0 j1 j2 =>
      f9 Delta Gamma A B f23 ts init j0
        (F Delta Gamma f23 (TFun A (TFun B B)) j0) i i0 j1
        (F Delta Gamma ts (TArray A) j1) j2 (F Delta Gamma init B j2)
  | JTESome Delta Gamma t1 T j0 i =>
      f10 Delta Gamma t1 T j0 (F Delta Gamma t1 T j0) i
  | JTENone Delta Gamma T i => f11 Delta Gamma T i
  | JTEEmpty Delta Gamma T i => f12 Delta Gamma T i
  | JTEConflict Delta Gamma T i => f13 Delta Gamma T i
  | JTEIf Delta Gamma u ta tb T j0 j1 j2 i =>
      f14 Delta Gamma u ta tb T j0 (F Delta Gamma u TBool j0) j1
        (F Delta Gamma ta T j1) j2 (F Delta Gamma tb T j2) i
  end
with F0
  (o : string -> option type) (v : value) (t : type) 
  (j : jt_value o v t) {struct j} : P0 o v t :=
  match j as j0 in (jt_value o0 v0 t0) return (P0 o0 v0 t0) with
  | JTValueBool Delta b => f15 Delta b
  | JTValueInt Delta i => f16 Delta i
  | JTValueClosure Delta tcl sigma_cl Gamma_cl T1 T2 f23 j0 =>
      f17 Delta tcl sigma_cl Gamma_cl T1 T2 f23 (Forall2_ind
      (fun sigma_cl0 Gamma_cl0 =>
       Forall2 (P0 Delta) sigma_cl0 Gamma_cl0) (Forall2_nil (P0 Delta))
      (fun x y l l'
         H _
         IHf23 =>
       Forall2_cons x y (F0 Delta x y H) IHf23) f23) j0
        (F Delta Gamma_cl (Lam tcl) (TFun T1 T2) j0)
  | JTValueVNone Delta T i => f18 Delta T i
  | JTValueVSome Delta v0 T j0 i => f19 Delta v0 T j0 (F0 Delta v0 T j0) i
  | JTValueUnit Delta => f20 Delta
  | JTValueVPure Delta v0 T j0 i => f21 Delta v0 T j0 (F0 Delta v0 T j0) i
  | JTVArray Delta A vs i f23 => f22 Delta A vs i f23
    (Forall_ind
      (Forall (fun ti => P0 Delta ti A))
      (Forall_nil (fun ti => P0 Delta ti A))
      (fun x l H _ IHB => Forall_cons x (F0 Delta x A H) IHB) f23) 
  end
for
F.

Definition jt_value_ind' :=
fun
  (P : forall (o : string -> option type) (l : list type) 
	     (t : term) (t0 : type), Prop)
  (P0 : forall (o : string -> option type) (v : value) (t : type), Prop)
  (f : forall (Delta : string -> option type) (Gamma : list type) 
         (x : nat) (T : type) (e : Some T = nth_error Gamma x)
         (i : inv_base T),
       P Delta Gamma (Var x) T)
  (f0 : forall (Delta : string -> option type) (Gamma : list type)
          (t1 t2 : term) (T1 T2 : type)
          (j : jt_term Delta Gamma t1 (TFun T1 T2)),
        P Delta Gamma t1 (TFun T1 T2) ->
        forall j0 : jt_term Delta Gamma t2 T1,
        P Delta Gamma t2 T1 ->
        forall i : inv_base T2,
        P Delta Gamma (App t1 t2) T2)
  (f1 : forall (Delta : string -> option type) (Gamma : list type) 
          (t : term) (T1 T2 : type) (j : jt_term Delta (T1 :: Gamma) t T2),
        P Delta (T1 :: Gamma) t T2 ->
        forall i : inv_base (TFun T1 T2),
        P Delta Gamma (Lam t) (TFun T1 T2))
  (f2 : forall (Delta : string -> option type) (Gamma : list type)
          (ts : list term) (tj tc : term) (T : type)
          (f2 : Forall (fun ti : term => jt_term Delta Gamma ti (TDefault T))
                  ts)
          (f2' : Forall (fun ti : term => P Delta Gamma ti (TDefault T))
          ts) (j : jt_term Delta Gamma tj TBool),
        P Delta Gamma tj TBool ->
        forall j0 : jt_term Delta Gamma tc (TDefault T),
        P Delta Gamma tc (TDefault T) ->
        forall i : inv_base (TDefault T),
        P Delta Gamma (Default ts tj tc) (TDefault T))
  (f3 : forall (Delta : string -> option type) (Gamma : list type) 
          (t : term) (T : type) (j : jt_term Delta Gamma t T),
        P Delta Gamma t T ->
        forall i : inv_base (TDefault T),
        P Delta Gamma (DefaultPure t) (TDefault T))
  (f4 : forall (Delta : string -> option type) (Gamma : list type) 
          (t : term) (T : type) (j : jt_term Delta Gamma t (TDefault T)),
        P Delta Gamma t (TDefault T) ->
        forall i : inv_base T,
        P Delta Gamma (ErrorOnEmpty t) T)
  (f5 : forall (Delta : string -> option type) (Gamma : list type)
          (t1 t2 : term) (op : op) (T1 T2 T3 : type)
          (e : (T1, T2, T3) = jt_op op) (j : jt_term Delta Gamma t1 T1),
        P Delta Gamma t1 T1 ->
        forall j0 : jt_term Delta Gamma t2 T2,
        P Delta Gamma t2 T2 ->
        forall i : inv_base T3,
        P Delta Gamma (Binop op t1 t2) T3)
  (f6 : forall (Delta : string -> option type) (Gamma : list type)
          (v : value) (T : type) (j : jt_value Delta v T),
        P0 Delta v T ->
        forall i : inv_base T,
        P Delta Gamma (Value v) T)
  (f7 : forall (Delta : string -> option type) (Gamma : list type) 
          (u : term) (U : type) (t1 t2 : term) (T : type)
          (j : jt_term Delta Gamma u (TOption U)),
        P Delta Gamma u (TOption U) ->
        forall j0 : jt_term Delta Gamma t1 T,
        P Delta Gamma t1 T ->
        forall j1 : jt_term Delta (U :: Gamma) t2 T,
        P Delta (U :: Gamma) t2 T ->
        forall i : inv_base T,
        P Delta Gamma (Match_ u t1 t2) T)
  (f8 : forall (Delta : string -> option type) (Gamma : list type) 
          (A : type) (ts : list term)
          (f8 : Forall (fun t : term => jt_term Delta Gamma t A) ts)
          (f8' : Forall (fun t : term => P Delta Gamma t A) ts)
          (i : inv_no_immediate_default A),
        P Delta Gamma (EArray ts) (TArray A))
  (f9 : forall (Delta : string -> option type) (Gamma : list type)
          (A B : type) (f9 ts init : term)
          (j : jt_term Delta Gamma f9 (TFun A (TFun B B))),
        P Delta Gamma f9 (TFun A (TFun B B)) ->
        forall (i : inv_no_immediate_default A)
          (i0 : inv_no_immediate_default B)
          (j0 : jt_term Delta Gamma ts (TArray A)),
        P Delta Gamma ts (TArray A) ->
        forall j1 : jt_term Delta Gamma init B,
        P Delta Gamma init B ->
        P Delta Gamma (Fold f9 ts init) B)
  (f10 : forall (Delta : string -> option type) (Gamma : list type)
           (t : term) (T : type) (j : jt_term Delta Gamma t T),
         P Delta Gamma t T ->
         forall i : inv_base (TOption T),
         P Delta Gamma (ESome t) (TOption T))
  (f11 : forall (Delta : string -> option type) (Gamma : list type)
           (T : type) (i : inv_base (TOption T)),
         P Delta Gamma ENone (TOption T))
  (f12 : forall (Delta : string -> option type) (Gamma : list type)
           (T : type) (i : inv_base (TDefault T)),
         P Delta Gamma Empty (TDefault T))
  (f13 : forall (Delta : string -> option type) (Gamma : list type)
           (T : type) (i : inv_base T),
         P Delta Gamma Conflict T)
  (f14 : forall (Delta : string -> option type) (Gamma : list type)
           (u ta tb : term) (T : type) (j : jt_term Delta Gamma u TBool),
         P Delta Gamma u TBool ->
         forall j0 : jt_term Delta Gamma ta T,
         P Delta Gamma ta T ->
         forall j1 : jt_term Delta Gamma tb T,
         P Delta Gamma tb T ->
         forall i : inv_base T,
         P Delta Gamma (If u ta tb) T)
  (f15 : forall (Delta : string -> option type) (b : bool),
         P0 Delta (Bool b) TBool)
  (f16 : forall (Delta : string -> option type) (i : Z),
         P0 Delta (Int i) TInteger)
  (f17 : forall (Delta : string -> option type) (tcl : {bind term})
           (sigma_cl : list value) (Gamma_cl : list type) 
           (T1 T2 : type) (f17 : Forall2 (jt_value Delta) sigma_cl Gamma_cl)
           (f17' : Forall2 (P0 Delta) sigma_cl Gamma_cl)
           (j : jt_term Delta Gamma_cl (Lam tcl) (TFun T1 T2)),
         P Delta Gamma_cl (Lam tcl) (TFun T1 T2) ->
         P0 Delta (Closure tcl sigma_cl) (TFun T1 T2))
  (f18 : forall (Delta : string -> option type) (T : type)
           (i : inv_no_immediate_default T),
         P0 Delta VNone (TOption T))
  (f19 : forall (Delta : string -> option type) (v : value) 
           (T : type) (j : jt_value Delta v T),
         P0 Delta v T ->
         forall i : inv_no_immediate_default T,
         P0 Delta (VSome v) (TOption T))
  (f20 : forall Delta : string -> option type,
         P0 Delta VUnit TUnit)
  (f21 : forall (Delta : string -> option type) (v : value) 
           (T : type) (j : jt_value Delta v T),
         P0 Delta v T ->
         forall i : inv_no_immediate_default T,
         P0 Delta (VPure v) (TDefault T))
  (f22 : forall (Delta : string -> option type) (A : type) 
           (vs : list value) (i : inv_no_immediate_default A)
           (f22 : Forall (fun v : value => jt_value Delta v A) vs)
           (f22' : Forall (fun v : value => P0 Delta v A) vs),
         P0 Delta (VArray vs) (TArray A)) =>
fix F
  (o : string -> option type) (l : list type) (t : term) 
  (t0 : type) (j : jt_term o l t t0) {struct j} : 
P o l t t0 :=
  match j as j0 in (jt_term o0 l0 t1 t2) return (P o0 l0 t1 t2) with
  | JTVar Delta Gamma x T e i => f Delta Gamma x T e i
  | JTApp Delta Gamma t1 t2 T1 T2 j0 j1 i =>
      f0 Delta Gamma t1 t2 T1 T2 j0 (F Delta Gamma t1 (TFun T1 T2) j0) j1
        (F Delta Gamma t2 T1 j1) i
  | JTLam Delta Gamma t1 T1 T2 j0 i =>
      f1 Delta Gamma t1 T1 T2 j0 (F Delta (T1 :: Gamma) t1 T2 j0) i
  | JTDefault Delta Gamma ts tj tc T f23 j0 j1 i =>
      f2 Delta Gamma ts tj tc T f23 (Forall_ind
      (Forall (fun ti => P Delta Gamma ti (TDefault T)))
      (Forall_nil (fun ti => P Delta Gamma ti (TDefault T)))
      (fun x l H _ IHB => Forall_cons x (F Delta Gamma x (TDefault T) H) IHB) f23) j0 (F Delta Gamma tj TBool j0) j1
        (F Delta Gamma tc (TDefault T) j1) i
  | JTDefaultPure Delta Gamma t1 T j0 i =>
      f3 Delta Gamma t1 T j0 (F Delta Gamma t1 T j0) i
  | JTErrorOnEmpty Delta Gamma t1 T j0 i =>
      f4 Delta Gamma t1 T j0 (F Delta Gamma t1 (TDefault T) j0) i
  | JTBinop Delta Gamma t1 t2 op T1 T2 T3 e j0 j1 i =>
      f5 Delta Gamma t1 t2 op T1 T2 T3 e j0 (F Delta Gamma t1 T1 j0) j1
        (F Delta Gamma t2 T2 j1) i
  | JTValue Delta Gamma v T j0 i => f6 Delta Gamma v T j0 (F0 Delta v T j0) i
  | JTMatch Delta Gamma u U t1 t2 T j0 j1 j2 i =>
      f7 Delta Gamma u U t1 t2 T j0 (F Delta Gamma u (TOption U) j0) j1
        (F Delta Gamma t1 T j1) j2 (F Delta (U :: Gamma) t2 T j2) i
  | JTEArray Delta Gamma A ts f23 i => f8 Delta Gamma A ts f23 (Forall_ind
  (Forall (fun ti => P Delta Gamma ti A))
  (Forall_nil (fun ti => P Delta Gamma ti A))
  (fun x l H _ IHB => Forall_cons x (F Delta Gamma x A H) IHB) f23) i
  | JTEFold Delta Gamma A B f23 ts init j0 i i0 j1 j2 =>
      f9 Delta Gamma A B f23 ts init j0
        (F Delta Gamma f23 (TFun A (TFun B B)) j0) i i0 j1
        (F Delta Gamma ts (TArray A) j1) j2 (F Delta Gamma init B j2)
  | JTESome Delta Gamma t1 T j0 i =>
      f10 Delta Gamma t1 T j0 (F Delta Gamma t1 T j0) i
  | JTENone Delta Gamma T i => f11 Delta Gamma T i
  | JTEEmpty Delta Gamma T i => f12 Delta Gamma T i
  | JTEConflict Delta Gamma T i => f13 Delta Gamma T i
  | JTEIf Delta Gamma u ta tb T j0 j1 j2 i =>
      f14 Delta Gamma u ta tb T j0 (F Delta Gamma u TBool j0) j1
        (F Delta Gamma ta T j1) j2 (F Delta Gamma tb T j2) i
  end
with F0
  (o : string -> option type) (v : value) (t : type) 
  (j : jt_value o v t) {struct j} : P0 o v t :=
  match j as j0 in (jt_value o0 v0 t0) return (P0 o0 v0 t0) with
  | JTValueBool Delta b => f15 Delta b
  | JTValueInt Delta i => f16 Delta i
  | JTValueClosure Delta tcl sigma_cl Gamma_cl T1 T2 f23 j0 =>
      f17 Delta tcl sigma_cl Gamma_cl T1 T2 f23 (Forall2_ind
      (fun sigma_cl0 Gamma_cl0 =>
       Forall2 (P0 Delta) sigma_cl0 Gamma_cl0) (Forall2_nil (P0 Delta))
      (fun x y l l'
         H _
         IHf23 =>
       Forall2_cons x y (F0 Delta x y H) IHf23) f23) j0
        (F Delta Gamma_cl (Lam tcl) (TFun T1 T2) j0)
  | JTValueVNone Delta T i => f18 Delta T i
  | JTValueVSome Delta v0 T j0 i => f19 Delta v0 T j0 (F0 Delta v0 T j0) i
  | JTValueUnit Delta => f20 Delta
  | JTValueVPure Delta v0 T j0 i => f21 Delta v0 T j0 (F0 Delta v0 T j0) i
  | JTVArray Delta A vs i f23 => f22 Delta A vs i f23
    (Forall_ind
      (Forall (fun ti => P0 Delta ti A))
      (Forall_nil (fun ti => P0 Delta ti A))
      (fun x l H _ IHB => Forall_cons x (F0 Delta x A H) IHB) f23) 
  end
for
F0.


Inductive jt_result: (string -> option type) -> result -> type -> Prop := 
  | JTRValue:
    forall Delta v T,
    jt_value Delta v T ->
    jt_result Delta (RValue v) T
  | JTREmpty:
    forall Delta T,
    inv_no_immediate_default T ->
    jt_result Delta REmpty (TDefault T)
  | JTRConflict:
    forall Delta T,
    inv_base T ->
    jt_result Delta RConflict T
.

Inductive jt_cont: (string -> option type) -> list type -> list type -> cont -> type -> type -> Prop :=
  | JTCAppR:
    forall Delta Gamma t2 T1 T2,
      jt_term Delta Gamma t2 T1 ->
      jt_cont Delta Gamma Gamma (CAppR t2) (TFun T1 T2) T2
  | JTCClosure:
    forall Delta Gamma Gamma_cl sigma_cl T1 T2 tcl,
      jt_term Delta Gamma_cl (Lam tcl) (TFun T1 T2) ->
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
      inv_no_immediate_default T ->
      jt_cont Delta Gamma Gamma (CDefaultPure) T (TDefault T)
  | JTCErrorOnEmpty:
    forall Delta Gamma T,
      jt_cont Delta Gamma Gamma (CErrorOnEmpty) (TDefault T) T
  | JTCMatch:
    forall Delta Gamma t1 t2 U T,
      jt_term Delta Gamma t1 T ->
      jt_term Delta (U::Gamma) t2 T ->
      jt_cont Delta Gamma Gamma (CMatch t1 t2) (TOption U) T
  | JTCFoldAcc:
    forall Delta Gamma f ts A B,
      jt_term Delta Gamma f (TFun A (TFun B B)) ->
      inv_no_immediate_default A ->
      inv_no_immediate_default B ->
      jt_value Delta ts (TArray A) ->
      jt_cont Delta Gamma Gamma (CFoldAcc f ts) B B
  | JTCFold:
    forall Delta Gamma f acc A B,
      jt_term Delta Gamma f (TFun A (TFun B B)) ->
      inv_no_immediate_default A ->
      inv_no_immediate_default B ->
      jt_term Delta Gamma acc B ->
      jt_cont Delta Gamma Gamma (CFold f acc) (TArray A) B
  | JTCArray:
    forall Delta Gamma ts vs A,
      List.Forall (fun ti => jt_term Delta Gamma ti A) ts ->
      List.Forall (fun vi => jt_value Delta vi A) vs ->
      inv_no_immediate_default A ->
      jt_cont Delta Gamma Gamma (CArray ts vs) A (TArray A)
  | JTCSome:
    forall Delta Gamma T,
      inv_no_immediate_default T ->
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

Inductive jt_conts: (string -> option type) -> list type -> list type -> list cont -> type -> type -> Prop :=
  | JTNil:
    forall Delta Gamma T,
      inv_base T ->
      jt_conts Delta Gamma Gamma nil T T
  | JTCons:
    forall Delta Gamma1 Gamma2 Gamma3 cont kappa T1 T2 T3,
      jt_cont Delta Gamma1 Gamma2 cont T1 T2 ->
      jt_conts Delta Gamma2 Gamma3 kappa T2 T3 ->
      jt_conts Delta Gamma1 Gamma3 (cont :: kappa) T1 T3
.

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
      jt_conts Delta Gamma1 Gamma2 kappa T1 T2 ->
      jt_result Delta r T1 ->
      jt_state Delta Gamma2 (mode_cont kappa sigma r) T2
.


Ltac2 sinv_jt () :=
  match! goal with
  | [ h: jt_term _ _ ?c _ |- _ ] => smart_inversion c h
  | [ h: jt_value _ ?c _ |- _ ] => smart_inversion c h
  | [ h: jt_value _ _ ?c |- _ ] => smart_inversion c h
  | [ h: jt_cont _ _ _ ?c _ _ |- _ ] => smart_inversion c h
  | [ h: jt_conts _ _ _ ?c _ _ |- _ ] => smart_inversion c h
  | [ h: jt_state _ _ ?c _ |- _ ] => smart_inversion c h
  | [ h: jt_result _ ?c _ |- _ ] => smart_inversion c h
  | [ h: List.Forall _ ?c |- _ ] => smart_inversion c h
  | [ h: List.Forall2 _ ?c _ |- _ ] => smart_inversion c h
  | [ h: List.Forall2 _ _ ?c |- _ ] => smart_inversion c h
  end.

Ltac2 econs_jt () :=
  match! goal with
  | [ |- jt_term _ _ _ _] => econstructor
  | [ |- jt_value _ _ _] => econstructor
  | [ |- jt_cont _ _ _ _ _ _] => econstructor
  | [ |- jt_conts _ _ _ _ _ _] => econstructor
  | [ |- jt_state _ _ _ _] => econstructor
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

Lemma jt_term_inv {Delta Gamma t T}:
    jt_term Delta Gamma t T ->
    inv_base T.
Proof.
  induction 1; eauto using inv_no_immediate_is_inv_base.
  { econstructor; eauto. }
Qed.

Lemma jt_value_inv {Delta t T}:
    jt_value Delta t T ->
    inv_base T.
Proof.
  induction 1; eauto using inv_no_immediate_is_inv_base.
  all: try solve [repeat econstructor; eauto].
  { eapply jt_term_inv; eauto. }
Qed.

Lemma jt_result_inv {Delta t T}:
    jt_result Delta t T ->
    inv_base T.
Proof.
  induction 1; eauto using inv_no_immediate_is_inv_base.
  { eapply jt_value_inv; eauto. }
  { econstructor; eauto. }
Qed.

Theorem jt_cont_inv {k}:
  forall {Delta Gamma1 Gamma2 T1 T2},
  inv_base T1 ->
  jt_cont Delta Gamma1 Gamma2 k T1 T2 -> inv_base T2.
Proof.
  induction k; intros; repeat sinv_jt.
  all: repeat match goal with
  | [h: jt_term _ _ _ _ |- _] => learn (jt_term_inv h)
  end.
  all: try solve [
      eauto
    | econstructor; eauto
    | repeat sinv_inv; eauto
  ].
  { induction op; simpl in *; inj; econstructor. }
  { induction op; simpl in *; inj; econstructor. }
  { repeat sinv_inv; eapply inv_no_immediate_is_inv_base; eauto. }
Qed.


Ltac learn_inv :=
  repeat match goal with
  | [Hjt: jt_result _ _ _ |- _] =>
    learn (jt_result_inv Hjt)
  | [Hjt: jt_term _ _ _ _ |- _] =>
    learn (jt_term_inv Hjt)
  | [Hinv: inv_base ?T, Hjt: jt_cont _ _ _ _ ?T _ |- _] =>
    learn (jt_cont_inv Hinv Hjt)
  end.

Theorem preservation s1 s2:
  cred s1 s2 ->
  forall Delta Gamma T,
  jt_state Delta Gamma s1 T ->
  jt_state Delta Gamma s2 T.
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
  all: try solve [repeat (econstructor; eauto using inv_no_immediate_is_inv_base)].
  (* Operator handling *)
  { repeat (econstructor; eauto).
    eapply common.Forall2_nth_error_Some; eauto.
  }
  { (* Returning an Conflict *)
    induction H5.
    all: repeat sinv_jt.
    all: repeat sinv_inv.
    all: try (induction op; simpl in *; inj).
    all: learn_inv.
    all: try solve [repeat (econstructor; eauto) | tryfalse].
  }
  { induction op, v1, v2; simpl in *; inj; repeat (econstructor; eauto). }
  { repeat (econstructor; eauto).
    eapply Forall_rev.
    repeat (econstructor; eauto).
  }
Qed.


Theorem star_preservation {s1 s2}:
  star cred s1 s2 ->
  forall {Delta Gamma T},
  jt_state Delta Gamma s1 T ->
  jt_state Delta Gamma s2 T.
Proof.
  induction 1; intros; eauto using preservation.
Qed.


Theorem progress_small_steps {t1 t2}:
  sred t1 t2 ->
  forall {Delta Gamma T},
  jt_term Delta Gamma t1 T ->
  jt_term Delta Gamma t2 T.
Proof.
  induction 1; intros.
  all: try solve [repeat sinv_jt; repeat econs_jt; eauto; try solve [repeat sinv_inv; repeat econs_inv; eauto using inv_no_immediate_is_inv_base]].
  { repeat sinv_jt; repeat econs_jt; eauto.
    admit "ok, in this case, we need to enforce the invariant that lam terms are actually".
  }
  { admit. }
  { induction op; simpl in *; inj.
    all: induction v1, v2; simpl in *; tryfalse; inj.
    all: repeat sinv_jt; inj; repeat econs_jt; repeat econs_inv.
  }
  { repeat sinv_jt. admit. }
  { repeat sinv_jt; repeat econs_jt;
    unpack; eauto; eapply Forall_app; split; eauto.
  }
  { admit "whatever". }
Admitted.

Theorem jt_conts_append_stack_app {kappa}:
  forall {Delta Gamma1 Gamma3 T1 T3 kappa'},
  inv_base T1 ->
  jt_conts Delta Gamma1 Gamma3 (kappa ++ kappa') T1 T3 ->
  exists Gamma2 T2,
    jt_conts Delta Gamma1 Gamma2 (kappa) T1 T2 /\
    jt_conts Delta Gamma2 Gamma3 (kappa') T2 T3
  .
Proof.
  induction kappa; simpl.
  all: intros.
  all: repeat sinv_inv.
  { intros; repeat eexists; eauto.
    { econstructor; eauto. }
  }
  { repeat sinv_jt.
    learn_inv.
    learn (IHkappa _ _ _ _ _ _ H0 H9); unpack.
    repeat econstructor; eauto.
  }
Qed.

Theorem append_stack_jt_state {Delta Gamma2 s1 kappa T2}:
  jt_state Delta Gamma2 (append_stack s1 kappa) T2 ->
  exists Gamma1 Gamma2 T1,
  jt_conts Delta Gamma1 Gamma2 kappa T1 T2 /\
  jt_state Delta Gamma1 s1 T1.
Proof.
  induction s1; simpl; inversion 1; subst; simpl in *; tryfalse.


  all: learn_inv.
  all: repeat match goal with
    | [h: jt_term _ _ _ _ |- _] => learn (jt_term_inv_base h)
    | [h1: jt_conts _ _ _ (_++_) ?T _, h2: inv_base ?T |- _] => learn (jt_conts_append_stack_app h2 h1); unpack
  end.
  all: repeat eexists; repeat econs_jt; eauto.
Qed.

Theorem progress s1:
  forall Delta Gamma T,
    jt_state Delta Gamma s1 T ->
    (exists s2, cred s1 s2) \/ (is_mode_cont s1 = true /\ stack s1 = nil).
Proof.
  induction s1 as [t kappa env|kappa env r]; intros.
  { repeat sinv_jt.
    left.
    induction t.
    all: repeat sinv_jt.
    all: try solve [eexists; econstructor].
    { symmetry in H0.
      destruct (common.Forall2_nth_error_Some_right _ _ _ H5 _ _ H0).
      eexists; econstructor; eauto.
    }
    {
      induction ts.
      eexists; econstructor; eauto.
      eexists; econstructor; eauto.
    }
  }
  { induction kappa as [|cont kappa].
    { right; simpl; eauto. }
    { left; induction cont; induction r.
      all: repeat sinv_jt. (* need to infer information about values that are boolean *)
      all: try match goal with [o: option value |- _ ] => induction o end.
      all: try match goal with [ts: list term |- _ ] => induction ts end.
      all: try match goal with [vs: list value |- _ ] => induction vs end.
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
    { repeat (econstructor; eauto). }
    induction s2; simpl in *; subst; inj.
    repeat eexists; eauto.
  Qed.

  Theorem correctness_small_steps:
    forall Delta Gamma t T,
      inv_base T ->
      jt_term Delta Gamma t T ->
      (exists v, star sred t (Value v))
      \/ (star sred t Empty)
      \/ (star sred t Conflict).
  Admitted.

End correctness.

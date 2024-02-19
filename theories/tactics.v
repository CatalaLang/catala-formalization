Require Export Arith.
Require Import Arith.Compare_dec.
Require Import Arith.Peano_dec.
Require Export Psatz.

Require Import Nat.

Require Import Arith.Peano_dec.

Require Import Decidable PeanoNat.
Require Eqdep_dec.

From Ltac2 Require Import Ltac2.
From Ltac2 Require Import Constr Std Message Control List.
Set Default Proof Mode "Classic".

(* -------------------------------------------------------------------------- *)

(* Source: Myself. *)

Tactic Notation "admit" "arthur" := admit.
Tactic Notation "admit" "arthur" string(x):= admit.

Tactic Notation "admit" "alain" := admit.
Tactic Notation "admit" "alain" string(x):= admit.

Tactic Notation "admit" := admit.
Tactic Notation "admit" string(x):= admit.


Ltac inj :=
  repeat match goal with
    | [h: _ = _ |- _] =>
        try discriminate h;
        try (injection h; intros; subst; clear h)
    end.

Require Import List.
Import List.ListNotations.

Ltac unpack :=
    repeat match goal with
     [h: _ /\ _ |- _ ] =>
      destruct h
    |[h: exists x, _ |- _] =>
      let x := fresh x in
      destruct h as [x h]
    |[h: List.Forall _ (_ :: _) |- _] =>
      inversion h;
      subst;
      clear h
    |[h: List.Forall _ (_ ++ _) |- _] =>
      rewrite List.Forall_app in h;
      destruct h
    end.

Ltac unzip :=
  repeat match goal with
  | [h: _ /\ _ |- _ ] =>
    destruct h
  | [h: _ \/ _ |- _ ] =>
    destruct h
  |[h: exists x, _ |- _] =>
    let x := fresh x in
    destruct h as [x h]
  |[h: List.Forall _ (_ :: _) |- _] =>
    inversion h;
    subst;
    clear h
  |[h: List.Forall _ (_ ++ _) |- _] =>
    rewrite List.Forall_app in h;
    destruct h
  end.

Section unpack_tests.
  Example unpacking_forall_ex1 {A} (P: A -> Prop) l1 l2:
    List.Forall P (l1 ++ l2)
    ->
    List.Forall P l1 /\ List.Forall P l2.
  Proof.
    intros.
    unpack; eauto.
  Qed.

  Example unpacking_forall_ex2 {A} (P: A -> Prop) x l1 l2:
    List.Forall P (l1 ++ x :: l2)
    ->
    List.Forall P l1 /\ List.Forall P l2 /\ P x.
  Proof.
    intros.
    unpack; eauto.
  Qed.

  Example unpacking_forall_ex3 {A} (P: A -> Prop) x l1 l2:
    List.Forall P (l1 ++ [x] ++ l2)
    ->
    List.Forall P l1 /\ List.Forall P l2 /\ P x.
  Proof.
    intros.
    unpack; eauto.
  Qed.
End unpack_tests.

(* -------------------------------------------------------------------------- *)

(* Source: MyTactics by François Pottier *)

(* [push h] moves the hypothesis [h] into the goal. *)

Ltac push h :=
  generalize h; clear h.

(* [ltac_Mark] and [ltac_mark] are dummies. They are used as sentinels by
   certain tactics, to mark a position in the context or in the goal. *)

Inductive ltac_Mark : Type :=
| ltac_mark : ltac_Mark.

(* [push_until_mark] moves all hypotheses from the context into the goal,
   starting from the bottom and stopping as soon as a mark (that is, a
   hypothesis of type [ltac_Mark]) is reached. The mark is thrown away. The
   tactic fails if no mark appears in the context. *)

Ltac push_until_mark :=
  match goal with h: ?T |- _ =>
  match T with
  | ltac_Mark => clear h
  | _ => push h; push_until_mark
  end end.

(** [pop_until_mark] moves all hypotheses from the goal into the context,
    until a hypothesis of type [ltac_Mark] is reached. The mark is thrown
    away. The tactic fails if no mark appears in the goal. *)

Ltac pop_until_mark :=
  match goal with
  | |- (ltac_Mark -> _) => intros _
  | _ => intro; pop_until_mark
  end.

Ltac injections :=
  (* Place an initial mark, so as to not disturb the goal. *)
  generalize ltac_mark;
  (* Look at every equality hypothesis. *)
  repeat match goal with
  | h: _ = _ |- _ =>
      (* Try to apply the primitive tactic [injection] to this hypothesis.
         If this succeeds, clear [h] and replace it with the results of
         [injection]. Another mark is used for this purpose. If this fails,
         just push [h] into the goal, as we do not wish to see it any more. *)
      first [
        generalize ltac_mark; injection h; clear h; pop_until_mark
      | push h ]
  end;
  (* Pop all of the hypotheses that have been set aside above. *)
  pop_until_mark.

(* -------------------------------------------------------------------------- *)

(* The following incantations are suppose to allow [eauto with lia] to solve
   goals of the form [_ < _] or [_ <= _]. *)

Global Hint Extern 1 (_ <  _) => lia : lia.
Global Hint Extern 1 (_ <= _) => lia : lia.

Global Hint Resolve Nat.succ_lt_mono : lia.

(* -------------------------------------------------------------------------- *)

(* [dblib_by_cases] simplifies goals in which a decidable integer comparison
  appears. *)

Ltac dblib_intro_case_clear :=
  let h := fresh in
  intro h; case h; clear h.


Ltac dblib_inspect_cases :=
  match goal with
  | |- context [le_gt_dec ?n ?n'] =>
      case (le_gt_dec n n')
  | h: context [le_gt_dec ?n ?n'] |- _ =>
      revert h; case (le_gt_dec n n'); intro h
  | |- context [Nat.eq_dec ?n ?n'] =>
      case (Nat.eq_dec n n')
  | h: context [Nat.eq_dec ?n ?n'] |- _ =>
      revert h; case (Nat.eq_dec n n'); intro h
  | |- context [(lt_eq_lt_dec ?n ?n')] =>
      case (lt_eq_lt_dec n n'); [ dblib_intro_case_clear | idtac ]
  | h: context [(lt_eq_lt_dec ?n ?n')] |- _ =>
      revert h; case (lt_eq_lt_dec n n'); [ dblib_intro_case_clear | idtac ]; intro h
  end.

Ltac dblib_by_cases :=
  repeat dblib_inspect_cases; try solve [ intros; exfalso; lia ]; intros.


(* -------------------------------------------------------------------------- *)

(* source : LibTactics.v from Arthur Chargeraux *)
Tactic Notation "tryfalse" := try solve [exfalso; solve [assumption | discriminate | congruence]].

Tactic Notation "tryfalse" tactic(cont) := try solve [
    exfalso; solve [
      assumption |
      discriminate |
      congruence |
      cont
    ]
  ].


(* -------------------------------------------------------------------------- *)

(* Forward chaining of applications, to facilitate "saturating" the known facts
without specializing. See Clément's thesis
http://pit-claudel.fr/clement/MSc/#org036d20e for a nicer explanation. *)
Module Learn.
  Inductive Learnt {P:Prop} :=
  | AlreadyLearnt (H:P).

  Local Ltac learn_fact H :=
    let P := type of H in
    lazymatch goal with
    (* matching the type of H with the Learnt hypotheses means the
    learning fails even when the proposition is known by a different
    but unifiable type term *)
    | [ Hlearnt: @Learnt P |- _ ] =>
      fail 0 "already knew" P "through" Hlearnt
    | _ =>
      pose proof H;
      pose proof (AlreadyLearnt H)
    end.

  Tactic Notation "learn" constr(H) := learn_fact H.
End Learn.
Export Learn.

(* -------------------------------------------------------------------------- *)

(* Locking mechanism. This permit for instance to run subst and not rewrite an equality. It is particulary usefull in the small step equivalence to keep trace of some usefull states or subterms. *)

Inductive locked (P: Prop) :=
| Lock (H: P).

Ltac lock_ident H :=
  let tmp := fresh "tmp" in
  rename H into tmp;
  pose proof (Lock _ tmp) as H;
  clear tmp
.

Ltac unlock_ident H :=
  destruct H as [H].

Ltac unlock :=
  repeat match goal with
  | [h: locked _ |- _ ] =>
    unlock_ident h
  end.

Ltac msubst :=
  unlock; subst.

Tactic Notation "unlock" := unlock.
Tactic Notation "unlock" ident(H) := unlock_ident H.
Tactic Notation "lock" ident(H) := lock_ident H.

(* -------------------------------------------------------------------------- *)

(* Source: myself *)

(**
The [smart_inversion] tactic, a custom Ltac2 implementation, streamlines the inversion process in Coq proofs. It efficiently handles inversions on hypotheses [h] when provided with a constructor term [c], applicable to both fully applied constructors (like [C _ _ _ _]) and their basic forms ([C]).

This tactic is exclusively usable within the Ltac2 context.

For instance, in the inversion of typing judgments, [smart_inversion] simplifies the traditional approach significantly. Compare the following tactics:

Original Ltac Approach:
```coq
Ltac inv_jt :=
  match goal with
  | [h: jt_term _ _ (Var _) _ |- _] =>
    inversion h; clear h; subst
  | [h: jt_term _ _ (App _ _) _ |- _] =>
    inversion h; clear h; subst
  | [h: jt_term _ _ (Lam _) _ |- _] =>
    inversion h; clear h; subst
  ...(* and so on for all cases *)
  end.
```

Refactored Using Ltac2 and `smart_inversion`:

```coq
Ltac2 inv_jt () :=
  match! goal with
  | [h: jt_term _ _ c _ |- _] =>
    smart_inversion c h
  end.

Ltac inv_jt := ltac2:(inv_jt ())
```

In the refactored version, [smart_inversion] elegantly replaces the verbose pattern matching, making the tactic more concise and maintainable.

*)

Ltac2 is_applied_constructor (c: constr) :=
  Bool.and
  (match Unsafe.kind (Constr.type c) with
  | Unsafe.App c _ =>
    is_ind c
  | Unsafe.Ind _ _ => true
  | _ => false
  end)
  (match Unsafe.kind c with
  | Unsafe.App c _ =>
    match Unsafe.kind c with
    | Unsafe.Constructor _ _ => true
    | _ => false
    end
  | Unsafe.Constructor _ _ => true
  | _ => false
  end).

Ltac2 smart_inversion c h :=
  (* check whenever c is a constructor either fully applied (C _ _ _ _) or C*)
  if is_applied_constructor c then
    (
      Std.inversion Std.FullInversion (Std.ElimOnIdent h) None None;
      Std.subst_all ();
      Std.clear [h]
    )
  else Control.zero Match_failure
.


(** [econs] Is a tactic that tries to do econstructor only if the current type is in the list.
*)
Local Ltac2 econs_tactic l :=
  let c := Control.goal () in
  Control.enter 
  (fun () =>
    Std.intros false [];
    if (match Unsafe.kind c with
      | Unsafe.App c _ =>
        Bool.and
          (is_ind c)
          (List.mem Constr.equal c l)
      | Unsafe.Ind _ _ => (List.mem Constr.equal c l)
      | _ => false
      end)
    then
      (Std.constructor true)
    else
      ()).

Ltac2 Notation "econs" l(list1(constr, ",")) := econs_tactic l.

Goal forall n, exists n', n' = n+1.
  repeat ltac2:(econs ex, nat).
  eauto.
Qed.


Ltac sp :=
  repeat match goal with
  | [ |- context [let '(_, _) := ?p in _]] =>
    rewrite (surjective_pairing p)
  | [h: context [let '(_, _) := ?p in _] |- _] =>
    rewrite (surjective_pairing p) in h
  end
.
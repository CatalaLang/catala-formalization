Require Export Arith.
Require Import Arith.Compare_dec.
Require Import Arith.Peano_dec.
Require Export Psatz.

Require Import Nat.

Require Import Arith.Peano_dec.

Require Import Decidable PeanoNat.
Require Eqdep_dec.

Require Export LibTactics.

(* -------------------------------------------------------------------------- *)

(* [false] replaces the current goal with [False]. *)

Ltac false :=
  elimtype False.

(* -------------------------------------------------------------------------- *)

(* [tc] is a shortcut for [eauto with typeclass_instances]. For some reason,
   it is often necessary to use [rewrite ... by tc]. *)

Ltac tc :=
  eauto with typeclass_instances.

(* -------------------------------------------------------------------------- *)

(* The tactic [obvious] does nothing by default, but can be extended with hints
   so as to solve relatively easy goals -- e.g., proving that a term is a value,
   proving a size inequality, proving that a substitution is a renaming, etc.
   These predicates are sometimes interrelated (e.g., size is preserved by
   renamings; the property of being a value is preserved by renamings) so it
   would be counterproductive to distinguish several hint databases. *)

Create HintDb obvious.

Ltac obvious :=
  eauto with obvious typeclass_instances.

(* -------------------------------------------------------------------------- *)

(* The tactic [pick R k] picks a hypothesis [h] whose statement is an
   application of the inductive predicate [R], and passes [h] to the (Ltac)
   continuation [k]. *)

Ltac pick R k :=
  match goal with
  | h: R _         |- _ => k h
  | h: R _ _       |- _ => k h
  | h: R _ _ _     |- _ => k h
  | h: R _ _ _ _   |- _ => k h
  | h: R _ _ _ _ _ |- _ => k h
  end.

(* -------------------------------------------------------------------------- *)

(* The tactic [invert h] case-analyzes the hypothesis [h], whose statement
   should be an application of an inductive predicate. *)

Ltac invert h :=
  inversion h; clear h; try subst.

(* The tactic [inv R] looks for a hypothesis [h] whose statement is an
   application of the inductive predicate [R], and case-analyzes this
   hypothesis. *)

Ltac inv R :=
  pick R invert.

(* -------------------------------------------------------------------------- *)

(* The tactic [unpack] decomposes conjunctions and existential quantifiers
   in the hypotheses. Then, it attempts to perform substitutions, if possible. *)

Ltac unpack :=
  repeat match goal with
  | h: _ /\ _ |- _ =>
      destruct h
  | h: exists _, _ |- _ =>
      destruct h
  end;
  try subst.


Ltac unzip :=
  repeat match goal with
  | h: _ /\ _ |- _ =>
      destruct h
  | h: exists _, _ |- _ =>
      destruct h
  | h: _ \/ _ |- _ =>
    destruct h
  | h: sumbool _ _  |- _ =>
    destruct h
  | h: sumor _ _ |- _ =>
    destruct h
  | h: sum _ _  |- _ =>
    destruct h
  | h: sig _ |- _ =>
    destruct h
  end;
  try subst; repeat split.
  


(* -------------------------------------------------------------------------- *)

(* The tactic [forward lemma] applies [lemma] in a forward way. That is,
   it asserts that a certain fact holds, and that this fact follows from
   an application of [lemma]. If the lemma has hypotheses, it attempts
   to prove them via the tactic [obvious]. If the lemma has a complex
   conclusion, involving existential quantifiers and conjunction, it
   deconstructs it using [unpack]. *)

Ltac forward lemma :=
  let fact := fresh "fact" in
  evar (fact : Prop);
  assert fact; [
    (* Attempt to prove the lemma's hypotheses using [obvious]. *)
    eapply lemma; obvious
  | (* Deconstruct the lemma's conclusion using [unpack]. *)
    unfold fact in *; clear fact; unpack ].

(* -------------------------------------------------------------------------- *)

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


Global Hint Resolve Arith.Lt.lt_n_S : lia.

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
  repeat dblib_inspect_cases; try solve [ intros; false; lia ]; intros.

(* The tactic [inverts_Forall] search of every possible List.Forall or
   Option.Forall in the hypotheses and inverts it. *)


Lemma Forall_nil_iff {A} {P} : @List.Forall A P nil <-> True.
Proof.
  easy.
Qed.

Lemma Forall_cons_iff {A} {P} : forall (a:A) l, @List.Forall A P (a :: l)%list <-> P a /\ @List.Forall A P l.
Proof.
  intros. now split; [intro H; inversion H|constructor].
Qed.

Lemma Forall_app A (P: A -> Prop) l1 l2 :
   List.Forall P (l1 ++ l2) <-> List.Forall P l1 /\ List.Forall P l2.
Proof.
  induction l1 as [|a l1 IH]; cbn.
  - now rewrite Forall_nil_iff.
  - now rewrite !Forall_cons_iff, IH, and_assoc.
Qed.

Lemma Forall_app_dir A (P: A -> Prop) l1 l2 :
   List.Forall P (l1 ++ l2) -> List.Forall P l1 /\ List.Forall P l2.
Proof.
  eapply Forall_app.
Qed.


Ltac inverts_Forall :=
repeat match goal with
| h: @List.Forall _ _ (_ :: _) |- _ => inverts h
| h: @List.Forall2 _ _ _ (_ :: _) (_ :: _) |- _ => inverts h
| h: @List.Forall _ _ (_ ++ _) |- _ =>
  let tmp := fresh "tmp" in
  rename h into tmp;
  destruct (Forall_app_dir _ _ _ _ tmp); clear tmp
(* | h: @Option.Forall _ _ (Some _) |- _ => inverts h *)
end.

Goal forall A ts1 ti ts2 tj ts3 (P: A -> Prop),
  List.Forall P (ts1 ++ ti :: ts2 ++ tj :: ts3) ->
  List.Forall P ts1 /\ P ti /\ List.Forall P ts2 /\ P tj /\ List.Forall P ts3.
Proof.
  intros.
  inverts_Forall.
  eauto.
Qed.

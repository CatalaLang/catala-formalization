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

Ltac unzip_0 :=
  match goal with
  | [h: _ /\ _ |- _ ] =>
    destruct h
  | [h: _ \/ _ |- _ ] =>
    destruct h
  | [h: {_}+{_} |- _ ] =>
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

Ltac unzip := repeat unzip_0.

Ltac unzip_match :=
  match goal with
  | _ => unzip_0
  | [h: context [ match ?t with _ => _ end ] |- _] =>
    destruct t eqn:?
  | [ |- context [ match ?t with _ => _ end ] ] =>
    destruct t eqn:?
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
  
  Example unzip_match_test (P: nat -> Prop) x l1 l2:
  match x with S _ => True | O => False end ->
  List.Forall P (l1 ++ [x] ++ l2)
  ->
  List.Forall P l1 /\ List.Forall P l2 /\ P x.
Proof.
  intros.
  unzip_match.
  unzip_match.
  unzip_match.
  unzip_match.
  { eauto. }
  { eauto. }
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

(* source : LibTactics.v from Arthur Chargeraux adapted for our use *)
Tactic Notation "tryfalse" := try solve [
  unzip; exfalso;
  solve [assumption | discriminate | congruence]].

Tactic Notation "tryfalse" tactic(cont) := try solve [
    unzip; exfalso; solve [
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


(** Ported the above tactic to ltac2. *)
(* 
Module Learn2.
  Inductive Learnt {P:Prop} :=
  | AlreadyLearnt (H:P).

  Local Ltac2 learn_fact (h: constr) :=
    let p := Constr.type h in
    let q := constr:(@Learnt $p) in
    if List.for_all (fun (_, _, v) =>
      Bool.neg (Constr.equal q v)
    ) (Control.hyps ()) then
      let hname := Fresh.in_goal @H0 in
      let lname := Fresh.in_goal @L0 in
      Std.assert (Std.AssertValue hname h);
      Std.assert (Std.AssertValue lname constr:(AlreadyLearnt $h))
    else
      Control.backtrack_tactic_failure "Fact already known"
    .

  Ltac2 Notation "learn"
    arg(constr) :=
    learn_fact arg.
End Learn2.
Export Learn2. *)

(* -------------------------------------------------------------------------- *)

(* Complementary to the learn tactic: prints everything that has been learn in the current context. Source: myself*)

Ltac print_learnt :=
  repeat multimatch goal with
  | [h: @Learnt ?t |- _] => idtac t
  end.

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


Ltac2 get_head (c: constr) : constr option :=
    match Unsafe.kind c with
    | Unsafe.App c _ =>
      match Unsafe.kind c with
      | Unsafe.Constructor _ _ => Some c
      | _ => None
      end
    | Unsafe.Constructor _ _ => Some c
    | _ => None
    end.

Ltac2 Eval get_head (constr : ( @List.nil nat )).

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

(* Typical optimization that can be found inside normal compiler. But applied on galina code for ease of use. *)
Ltac sp :=
  repeat match goal with
  | [ |- context [let '(_, _) := ?p in _]] =>
    rewrite (surjective_pairing p)
  | [h: context [let '(_, _) := ?p in _] |- _] =>
    rewrite (surjective_pairing p) in h
  end
.

(** simple information property that help knowing what is the current case *)

Require Export String.
Require Import List.

Inductive info: string -> Prop :=
| True_info: forall s: string, info s.
Hint Constructors info : core.


Ltac check s := match goal with
  | [h: info s |- _] => idtac
  | _ => fail 1 "the identifier was not found the the current context"
  end. 

Tactic Notation "check" constr(x):= check x.

Open Scope string.
Open Scope list.

Goal info "test" -> info "bidule".
Proof.
  intros.
  check "test".
  Fail check "autre".
  eauto.
Abort.


(* Tactic that discard from the current context every hypothesis that can be derived using simpl; eauto *)

Ltac cleanup := match goal with
  |[h: ?T |- _] =>
    let h' := fresh h in
    match T with
    | info _ => idtac
    | _ => 
      assert (h': T); [solve[clear; simpl; eauto]|];
      clear h h'
    end
  end
  .

(* cleanup get rid of spurious hypothesis. *)
Goal True -> False.
Proof.
  intros.
  repeat cleanup.
Abort.

(* But does not touch info *)
Goal info "test" -> True -> False.
Proof.
  intros.
  check "test".
  repeat cleanup.
  check "test".
Abort.




(* From compcert.lib.Coqlib *)

Lemma modusponens: forall (P Q: Prop), P -> (P -> Q) -> Q.
Proof. auto. Qed.

Ltac exploit x :=
    refine (modusponens _ _ (x _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _)
 || refine (modusponens _ _ (x _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _)
 || refine (modusponens _ _ (x _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _)
 || refine (modusponens _ _ (x _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _)
 || refine (modusponens _ _ (x _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _)
 || refine (modusponens _ _ (x _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _)
 || refine (modusponens _ _ (x _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _)
 || refine (modusponens _ _ (x _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _)
 || refine (modusponens _ _ (x _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _)
 || refine (modusponens _ _ (x _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _)
 || refine (modusponens _ _ (x _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _)
 || refine (modusponens _ _ (x _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _)
 || refine (modusponens _ _ (x _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _)
 || refine (modusponens _ _ (x _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _)
 || refine (modusponens _ _ (x _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _)
 || refine (modusponens _ _ (x _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _)
 || refine (modusponens _ _ (x _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _)
 || refine (modusponens _ _ (x _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _)
 || refine (modusponens _ _ (x _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _)
 || refine (modusponens _ _ (x _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _)
 || refine (modusponens _ _ (x _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _)
 || refine (modusponens _ _ (x _ _ _ _ _ _ _ _ _ _ _ _ _ _) _)
 || refine (modusponens _ _ (x _ _ _ _ _ _ _ _ _ _ _ _ _) _)
 || refine (modusponens _ _ (x _ _ _ _ _ _ _ _ _ _ _ _) _)
 || refine (modusponens _ _ (x _ _ _ _ _ _ _ _ _ _ _) _)
 || refine (modusponens _ _ (x _ _ _ _ _ _ _ _ _ _) _)
 || refine (modusponens _ _ (x _ _ _ _ _ _ _ _ _) _)
 || refine (modusponens _ _ (x _ _ _ _ _ _ _ _) _)
 || refine (modusponens _ _ (x _ _ _ _ _ _ _) _)
 || refine (modusponens _ _ (x _ _ _ _ _ _) _)
 || refine (modusponens _ _ (x _ _ _ _ _) _)
 || refine (modusponens _ _ (x _ _ _ _) _)
 || refine (modusponens _ _ (x _ _ _) _)
 || refine (modusponens _ _ (x _ _) _)
 || refine (modusponens _ _ (x _) _).

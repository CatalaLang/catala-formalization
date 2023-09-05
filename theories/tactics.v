(* -------------------------------------------------------------------------- *)

(* Source: Myself. *)

Tactic Notation "admit" "arthur" := admit.
Tactic Notation "admit" "arthur" string(x):= admit.

Tactic Notation "admit" "alain" := admit.
Tactic Notation "admit" "alain" string(x):= admit.

Tactic Notation "admit" := fail.

Ltac inj :=
  repeat match goal with
    [h: _ = _ |- _] =>
        try discriminate h;
        try (injection h; intros; subst; clear h)
    end.

Ltac unpack :=
    repeat match goal with
     [h: _ /\ _ |- _ ] =>
        destruct h
    |[h: exists _, _ |- _] =>
        destruct h
    end.

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

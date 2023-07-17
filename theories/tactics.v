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
    end.

(* -------------------------------------------------------------------------- *)

(* The [bind] combinator of the option monad. *)

Definition bind {A B} (f : option A) (k : A -> option B) : option B :=
  match f with
  | None =>
      None
  | Some a =>
      k a
  end.

(* The standard syntactic sugar for [bind]. [f >>= k] can be read as ``first
   do [f]; then, if successful, with the result of [f], do [k]''. *)

Notation "f >>= k" := (bind f k) (at level 55).

(* -------------------------------------------------------------------------- *)

(* These lemmas help prove an equation of the form [f >>= k = b]. *)

Lemma prove_bind_None:
  forall {A B} {f} {k : A -> option B},
  f = None ->
  f >>= k = None.
Proof.
  intros. subst. eauto.
Qed.

Lemma prove_bind_Some:
  forall {A B} {f} {k : A -> option B} {a b},
  f = Some a ->
  k a = b ->
  f >>= k = b.
Proof.
  intros. subst. eauto.
Qed.

(* This lemma helps exploit an equation of the form [f >>= k = Some b]. *)

Lemma invert_bind_Some:
  forall {A B} {f} {k : A -> option B} {b},
  f >>= k = Some b ->
  exists a, f = Some a /\ k a = Some b.
Proof.
  destruct f; simpl; intros.
  { eauto. }
  { congruence. }
Qed.

Ltac invert_bind_Some :=
  match goal with
  h: ?f >>= _ = Some _ |- _ =>
    let heq := fresh in
    generalize (invert_bind_Some h); clear h; intros (?&?&h)
  end.

(* -------------------------------------------------------------------------- *)

(* The standard ordering on options, where [None] is less defined then
   everything, and every element of the form [Some a] is less defined
   than itself only. *)

Definition less_defined {A} (o1 o2 : option A) :=
  forall a, o1 = Some a -> o2 = Some a.

(* -------------------------------------------------------------------------- *)

(* This lemma exploits an assertion of the form [less_defined (Some _) _]. *)

Lemma invert_less_defined_Some:
  forall {A} {a : A} {o : option A},
  less_defined (Some a) o ->
  Some a = o.
Proof.
  unfold less_defined. intros. symmetry. eauto.
Qed.

Ltac invert_less_defined :=
  match goal with
  | h: less_defined (Some _) _ |- _ =>
      generalize (invert_less_defined_Some h); clear h; intro h
  end.

(* -------------------------------------------------------------------------- *)

(* These lemmas help prove assertions of the form [less_defined _ _]. *)

Lemma prove_less_defined_None:
  forall {A} {o : option A},
  less_defined None o.
Proof.
  unfold less_defined. intros. congruence.
Qed.

Lemma reflexive_less_defined:
  forall {A} {o : option A},
  less_defined o o.
Proof.
  unfold less_defined. eauto.
Qed.

Local Hint Extern 1 (_ <> _) => congruence : congruence.

Lemma prove_less_defined_bind:
  forall {A B} {f1 f2 : option A} {k1 k2 : A -> option B},
  less_defined f1 f2 ->
  (f1 <> None -> forall a, less_defined (k1 a) (k2 a)) ->
  less_defined (f1 >>= k1) (f2 >>= k2).
Proof.
  intros. destruct f1; simpl in *.
  (* Case: [f1] is [Some _]. *)
  { invert_less_defined. subst. simpl. eauto with congruence. }
  (* Case: [f1] is [None]. *)
  { eauto using prove_less_defined_None. }
Qed.

Global Hint Resolve
  prove_less_defined_None reflexive_less_defined prove_less_defined_bind
: less_defined.

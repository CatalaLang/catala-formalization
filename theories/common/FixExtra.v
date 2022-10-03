Require Import Coq.Logic.FunctionalExtensionality.

(* This is a simplified version of the lemma [Fix_eq], which is defined in
   [Coq.Init.Wf]. We use functional extensionality to remove one hypothesis.
   Furthermore, we introduce the auxiliary equality [f = Fix Rwf P F] so as
   to avoid duplicating the (usually large) term [F] in the right-hand side
   of the conclusion. *)

Lemma Fix_eq_simplified
  (A : Type) (R : A -> A -> Prop) (Rwf : well_founded R)
  (P : A -> Type)
  (F : forall x : A, (forall y : A, R y x -> P y) -> P x)
  (f : forall x, P x) :
  f = Fix Rwf P F ->
  forall x : A,
  f x = F x (fun (y : A) (_ : R y x) => f y).
Proof.
  intros. subst. eapply Fix_eq. intros. f_equal.
  eauto using functional_extensionality_dep, functional_extensionality.
Qed.

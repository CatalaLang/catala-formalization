Require Import Coq.Logic.ClassicalUniqueChoice.
Require Import Autosubst.Autosubst.
Require Import AutosubstExtra.

Section Lemmas.

Context {A} `{Ids A, Rename A, Subst A, SubstLemmas A}.

(* The predicate [is_ren sigma] means that the substitution [sigma] is in fact
   a renaming [ren xi]. *)

(* When stating a lemma that involves a renaming, it is preferable to use a
   substitution [sigma], together with a hypothesis [is_ren sigma], rather
   than request that [sigma] be of the form [ren xi]. This allows us to use
   [obvious] to check that [sigma] is a renaming, whereas we would otherwise
   have to manually rewrite [sigma] to the form [ren xi]. *)

Definition is_ren sigma :=
  exists xi, sigma = ren xi.

(* One way of proving that [sigma] is a renaming is to prove that [sigma] maps
   every variable [x] to a variable [y]. *)

Lemma prove_is_ren:
  forall sigma,
  (forall x y, ids x = ids y -> x = y) ->
  (forall x, exists y, sigma x = ids y) ->
  is_ren sigma.
Proof.
  (* This proof uses the axiom of unique choice. If one is willing to use
     the stronger axiom of choice, then one can remove the hypothesis that
     [ids] is injective. *)
  intros ? Hinj Hxy.
  assert (Hxi: exists xi : var -> var, forall x, sigma x = ids (xi x)).
  { eapply unique_choice with (R := fun x y => sigma x = ids y).
    intros x. destruct (Hxy x) as [ y Heqy ]. exists y.
    split.
    { assumption. }
    { intros x' Heqx'. eapply Hinj. congruence. }
  }
  destruct Hxi as [ xi ? ].
  exists xi.
  f_ext; intros x. eauto.
Qed.

(* Applying [up] or [upn i] to a renaming produces a renaming. *)

Lemma up_is_ren:
  forall sigma,
  is_ren sigma ->
  is_ren (up sigma).
Proof.
  intros ? [ xi ? ]. subst. exists (upren xi).
  erewrite <- up_ren by eauto with typeclass_instances. reflexivity.
Qed.

Lemma upn_is_ren:
  forall sigma i,
  is_ren sigma ->
  is_ren (upn i sigma).
Proof.
  intros ? ? [ xi ? ]. subst. exists (iterate upren i xi).
  erewrite <- upn_ren by eauto with typeclass_instances. reflexivity.
Qed.

(* Composing two renamings yields a renaming. *)

Lemma comp_is_ren:
  forall sigma1 sigma2,
  is_ren sigma1 ->
  is_ren sigma2 ->
  is_ren (sigma1 >> sigma2).
Proof.
  intros ? ? [ xi1 ? ] [ xi2 ? ]. subst. exists (xi1 >>> xi2). autosubst.
Qed.

Lemma is_ren_ids:
  is_ren ids.
Proof.
  exists id. autosubst.
Qed.

End Lemmas.

Global Hint Unfold is_ren : is_ren obvious.

Global Hint Resolve up_is_ren upn_is_ren comp_is_ren is_ren_ids : is_ren obvious.

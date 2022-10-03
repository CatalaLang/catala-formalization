Require Import Arith.
Require Import PeanoNat.
Require Import Psatz.
Require Import Autosubst.Autosubst.
Require Import AutosubstExtra.
Require Import Autosubst_EOS.

(* -------------------------------------------------------------------------- *)

Class IdsLemmas (term : Type) {Ids_term : Ids term} := {
  (* The identity substitution is injective. *)
  ids_inj:
    forall x y,
    ids x = ids y ->
    x = y
}.

(* -------------------------------------------------------------------------- *)

Section FreeVars.

Context
  {A : Type}
  {Ids_A : Ids A}
  {Rename_A : Rename A}
  {Subst_A : Subst A}
  {IdsLemmas_A : IdsLemmas A}
  {SubstLemmas_A : SubstLemmas A}.

(* -------------------------------------------------------------------------- *)

(* A reformulation of [ids_inj]. *)

Lemma ids_inj_False:
  forall x y,
  ids x = ids y ->
  x <> y ->
  False.
Proof.
  intros.
  assert (x = y). { eauto using ids_inj. }
  unfold var in *.
  lia.
Qed.

(* -------------------------------------------------------------------------- *)

(* The predicate [fv k t] means that the free variables of the term [t] are
   contained in the semi-open interval [0..k). *)

Definition fv k t :=
  t.[upn k (ren (+1))] = t.

(* -------------------------------------------------------------------------- *)

(* The predicate [closed t] means that the term [t] is closed, that is, [t]
   has no free variables. *)

Definition closed :=
  fv 0.

(* -------------------------------------------------------------------------- *)

(* This technical lemma states that the renaming [+1] is injective. *)

Lemma lift_inj_ids:
  forall t x,
  t.[ren (+1)] = ids (S x) <-> t = ids x.
Proof.
  split; intros.
  { eapply lift_inj. autosubst. }
  { subst. autosubst. }
Qed.

(* -------------------------------------------------------------------------- *)

(* This lemma characterizes the meaning of [fv k] when applied to a variable. *)

Lemma fv_ids_eq:
  forall k x,
  fv k (ids x) <-> x < k.
Proof.
  unfold fv. induction k; intros.
  (* Base case. *)
  { asimpl. split; intros; elimtype False.
    { eauto using ids_inj_False. }
    { lia. }
  }
  (* Step. *)
  { destruct x; asimpl.
    { split; intros. { lia. } { reflexivity. } }
    { rewrite lift_inj_ids.
      rewrite <- id_subst.
      rewrite IHk. lia. }
  }
Qed.

(* -------------------------------------------------------------------------- *)

(* A simplification lemma. *)

Lemma fv_lift:
  forall k i t,
  fv (k + i) t.[ren (+i)] <-> fv k t.
Proof.
  unfold fv. intros. asimpl.
  rewrite Nat.add_comm.
  rewrite <- upn_upn.
  erewrite plus_upn by eauto.
  rewrite <- subst_comp.
  split; intros.
  { eauto using lift_injn. }
  { f_equal. eauto. }
Qed.

(* -------------------------------------------------------------------------- *)

(* If [t] has at most [n - 1] free variables,
   and if [x] is inserted among them,
   then we get [eos x t],
   which has at most [n] free variables. *)

Lemma fv_eos:
  forall x n t,
  x < n ->
  fv (n - 1) t ->
  fv n (eos x t).
Proof.
  unfold fv. intros x n t ? ht.
  rewrite eos_eq in ht.
  rewrite eos_eq.
  rewrite eos_eos_reversed by lia. (* nice! *)
  rewrite ht.
  reflexivity.
Qed.

Lemma fv_eos_eq:
  forall x n t,
  x < n ->
  fv n (eos x t) <->
  fv (n - 1) t.
Proof.
  unfold fv. intros x n t ?.
  rewrite eos_eq.
  rewrite eos_eq.
  rewrite eos_eos_reversed by lia. (* nice! *)
  split; intros h.
  { eauto using eos_injective. }
  { rewrite h. reflexivity. }
Qed.

(* -------------------------------------------------------------------------- *)

(* A substitution [sigma] is regular if and only if, for some [j], for
   sufficiently large [x], [sigma x] is [x + j]. *)

Definition regular (sigma : var -> A) :=
  exists i j,
  ren (+i) >> sigma = ren (+j).

Lemma regular_ids:
  regular ids.
Proof.
  exists 0. exists 0. autosubst.
Qed.

Lemma regular_plus:
  forall i,
  regular (ren (+i)).
Proof.
  intros. exists 0. exists i. autosubst.
Qed.

Lemma regular_upn:
  forall n sigma,
  regular sigma ->
  regular (upn n sigma).
Proof.
  intros ? ? (i&j&hsigma).
  exists (n + i). eexists (n + j).
  replace (ren (+(n + i))) with (ren (+i) >> ren (+n)) by autosubst.
  rewrite <- (@scompA A Ids_A Rename_A Subst_A SubstLemmas_A).
  rewrite up_liftn.
  rewrite (@scompA A Ids_A Rename_A Subst_A SubstLemmas_A).
  rewrite hsigma.
  autosubst.
Qed.

(* -------------------------------------------------------------------------- *)

(* If the free variables of the term [t] are below [k], then [t] is unaffected
   by a substitution of the form [upn k sigma]. *)

(* Unfortunately, in this file, where the definition of type [A] is unknown, I
   am unable to establish this result for arbitrary substitutions [sigma]. I
   am able to establish it for *regular* substitutions, where The proof is somewhat interesting, so it is given here, even
   though, once the definition of the type [A] is known, a more direct proof,
   without a regularity hypothesis, can usually be given. *)

(* An intermediate result states that, since [upn k (ren (+1))] does not
   affect [t], then (by iteration) neither does [upn k (ren (+j))]. *)

Lemma fv_unaffected_lift:
  forall j t k,
  fv k t ->
  t.[upn k (ren (+j))] = t.
Proof.
  induction j as [| j ]; intros t k ht.
  { asimpl. rewrite up_id_n. autosubst. }
  { replace (ren (+S j)) with (ren (+1) >> ren (+j)) by autosubst.
    rewrite <- up_comp_n.
    replace (t.[upn k (ren (+1)) >> upn k (ren (+j))])
       with (t.[upn k (ren (+1))].[upn k (ren (+j))]) by autosubst.
    rewrite ht.
    rewrite IHj by eauto.
    eauto. }
Qed.

(* There follows that a substitution of the form [upn k sigma], where [sigma]
   is regular, does not affect [t]. The proof is slightly subtle but very
   short. The previous lemma is used twice. *)

Lemma fv_unaffected_regular:
  forall k t sigma,
  fv k t ->
  regular sigma ->
  t.[upn k sigma] = t.
Proof.
  intros k t sigma ? (i&j&hsigma).
  rewrite <- (fv_unaffected_lift i t k) at 1 by eauto.
  asimpl. rewrite up_comp_n.
  rewrite hsigma.
  rewrite fv_unaffected_lift by eauto.
  reflexivity.
Qed.

(* A corollary. *)

Lemma closed_unaffected_regular:
  forall t sigma,
  closed t ->
  regular sigma ->
  t.[sigma] = t.
Proof.
  unfold closed. intros.
  rewrite <- (upn0 sigma).
  eauto using fv_unaffected_regular.
Qed.

(*One might also wish to prove a result along the following lines:

  Goal
    forall t k sigma1 sigma2,
    fv k t ->
    (forall x, x < k -> sigma1 x = sigma2 x) ->
    t.[sigma1] = t.[sigma2].

  I have not yet investigated how this could be proved. *)

(* -------------------------------------------------------------------------- *)

(* If some term [t] has free variables under [j], then it also has free
   variables under [k], where [j <= k]. *)

Lemma fv_monotonic:
  forall j k t,
  fv j t ->
  j <= k ->
  fv k t.
Proof.
  intros. unfold fv.
  replace k with (j + (k - j)) by lia.
  rewrite <- upn_upn.
  eauto using fv_unaffected_regular, regular_upn, regular_plus.
Qed.

(* -------------------------------------------------------------------------- *)

(* These little lemmas may be occasionally useful. *)

Lemma use_fv_length_cons:
  forall A (x : A) (xs : list A) n t,
  (forall x, fv (length (x :: xs)) t) ->
  n = length xs ->
  fv (n + 1) t.
Proof.
  intros. subst.
  replace (length xs + 1) with (length (x :: xs)) by (simpl; lia).
  eauto.
Qed.

Lemma prove_fv_length_cons:
  forall A (x : A) (xs : list A) n t,
  n = length xs ->
  fv (n + 1) t ->
  fv (length (x :: xs)) t.
Proof.
  intros. subst.
  replace (length (x :: xs)) with  (length xs + 1) by (simpl; lia).
  eauto.
Qed.

(* -------------------------------------------------------------------------- *)

(* [closed t] is equivalent to [t.[ren (+1)] = t]. *)

Lemma closed_eq:
  forall t,
  closed t <-> t.[ren (+1)] = t.
Proof.
  unfold closed, fv. asimpl. tauto.
Qed.

(* -------------------------------------------------------------------------- *)

(* A variable is not closed. *)

Lemma closed_ids:
  forall x,
  ~ closed (ids x).
Proof.
  unfold closed, fv. intros. asimpl. intro.
  eauto using ids_inj_False.
Qed.

End FreeVars.

(* -------------------------------------------------------------------------- *)

(* The tactic [fv] is intended to use a number of lemmas as rewriting rules.
   The hint database [fv] can be extended with language-specific lemmas. *)

Hint Rewrite @fv_ids_eq @fv_lift @fv_eos_eq : fv.

Ltac fv :=
  autorewrite with fv in *;
  eauto with typeclass_instances.

(* -------------------------------------------------------------------------- *)

(* A hint database to prove goals of the form [~ (closed _)] or [closed _]. *)

Global Hint Resolve closed_ids : closed.

(* -------------------------------------------------------------------------- *)

Global Hint Resolve regular_ids regular_plus regular_upn : regular.

Require Import Autosubst.Autosubst.
Require Import Psatz.

(* -------------------------------------------------------------------------- *)

(* Basic lemmas. *)

Lemma iterate_iterate {A} (f : A -> A) i j x :
  iterate f i (iterate f j x) = iterate f (i + j) x.
Proof.
  induction i; intros.
  { now rewrite iterate_0. }
  { now rewrite plusSn, iterate_S, IHi. }
Qed.

(* -------------------------------------------------------------------------- *)

(* A more recognizable notation for lifting. *)

Notation lift i t := (t.[ren(+i)]).

(* -------------------------------------------------------------------------- *)

Section Extras.

Context A `{Ids A, Rename A, Subst A, SubstLemmas A}.

Lemma upn_upn:
  forall i j sigma,
  upn i (upn j sigma) = upn (i + j) sigma.
Proof using .
  eauto using iterate_iterate.
Qed.

Lemma lift_injn_eq:
  forall (a b : A),
  forall n,
  a.[ren(+n)] = b.[ren(+n)] <-> a = b.
Proof.
  split; intros; subst; eauto using lift_injn.
Qed.

Lemma up_ren:
  forall xi,
  ren (upren xi) = up (ren xi).
Proof.
  intros. autosubst.
Qed.

Lemma scompA:
  forall f g h,
  f >> (g >> h) = f >> g >> h.
Proof.
  intros. unfold scomp. now rewrite <- subst_compX, compA.
Qed.

Lemma upn_ren:
  forall i xi,
  ren (iterate upren i xi) = upn i (ren xi).
Proof.
  induction i; intros.
  { reflexivity. }
  { rewrite <- fold_up_upn. rewrite <- IHi. asimpl. reflexivity. }
Qed.

Lemma plus_upn: (* close to [up_liftn] *)
  forall i sigma,
  (+i) >>> upn i sigma = sigma >> ren (+i).
Proof.
  induction i; intros.
  { rewrite iterate_0. autosubst. }
  { rewrite iterate_S. asimpl. rewrite IHi. autosubst. }
Qed.

Lemma up_sigma_up_ren:
  forall t i sigma,
  t.[up sigma].[up (ren (+i))] = t.[up (ren (+i))].[upn (1 + i) sigma].
Proof.
  intros. asimpl. rewrite plus_upn. asimpl. reflexivity.
Qed.

Lemma upn_k_sigma_x:
  forall k sigma x,
  x < k ->
  upn k sigma x = ids x.
Proof.
  induction k; intros; asimpl.
  { lia. }
  { destruct x; asimpl.
    { eauto. }
    { rewrite IHk by lia. autosubst. }
  }
Qed.

Lemma push_substitution_last:
  forall t v i,
  t.[v .: ren (+i)] = t.[up (ren (+i))].[v/].
Proof.
  intros. autosubst.
Qed.

Lemma push_substitution_last_up_hoist:
  forall t v i j,
  t.[up (v .: ren (+i))].[up (ren (+j))] =
  t.[up (up (ren (+j + i)))].[up (lift j v .: ids)].
Proof.
  intros. autosubst.
Qed.

Lemma lift_lift:
  forall i j t,
  lift i (lift j t) = lift (i + j) t.
Proof.
  intros. autosubst.
Qed.

Lemma lift_upn:
  forall t i sigma,
  (lift i t).[upn i sigma] = lift i t.[sigma].
Proof.
  intros. asimpl.
  erewrite plus_upn.
  reflexivity.
Qed.

Lemma lift_up:
  forall t sigma,
  (lift 1 t).[up sigma] = lift 1 t.[sigma].
Proof.
  intros. change up with (upn 1). eapply lift_upn.
Qed.

Lemma up_sigma_f:
  forall (sigma : var -> A) (f : A -> A),
  f (ids 0) = ids 0 ->
  (forall i t, lift i (f t) = f (lift i t)) ->
  up (sigma >>> f) = up sigma >>> f.
Proof.
  intros. f_ext. intros [|x]; asimpl; eauto.
Qed.

Lemma upn_sigma_f:
  forall (sigma : var -> A) (f : A -> A),
  f (ids 0) = ids 0 ->
  (forall i t, lift i (f t) = f (lift i t)) ->
  forall i,
  upn i (sigma >>> f) = upn i sigma >>> f.
Proof.
  induction i; intros.
  { reflexivity. }
  { do 2 rewrite <- fold_up_upn. rewrite IHi. erewrite up_sigma_f by eauto. reflexivity. }
Qed.

Lemma upn_theta_sigma_ids:
  forall theta sigma i,
  theta >> sigma = ids ->
  upn i theta >> upn i sigma = ids.
Proof.
  intros theta sigma i Hid.
  rewrite up_comp_n.
  rewrite Hid.
  rewrite up_id_n.
  reflexivity.
Qed.

Lemma up_theta_sigma_ids:
  forall theta sigma,
  theta >> sigma = ids ->
  up theta >> up sigma = ids.
Proof.
  change up with (upn 1). eauto using upn_theta_sigma_ids.
Qed.

Lemma scons_scomp:
  forall (T : A) Gamma theta,
  T.[theta] .: (Gamma >> theta) = (T .: Gamma) >> theta.
Proof.
  intros. autosubst.
Qed.

(* BUG: the two sides of this equation are distinct, yet they are
   printed identically. *)

Goal
  forall v f,
  v .: (ids >>> f) = (v .: ids) >>> f.
Proof.
  intros.
  Fail reflexivity.
Abort.

End Extras.

(* This incantation means that [eauto with autosubst] can use the tactic
   [autosubst] to prove an equality. *)

Global Hint Extern 1 (_ = _) => autosubst : autosubst.

(* This incantation means that [eauto with autosubst] can use the lemmas
   whose names are listed here. This is useful when an equality involves
   metavariables, so the tactic [autosubst] fails. *)

Global Hint Resolve scons_scomp : autosubst.



(* -------------------------------------------------------------------------- *)
(* 
(* Autosubst support for coq-elpi *)

From elpi Require Import derive.std.
Set Uniform Inductive Parameters.


Definition annotation (T2: Type) (n: nat) := T2.



derive annotation.



Definition is_annotation_functor
	 : 
       forall (T2 : Type) (P2a P2b : T2 -> Type),
       (forall x : T2, P2a x -> P2b x) ->
       forall (n : nat) (Pn : is_nat n) (x : annotation T2 n),
       is_annotation  T2 P2a n Pn x -> is_annotation T2 P2b n Pn x
. trivial. Defined.


Elpi Accumulate derive lp:{{
  param1-functor-db {{ is_annotation lp:T lp:P }} {{ is_annotation lp:T lp:Q }}
                    {{ is_annotation_functor lp:T lp:P lp:Q lp:H }} :-
                    param1-functor-db P Q H.
}}.

Inductive term :=
| Dummy (x: bool)
| Lam (t: annotation term 1).

#[verbose,recursive,only(induction)] derive term.
 *)

(* -------------------------------------------------------------------------- *)
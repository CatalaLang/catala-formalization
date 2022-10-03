Require Import List.
Require Import MyTactics.
Require Import MySequences.
Require Import LCSyntax.
Require Import LCFreeVars.
Require Import LCValues.
Require Import LCReduction.

(* -------------------------------------------------------------------------- *)
(* -------------------------------------------------------------------------- *)

(* A big-step call-by-value semantics. *)

Inductive bigcbv : term -> term -> Prop :=
| BigcbvValue:
    forall v,
    is_value v ->
    bigcbv v v
| BigcbvApp:
    forall t1 t2 u1 v2 v,
    bigcbv t1 (Lam u1) ->
    bigcbv t2 v2 ->
    bigcbv u1.[v2/] v ->
    bigcbv (App t1 t2) v
| BigcbvLet:
    forall t1 t2 v1 v,
    bigcbv t1 v1 ->
    bigcbv t2.[v1/] v ->
    bigcbv (Let t1 t2) v
| BigcbvMatchNone:
  forall tc t1 v1 t2,
  bigcbv tc VariantNone ->
  bigcbv t1 v1 ->
  bigcbv (Match tc t1 t2) v1
| BigcbvMatchSome:
  forall tc t1 t2 vc v2,
  is_value vc ->
  bigcbv tc (VariantSome vc) ->
  bigcbv t2.[vc/]  v2 ->
  bigcbv (Match tc t1 t2) v2
| BigcbvSome:
  forall t v,
  bigcbv t v ->
  bigcbv (VariantSome t) (VariantSome v)
.

Global Hint Constructors bigcbv : bigcbv.

(* The tactic [invert_bigcbv] looks for a hypothesis of the form [bigcbv t v]
   and inverts it. *)

Ltac invert_bigcbv :=
  pick bigcbv invert;
  try solve [ false; eauto 3 with obvious ].

(* -------------------------------------------------------------------------- *)

(* If [bigcbv t v] holds, then [v] must be a value. *)

Lemma bigcbv_is_value:
  forall t v,
  bigcbv t v ->
  is_value v.
Proof.
  induction 1; eauto.
Qed.

Global Hint Resolve bigcbv_is_value : is_value obvious.

(* -------------------------------------------------------------------------- *)

(* If [t] evaluates to [v] according to the big-step semantics,
   then [t] reduces to [v] according to the small-step semantics. *)

Lemma bigcbv_star_cbv:
  forall t v,
  bigcbv t v ->
  star cbv t v.
Proof.
  (* A detailed proof: *)
  induction 1.
  (* BigcbvValue *)
  { eapply star_refl. }
  (* BigcbvApp *)
  { eapply star_trans. obvious.
    eapply star_trans. obvious.
    eapply star_step. obvious.
    eauto. }
  (* BigcbvLet *)
  { eapply star_trans. obvious.
    eapply star_step. obvious.
    eauto. }
  {
    eapply star_trans with (Match VariantNone t1 t2).
    { clear -IHbigcbv1. induction IHbigcbv1.
      * eapply star_refl.
      * eapply star_step; obvious.
    }
    eapply star_step. obvious.
    eauto.
  }
  {
    eapply star_trans with (Match (VariantSome vc) t1 t2).
    { clear -IHbigcbv1. induction IHbigcbv1;
      eauto with sequences obvious.
    }
    eapply star_step. obvious.
    eauto.
  }
  {
    { clear -IHbigcbv. induction IHbigcbv;
      eauto with sequences obvious. }
  }
  (* A much shorter proof: *)
  (* induction 1; eauto 6 with sequences obvious. *)
Qed.

(* Conversely, if [t] reduces to [v] in the small-step semantics,
   then [t] evaluates to [v] in the big-step semantics. *)

Lemma cbv_bigcbv_bigcbv:
  forall t1 t2,
  cbv t1 t2 ->
  forall v,
  bigcbv t2 v ->
  bigcbv t1 v.
Proof.

  (* A detailed proof: *)
  induction 1; intros; subst; try solve [ false; tauto ].
  (* BetaV *)
  { econstructor; eauto with bigcbv. }
  (* LetV *)
  { econstructor; eauto with bigcbv. }
  (* AppL *)
  { invert_bigcbv. eauto with bigcbv. }
  (* AppR *)
  { invert_bigcbv. eauto with bigcbv. }
  (* LetL *)
  { invert_bigcbv. eauto with bigcbv. }
  (* IteTrue *)
  { eapply BigcbvMatchNone; eauto with bigcbv. }
  (* IteFalse *)
  { eapply BigcbvMatchSome; eauto with bigcbv. }
  { invert_bigcbv; eauto with bigcbv. }
  { invert_bigcbv; eauto with bigcbv. }
(* (* Restart. *)
  (* A shorter proof: *)
  induction 1; intros; subst; try solve [ false; tauto
  | econstructor; eauto with bigcbv
  | invert_bigcbv; eauto with bigcbv
  ]. *)
Qed.

Lemma star_cbv_bigcbv:
  forall t v,
  star cbv t v ->
  is_value v ->
  bigcbv t v.
Proof.
  induction 1; eauto using cbv_bigcbv_bigcbv with bigcbv.
Qed.

(* In conclusion, we have the following equivalence: *)

Lemma star_cbv_bigcbv_eq:
  forall t v,
  (star cbv t v /\ is_value v) <-> bigcbv t v.
Proof.
  split; intros; unpack;
  eauto using star_cbv_bigcbv, bigcbv_star_cbv with is_value.
Qed.

(* -------------------------------------------------------------------------- *)
(* -------------------------------------------------------------------------- *)

(* Suppose the big-step semantics [bigcbv] is taken as the primary definition
   of the meaning of terms. Then, in terms of [bigcbv], we can define a
   relation [sim] between terms, which has the flavor of a small-step
   reduction relation. *)

(* The definition is as follows: if, whenever [u] can produce the value [v],
   [t] can produce [v] as well, then [t] simulates [u]. *)

Definition sim t u :=
  forall v,
  bigcbv u v ->
  bigcbv t v.

(* This simulation relation is reflexive and transitive, hence a preorder. *)

Lemma reflexive_sim:
  forall t,
  sim t t.
Proof.
  unfold sim. eauto.
Qed.

Lemma transitive_sim:
  forall t1 t2 t3,
  sim t1 t2 ->
  sim t2 t3 ->
  sim t1 t3.
Proof.
  unfold sim. eauto.
Qed.

Global Hint Resolve reflexive_sim transitive_sim : sim.

(* This simulation relation includes the small-step relation [cbv]. *)

Lemma cbv_sim:
  forall t u,
  cbv t u ->
  sim t u.
Proof.
  (* This is a direct consequence of the fact that the composition
     [cbv . bigcbv] is a subset of [bigcbv] -- a fact that was proved above. *)
  unfold sim. eauto using cbv_bigcbv_bigcbv.
Qed.

(* As a consequence, [star cbv] is also a subset of [sim]. *)

Lemma star_cbv_sim:
  forall t u,
  star cbv t u ->
  sim t u.
Proof.
  induction 1; eauto using cbv_sim with sim.
Qed.

(* The converse is not true. Clearly, [star cbv] forbids all reductions under
   a lambda-abstraction, whereas (somewhat nonobviously) [sim] allows certain
   reductions under lambda-abstractions: intuitively, it allows all necessary
   reductions, in a certain sense (?). *)

(* For this reason, [sim] can be more comfortable to work with than [star cbv].
   The proof of correctness of the CPS transformation in CPSCorrectnessBigStep
   provides an example. *)

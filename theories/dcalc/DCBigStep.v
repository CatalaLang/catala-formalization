Require Import List.
Require Import MyTactics.
Require Import MySequences.
Require Import DCSyntax.
Require Import DCFreeVars.
Require Import DCValues.
Require Import DCValuesRes.
Require Import DCReduction.

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
  ~ is_error v2 ->
  bigcbv u1.[v2/] v ->
  bigcbv (App t1 t2) v
| BigcbvAppConflict1:
  forall t1 t2,
  bigcbv t1 Conflict ->
  bigcbv (App t1 t2) Conflict
| BigcbvAppConflict2:
  forall t1 t2 u1,
  bigcbv t1 (Lam u1) ->
  bigcbv t2 Conflict ->
  bigcbv (App t1 t2) Conflict
| BigcbvAppEmpty1:
  forall t1 t2,
  bigcbv t1 Empty ->
  bigcbv (App t1 t2) Empty
| BigcbvAppEmpty2:
  forall t1 t2 u1,
  bigcbv t1 (Lam u1) ->
  bigcbv t2 Empty ->
  bigcbv (App t1 t2) Empty
| BigcbvDefaultJTrue:
  forall ts vs tj tc v,
  List.Forall2 bigcbv ts vs ->
  List.Forall (eq Empty) vs ->
  bigcbv tj (Const true) ->
  bigcbv tc v ->
  bigcbv (Default ts tj tc) v
| BigcbvDefaultJFalse:
  forall ts vs tj tc,
  List.Forall2 bigcbv ts vs ->
  List.Forall (eq Empty) vs ->
  bigcbv tj (Const false) ->
  bigcbv (Default ts tj tc) Empty
| BigcbvDefaultV:
  forall ts vs vs1 v vs2 tj tc,
  vs = vs1 ++ v :: vs2 ->
  List.Forall2 bigcbv ts vs ->
  List.Forall (eq Empty) vs1 ->
  List.Forall (eq Empty) vs2 ->
  v <> Empty ->
  bigcbv (Default ts tj tc) v
| BigcbvDefaultConflict:
  forall ts vs vs1 v1 vs2 v2 vs3 tj tc,
  vs = vs1 ++ v1 :: vs2 ++ v2 :: vs3 ->
  List.Forall2 bigcbv ts vs ->
  v1 <> Empty ->
  v2 <> Empty ->
  bigcbv (Default ts tj tc) Conflict
.

Check bigcbv_ind.

Theorem bigcbv_ind'
: forall P : term -> term -> Prop,
(forall v : term, is_value v -> P v v) ->
(forall (t1 t2 : term) (u1 : {bind term}) (v2 v : term),
 bigcbv t1 (Lam u1) ->
 P t1 (Lam u1) ->
 bigcbv t2 v2 ->
 P t2 v2 ->
 ~ match v2 with
   | Empty | Conflict => True
   | _ => False
   end -> bigcbv u1.[v2/] v -> P u1.[v2/] v -> P (App t1 t2) v) ->
(forall t1 t2 : term,
 bigcbv t1 Conflict -> P t1 Conflict -> P (App t1 t2) Conflict) ->
(forall (t1 t2 : term) (u1 : {bind term}),
 bigcbv t1 (Lam u1) ->
 P t1 (Lam u1) ->
 bigcbv t2 Conflict -> P t2 Conflict -> P (App t1 t2) Conflict) ->
(forall t1 t2 : term,
 bigcbv t1 Empty -> P t1 Empty -> P (App t1 t2) Empty) ->
(forall (t1 t2 : term) (u1 : {bind term}),
 bigcbv t1 (Lam u1) ->
 P t1 (Lam u1) -> bigcbv t2 Empty -> P t2 Empty -> P (App t1 t2) Empty) ->
(forall (ts vs : list term) (tj tc v : term),
 Forall2 bigcbv ts vs ->
 Forall2 P ts vs ->
 Forall (eq Empty) vs ->
 bigcbv tj (Const true) ->
 P tj (Const true) -> bigcbv tc v -> P tc v -> P (Default ts tj tc) v) ->
(forall (ts vs : list term) (tj tc : term),
 Forall2 bigcbv ts vs ->
 Forall2 P ts vs ->
 Forall (eq Empty) vs ->
 bigcbv tj (Const false) ->
 P tj (Const false) -> P (Default ts tj tc) Empty) ->
(forall (ts vs vs1 : list term) (v : term) 
   (vs2 : list term) (tj tc : term),
 vs = vs1 ++ v :: vs2 ->
 Forall2 bigcbv ts vs ->
 Forall2 P ts vs ->
 Forall (eq Empty) vs1 ->
 Forall (eq Empty) vs2 -> v <> Empty -> P (Default ts tj tc) v) ->
(forall (ts vs vs1 : list term) (v1 : term) 
   (vs2 : list term) (v2 : term) (vs3 : list term) 
   (tj tc : term),
 vs = vs1 ++ v1 :: vs2 ++ v2 :: vs3 ->
 Forall2 bigcbv ts vs ->
 Forall2 P ts vs ->
 v1 <> Empty -> v2 <> Empty -> P (Default ts tj tc) Conflict) ->
forall t t0 : term, bigcbv t t0 -> P t t0.
Admitted.


Global Hint Constructors bigcbv : bigcbv.

(* The tactic [invert_bigcbv] looks for a hypothesis of the form [bigcbv t v]
   and inverts it. *)

Ltac invert_bigcbv :=
  pick bigcbv invert;
  try solve [ false; eauto 3 with obvious ].

(* -------------------------------------------------------------------------- *)

(* If [bigcbv t v] holds, then [v] must be a value. *)

Lemma is_value_res_bigcbv:
  forall t, is_value_res t -> bigcbv t t.
Proof.
  intros t Ht.
  eapply BigcbvValue.
  induction t; simpl in *; eauto.
Qed.

Lemma bigcbv_is_value:
  forall t v,
  bigcbv t v ->
  is_value v.
Proof.
  induction 1 using bigcbv_ind'; subst; inverts_Forall; simpl; eauto.
Qed.

Lemma bigcbv_is_value_refl:
  forall t v,
  bigcbv t v ->
  is_value t ->
  t = v.
Proof.
  induction 1 using bigcbv_ind'; intros; simpl in *; tryfalse; eauto.
Qed.

 

Global Hint Resolve bigcbv_is_value is_value_res_bigcbv bigcbv_is_value_refl: is_value obvious.

(* -------------------------------------------------------------------------- *)

(* If [t] evaluates to [v] according to the big-step semantics,
   then [t] reduces to [v] according to the small-step semantics. *)

Lemma bigcbv_star_cbv:
  forall t v,
  bigcbv t v ->
  star cbv t v.
Proof.
(* 
  (* A detailed proof: *)
  induction 1.
  (* BigcbvValue *)
  { eapply star_refl. }
  (* BigcbvApp *)
  { eapply star_trans with (App (Lam u1) v2). obvious.
    eapply star_trans with (App (Lam u1) t2). obvious.
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
  } *)
  (* A much shorter proof: *)
  induction 1 using bigcbv_ind'; eauto 6 with sequences obvious.
  * eapply star_trans with (App (Lam u1) t2). {
      eapply star_cbv_AppL; eauto.
      eapply star_cbv_is_error; eauto.
    }
    eapply star_trans with (App (Lam u1) v2). { obvious. }
    eapply star_step. { eapply RedBetaV; asimpl; obvious. induction v2; eauto. }
    eauto.
  * admit. (* incorrect rules *)
  * admit. (* incorrect rules *)
  * admit. (* incorrect rules *)
  * admit. (* incorrect rules *) 
  * (* i need some external lemmas here. *) 
    admit.
  * admit.
  * admit.
  * admit.
Admitted.

(* Conversely, if [t] reduces to [v] in the small-step semantics,
   then [t] evaluates to [v] in the big-step semantics. *)


Lemma is_value_res_is_value:
  forall v,
  is_value_res v -> is_value v.
Proof.
  induction v; simpl in *; eauto.
Qed.

Global Hint Resolve is_value_res_is_value: is_value is_value_res obvious.

Lemma cbv_bigcbv_bigcbv:
  forall t1 t2,
  cbv t1 t2 ->
  forall v,
  bigcbv t2 v ->
  bigcbv t1 v.
Proof.
  (* A shorter proof: *)
  induction 1; intros; subst; try solve [ false; tauto
  | econstructor; eauto with bigcbv
  | invert_bigcbv; eauto with bigcbv
  ].
  * eapply BigcbvApp; eauto using bigcbv.
    induction v; simpl in *; eauto.
  * admit.
  * admit.
  * inverts_Forall.
    assert (is_value Conflict). { simpl; eauto. }
    assert (v = Conflict). { symmetry; eapply bigcbv_is_value_refl; eauto. } subst.
    eapply BigcbvDefaultConflict.
    4: exact H2.
    3: exact H1.
    1: {
      assert (Heq: ts1 ++ ti :: ts2 ++ tj :: ts3 = ts1 ++ ti :: ts2 ++ tj :: ts3). { reflexivity. }
      apply Heq.
    }

    repeat match goal with
    | [ |- List.Forall2 _ ( _ ++ _ ) (_ ++ _)] => eapply Forall2_app
    | [ |- List.Forall2 _ ( _ :: _ ) (_ :: _)] => eapply Forall2_cons
    end.

    all: try eauto with obvious.

    all: match goal with [ |- List.Forall2 bigcbv ?ts _ ] =>
    induction ts; econstructor; inverts_Forall; eauto with obvious end.
  * eapply BigcbvDefaultV.
    { assert (Heq: ts1 ++ v :: ts2 = ts1 ++ v :: ts2). { reflexivity. }
      eapply Heq.
    }
    {
      repeat match goal with
      | [ |- List.Forall2 _ ( _ ++ _ ) (_ ++ _)] => eapply Forall2_app
      | [ |- List.Forall2 _ ( _ :: _ ) (_ :: _)] => eapply Forall2_cons
      end.

      all: try eauto with obvious.

      all: match goal with [ |- List.Forall2 bigcbv ?ts _ ] =>
      induction ts; econstructor; inverts_Forall; eauto with obvious end.
    }
    all: eauto.

    assert (Heq: ti = v).
    { eapply bigcbv_is_value_refl; eauto with obvious. }
    rewrite <- Heq; eauto.
  * assert (forall ts ts' vs tj tc v,
      bigcbv (Default ts tj tc) v ->
      List.Forall2 bigcbv ts vs ->
      List.Forall2 bigcbv ts' vs ->
      bigcbv (Default ts' tj tc) v
    ).
    { 
      inversion 1; intros; simpl in *; tryfalse; subst; admit.
    }
    eapply H3.
    eapply H2.
    inverts H2; tryfalse.
    { inverts_Forall.
      repeat match goal with
      | [ |- List.Forall2 _ ( _ ++ _ ) _] => eapply Forall2_app
      | [ |- List.Forall2 _ ( _ :: _ ) _] => eapply Forall2_cons
      end.
      - eapply H4.
      eauto.

    }

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
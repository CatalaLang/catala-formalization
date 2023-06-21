Require Import MyTactics.
Require Import DCSyntax.

(* This technical lemma states that the renaming [lift 1] is injective. *)

Lemma lift_inj_Var:
  forall t x,
  lift 1 t = Var (S x) <-> t = Var x.
Proof.
  split; intros.
  { eauto using lift_inj. }
  { subst. eauto. }
Qed.

(* -------------------------------------------------------------------------- *)

(* The predicate [fv] is characterized by the following lemmas. *)

Lemma fv_Var_eq:
  forall k x,
  fv k (Var x) <-> x < k.
Proof.
  unfold fv. asimpl. induction k; intros.
  (* Base case. *)
  { asimpl. split; intros; false.
    { unfold ids, Ids_term in *. injections.
      (* In Coq 8.12, this goal is solved by [lia], but not in Coq 8.10. *)
      eapply Nat.neq_succ_diag_l. eauto. }
    { lia. }
  }
  (* Step. *)
  { destruct x; asimpl.
    { split; intros. { lia. } { reflexivity. } }
    rewrite lift_inj_Var. rewrite IHk. lia. }
Qed.

Lemma fv_Lam_eq:
  forall k t,
  fv k (Lam t) <-> fv (S k) t.
Proof.
  unfold fv. intros. asimpl. split; intros.
  { injections. eauto. }
  { unpack. congruence. }
Qed.

Lemma fv_App_eq:
  forall k t1 t2,
  fv k (App t1 t2) <-> fv k t1 /\ fv k t2.
Proof.
  unfold fv. intros. asimpl. split; intros.
  { injections. eauto. }
  { unpack. congruence. }
Qed.

(* Lemma fv_BinOp_eq:
  forall k op t1 t2,
  fv k (BinOp op t1 t2) <-> fv k t1 /\ fv k t2.
Proof.
  unfold fv. intros. asimpl. split; intros.
  { injections. eauto. }
  { unpack. congruence. }
Qed. *)

Lemma thing: forall ts sigma,
  ts..[sigma] = ts <-> List.Forall (fun ti : term => ti.[sigma] = ti) ts.
Proof.
  induction ts.
  * split; intros; eauto.
  * split; intros; msimpl in *.
    - injections.
      econstructor; eauto.
      { apply IHts. eauto. }
    - inverts H.
      f_equal; [eauto | now eapply IHts].
Qed.

Lemma fv_Default_eq:
  forall k ts tj tc,
  fv k (Default ts tj tc) <->
    (List.Forall (fun ti => fv k ti) ts) /\ fv k tj /\ fv k tc.
Proof.
  unfold fv. intros. asimpl. split; intros.
  { injections. repeat split; eauto.
    { apply thing; assumption. }
  }
  { unpack. rewrite H0; rewrite H1.
    remember (thing ts (upn k (ren (+1)))).
    destruct i.
    remember (e H).
    rewrite e0.
    reflexivity. }
Qed.

Global Hint Rewrite fv_Var_eq fv_Lam_eq fv_App_eq (* fv_BinOp_eq *) fv_Default_eq : fv.

(* -------------------------------------------------------------------------- *)

(* The following lemmas allow decomposing a closedness hypothesis.
   Because [closed] is not an inductive notion, there is no lemma
   for [Lam] and for the right-hand side of [Let]. *)

Lemma closed_Var:
  forall x,
  closed (Var x) ->
  False.
Proof.
  unfold closed; intros; fv. lia.
Qed.

Lemma closed_AppL:
  forall t1 t2,
  closed (App t1 t2) ->
  closed t1.
Proof.
  unfold closed; intros; fv. tauto.
Qed.

(* Lemma closed_BinOpR:
  forall op t1 t2,
  closed (BinOp op t1 t2) ->
  closed t2.
Proof.
  unfold closed; intros; fv. tauto.
Qed.

Lemma closed_BinOpL:
  forall op t1 t2,
  closed (BinOp op t1 t2) ->
  closed t1.
Proof.
  unfold closed; intros; fv. tauto.
Qed. *)

Lemma closed_AppR:
  forall t1 t2,
  closed (App t1 t2) ->
  closed t2.
Proof.
  unfold closed; intros; fv. tauto.
Qed.


Lemma closed_DefaultJ:
  forall ts tj tc, 
  closed (Default ts tj tc) ->
  closed tj.
Proof.
  unfold closed; intros; fv. tauto.
Qed.

Lemma closed_DefaultC:
  forall ts tj tc, 
  closed (Default ts tj tc) ->
  closed tc.
Proof.
  unfold closed; intros; fv. tauto.
Qed.

Lemma closed_DefaultE:
  forall ts tj tc,
  closed (Default ts tj tc) ->
  List.Forall (fun ti => closed ti) ts.
Proof.
  unfold closed; intros; fv. tauto.
Qed.

Lemma closed_DefaultE0:
  forall ti ts tj tc,
  closed (Default (ti::ts) tj tc) ->
  closed ti.
Proof.
  unfold closed; intros; fv.
  destruct H as [H1 [H2 H3]].
  now invert H1.
Qed.

Lemma closed_DefaultEi:
  forall ts1 ti ts2 tj tc,
  closed (Default (ts1++ti::ts2) tj tc) ->
  closed ti.
Proof.
  unfold closed; intros; fv.
  destruct H as [H1 [H2 H3]].
  eapply List.Forall_elt; eauto.
Qed.


Lemma closed_DefaultEin:
  forall ti ts tj tc,
  List.In ti ts ->
  closed (Default ts tj tc) ->
  closed ti.
Proof.
  unfold closed; intros ti ts tj tc Hin H; fv.
  destruct H as [H1 [H2 H3]].
  eapply List.Forall_forall; eauto.
Qed.


Global Hint Resolve
  closed_Var
  closed_AppL
  closed_AppR
  closed_DefaultC
  closed_DefaultJ
  closed_DefaultE
  closed_DefaultE0
  closed_DefaultEi
  closed_DefaultEin
  (* closed_BinOpR
  closed_BinOpL *)
: closed.

(* -------------------------------------------------------------------------- *)

(* If the free variables of the term [t] are below [k], then [t] is unaffected
   by a substitution of the form [upn k sigma]. *)

Lemma fv_unaffected:
  forall t k sigma,
  fv k t ->
  t.[upn k sigma] = t.
Proof.
  induction t using term_ind'; intros; fv; unpack; asimpl;
  try solve [ eauto using upn_k_sigma_x with typeclass_instances
            | f_equal; eauto ].
  { f_equal; eauto using upn_k_sigma_x with typeclass_instances.
    { apply thing.
      induction ts; econstructor.
      * rename a into ti.
        inverts H0; inverts H.
        eauto.
      * inverts H0; inverts H.
        eapply IHts; eauto.
    }
  }
Qed.
  
(* If the term [t] is closed, then [t] is unaffected by any substitution. *)

Lemma closed_unaffected:
  forall t sigma,
  closed t ->
  t.[sigma] = t.
Proof.
  intros. eapply fv_unaffected with (k := 0). eauto.
Qed.

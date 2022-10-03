Require Import MyTactics.
Require Import LCSyntax.
Require Import LCValues.
Require Import LCReduction.
Require Import Arith.

(*|

-----
Types
-----

Here is the syntax of simple types:

|*)

Inductive ty :=
| TyVar (x : var)
| TyFun (A B : ty)
| TyOption (T: ty).

Fixpoint size (T: ty) { struct T } :=
  match T with
  | TyVar _ => 0
  | TyFun A B => 1 + size A + size B
  | TyOption A => 1 + size A
  end
.

(*|

A type environment is viewed as a total function of variables to types.

In principle, an environment should be modeled as a list of types, which
represents a partial function of variables to types. This introduces a few
complications, and is left as an exercise for the reader.

|*)

Definition tyenv := var -> ty.

(*|

--------------------
The typing judgement
--------------------

The simply-typed lambda-calculus is defined by the following three
typing rules.

|*)

Inductive jt : tyenv -> term -> ty -> Prop :=
| JTVar:
    forall Gamma x T,
    Gamma x = T ->
    jt Gamma (Var x) T
| JTLam:
    forall Gamma t T U,
    jt (T .: Gamma) t U ->
    jt Gamma (Lam t) (TyFun T U)
| JTApp:
    forall Gamma t1 t2 T U,
    jt Gamma t1 (TyFun T U) ->
    jt Gamma t2 T ->
    jt Gamma (App t1 t2) U
| JtNone:
  forall Gamma T,
  jt Gamma VariantNone (TyOption T)
| JtSome:
  forall Gamma t T,
  jt Gamma t T ->
  jt Gamma (VariantSome t) (TyOption T)
| JtMatch:
  forall Gamma tc t1 t2 T U,
  jt Gamma tc (TyOption U) ->
  jt Gamma t1 T ->
  jt ( U .: Gamma) t2 T ->
  jt Gamma (Match tc t1 t2) T
.


Lemma empty_is_sound:
  forall t T Gamma,
  jt Gamma t T -> 
  forall k,
  fv k t ->
  forall Gamma',
  (forall i, i < k  -> Gamma' i = Gamma i) -> jt Gamma' t T.
Proof.
  intros t T Gamma H; induction H; intros.
  * econstructor.
    rewrite H1; eauto.
    fv.
  * econstructor.
    eapply IHjt.
    fv.
    induction i; eauto.
    simpl; intros. apply H1. lia.
  * econstructor; fv; unpack.
    - eapply IHjt1; eauto.
    - eapply IHjt2; eauto.
  * admit.
  * admit.
  * admit.
Admitted.

Lemma jt_determ:
  forall Gamma x T,
  jt Gamma (Var x) T ->
  forall U,
  jt Gamma (Var x) U ->
  T = U.
Proof.
  intros Gamma t x Hjtx.
  inverts Hjtx.
  intros.
  now inverts H.
Qed.


Lemma exists_diff (T: ty):
  exists U, T <> U.
Proof.
  exists (TyFun T T).
  remember (size T).
  assert (size T <> 1 + size T + size T).
  { lia. }
  intro.
  eapply H.
  rewrite H0 at 1. simpl; eauto.
Qed.


Require Import PeanoNat.
Require Import Bool.

Lemma reflect_lt_ltb:
  forall n m, reflect (n < m) (n <? m).
Proof.
  intros.
  remember (n <? m).
  induction b; econstructor.
  * eapply Nat.ltb_lt; eauto.
  * eapply Nat.ltb_nlt; eauto.
Qed.



(*|

The tactic [pick_jt t] picks a hypothesis [h] whose statement is a typing
judgement about the term [t], and passes [h] to the Ltac continuation [k].

Thus, for instance, [pick_jt t invert] selects a typing judgement that is
at hand for the term [t] and inverts it.

|*)

Ltac pick_jt t k :=
  match goal with h: jt _ t _ |- _ => k h end.

(*|

The following hint allows `eauto with jt` to apply the above typing rules.

|*)

Global Hint Constructors jt : jt.

Require Import FunctionalExtensionality.

Lemma empty_is_complete:
forall t T Gamma,
  jt Gamma t T -> 
  forall k,
  (forall Gamma', (forall i, i < k  -> Gamma' i = Gamma i) -> jt Gamma' t T) ->
  fv k t.
Proof. (*| Let's start the proof. |*)
  introv Hjt.
  induction Hjt.
  * introv Hsame; fv.
    (*| Case JtVar. Either x < k or x >= k. In the first case, we are ok. In the second one, we build Gamma' as (fun i => if i <? k then Gamma i else U) where U is an element such that U <> T. |*)
    destruct reflect_lt_ltb with x k.
    - eauto.
    - false.
      forwards [U HU]: exists_diff T.
      eapply HU.
      eapply jt_determ with (fun i => if i <? k then Gamma i else U) x.
      + eapply Hsame.
        { intros.
          replace (i <? k) with true; eauto.
            { symmetry. destruct Nat.ltb_lt with i k. eauto. }
        }
      + econstructor.
        replace (x <? k) with false; eauto.
          { symmetry. eapply Nat.ltb_nlt. eauto. }
  * (*| Case JtLam. By induction hypothesis, it suffice to prove |*)
    introv Hsame; fv.
    eapply IHHjt; intros.
    assert (
      exists Gamma'', T.: Gamma'' = Gamma' ).
    { exists (fun x => Gamma' (S x)).
      eapply functional_extensionality; intros.
      induction x.
      - rewrite H; simpl; eauto with lia.
      - now simpl.
    } unpack; replace Gamma' with (T .: Gamma'') in *; clear Gamma'; rename Gamma'' into Gamma'; clear H0.

    forwards: Hsame Gamma'.
    { intros. eapply (H (S i)). lia. }
    now match goal with h: jt _ _ _ |- _ => inverts h end.
  
  * (*| Case JtApp |*)
    introv Hsame; fv.
    split.
    - eapply IHHjt1; intros.
      forwards tmp: Hsame Gamma' ; eauto. inverts tmp.
      admit. (* ??? *)
    - eapply IHHjt2; intros.
      forwards tmp: Hsame Gamma'; eauto; inverts tmp. 

      admit.

      (* eapply H1.
      eapply jt_determ.
      eapply Hsame.

      eapply jt_determ. *)

    

    (* eapply (H0 (fun i => if i <=? k then Gamma i else U)).  *)
  * set (Gamma' := (fun x: nat => TyFun T T)).
    admit.
    (*
    assert (T = TyFun T T).
    {
      eapply jt_determ.
      eapply (H Gamma').
      econstructor.
      subst Gamma'.
      eauto.
    }
    false.
    admit. (* with a size on types *) *)
  *  
Admitted.

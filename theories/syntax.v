Require Import String.
Require Import Coq.ZArith.ZArith.
Require Export Coq.Classes.RelationClasses.
Require Import Ltac2.Ltac2.
Set Default Proof Mode "Classic".

Require Import tactics.

Inductive op :=
  | Add
  | Eq
.

Theorem op_eq_dec:
  forall o1 o2: op, {o1 = o2} + {o1 <> o2}.
Proof.
  decide equality.
Qed.

Inductive term :=
  (* Lambda calculus part of the language*)
  | Var (x: nat)
  | App (t1 t2: term)
  | Lam (t: term)

  (* Default fragment of the language. *)
  | ErrorOnEmpty (arg: term)
  | DefaultPure (arg: term)
  | Default (ts: list term) (tj tc: term)
  | Empty
  | Conflict

  (* value computating fragment of the language*)
  | Value (v: value)
  | Binop (op: op) (t1 t2: term)

  | Match_ (u t1: term) (t2: term)
  | ENone
  | ESome (t: term)
  | Fold (f: term) (ts: list term) (t: term)

  | If (t ta tb: term)

with value :=
  | Bool (b: bool)
  | Int (i: Z)
  | Closure (t: term) (sigma: list value)
  | VNone
  | VUnit
  | VSome (v: value)
  | VPure (v: value)
.


Fixpoint size_term (t : term) : nat :=
  match t with
  | Var _ => 0
  | App t1 t2 => S (size_term t1 + size_term t2)
  | Lam t => S (size_term t)
  | Value v => S (size_value v)
  | ErrorOnEmpty arg => S (size_term arg)
  | DefaultPure arg => S (size_term arg)
  | Default ts tj tc => S (List.list_sum (List.map size_term ts) + size_term tj + size_term tc)
  | Empty => 0
  | Conflict => 0
  | Binop _ t1 t2 => S (size_term t1 + size_term t2)
  | Match_ u t1 t2 => S (size_term u + size_term t1 + size_term t2)
  | ENone => 0
  | ESome t => S (size_term t)
  | Fold f ts t => S (size_term f + List.list_sum (List.map size_term ts) + size_term t)
  | If t ta tb => S (size_term t + size_term ta + size_term tb)
  end
with size_value (v : value) : nat :=
  match v with
  | Bool _ => 0
  | Int _ => 0
  | Closure t sigma => S (size_term t +  (List.list_sum (List.map size_value sigma)))
  | VNone => 0
  | VUnit => 0
  | VSome v => S (size_value v)
  | VPure v => S (size_value v)
  end.

Definition size_term_value (x : term + value) :=
  match x with
  | inl t => size_term t
  | inr v => size_value v
  end.

(* Scheme term_ind_aux := Induction for term Sort Prop
with value_ind_aux := Induction for value Sort Prop. *)

Require Import Wellfounded.

Lemma term_ind_aux (P: term -> Prop) (P0: value -> Prop):
  (forall t, P t) /\ (forall v, P0 v) <->
  (forall x: term + value, match x with inl t => P t | inr v => P0 v end).
Proof.
  split; intros.
  { destruct x; unpack; eauto. }
  { split; intros. eapply (H (inl _)). eapply (H (inr _)). }
Qed.

Lemma term_value_ind
	 : forall (P : term -> Prop) (P0 : value -> Prop),
       (forall x : nat, P (Var x)) ->
       (forall t1 : term, P t1 -> forall t2 : term, P t2 -> P (App t1 t2)) ->
       (forall t : term, P t -> P (Lam t)) ->
       (forall arg : term, P arg -> P (ErrorOnEmpty arg)) ->
       (forall arg : term, P arg -> P (DefaultPure arg)) ->
       (forall (ts : list term), List.Forall P ts -> forall (tj : term),
        P tj -> forall tc : term, P tc -> P (Default ts tj tc)) ->
       P Empty ->
       P Conflict ->
       (forall v : value, P0 v -> P (Value v)) ->
       (forall (op : op) (t1 : term),
        P t1 -> forall t2 : term, P t2 -> P (Binop op t1 t2)) ->
       (forall u : term,
        P u ->
        forall t1 : term,
        P t1 -> forall t2 : term, P t2 -> P (Match_ u t1 t2)) ->
       P ENone ->
       (forall t : term, P t -> P (ESome t)) ->
       (forall f : term,
        P f -> forall (ts : list term), List.Forall P ts -> forall (t : term), P t -> P (Fold f ts t)) ->
       (forall t : term,
        P t ->
        forall ta : term, P ta -> forall tb : term, P tb -> P (If t ta tb)) ->
       (forall b : bool, P0 (Bool b)) ->
       (forall i : Z, P0 (Int i)) ->
       (forall t : term,
        P t -> forall sigma : list value, List.Forall P0 sigma -> P0 (Closure t sigma)) ->
       P0 VNone ->
       P0 VUnit ->
       (forall v : value, P0 v -> P0 (VSome v)) ->
       (forall v : value, P0 v -> P0 (VPure v)) ->
       (forall t, P t) /\ (forall v, P0 v).
Proof.
  intros.
  rewrite term_ind_aux.
  induction x as [x IHx] using (
    well_founded_induction
      (wf_inverse_image _ nat _ size_term_value 
      PeanoNat.Nat.lt_wf_0)).
  
  lock IHx.

  intros.
  destruct x.
  { destruct t.
    all: match goal with
    | [h: _ |- _] => eapply h
    end.
    all: unlock IHx.
    all: try match goal with [|- List.Forall _ ?ts] => induction ts; econstructor; eauto end.
    all: try (first [eapply (IHx (inl _))| eapply (IHx (inr _))]; simpl; lia).
    all: eapply IHts; intros; eapply IHx; simpl in *; lia.
  }
  { destruct v.
    all: match goal with
    | [h: _ |- _] => eapply h
    end.
    all: unlock IHx.
    all: try match goal with [|- List.Forall _ ?ts] => induction ts; econstructor; eauto end.
    all: try (first [eapply (IHx (inl _))| eapply (IHx (inr _))]; simpl; lia).
    all: eapply IHsigma; intros; eapply IHx; simpl in *; lia.
  }
Qed.

Definition term_ind' P Q H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15 H16 H17 H18 H19 H20 H21 := 
  proj1 (term_value_ind P Q H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15 H16 H17 H18 H19 H20 H21).

Definition value_ind' P Q H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15 H16 H17 H18 H19 H20 H21 := 
  proj2 (term_value_ind P Q H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15 H16 H17 H18 H19 H20 H21).


Theorem term_value_eq_dec:
  forall x: term + value,
    match x with
    | inl x => (forall (y : term), {x = y}+{x <> y})
    | inr x => (forall (y : value), {x = y}+{x <> y})
    end.
  Ltac finish := unzip; subst; try solve [left; eauto| right; repeat intro; tryfalse].
  intros.
  induction x as [x IHx] using (
    well_founded_induction_type
      (wf_inverse_image _ nat _ size_term_value 
      PeanoNat.Nat.lt_wf_0)).
  destruct x.
  { destruct t, y; finish.
    { epose proof (Nat.eq_dec x x0).
      finish.
    }
    {
      epose proof (IHx (inl t1) _ y1).
      epose proof (IHx (inl t2) _ y2).
      finish.
    }
    { epose proof (IHx (inl t) _ y); finish. }
    { epose proof (IHx (inl t) _ y); finish. }
    { epose proof (IHx (inl t) _ y); finish. }
    { epose proof (IHx (inl t1) _ y1).
      epose proof (IHx (inl t2) _ y2).
      assert ({ts = ts0} + {ts <> ts0}).
      { clear -IHx.
        generalize dependent ts0; induction ts; destruct ts0; finish.
        epose proof (IHx (inl a) _ t).
        unshelve epose proof (IHts _ ts0).
        { intros.
          eapply IHx.
          simpl in *; lia. }
        finish.
      }
      finish.
    }
    { epose proof (IHx (inr v) _ v0); finish. }
    { epose proof (op_eq_dec op0 op1).
      epose proof (IHx (inl t1) _ y1).
      epose proof (IHx (inl t2) _ y2).
      finish.
    }
    { simpl in *.
      epose proof (IHx (inl t1) _ y1).
      epose proof (IHx (inl t2) _ y2).
      epose proof (IHx (inl t3) _ y3).
      finish.
    }
    { epose proof (IHx (inl t) _ y).
      finish.
    }
    { epose proof (IHx (inl t1) _ y1).
      epose proof (IHx (inl t2) _ y2).
      assert ({ts = ts0} + {ts <> ts0}).
      { clear -IHx.
        generalize dependent ts0; induction ts; destruct ts0; finish.
        epose proof (IHx (inl a) _ t).
        unshelve epose proof (IHts _ ts0).
        { intros.
          eapply IHx.
          simpl in *; lia. }
        finish.
      }
      finish.
    }
    { epose proof (IHx (inl t1) _ y1).
      epose proof (IHx (inl t2) _ y2).
      epose proof (IHx (inl t3) _ y3).
      finish.
    }
  }
  { destruct v, y; finish.
    { pose proof (Bool.bool_dec b b0); finish. }
    { pose proof (Z.eq_dec i i0); finish. }
    { epose proof (IHx (inl t) _ t0).
      assert ({sigma = sigma0} + {sigma <> sigma0}).
      { clear -IHx.
        generalize dependent sigma0; induction sigma; destruct sigma0; finish.
        epose proof (IHx (inr a) _ v).
        unshelve epose proof (IHsigma _ sigma0).
        { intros.
          eapply IHx.
          simpl in *; lia. }
        finish.
      }
      finish.
    }
    { epose proof (IHx (inr v) _ y).
      finish.
    }
    { epose proof (IHx (inr v) _ y).
      finish.
    }
  }

  Unshelve.
  all: simpl; lia.
Qed.

Definition term_eq_dec: forall t1 t2: term, {t1 = t2} + {t1 <> t2} :=
  fun t1 t2 => term_value_eq_dec (inl t1) t2.

Definition value_eq_dec: forall v1 v2: value, {v1 = v2} + {v1 <> v2} :=
  fun v1 v2 => term_value_eq_dec (inr v1) v2.

Definition get_op op i1 i2 :=
  match op, i1, i2 with
  | Add, Int i1, Int i2 => Some (Int (Z.add i1 i2))
  | Eq, Int i1, Int i2 => Some (Bool (Z.eqb i1 i2))
  | _, _, _ => None
  end.

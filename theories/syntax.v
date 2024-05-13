Require Export Autosubst.Autosubst.
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
  | Var (x: var)
  | App (t1 t2: term)
  | Lam (t: {bind term})

  (* Default fragment of the language. *)
  | ErrorOnEmpty (arg: term)
  | DefaultPure (arg: term)
  | Default (ts: list term) (tj tc: term)
  | Empty
  | Conflict

  (* value computating fragment of the language*)
  | Value (v: value)
  | Binop (op: op) (t1 t2: term)

  | Match_ (u t1: term) (t2: {bind term})
  | ENone
  | ESome (t: term)
  | Fold (f: term) (ts: term) (t: term)

  | If (t ta tb: term)

  | ECons (h t: term)
  | ENil

with value :=
  | Bool (b: bool)
  | Int (i: Z)
  | Closure (t: {bind term}) (sigma: list value)
  | VNone
  | VUnit
  | VSome (v: value)
  | VPure (v: value)
  | VCons (h t: value)
  | VNil
.

Definition get_op op i1 i2 :=
  match op, i1, i2 with
  | Add, Int i1, Int i2 => Some (Int (Z.add i1 i2))
  | Eq, Int i1, Int i2 => Some (Bool (Z.eqb i1 i2))
  | _, _, _ => None
  end.


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
  | Fold f ts t => S (size_term f + size_term ts + size_term t)
  | If t ta tb => S (size_term t + size_term ta + size_term tb)
  | ECons h t => S (size_term h + size_term t)
  | ENil => 0
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
  | VCons h t => S (size_value h + size_value t)
  | VNil => 0
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
       (forall x : var, P (Var x)) ->
       (forall t1 : term, P t1 -> forall t2 : term, P t2 -> P (App t1 t2)) ->
       (forall t : {bind term}, P t -> P (Lam t)) ->
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
        P t1 -> forall t2 : {bind term}, P t2 -> P (Match_ u t1 t2)) ->
       P ENone ->
       (forall t : term, P t -> P (ESome t)) ->
       (forall f : term,
        P f -> forall (ts : term), P ts -> forall (t : term), P t -> P (Fold f ts t)) ->
       (forall t : term,
        P t ->
        forall ta : term, P ta -> forall tb : term, P tb -> P (If t ta tb)) ->
       P ENil ->
       (forall ta, P ta -> forall tb, P tb -> P (ECons ta tb)) ->
       (forall b : bool, P0 (Bool b)) ->
       (forall i : Z, P0 (Int i)) ->
       (forall t : {bind term},
        P t -> forall sigma : list value, List.Forall P0 sigma -> P0 (Closure t sigma)) ->
       P0 VNone ->
       P0 VUnit ->
       (forall v : value, P0 v -> P0 (VSome v)) ->
       (forall v : value, P0 v -> P0 (VPure v)) ->
       P0 VNil ->
       (forall va, P0 va -> forall vb, P0 vb -> P0 (VCons va vb)) ->
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

Definition term_ind' P Q H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15 H16 H17 H18 H19 H20 H21 H22 H23 H24 H25 := 
  proj1 (term_value_ind P Q H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15 H16 H17 H18 H19 H20 H21 H22 H23 H24 H25).

Definition value_ind' P Q H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15 H16 H17 H18 H19 H20 H21 H22 H23 H24 H25 := 
  proj2 (term_value_ind P Q H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15 H16 H17 H18 H19 H20 H21 H22 H23 H24 H25).


Theorem term_value_eq_dec:
  forall x: term + value,
    match x with
    | inl x => (forall (y : term), {x = y}+{x <> y})
    | inr x => (forall (y : value), {x = y}+{x <> y})
    end.
Admitted.

Definition term_eq_dec: forall t1 t2: term, {t1 = t2} + {t1 <> t2} :=
  fun t1 t2 => term_value_eq_dec (inl t1) t2.

Definition value_eq_dec: forall v1 v2: value, {v1 = v2} + {v1 <> v2} :=
  fun v1 v2 => term_value_eq_dec (inr v1) v2.

#[export] Instance Ids_term : Ids term. derive. Defined.
#[export] Instance Rename_term : Rename term. derive. Defined.
#[export] Instance Subst_term : Subst term. derive. Defined.
#[export] Instance SubstLemmas_term : SubstLemmas term. derive. Qed.


(* -------------------------------------------------------------------------- *)
(** autosubst and lists*)

Lemma subst_cons:
  forall ti ts sigma,
  ((ti::ts)..[sigma] = (ti.[sigma] :: ts..[sigma]))%list.
Proof.
  autosubst.
Qed.


Global Hint Rewrite subst_cons: autosubst.





Import List.ListNotations.
Open Scope list.
  
Definition subst_of_env sigma :=
  fun n =>
  match List.nth_error sigma n with
  | None => ids (n - List.length sigma)
  | Some t => Value t
  end
.

Notation "'soe' sigma n" := (
match List.nth_error sigma n with
| None => ids (n - List.length sigma)
| Some t => Value t
end)
(at level 69, sigma at level 1, n at level 1).

Theorem soe_nil:
  subst_of_env [] = ids.
Proof.
  eapply FunctionalExtensionality.functional_extensionality.
  induction x; eauto.
Qed.

Lemma soe_cons v sigma:
  subst_of_env (v :: sigma) = (Value v) .: subst_of_env sigma.
Proof.
  eapply FunctionalExtensionality.functional_extensionality.
  induction x; asimpl; eauto.
Qed.

Lemma subst_of_env_decompose { t v sigma }:
  t.[subst_of_env (v :: sigma)] = t.[up (subst_of_env sigma)].[Value v/].
Proof.
  asimpl; rewrite soe_cons.
  eauto.
Qed.


(* ----------------------------------------------------------------------- *)

(* simulation between terms *)

Inductive sim_term : term -> term -> Prop :=
  | sim_term_var : forall x y, x = y -> sim_term (Var x) (Var y)
  | sim_term_app : forall t1 t2 u1 u2,
      sim_term t1 u1 ->
      sim_term t2 u2 ->
      sim_term (App t1 t2) (App u1 u2)
  | sim_term_lam : forall t1 u1,
      sim_term t1 u1 ->
      sim_term (Lam t1) (Lam u1)
  | sim_term_value : forall v1 w1,
      sim_value v1 w1 ->
      sim_term (Value v1) (Value w1)
  | sim_term_erroronempty : forall t1 t2,
      sim_term t1 t2 ->
      sim_term (ErrorOnEmpty t1) (ErrorOnEmpty t2)
  | sim_term_defaultpure : forall t1 t2,
      sim_term t1 t2 ->
      sim_term (DefaultPure t1) (DefaultPure t2)
  | sim_term_default : forall ts1 ts2 tj1 tj2 tc1 tc2,
      List.Forall2 sim_term ts1 ts2 ->
      sim_term tj1 tj2 ->
      sim_term tc1 tc2 ->
      sim_term (Default ts1 tj1 tc1) (Default ts2 tj2 tc2)
  | sim_term_empty : sim_term Empty Empty
  | sim_term_conflict : sim_term Conflict Conflict
  | sim_term_binop : forall op1 op2 t1 t2 u1 u2,
      op1 = op2 ->
      sim_term t1 u1 ->
      sim_term t2 u2 ->
      sim_term (Binop op1 t1 t2) (Binop op2 u1 u2)
  | sim_term_match : forall u1 u2 t1 t2 t3 t4,
      sim_term u1 u2 ->
      sim_term t1 t2 ->
      sim_term t3 t4 ->
      sim_term (Match_ u1 t1 t3) (Match_ u2 t2 t4)
  | sim_term_enone : sim_term ENone ENone
  | sim_term_esome : forall t1 t2,
      sim_term t1 t2 ->
      sim_term (ESome t1) (ESome t2)
  | sim_term_fold : forall f1 f2 ts1 ts2 t1 t2,
      sim_term f1 f2 ->
      sim_term ts1 ts2 ->
      sim_term t1 t2 ->
      sim_term (Fold f1 ts1 t1) (Fold f2 ts2 t2)
  | sim_term_if : forall t1 t2 ta1 ta2 tb1 tb2,
      sim_term t1 t2 ->
      sim_term ta1 ta2 ->
      sim_term tb1 tb2 ->
      sim_term (If t1 ta1 tb1) (If t2 ta2 tb2)
  | sim_term_nil:
    sim_term ENil ENil
  | sim_term_cons: forall ta1 ta2 tb1 tb2,
    sim_term ta1 ta2 ->
    sim_term tb1 tb2 ->
    sim_term (ECons ta1 tb1) (ECons ta2 tb2)

with sim_value : value -> value -> Prop :=
  | sim_value_bool : forall b1 b2,
      b1 = b2 ->
      sim_value (Bool b1) (Bool b2)
  | sim_value_int : forall i1 i2,
      i1 = i2 ->
      sim_value (Int i1) (Int i2)
  | sim_value_closure : forall t1 t2 sigma1 sigma2,
      sim_term t1.[up (subst_of_env sigma1)] t2.[up (subst_of_env sigma2)] ->
      sim_value (Closure t1 sigma1) (Closure t2 sigma2)
  | sim_value_vnone : sim_value VNone VNone
  | sim_value_vunit : sim_value VUnit VUnit
  | sim_value_vsome : forall v1 v2,
      sim_value v1 v2 ->
      sim_value (VSome v1) (VSome v2)
  | sim_value_vpure : forall v1 v2,
      sim_value v1 v2 ->
      sim_value (VPure v1) (VPure v2)
  | sim_value_nil:
      sim_value VNil VNil
  | sim_value_cons: forall ta1 ta2 tb1 tb2,
      sim_value ta1 ta2 ->
      sim_value tb1 tb2 ->
      sim_value (VCons ta1 tb1) (VCons ta2 tb2)
  .

Local Ltac2 sinv_sim_term () :=
  match! goal with
  | [ h: sim_term _ ?c |- _ ] => smart_inversion c h
  | [ h: sim_term ?c _ |- _ ] => smart_inversion c h
  | [ h: sim_value _ ?c |- _ ] => smart_inversion c h
  | [ h: sim_value ?c _ |- _ ] => smart_inversion c h

  | [ h: List.Forall _ (_ :: _) |- _ ] => 
    Std.inversion Std.FullInversion (Std.ElimOnIdent h) None None;
    Std.subst_all ();
    Std.clear [h]
  | [ h: List.Forall2 _ (_ :: _) _ |- _ ] => 
    Std.inversion Std.FullInversion (Std.ElimOnIdent h) None None;
    Std.subst_all ();
    Std.clear [h]
  | [ h: List.Forall2 _ _ (_ :: _) |- _ ] => 
    Std.inversion Std.FullInversion (Std.ElimOnIdent h) None None;
    Std.subst_all ();
    Std.clear [h]
  | [ h: List.Forall2 _ [] _ |- _ ] => 
    Std.inversion Std.FullInversion (Std.ElimOnIdent h) None None;
    Std.subst_all ();
    Std.clear [h]
  | [ h: List.Forall2 _ _ [] |- _ ] => 
    Std.inversion Std.FullInversion (Std.ElimOnIdent h) None None;
    Std.subst_all ();
    Std.clear [h]
  end.

Ltac sinv_sim_term := ltac2:(Control.enter sinv_sim_term).


Require Import Coq.Classes.SetoidClass.

Lemma sim_term_ren:
  forall t1 t2,
    (sim_term t1 t2 ->
    forall xi,
      sim_term t1.[ren xi] t2.[ren xi]).
Proof.
  einduction t1 using term_ind'; intros; repeat sinv_sim_term; intros; subst; asimpl.
  all: repeat econstructor; eauto.
  { generalize dependent ts2. induction H; intros; sinv_sim_term; asimpl; repeat econstructor; eauto. }
  Unshelve.
  10:{ exact (fun _ => True). }
  all: simpl; eauto. 
Qed.

Lemma sim_term_subst:
  forall t1 t2,
    sim_term t1 t2 ->
    forall sigma1 sigma2,
      (forall x, sim_term (sigma1 x) (sigma2 x)) ->
      sim_term t1.[sigma1] t2.[sigma2].
Proof.
  einduction t1 using term_ind'; intros; repeat sinv_sim_term; intros; subst; asimpl.
  all: repeat econstructor; eauto.
  { eapply IHt; eauto.
    induction x; asimpl.
    { econstructor; eauto. }
    { eapply sim_term_ren; eauto. }
  }
  { generalize dependent ts2; induction H; intros; sinv_sim_term; asimpl; econstructor; eauto. }
  { eapply IHt3; eauto.
    induction x; asimpl.
    { econstructor; eauto. }
    { eapply sim_term_ren; eauto. }
  }

  Unshelve.
  10:{ exact (fun _ => True). }
  all: simpl; eauto. 
Qed.


Theorem sim_term_value_ind'
	 : forall (P : term -> term -> Prop)
         (P0 : value -> value -> Prop),
       (forall (x y : var) (e : x = y),
        P (Var x) (Var y)) ->
       (forall (t1 t2 u1 u2 : term) (s : sim_term t1 u1),
        P t1 u1 ->
        forall s0 : sim_term t2 u2,
        P t2 u2 ->
        P (App t1 t2) (App u1 u2)) ->
       (forall (t1 u1 : term) (s : sim_term t1 u1),
        P t1 u1 -> P (Lam t1) (Lam u1)) ->
       (forall (v1 w1 : value) (s : sim_value v1 w1),
        P0 v1 w1 -> P (Value v1) (Value w1)) ->
       (forall (t1 t2 : term) (s : sim_term t1 t2),
        P t1 t2 ->
        P (ErrorOnEmpty t1) (ErrorOnEmpty t2)) ->
       (forall (t1 t2 : term) (s : sim_term t1 t2),
        P t1 t2 ->
        P (DefaultPure t1) (DefaultPure t2)) ->
       (forall (ts1 ts2 : list term) (tj1 tj2 tc1 tc2 : term)
          (f : List.Forall2 sim_term ts1 ts2),
        List.Forall2 P ts1 ts2 ->
        forall (s : sim_term tj1 tj2),
        P tj1 tj2 ->
        forall s0 : sim_term tc1 tc2,
        P tc1 tc2 ->
        P (Default ts1 tj1 tc1) (Default ts2 tj2 tc2)
          ) ->
       P Empty Empty ->
       P Conflict Conflict ->
       (forall (op1 op2 : op) (t1 t2 u1 u2 : term) 
          (e : op1 = op2) (s : sim_term t1 u1),
        P t1 u1 ->
        forall s0 : sim_term t2 u2,
        P t2 u2 ->
        P (Binop op1 t1 t2) (Binop op2 u1 u2)
          ) ->
       (forall (u1 u2 t1 t2 t3 t4 : term) (s : sim_term u1 u2),
        P u1 u2 ->
        forall s0 : sim_term t1 t2,
        P t1 t2 ->
        forall s1 : sim_term t3 t4,
        P t3 t4 ->
        P (Match_ u1 t1 t3) (Match_ u2 t2 t4)
          ) ->
       P ENone ENone ->
       (forall (t1 t2 : term) (s : sim_term t1 t2),
        P t1 t2 -> P (ESome t1) (ESome t2) ) ->
       (forall (f1 f2 : term) (ts1 ts2 : term) 
          (t1 t2 : term) (s : sim_term f1 f2),
        P f1 f2 ->
        forall (f : sim_term ts1 ts2), P ts1 ts2 ->forall (s0 : sim_term t1 t2),
        P t1 t2 ->
        P (Fold f1 ts1 t1) (Fold f2 ts2 t2)
          ) ->
       (forall (t1 t2 ta1 ta2 tb1 tb2 : term) (s : sim_term t1 t2),
        P t1 t2 ->
        forall s0 : sim_term ta1 ta2,
        P ta1 ta2 ->
        forall s1 : sim_term tb1 tb2,
        P tb1 tb2 ->
        P (If t1 ta1 tb1) (If t2 ta2 tb2)
          ) ->
       (forall (b1 b2 : bool) (e : b1 = b2),
        P0 (Bool b1) (Bool b2) ) ->
       (forall (i1 i2 : Z) (e : i1 = i2),
        P0 (Int i1) (Int i2) ) ->
       (forall (t1 t2 : term) (sigma1 sigma2 : list value)
          (s : sim_term t1.[up (subst_of_env sigma1)]
                 t2.[up (subst_of_env sigma2)]),
        P t1.[up (subst_of_env sigma1)] t2.[up (subst_of_env sigma2)] ->
        P0 (Closure t1 sigma1) (Closure t2 sigma2)
          ) ->
       P0 VNone VNone ->
       P0 VUnit VUnit ->

       (* List related *)
       P ENil ENil ->
       (forall ta1 ta2, P ta1 ta2 ->
        forall tb1 tb2, P tb1 tb2 ->
        P (ECons ta1 tb1) (ECons ta2 tb2)) ->
       P0 VNil VNil ->
       (forall va1 va2, P0 va1 va2 ->
        forall vb1 vb2, P0 vb1 vb2 ->
        P0 (VCons va1 vb1) (VCons va2 vb2)) ->
       (forall (v1 v2 : value) (s : sim_value v1 v2),
        P0 v1 v2 -> P0 (VSome v1) (VSome v2)) ->
       (forall (v1 v2 : value) (s : sim_value v1 v2),
        P0 v1 v2 -> P0 (VPure v1) (VPure v2) ) ->
       (forall (t t0 : term) (s : sim_term t t0), P t t0 )
with sim_value_term_ind'
: forall (P : term -> term -> Prop)
      (P0 : value -> value -> Prop),
    (forall (x y : var) (e : x = y),
     P (Var x) (Var y)) ->
    (forall (t1 t2 u1 u2 : term) (s : sim_term t1 u1),
     P t1 u1 ->
     forall s0 : sim_term t2 u2,
     P t2 u2 ->
     P (App t1 t2) (App u1 u2)) ->
    (forall (t1 u1 : term) (s : sim_term t1 u1),
     P t1 u1 -> P (Lam t1) (Lam u1)) ->
    (forall (v1 w1 : value) (s : sim_value v1 w1),
     P0 v1 w1 -> P (Value v1) (Value w1)) ->
    (forall (t1 t2 : term) (s : sim_term t1 t2),
     P t1 t2 ->
     P (ErrorOnEmpty t1) (ErrorOnEmpty t2)) ->
    (forall (t1 t2 : term) (s : sim_term t1 t2),
     P t1 t2 ->
     P (DefaultPure t1) (DefaultPure t2)) ->
    (forall (ts1 ts2 : list term) (tj1 tj2 tc1 tc2 : term)
       (f : List.Forall2 sim_term ts1 ts2),
     List.Forall2 P ts1 ts2 ->
     forall (s : sim_term tj1 tj2),
     P tj1 tj2 ->
     forall s0 : sim_term tc1 tc2,
     P tc1 tc2 ->
     P (Default ts1 tj1 tc1) (Default ts2 tj2 tc2)
       ) ->
    P Empty Empty ->
    P Conflict Conflict ->
    (forall (op1 op2 : op) (t1 t2 u1 u2 : term) 
       (e : op1 = op2) (s : sim_term t1 u1),
     P t1 u1 ->
     forall s0 : sim_term t2 u2,
     P t2 u2 ->
     P (Binop op1 t1 t2) (Binop op2 u1 u2)
       ) ->
    (forall (u1 u2 t1 t2 t3 t4 : term) (s : sim_term u1 u2),
     P u1 u2 ->
     forall s0 : sim_term t1 t2,
     P t1 t2 ->
     forall s1 : sim_term t3 t4,
     P t3 t4 ->
     P (Match_ u1 t1 t3) (Match_ u2 t2 t4)
       ) ->
    P ENone ENone ->
    (forall (t1 t2 : term) (s : sim_term t1 t2),
     P t1 t2 -> P (ESome t1) (ESome t2) ) ->
    (forall (f1 f2 : term) (ts1 ts2 : term) 
       (t1 t2 : term) (s : sim_term f1 f2),
     P f1 f2 ->
     forall (f : sim_term ts1 ts2), P ts1 ts2 ->forall (s0 : sim_term t1 t2),
     P t1 t2 ->
     P (Fold f1 ts1 t1) (Fold f2 ts2 t2)
       ) ->
    (forall (t1 t2 ta1 ta2 tb1 tb2 : term) (s : sim_term t1 t2),
     P t1 t2 ->
     forall s0 : sim_term ta1 ta2,
     P ta1 ta2 ->
     forall s1 : sim_term tb1 tb2,
     P tb1 tb2 ->
     P (If t1 ta1 tb1) (If t2 ta2 tb2)
       ) ->
    (forall (b1 b2 : bool) (e : b1 = b2),
     P0 (Bool b1) (Bool b2) ) ->
    (forall (i1 i2 : Z) (e : i1 = i2),
     P0 (Int i1) (Int i2) ) ->
    (forall (t1 t2 : term) (sigma1 sigma2 : list value)
       (s : sim_term t1.[up (subst_of_env sigma1)]
              t2.[up (subst_of_env sigma2)]),
     P t1.[up (subst_of_env sigma1)] t2.[up (subst_of_env sigma2)] ->
     P0 (Closure t1 sigma1) (Closure t2 sigma2)
       ) ->
    P0 VNone VNone ->
    P0 VUnit VUnit ->
    (* List related *)
    P ENil ENil ->
    (forall ta1 ta2, P ta1 ta2 ->
     forall tb1 tb2, P tb1 tb2 ->
     P (ECons ta1 tb1) (ECons ta2 tb2)) ->
    P0 VNil VNil ->
    (forall va1 va2, P0 va1 va2 ->
     forall vb1 vb2, P0 vb1 vb2 ->
     P0 (VCons va1 vb1) (VCons va2 vb2)) ->
    (forall (v1 v2 : value) (s : sim_value v1 v2),
     P0 v1 v2 -> P0 (VSome v1) (VSome v2)) ->
    (forall (v1 v2 : value) (s : sim_value v1 v2),
     P0 v1 v2 -> P0 (VPure v1) (VPure v2) ) ->
  (forall (v v0 : value) (s : sim_value v v0), P0 v v0).
Proof.
  all: intros; destruct s.
  all: match goal with
    | [h: _ |- _] => eapply h
    end; eauto.
  all:
    try solve 
    [ eapply sim_term_value_ind'; eassumption
    | eapply sim_value_term_ind'; eassumption].
  { induction H25; econstructor; eauto.
    eapply sim_term_value_ind'; eassumption.
  }
Qed.

Theorem combined_sim_term_value_term_ind: forall (P : term -> term -> Prop)
(P0 : value -> value -> Prop),
(forall (x y : var) (e : x = y),
P (Var x) (Var y)) ->
(forall (t1 t2 u1 u2 : term) (s : sim_term t1 u1),
P t1 u1 ->
forall s0 : sim_term t2 u2,
P t2 u2 ->
P (App t1 t2) (App u1 u2)) ->
(forall (t1 u1 : term) (s : sim_term t1 u1),
P t1 u1 -> P (Lam t1) (Lam u1)) ->
(forall (v1 w1 : value) (s : sim_value v1 w1),
P0 v1 w1 -> P (Value v1) (Value w1)) ->
(forall (t1 t2 : term) (s : sim_term t1 t2),
P t1 t2 ->
P (ErrorOnEmpty t1) (ErrorOnEmpty t2)) ->
(forall (t1 t2 : term) (s : sim_term t1 t2),
P t1 t2 ->
P (DefaultPure t1) (DefaultPure t2)) ->
(forall (ts1 ts2 : list term) (tj1 tj2 tc1 tc2 : term)
 (f : List.Forall2 sim_term ts1 ts2),
List.Forall2 P ts1 ts2 ->
forall (s : sim_term tj1 tj2),
P tj1 tj2 ->
forall s0 : sim_term tc1 tc2,
P tc1 tc2 ->
P (Default ts1 tj1 tc1) (Default ts2 tj2 tc2)
 ) ->
P Empty Empty ->
P Conflict Conflict ->
(forall (op1 op2 : op) (t1 t2 u1 u2 : term) 
 (e : op1 = op2) (s : sim_term t1 u1),
P t1 u1 ->
forall s0 : sim_term t2 u2,
P t2 u2 ->
P (Binop op1 t1 t2) (Binop op2 u1 u2)
 ) ->
(forall (u1 u2 t1 t2 t3 t4 : term) (s : sim_term u1 u2),
P u1 u2 ->
forall s0 : sim_term t1 t2,
P t1 t2 ->
forall s1 : sim_term t3 t4,
P t3 t4 ->
P (Match_ u1 t1 t3) (Match_ u2 t2 t4)
 ) ->
P ENone ENone ->
(forall (t1 t2 : term) (s : sim_term t1 t2),
P t1 t2 -> P (ESome t1) (ESome t2) ) ->
(forall (f1 f2 : term) (ts1 ts2 : term) 
 (t1 t2 : term) (s : sim_term f1 f2),
P f1 f2 ->
forall (f : sim_term ts1 ts2), P ts1 ts2 ->forall (s0 : sim_term t1 t2),
P t1 t2 ->
P (Fold f1 ts1 t1) (Fold f2 ts2 t2)
 ) ->
(forall (t1 t2 ta1 ta2 tb1 tb2 : term) (s : sim_term t1 t2),
P t1 t2 ->
forall s0 : sim_term ta1 ta2,
P ta1 ta2 ->
forall s1 : sim_term tb1 tb2,
P tb1 tb2 ->
P (If t1 ta1 tb1) (If t2 ta2 tb2)
 ) ->
(forall (b1 b2 : bool) (e : b1 = b2),
P0 (Bool b1) (Bool b2) ) ->
(forall (i1 i2 : Z) (e : i1 = i2),
P0 (Int i1) (Int i2) ) ->
(forall (t1 t2 : term) (sigma1 sigma2 : list value)
 (s : sim_term t1.[up (subst_of_env sigma1)]
        t2.[up (subst_of_env sigma2)]),
P t1.[up (subst_of_env sigma1)] t2.[up (subst_of_env sigma2)] ->
P0 (Closure t1 sigma1) (Closure t2 sigma2)
 ) ->
P0 VNone VNone ->
P0 VUnit VUnit ->
(* List related *)
P ENil ENil ->
(forall ta1 ta2, P ta1 ta2 ->
forall tb1 tb2, P tb1 tb2 ->
P (ECons ta1 tb1) (ECons ta2 tb2)) ->
P0 VNil VNil ->
(forall va1 va2, P0 va1 va2 ->
forall vb1 vb2, P0 vb1 vb2 ->
P0 (VCons va1 vb1) (VCons va2 vb2)) ->
(forall (v1 v2 : value) (s : sim_value v1 v2),
P0 v1 v2 -> P0 (VSome v1) (VSome v2)) ->
(forall (v1 v2 : value) (s : sim_value v1 v2),
P0 v1 v2 -> P0 (VPure v1) (VPure v2) ) ->
(forall (t t0 : term) (s : sim_term t t0), P t t0 ) /\
(forall (v v0 : value) (s : sim_value v v0), P0 v v0).
Proof.
  split.
  { eapply sim_term_value_ind'; eassumption. }
  { eapply sim_value_term_ind'; eassumption. }
Qed.

Lemma sim_term_refl: Reflexive sim_term /\ Reflexive sim_value.
Proof.
  eapply term_value_ind; intros.
  all: try (econstructor; eauto).
  { induction H; econstructor; eauto. }
  {
    eapply sim_term_subst.
    { eauto. }
    { intro x; case x; asimpl.
      { econstructor; eauto. }
      { intros; eapply sim_term_ren.
        revert n.
        induction sigma.
        { rewrite soe_nil; econstructor; eauto. }
        { inversion H0; subst; intros. case n; asimpl.
          { econstructor; eauto. }
          { intros. rewrite soe_cons.
            eapply IHsigma; eauto.
          }
        }
      }
    }
  }
Qed.

Lemma sim_symmetric: Symmetric sim_term /\ Symmetric sim_value.
  eapply combined_sim_term_value_term_ind; intros; repeat sinv_sim_term; econstructor; eauto.
  { induction H; econstructor; sinv_sim_term; eauto. }
Qed.

Lemma sim_transitive:
  (forall x y : term, sim_term x y -> forall z, sim_term y z -> sim_term x z) /\
  (forall x y : value, sim_value x y -> forall z, sim_value y z -> sim_value x z).
  eapply combined_sim_term_value_term_ind.
  all: intros; repeat sinv_sim_term; subst; repeat econstructor; eauto.
  { generalize dependent ts3.
    induction H; intros; sinv_sim_term; econstructor; sinv_sim_term; eauto.
  }
Qed.


Instance Reflexive_sim_term : Reflexive sim_term. eapply sim_term_refl. Qed. 
Instance Symmetric_sim_term : Symmetric sim_term. repeat intro; eapply sim_symmetric; eauto. Qed.
Instance Transtive_sim_term : Transitive sim_term. repeat intro; eapply sim_transitive; eauto. Qed.


Instance Reflexive_sim_value : Reflexive sim_value. eapply sim_term_refl. Qed. 
Instance Symmetric_sim_value : Symmetric sim_value. repeat intro; eapply sim_symmetric; eauto. Qed.
Instance Transtive_sim_value : Transitive sim_value. repeat intro; eapply sim_transitive; eauto. Qed.


Instance Reflexive_Forall2_sim_term : Reflexive (List.Forall2 sim_term).
  intro.
  induction x; econstructor; eauto; reflexivity.
Qed.
Instance Reflexive_Forall2_sim_value : Reflexive (List.Forall2 sim_value).
  intro.
  induction x; econstructor; eauto; reflexivity.
Qed.

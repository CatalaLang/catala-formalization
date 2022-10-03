From QuickChick Require Import QuickChick.

Require Import DCSyntax.
Require Import LCSyntax.

Require Import MyTactics.

Require Import DCReduction.
Require Import LCReduction.

Require Import MySequences.
Require Import Simulation.

Definition dterm := DCSyntax.term.
Definition lterm := LCSyntax.term.

Module DC := DCSyntax.
Module LC := LCSyntax.

Module DCR := DCReduction.
Module LCR := LCReduction.

Definition dcbv := DCR.cbv.
Definition Lcbv := LCR.cbv.


Section FirstSim.
Import DC.


(*

  We define the invariant using an normal form. The function normalize is the same as the predicate nf as shown in the lemma nf_normalize

  Lemma nf_normalize: forall t1 t2, nf t1 t2 <-> normalize t1 = t2.

  we then define two differents invariances, depending on either nf or normalize. We prove tha normalize is idempotent.

*)

Inductive nf: dterm -> dterm -> Prop :=
| Ivar:
  forall x,
    nf (Var x) (Var x)
| Ilam:
  forall t t',
    nf t t' -> nf (Lam t) (Lam t')
| Iapp:
  forall t1 t2 t1' t2',
    nf t1 t1' ->
    nf t2 t2' ->
    nf (App t1 t2) (App t1' t2')
| Iempty: nf Empty Empty
| Iconflict: nf Conflict Conflict
| Iconst:
  forall a,
    nf (Const a) (Const a)
| Ilet:
  forall t1 t2 t1' t2',
    nf t1 t1' ->
    nf t2 t2' ->
    nf (Let t1 t2) (Let t1' t2')
| Idefault:
  forall ts ts' ts'' tj tj' tc tc',
    List.Forall2 nf ts ts' ->
    ts'' = List.filter (fun ti =>
      match ti with
      | Empty => false
      | _ => true
      end
    ) ts' ->
    nf tj tj' ->
    nf tc tc' ->
    nf (Default ts tj tc) (Default ts'' tj' tc')
.


Theorem nf_ind' :forall P : dterm -> dterm -> Prop,
(forall x : var, P (Var x) (Var x)) ->
(forall t t' : dterm, nf t t' -> P t t' -> P (Lam t) (Lam t')) ->
(forall t1 t2 t1' t2' : dterm,
 nf t1 t1' ->
 P t1 t1' -> nf t2 t2' -> P t2 t2' -> P (App t1 t2) (App t1' t2')) ->
P Empty Empty ->
P Conflict Conflict ->
(forall a : bool, P (Const a) (Const a)) ->
(forall t1 t2 t1' t2' : dterm,
 nf t1 t1' ->
 P t1 t1' -> nf t2 t2' -> P t2 t2' -> P (Let t1 t2) (Let t1' t2')) ->
(forall (ts ts' : list dterm) (ts'' : list term)
   (tj tj' tc tc' : dterm),
 List.Forall2 P ts ts' ->
 List.Forall2 nf ts ts' ->
 ts'' =
 List.filter
   (fun ti : term => match ti with
                     | Empty => false
                     | _ => true
                     end) ts' ->
 nf tj tj' ->
 P tj tj' ->
 nf tc tc' -> P tc tc' -> P (Default ts tj tc) (Default ts'' tj' tc')) ->
forall d d0 : dterm, nf d d0 -> P d d0.
Admitted.


Fixpoint normalize t :=
  match t with
  | Var x => Var x
  | Const x  => Const x
  | Empty => Empty
  | Conflict => Conflict
  | Lam t' => Lam (normalize t')
  | App t1 t2 =>
    App (normalize t1) (normalize t2)
  | Let t1 t2 =>
    Let (normalize t1) (normalize t2)
  | Default ts tj tc =>
    let ts' := List.map normalize ts in
    let ts'' := (List.filter )
    (fun ti => match ti with | Empty => false | _ => true end) ts' in
    Default ts'' (normalize tj) (normalize tc)
  end
.

Lemma nf_safe: forall t, nf t (normalize t).
Proof.
  intros.
  induction t using term_ind'; simpl; econstructor; eauto.
  - induction H; simpl; econstructor; eauto.
Qed.

Lemma nf_correct: forall t t', nf t t' -> normalize t = t'.
Proof.
  intros. gen t'.
  induction t using term_ind'; try (introv H; inverts H; simpl; eauto).
  * erewrite IHt; eauto.
  * erewrite IHt1, IHt2; eauto.
  * erewrite IHt, IHt0; eauto.
  * introv Hnf; inverts Hnf; simpl. erewrite IHt1, IHt2; fequal; eauto.
    induction H3; simpl; eauto. 
    rewrite IHForall2; fequal; eauto; inverts H.
    - erewrite H4; try eassumption; eauto.
    - assumption.
Qed.

Lemma nf_normalize:
  forall t1 t2,
    nf t1 t2 <-> normalize t1 = t2.
Proof.
  intros.
  split; intros; subst; eauto using nf_correct, nf_safe.
Qed.

Lemma nf_unique:
  forall t1 t2 t3,
    nf t1 t2 -> nf t1 t3 -> t2 = t3.
Proof.
  intros; rewrite nf_normalize in *; subst; eauto.
Qed.

Lemma nf_normalize':
  forall t1 t2,
    normalize t1 = t2 -> (forall t3, nf t1 t3 -> t2 = t3).
Proof.
  now intros; subst; rewrite nf_normalize in *.
Qed.

Definition inv t1 t2 := normalize t1 = normalize t2.

Definition inv' t1 t2 := exists u, nf t1 u /\ nf t2 u.

Inductive inv'': dterm -> dterm -> Prop :=
| IIvar:
  forall x,
    inv'' (Var x) (Var x)
| IIlam:
  forall t t',
    inv'' t t' -> inv'' (Lam t) (Lam t')
| IIapp:
  forall t1 t2 t1' t2',
    inv'' t1 t1' ->
    inv'' t2 t2' ->
    inv'' (App t1 t2) (App t1' t2')
| IIempty: inv'' Empty Empty
| IIconflict: inv'' Conflict Conflict
| IIconst:
  forall a,
    inv'' (Const a) (Const a)
| IIlet:
  forall t1 t2 t1' t2',
    inv'' t1 t1' ->
    inv'' t2 t2' ->
    inv'' (Let t1 t2) (Let t1' t2')
| IIdefault:
  forall ts ts' tj tj' tc tc',
    List.Forall2 inv''
      (List.filter (fun ti => match ti with |Empty => false | _ => true end) ts)
      (List.filter (fun ti => match ti with |Empty => false | _ => true end) ts') ->
    inv'' tj tj' ->
    inv'' tc tc' ->
    inv'' (Default ts tj tc) (Default ts' tj' tc')
.

Lemma inv''_ind'
: forall P : dterm -> dterm -> Prop,
    (forall x : var, P (Var x) (Var x)) ->
    (forall t t' : dterm, inv'' t t' -> P t t' -> P (Lam t) (Lam t')) ->
    (forall t1 t2 t1' t2' : dterm,
     inv'' t1 t1' ->
     P t1 t1' -> inv'' t2 t2' -> P t2 t2' -> P (App t1 t2) (App t1' t2')) ->
    P Empty Empty ->
    P Conflict Conflict ->
    (forall a : bool, P (Const a) (Const a)) ->
    (forall t1 t2 t1' t2' : dterm,
     inv'' t1 t1' ->
     P t1 t1' -> inv'' t2 t2' -> P t2 t2' -> P (Let t1 t2) (Let t1' t2')) ->
    (forall (ts ts' : list term) (tj tj' tc tc' : dterm),
    List.Forall2 P
    (List.filter
       (fun ti : term => match ti with
                         | Empty => false
                         | _ => true
                         end) ts)
    (List.filter
       (fun ti : term => match ti with
                         | Empty => false
                         | _ => true
                         end) ts') ->
     List.Forall2 inv''
       (List.filter
          (fun ti : term => match ti with
                            | Empty => false
                            | _ => true
                            end) ts)
       (List.filter
          (fun ti : term => match ti with
                            | Empty => false
                            | _ => true
                            end) ts') ->
     inv'' tj tj' ->
     P tj tj' ->
     inv'' tc tc' ->
     P tc tc' -> P (Default ts tj tc) (Default ts' tj' tc')) ->
    forall d d0 : dterm, inv'' d d0 -> P d d0.
Proof.
Admitted.

Lemma nf_backimg_empty:
  forall t, nf t Empty -> t = Empty.
Proof.
  intros; induction t; inverts H; eauto.
Qed.

Lemma nf_Empty:
  forall t1 t2, nf t1 t2 -> (t1 = Empty <-> t2 = Empty).
Proof.
  introv H. induction H; split; intros; tryfalse; eauto.
Qed.

Lemma inv_inv': forall t1 t2, inv t1 t2 <-> inv' t1 t2.
Proof.
  split; unfold inv', inv; intros.
  { exists (normalize t1); split.
    - eapply nf_safe.
    - rewrite H. eapply nf_safe.
  } {
    unpack.
    replace (normalize t1) with u.
    replace (normalize t2) with u.
    all: symmetry; eauto using nf_correct.
  } 
Qed.

Lemma inv''_sym:
  forall t1 t2,
  inv'' t1 t2 -> inv'' t2 t1.
Proof.
  intros.
  induction H using inv''_ind'; econstructor; eauto.
  * induction H0; econstructor; inverts H; eauto.
Qed.

Lemma filter_Forall:
  forall A P (ts: list A),
   List.filter P ts = nil <-> List.Forall (fun ti => (P ti) = false) ts.
Proof.
  intros; induction ts; split; simpl; eauto.
  * intros. remember (P a).
    induction b; subst; tryfalse.
    econstructor; try rewrite <- IHts; eauto.
  * intros. inverts H. rewrite H2. eapply IHts; eauto.
Qed.

Lemma technical:
  forall ts1 ts1' ts2 ts2',
    let f :=  (fun ti : term => match ti with
    | Empty => false
    | _ => true
    end)
    in

    List.Forall2 nf ts1 ts1' ->
    List.Forall2 nf ts2 ts2' ->
    List.filter f ts1' = List.filter f ts2' ->
    List.filter f ts1  = List.filter f ts2.

    (* false lemma! Counter example:
       ts1 = <<empty, empty :- > :- >
       ts2 = << :- > :- >
       *)
Proof.
Abort.

Lemma Forall2_of_eq {A} {ts1 ts2: list A} :
  ts1 = ts2 ->
  List.Forall2 (eq) ts1 ts2.
Proof.
  intros; gen ts2; induction ts1; intros.
  * subst; econstructor.
  * subst. econstructor; eauto.
Qed.

Lemma case_nil:
  forall ts ts',
  let f := [set ti | match ti with
  | Empty => false
  | _ => true
  end] in
  nil = List.filter f ts' -> List.Forall2 nf ts ts' -> nil = List.filter f ts.
Proof.
  intros.
  induction H0; simpl in *.
  * reflexivity.
  * remember (f y) as b; induction b; inverts H.
    induction x; inverts H0; simpl in Heqb; tryfalse.
    simpl.
    now eapply IHForall2.
Qed.




Lemma inv'_inv'': forall t1 t2, inv' t1 t2 <-> inv'' t1 t2.
Proof.
  admit.
  (*
  split; unfold inv'; intros.
  * unpack. gen t2.
    induction H using nf_ind'; try solve [introv H'; inverts H'; econstructor; eauto].
    - introv H'.
      inverts H'.
      rename ts into ts1, ts' into ts1', ts'0 into ts2', ts0 into ts2.
      econstructor; eauto. (* Conclusion and justification are trivial. *)

      (* only the list case is not trivial. *)




      remember (fun ti => match ti with | Empty => false | _ => true end) as f.

      (* List.filter f ts1 and List.filter f ts2 have the same lenght since nf preserve length and by TEMP, List.filter f ts1' and List.filter f ts2' have the same length. *)

      (* let's check that *)

      forwards: @Forall2_of_eq term TEMP.
      remember (List.filter f ts1') as ts1''; remember (List.filter f ts2') as ts2''.

      gen ts1' ts2' ts1 ts2.
      induction ts1.
      2: {

      }
      + intros.
        (* because H, ts1' contains only empties. *)
        inverts H0.

      induction H1.
      + intros.
        forwards: case_nil ts1 ts1'.
          { now rewrite <- Heqf. }
          { eauto. }
        forwards: case_nil ts2 ts2'.
          { now rewrite <- Heqf. }
          { eauto. }
        rewrite <- Heqf in *.
        rewrite <- H1, <- H4.
        econstructor.
      + induction ts1. 






        admit. (* trivial case. *)
      + injection TEMP; intros.
      

      econstructor.

      induction H0; inverts H; simpl in *.
      + induction ts0; simpl.
        { econstructor. }
        { remember (f a); induction b. inverts H7. inverts H7; simpl in *. remember (f y). induction b; tryfalse.
          remember (f a). induction b; tryfalse.
         }

      
      induction H; simpl in *.
      induction H; simpl in *; admit.
  * exists (normalize t1); split.
    - eapply nf_safe.
    - induction H using inv''_ind'; simpl; econstructor; eauto.
      {
        remember (List.filter (fun ti : term => match ti with
        | Empty => false
        | _ => true
        end) ts).

        remember (List.filter (fun ti : term => match ti with
        | Empty => false
        | _ => true
        end) ts').

        induction H0; inverts H.
        -  
      }
        induction ts, ts'; simpl.
        - econstructor.
        - simpl in *. inverts H; inverts H0. congruence.  }


      admit.
  *)
Admitted.


Lemma normalize_idempotent:
  forall t, normalize t = normalize (normalize t).
Proof.
  induction t using term_ind'; simpl; fequal; eauto.
  * rename H into IHts. clear - IHts.

    set (no_empty := (fun ti : term =>
    match ti with
    | Empty => false
    | _ => true
    end)) in *.    

    induction ts; simpl; eauto.
    inverts IHts.

    remember (no_empty (normalize a)).

    induction b.
    - simpl.
      rewrite <- H1, <- Heqb.
      fequal; eauto.
    - simpl. eauto.
Qed.

Lemma nf_idempotent:
  forall x y z, nf x y -> nf y z -> y = z.
Proof.
  intros.
  rewrite nf_normalize in *.
  subst. eapply normalize_idempotent.
Qed.

Lemma nf_idempotent':
  forall x y z, nf x y -> nf y z -> nf x z.
Proof.
  intros; rewrite nf_normalize in *; subst; eapply normalize_idempotent.
Qed.

Require Import DCValues.

Lemma inv_is_value:
  forall t1 t2,
  inv' t1 t2 ->
  is_value t1 ->
  is_value t2.
Proof.
  induction t1; simpl; introv H; inverts H; unpack; intros; tryfalse.
  * inverts H; inverts H0; simpl; eauto.
  * inverts H; inverts H0; simpl; eauto. 
  * inverts H; inverts H0; simpl; eauto.
  * inverts H; inverts H0; simpl; eauto.
  * inverts H; inverts H0; simpl; eauto.
Qed.

Lemma nf_ren:
  forall t t',
    nf t t' ->
    forall xi, nf t.[ren xi] t'.[ren xi].
Proof.
  induction 1 using nf_ind'; intros; subst; asimpl; try solve [econstructor; eauto].
  * eapply Idefault with (ts'..[ren xi]); eauto.
    { induction H; econstructor; inverts_Forall; eauto.  }
    { induction H; inverts_Forall; asimpl; eauto.
      case y; intros; asimpl; rewrite IHForall2; eauto. }
Qed.


Require Import Classes.Equivalence.

Instance Equivalence_inv: Equivalence inv.
Proof.
  unfold inv.
  repeat split; unfolds; intros;
  repeat match goal with h: _ = _ |- _ => destruct h end; eauto.
Qed.


Hint Constructors inv'': bla.


Lemma smart_ite:
  forall t t1 t2 (P: term -> bool) xi,
  (forall t, P t = P t.[ren xi]) ->
  (if P t then t1 else t2).[ren xi] = (if P t.[ren xi] then t1.[ren xi] else t2.[ren xi]).
Proof.
  introv H.
  rewrite <- H.
  set (b := P t).
  induction b; reflexivity.
Qed.

Lemma smart_filter:
  forall l (P: term -> bool) xi,
  (forall  xi t, P t = P t.[ren xi]) ->
  List.filter P l..[ren xi] = (List.filter P l)..[ren xi].
Proof.
  introv H.
  induction l.
  * simpl; eauto.
  * asimpl in *.
    rewrite <- (H xi).
    set (b:= P a).
    case b; asimpl; rewrite IHl; eauto.
Qed.

Lemma smart_filter':
  forall l (P: term -> bool) sigma,
  (forall  t, P t = P t.[sigma]) ->
  List.filter P l..[sigma] = (List.filter P l)..[sigma].
Proof.
  introv H.
  induction l.
  * simpl; eauto.
  * asimpl in *.
    rewrite <- H.
    set (b:= P a).
    case b; asimpl; rewrite IHl; eauto.
Qed.

Import IfNotations.

Goal
  let P := (fun ti : term => if ti is Empty then true else false) in
  forall xi l, List.filter P l..[ren xi] = (List.filter P l)..[ren xi].
Proof.
  intros.
  rewrite smart_filter; eauto.
  * intros.
    induction t; simpl; eauto.
Qed.

Lemma inv''_ren:
  forall v v',
    inv'' v v' ->
  forall xi, inv'' v.[ren xi] v'.[ren xi].
Proof.
  induction 1 using inv''_ind'; intros; subst; asimpl; econstructor; eauto.
  + (* case default*)
    repeat rewrite smart_filter.
    { induction H; asimpl; econstructor; inverts_Forall; eauto. }
    { clear; intros; case t; simpl; eauto. }
    { clear; intros; case t; simpl; eauto. }
Qed.

Lemma inv''_refl:
  forall t, inv'' t t.
Proof.
  induction t using term_ind'; econstructor; eauto.
  induction H; simpl.
  * econstructor.
  * set (b := if x is Empty then false else true).
    case b; try econstructor; eauto.
Qed.



Lemma inv''_subst:
  forall t t',
    inv'' t t' ->
    forall sigma,
      (forall x, sigma x <> Empty) ->
      inv'' t.[sigma] t'.[sigma].
Proof.
  induction 1 using inv''_ind'; intros; subst; asimpl; try econstructor; eauto.
  * eapply inv''_refl.
  * eapply IHinv''.
    induction x; asimpl; intro; tryfalse.
    apply H0 with x; revert H1; clear; set (t := sigma x); case t; asimpl; intros; tryfalse; eauto.
  * eapply IHinv''2.
    induction x; asimpl; intro; tryfalse.
    apply H1 with x; revert H2; clear; set (t := sigma x); case t; asimpl; intros; tryfalse; eauto.
  * repeat rewrite smart_filter'.
    {
      induction H; asimpl; econstructor; inverts_Forall; eauto.
    }
    { clear -H3; intros; case t; asimpl; eauto.
      intros x; forwards: H3 x; set (t' := sigma x) in *.
      induction t'; eauto; tryfalse.
    }
    { clear -H3; intros; case t; asimpl; eauto.
      intros x; forwards: H3 x; set (t' := sigma x) in *.
      induction t'; eauto; tryfalse.
    }
Qed.

Lemma inv''_subst':
  forall t t',
    inv'' t t' ->
    forall sigma,
      inv'' t.[sigma] t'.[sigma].
Proof.
  induction 1 using inv''_ind'; intros; subst; asimpl; try econstructor; eauto.
  * eapply inv''_refl.
  * eapply IHinv''2.
    induction x; asimpl; intro; tryfalse.
    apply H1 with x; revert H2; clear; set (t := sigma x); case t; asimpl; intros; tryfalse; eauto.
  * repeat rewrite smart_filter'.
    {
      induction H; asimpl; econstructor; inverts_Forall; eauto.
    }
    { clear -H3; intros; case t; asimpl; eauto.
      intros x; forwards: H3 x; set (t' := sigma x) in *.
      induction t'; eauto; tryfalse.
    }
    { clear -H3; intros; case t; asimpl; eauto.
      intros x; forwards: H3 x; set (t' := sigma x) in *.
      induction t'; eauto; tryfalse.
    }
Qed.

Lemma inv'_ren:
  forall v v',
    inv' v v' ->
  forall xi, inv' v.[ren xi] v'.[ren xi].
Proof.
  unfold inv'; intros; unpack.
  exists u.[ren xi]; split; eauto using nf_ren.
Qed.

Lemma subst_empty:
  forall a, normalize a = Empty <-> a = Empty.
Proof.
  induction a; simpl; split; intros; tryfalse; eauto.
Qed.

Hint Constructors nf: nf.

Lemma inv'_subst:
  forall t t',
  inv' t t' ->
  forall sigma sigma',
  (forall x, inv' (sigma x) (sigma' x)) ->
  inv' t.[sigma] t'.[sigma'].
Proof.
  induction t using term_ind'; intros; subst; asimpl.
  * ainv; asimpl; eauto.
  * ainv; asimpl. unfold inv' in *.
    edestruct (IHt t0).
    1:{ exists t'0; eauto. }
    2:{ exists (Lam x). split; unpack; eauto with nf. }
    1:{ intros. case x; asimpl.
        - exists (Var 0); eauto with nf.
        - intros. unfold lift.
          eapply inv'_ren.
          eapply H0. }
  * ainv; asimpl. unfold inv' in *.
    edestruct (IHt1 t0).
    { exists t1'; eauto. }
    { exact H0. }
    edestruct (IHt2 t3).
    { exists t2'; eauto. }
    { exact H0. }

    { unpack. eexists. split.
      econstructor; eauto.
      econstructor; eauto. }
  * admit.
  * rename H into IHts.

    inverts H0; unpack. inverts H. inverts H0. 
    
    edestruct (IHt1 tj).
    { repeat econstructor; eassumption. }
    { eapply H1. }

    edestruct (IHt2 tc).
    { repeat econstructor; eassumption. }
    { eapply H1. }

    assert (List.Forall2 nf ts..[sigma] ts'..[sigma]).
    {
      induction H5; asimpl; econstructor.
      - inverts IHts. unfold inv' in *.
        edestruct H12.
        { admit. }
        admit.
        admit.
      - admit.
    }

    asimpl; econstructor; unpack.
    split.
    - econstructor.
      3, 4: eassumption.
      admit.
      admit.
    - econstructor.
      3, 4: eassumption.
      admit.
      admit.
  * ainv; asimpl; repeat econstructor.
  * ainv; asimpl; repeat econstructor.
  * ainv; asimpl; repeat econstructor.
Admitted.


Lemma is_value_nf:
  forall v t, nf v t -> is_value v -> is_value t.
Proof.
  introv Hnf Hvalue.
  induction Hnf; simpl in Hvalue; destruct Hvalue; now simpl.
Qed.

Lemma is_value_nf':
  forall t1 t2, nf t1 t2 -> is_value t2 -> is_value t1.
Proof.
  introv Hnf Hvalue.
  induction Hnf; simpl in Hvalue; destruct Hvalue; now simpl.
Qed.

Lemma nf_subst:
  forall t t',
    nf t t' ->
    forall sigma sigma',
    (forall x, nf (sigma x) (sigma' x)) ->
    nf t.[sigma] t'.[sigma'].
Proof.
  introv Hnf.
  induction Hnf using nf_ind'; introv Hsigma; intros; asimpl.
  * eapply Hsigma.
  * admit.

  * econstructor.
    - now eapply IHHnf1.
    - now eapply IHHnf2.
  * econstructor.
  * econstructor.
  * econstructor.
  * econstructor.
    - now eapply IHHnf1.
    - now eapply IHHnf2.
  * econstructor.
    - assert (result: List.Forall2 nf ts..[sigma] ts'..[sigma]).
      {
        clear H1.
        induction H; asimpl; econstructor; inverts H0.
        * eapply H.
        * eapply IHForall2; eauto.
      }
      eapply result.
    - clear -H1.
      induction ts'; asimpl in *.
      + subst; asimpl; eauto.
      + (* this is false. a.[sigma] can be empty if a = Var x and sigma x = Empty while a is not Empty. The requirement on sigma is the same as before *)
        admit.
    - eapply IHHnf1.
    - eapply IHHnf2.
Admitted.  

Lemma inv'_subst':
  forall t1 t2, inv' t1 t2 -> forall v, is_value v -> inv' t1.[v/] t2.[v/].
Proof.
  introv [u [Hnf1 Hnf2]] Hval.
  eexists.
  split; eapply nf_subst; eauto.
Qed.

Theorem simulation_inv':
    forall c1 c2,  inv' c1  c2 ->
    forall c1', dcbv c1 c1' ->
    exists c2', inv' c1' c2' /\ dcbv c2 c2'
.
Proof.
  induction 1; intros c1' H_step; asimpl; inverts H_step; unpack; try solve [simpl in *; tryfalse].
  * ainv.
    forwards: is_value_nf v t2'; eauto.
    forwards: is_value_nf' t2 t2'; eauto.
    eexists; split.
    2: {
      eapply DCR.RedBetaV; simpl; eauto.
    }
    eapply inv...
    unfold inv'.

Admitted.


Theorem simulation_inv':
    forall c1 c1', dcbv c1 c1' ->
    forall c2,  inv' c1  c2 ->
    exists c2', inv' c1' c2' /\ dcbv c2 c2'
.
Proof.
  size_induction c1.
  destruct c1; intros.
  * inverts H; simpl in *; tryfalse.
  * inverts H; simpl in *; tryfalse.
  * inversion H; subst; simpl in *; tryfalse.
    - unfold inv' in H0.
      simpl in H0.
      destruct c2; simpl in H0; tryfalse.
      destruct c2_1; simpl in H0; tryfalse.
      injection H0; intros.
      eexists.
      split.
      2:{
        eapply DCR.RedBetaV.
        - simpl; eauto.
        - eauto using inv'_is_value.
        - reflexivity. 
      }
      unfold inv'.
      unfold 
    - 


  intro c1.
  set (n := size c1).
  assert (H_eqn : size c1 <= n). { eapply le_n. }
  clearbody n.
  induction n.
  { destruct c1; simpl in H_eqn. }
  * 
  intros.
  eexists; split.
  2: {

  }
  swap.



Print inv_ind.

Lemma inv_ind': forall P : dterm -> dterm -> Prop,
(forall x : var, P (Var x) (Var x)) ->
(forall t t' : dterm, inv t t' -> P t t' -> P (Lam t) (Lam t')) ->
(forall t1 t2 t1' t2' : dterm,
 inv t1 t1' ->
 P t1 t1' -> inv t2 t2' -> P t2 t2' -> P (App t1 t2) (App t1' t2')) ->
P Empty Empty ->
P Conflict Conflict ->
(forall a : bool, P (Const a) (Const a)) ->
(forall t1 t2 t1' t2' : dterm,
 inv t1 t1' ->
 P t1 t1' -> inv t2 t2' -> P t2 t2' -> P (Let t1 t2) (Let t1' t2')) ->
(forall (ts ts' : list dterm) (ts'' : list term)
   (tj tj' tc tc' : dterm),
 List.Forall2 P ts ts' ->
 List.Forall2 inv ts ts' ->
 ts'' =
 List.filter
   (fun ti : term => match ti with
                     | Empty => false
                     | _ => true
                     end) ts' ->
 inv tj tj' ->
 P tj tj' ->
 inv tc tc' -> P tc tc' -> P (Default ts tj tc) (Default ts'' tj' tc')) ->
forall d d0 : dterm, inv d d0 -> P d d0.
Proof.
  admit.
Admitted.

(* ok we need a stronger inductive predicate... *)

Require Import DCValues.

Lemma inv_is_value:
  forall v v',
  is_value v -> inv v v' -> is_value v'.
Proof.
  intros.
  induction v;
  try solve [simpl in *; tryfalse];
  pick inv invert; simpl; eauto.
Qed.

Lemma inv_ren:
  forall v v',
    inv v v' ->
  forall xi, inv v.[ren xi] v'.[ren xi].
Proof.
  introv Hinv. induction Hinv using inv_ind'; asimpl in *;
    try solve [econstructor; eauto].
  * econstructor; eauto.
    induction H.
    - simpl.
      admit.
    - econstructor; inverts_Forall.
      inverts_Forall. 
    -  
Admitted.

Print up.

Lemma bla:
  forall sigma sigma',
(forall x : var, inv (sigma x) (sigma' x)) ->
forall x : var, inv (up sigma x) (up sigma' x).
Proof.
  intros.
  case x.
  - econstructor.
  - intros. asimpl. admit.

Admitted.

(* does not work:
  with x |-> Empty, we have
  inv <x | ej :- ec> <x | ej :- ec>
  but
  inv <Empty | ej :- ec> < | ej :- ec> *)
Lemma inv_subst:
  forall v v',
  inv v v' ->
  forall sigma sigma',
  (forall x, inv (sigma x) (sigma' x)) ->
  inv v.[sigma] v'.[sigma'].
Proof.
  induction v; introv H; inverts H; asimpl;
  try solve [ econstructor; eauto | eauto ].
  * econstructor; eauto using IHv, bla.
  * econstructor; eauto using IHv, IHv0, bla.
  * introv Hsigma.
    apply Idefault with (ts'..[sigma']).
    - induction H3; asimpl; econstructor; eauto.
      { (* induction hypothesis *) admit. }
    - induction ts'; simpl; eauto.
      repeat fequal.
      admit.


    constructor with (ts'..[sigma]).
    constructor with (ts'..[sigma]).
    - (* induction hypothesis *)
      admit.
    - 
    econstructor. intros.
    econstructor; eauto.
    eapply IHv; eauto.
    intros. induction x; asimpl.
    - econstructor.
    - 




Theorem simulation_inv:
    forall c1 c1', dcbv c1 c1' ->
    forall c2, inv c1 c2 ->
    exists c2',
      plus dcbv c2 c2'
      /\ inv c1' c2'
.
Proof.
  intros c1 c1' Hcbv.
  induction Hcbv; try solve [simpl in *; tryfalse];
  intros c2 Hinv; inverts Hinv.
  * inverts H4.
    eexists; split; subst.
    - eapply plus_one.
      eapply DCR.RedBetaV; try eauto using inv_is_value.
    - subst. 


dterm dterm cbv cbv inv 


Inductive compiles: dterm -> lterm -> Prop :=
| CVar: forall x, compiles (DC.Var x) (LC.Var x)
| CLambda: forall t t',
  compiles t t' ->
  compiles (DC.Lam t) (LC.Lam t')
| CApp: forall t1 t1' t2 t2',
  compiles t1 t1' ->
  compiles t2 t2' ->
  compiles (DC.App t1 t2) (LC.Match t1' (VariantNone) (LC.App (Var 0) (lift 1 t2')))
.




Lemma correctness:
  let step1 := DCR.cbv in
  let step2 := LCR.cbv in
  let inv := compiles in
  let measure := fun _ => 0 in
  forall c1 c1', step1 c1 c1' ->
  forall c2, inv c1 c2 ->
  exists c2',
    (plus step2 c2 c2' \/ (star step2 c2 c2' /\ measure c1' < measure c1))
  /\ inv c1' c2'.
Proof.
  simpl.
  intros c1 c1' Hcbv1.
  induction Hcbv1; try solve [simpl in *; tryfalse];
  intros c2 Hinv; inverts Hinv.
  * eexists; split.
    - left.
      inverts H4.
      (* does not work. *)
      admit.
    - (* require an technical lemma *)
      admit.
  * eexists; split.
    - left.

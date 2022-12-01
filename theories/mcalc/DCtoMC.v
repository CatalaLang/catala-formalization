Require Import MCSyntax.
Require Import DCSyntax.

Require Import MyTactics.

Definition dterm := DCSyntax.term.

Module M := MCSyntax.

Fixpoint remove_options {A} (l: list (option A)): option (list A) :=
  match l with
  | nil => Some nil
  | cons (Some h) t =>
    match remove_options t with
    | Some t => Some (cons h t)
    | None => None
    end
  | cons None t => None
  end
.

Definition is_Some {A} (x: option A) :=
  match x with Some _ => True | _ => False end.

Lemma remove_options_spec {A} {l: list (option A)}:
  List.Forall is_Some l <->
  exists l', remove_options l = Some l'.
Proof. (* ugly proof *)
  split.
  * induction 1; simpl.
    - eexists; eauto.
    - destruct IHForall as [ l' Hl'].
      rewrite Hl'.
      induction x; simpl in *; tryfalse.
      eexists; eauto.
  * induction l; econstructor.
    - unzip.
      simpl in *.
      induction a; simpl; eauto.
      congruence.
    - eapply IHl.
      unzip. simpl in *.
      induction a; tryfalse.
      remember (remove_options l) as o.
      induction o; tryfalse. eauto.
Qed.

Definition return_ (t: M.term): option monad :=
  Some (Pure t).

Fixpoint bind_aux
  (m: monad)
  (cont: M.term -> option monad)
: option monad :=
  match m with
    M.Fake x => None
  | M.Empty => Some M.Empty
  | M.Conflict => Some M.Conflict
  | M.Bind m1 m2 =>
    match bind_aux m2 cont with
      Some m2' => Some (Bind m1 m2')
    | None => None
    end
  | M.Pure t => cont t

  | M.Default ms mj mc =>
    match cont (M.Var 0) with
      Some m' => Some (Bind (M.Default ms mj mc) m')
    | None => None
    end
  end.

Definition bind
  (m: option monad)
  (cont: M.term -> option monad)
: option monad :=
  match m with
  | Some m => bind_aux m cont
  | None => None
  end
.

Lemma bind_ex1: (bind (Some (Bind M.Empty (M.Pure (M.Var 0))))) (fun t => Some (Pure (M.App t t))) = Some (Bind M.Empty
   (Pure (M.App (M.Var 0) (M.Var 0)))).
Proof. simpl; eauto. Qed.


Lemma left_identity: forall a m, bind (return_ a) m = m a.
Proof.
  simpl; eauto.
Qed.

Lemma right_identity: forall m, bind m return_ = m.
Proof.
  induction m; simpl; eauto.
  induction a; simpl; eauto.
  - admit.
  - admit.
  - replace (bind_aux x return_) with (Some x).
    eauto.
Admitted.


Lemma associativity: forall m1 m2 m3,
  bind (bind m1 m2) m3 = bind m1 (fun x => bind (m2 x) m3).
Proof.
  induction m1.
  - intros.
    induction a using monad_ind'; simpl; eauto; admit.
  - simpl; eauto.
Admitted.

Definition bind2
  (m1: option monad)
  (m2: option monad)
  (cont: M.term -> M.term -> option monad)
: option monad :=
  bind m1 (fun t1 => bind m2 (fun t2 => cont t1 t2))
.


Compute (
  bind2
    (Some (Bind (M.Pure (M.Const true)) (M.Pure (M.Var 0))))
    (Some (Bind (M.Pure (M.Const false)) (M.Pure (M.Var 0))))
    (fun t1 t2 => return_ (M.App t1 t2))
  ). (* incorrect translation for the moment. *)

Fixpoint trans (t: dterm) : option monad :=
  match t with
    Empty => Some M.Empty
  | Conflict => Some M.Conflict
  | Lam t =>
    bind (trans t) (fun t => return_ (M.Lam t))
  | App t1 t2 =>
    bind2 (trans t1) (trans t2) (fun t1 t2 => return_ (M.App t1 t2))
  | Const b => Some (Pure (M.Const b))
  | Var x => Some (Pure (M.Var x))
  | Default ts tj tc =>
    let ms := remove_options (List.map trans ts) in
    let mj := trans tj in
    let mc := trans tc in

    match ms, mj, mc with
    Some ms, Some mj, Some mc => Some (M.Default ms mj mc)
    | _, _, _ => None
    end

  | _ => None
  end
.


(* no induction principle derived from this definition... *)
Example ex1: trans (App (Lam (Var 0)) (Const true)) = Some (Pure (M.App (M.Lam (M.Var 0)) (M.Const true))).
Proof.
  simpl; eauto.
Qed.

Example ex2: trans (Default nil (Const true) (Const false)) = Some (M.Default nil (Pure (M.Const true)) (Pure (M.Const false))).
Proof.
  simpl; eauto.
Qed.

Compute (trans ((Default nil (Const true) (Lam (Var 0))))).

Compute (bind (Some
(MCSyntax.Default nil (Pure (MCSyntax.Const true))
   (Pure (MCSyntax.Lam (MCSyntax.Var 0))))) (fun t => return_ (M.Lam t))).

Example ex3: trans (Lam (Default nil (Const true) (Lam (Var 0)))) =
  Some (
    Bind
      (M.Default nil (Pure (M.Const true)) (Pure (M.Lam (M.Var 0))))
      (Pure (M.Lam (M.Var 0)))
    )
    .
Proof.
  simpl. repeat f_equal.
Qed.

Example ex4: trans (App (Default nil (Const true) (Lam (Var 0))) (Const false)) =
  Some (
    Bind
      (M.Default nil (Pure (M.Const true)) (Pure (M.Lam (M.Var 0))))
      (Pure (M.App (M.Var 0) (M.Const false)))
    )
    .
Proof.
  simpl. repeat fequal.
Qed.

Example ex5: trans (App (Default nil (Const true) (Lam (Var 0))) (Default nil (Const false) (Lam (Var 0)))) =
  Some (
    Bind
      (M.Default nil (Pure (M.Const true)) (Pure (M.Lam (M.Var 0))))
      (Bind (M.Default nil (Pure (M.Const false)) (Pure (M.Lam (M.Var 0)))) (Pure (M.App (M.Var 0) (M.Var 1))))
    )
    .
Proof.
  simpl. repeat fequal. admit.
Admitted.


Require Import DCReduction.


(* this lemma is not true. Since [ [|Lam t|] = let* t = [|t|] in return_ (Lam t)], the transformation of Lam is not always an value. Hence, this lemmas does not hold. It is still true when v is Empty, Conflict, or an boolean, or when Lam does not have any defaults in its body. *)
Lemma is_value_trans_is_valuem:
  forall v, DCValuesRes.is_value_res v -> exists v', trans v = Some v' /\ is_valuem v'.
Proof.
  intros.
  induction v; simpl in H; tryfalse; simpl; eexists; simpl; eauto.
Abort.

Lemma checking_prop_on_subst:
  forall t v r, trans t.[v/] = Some r -> exists t' v', r = t'.|[v'/].
Proof.
  intros.
  (* does not holds *)
Abort.

(* does not holds *)
Lemma trans_correct: forall t1 t2,
  cbv t1 t2 ->
  forall t1',
  Some t1' = trans t1 -> 
  forall t2',
  Some t2' = trans t2 -> 
  (*--------------------*)
  M.redm t1' t2'
.
Proof.
  induction 1; tryfalse.
  * subst. simpl; intros.
    admit.
  * simpl; intros; tryfalse.
  * simpl.
    intros.
    (* I have no idea on how to prove this. *)
Abort.

Inductive is_pure : term -> Prop :=
  | PVar : forall x, is_pure (Var x)
  | PLam: forall t, is_pure t -> is_pure (Lam t)
  | PApp: forall t1 t2, is_pure t1 -> is_pure t2 -> is_pure (App t1 t2)
  | PConst: forall b, is_pure (Const b)
.

Lemma invert_trans_AppL:
  forall t1 t2 t', trans (App t1 t2) = Some t' -> exists t1', trans t1 = Some t1'.
Proof.
  intros.
  inverts H.
  unfold bind2 in *.
  unfold bind in *.
  remember (trans t1) as o.
  induction o; eauto.
Qed.

Lemma invert_trans_AppR:
  forall t1 t2 t', is_pure (App t1 t2) -> trans (App t1 t2) = Some t' -> exists t2', trans t2 = Some t2'.
Proof.
  introv Hpure H.
  inverts H.
  unfold bind2 in *.
  unfold bind in *.
  remember (trans t2) as o. 
  induction o; eauto.
  remember (trans t1) as oo.
  induction oo; eauto.
  induction a; eauto.
  - (* statment is false *) simpl in H1.
Abort.

Lemma trans_is_pure_is_pure:
  forall t, is_pure t -> exists t', trans t = Some (Pure t').
Proof.
  introv H.
  induction t; inverts H; tryfalse.
  * simpl; eexists; eauto.
  * destruct (IHt); eauto.
    simpl.
    rewrite H.
    simpl.
    unfold return_.
    eexists; eauto.
  * destruct (IHt1 H2); destruct (IHt2 H3).
    simpl.
    repeat match goal with [h: trans _ = Some (Pure _) |- _] => rewrite h end.
    simpl.
    unfold return_.
    eexists; eauto.
  * simpl.
    eexists; eauto.
Qed.


Lemma is_pure_renaming:
  forall t sigma,
  is_ren sigma ->
  is_pure t -> is_pure t.[sigma].
Proof.
  introv Hsigma Hpure; gen sigma.
  induction Hpure; introv Hsigma.
  * simpl. destruct Hsigma; subst. econstructor.
  * simpl. econstructor. eapply IHHpure.
    obvious.
  * simpl. econstructor; [eapply IHHpure1 |eapply IHHpure2]; eauto.
  * simpl; econstructor.
Qed.

Lemma is_pure_substitution:
  forall t sigma,
  (forall x, is_pure (sigma x)) ->
  is_pure t -> is_pure t.[sigma].
Proof.
  introv Hsigma Hpure. gen sigma.
  induction Hpure; introv Hsigma.
  * simpl. eapply Hsigma.
  * asimpl; econstructor; eapply IHHpure.
    induction x; asimpl.
    econstructor.
    eapply is_pure_renaming.
    - eexists; eauto.
    - eapply Hsigma.   
  * asimpl; econstructor; [eapply IHHpure1|eapply IHHpure2]; eauto.
  * asimpl; econstructor; eauto.
Qed.

Ltac is_pure := repeat match goal with
| [h: is_pure (Lam _) |- _] => inverts h
| [h: is_pure (App _ _) |- _] => inverts h
| [h: is_pure (Let _ _) |- _] => inverts h
| [h: is_pure (Default _ _ _) |- _] => inverts h
| [h: is_pure (Empty) |- _] => inverts h
| [h: is_pure (Conflict) |- _] => inverts h
| [h: is_pure (Const _) |- _] => inverts h
end; eauto.

Lemma cbv_is_pure_conserve:
  forall t1 t2, is_pure t1 -> cbv t1 t2 -> is_pure t2.
Proof.
  introv Hpure Hcbv.
  induction Hcbv; tryfalse; is_pure.
  * subst; eapply is_pure_substitution; eauto.
    induction x; asimpl; eauto; econstructor.
  * econstructor; eauto.
  * econstructor; eauto.
Qed.



Require Import Procrastination.

Lemma trans_is_pure_is_transp:
  exists trans_p, 
  forall t,
    is_pure t -> exists t', trans t = Some (Pure t') /\ trans_p t t'.
Proof.
  begin defer assuming transp.
  {
    exists transp.
    induction 1.
    * eexists.
      split.
      { simpl. reflexivity. }
      gen x; defer.
    * unzip. eexists; split.
      { simpl. rewrite H0; simpl. unfolds return_. reflexivity. }
      
      gen t x; defer.
    * unzip.
      eexists; split.
      simpl.
      repeat match goal with [h: trans _ = Some (Pure _) |- _] => rewrite h end.
      simpl; reflexivity.

      gen t1 t2 x0 x; defer.
    * eexists; simpl; split.
      reflexivity.
      gen b; defer.
  }
  end defer.
Abort.

Inductive transp: dterm -> M.term -> Prop:=
|TP_Var: (forall x : var, transp (Var x) (M.Var x))
|TP_Lam: (forall t : term,
 forall x : MCSyntax.term, transp t x -> transp (Lam t) (M.Lam x)) 
|TP_App: (forall t1 : term,
 forall t2 : term,
 forall x0 : MCSyntax.term,
 transp t1 x0 ->
 forall x : MCSyntax.term,
 transp t2 x -> transp (App t1 t2) (M.App x0 x)) 
|TP_Const: (forall b : bool, transp (Const b) (M.Const b))
.


Lemma trans_is_pure_is_transp:
  forall t,
    is_pure t -> exists t', transp t t' /\ trans t = Some (Pure t').
Proof.
  induction 1.
  * eexists; simpl; split; [econstructor|].
    eauto.
  * unzip; eexists; simpl; split; [econstructor|]; eauto.
    (* repeat rewrite $(trans _ = Some (Pure _)). *)
    repeat match goal with [h: trans _ = Some (Pure _) |- _] => rewrite h end.
    simpl; eauto.
  * unzip; eexists; simpl; split; [econstructor|]; eauto.
    repeat match goal with [h: trans _ = Some (Pure _) |- _] => rewrite h end.
    simpl; eauto.
  * unzip; eexists; simpl; split; [econstructor|]; eauto.
Qed.

Lemma trans_is_pure_is_transp':
  forall t t', is_pure t -> Some t' = trans t -> exists t'', t' = Pure t'' /\ transp t t''.
Proof.
  introv Hpure Htrans.
  forwards: trans_is_pure_is_transp Hpure.
  unzip. 
  eexists; split; eauto.
  rewrite <- Htrans in H0.
  injections.
  eauto.
Qed.


Lemma transp_value_conserve:
  forall v v', DCValuesRes.is_value_res v -> transp v v' -> M.is_value v'.
Proof.
  intros.
  match goal with [h: transp _ _ |- _] => induction h end; simpl in *; eauto.
Qed. 

Lemma trans_correct_pure:
  forall t1, forall t2, cbv t1 t2 ->
  forall t1', transp t1 t1' ->
  exists t2', transp t2 t2' /\ M.red t1' t2'.
Proof.
  (* we need a size induction since t.[v/] must be inside the induction hypothesis. *)

  introv Hcbv Htransp. gen t2.
  induction Htransp; introv Hcbv; inverts Hcbv; match goal with [h: cbv_mask _ |- _] => try solve [simpl h; tryfalse] end;
  repeat match goal with
  | [h: transp (Conflict) _ |- _] => inverts h
  | [h: transp (Empty) _ |- _] => inverts h
  end.
  * inverts Htransp1.
    eexists.
    split.
    2: {
      eapply M.RedBetaV. eapply transp_value_conserve; eauto.
      { (* whoups *) admit. }
      reflexivity. 
      }
      { (* todo *) admit. }
  *   
  * admit.
  * admit.
  * admit.
  * admit.
  * admit.
  * admit.
  * admit.

  * admit.
  * eexists.
    split.
    - econstructor.
  rename x into t1'.
  .
  * 
  induction Htransp; introv Hcbv; inverts Hcbv; .
  *  
  
  match goal with [h: transp t1 _ |- _] => rename h into Htransp end.
  rename x into t1'.

  induction Htransp; introv Hcbv; inverts Hcbv; match goal with [h: cbv_mask _ |- _] => try solve [simpl h; tryfalse] end.
  * admit.
  * 

  intros t1; induction t1; introv Ht1; inverts Ht1; introv Ht1t2 Ht2pure; inverts Ht1t2; try solve
    [ tryfalse
    | is_pure ].
  * is_pure.
    destruct (trans_is_pure_is_pure (App (Lam t) t1_2)).
    { repeat econstructor; eauto. }
    admit.

  * destruct (trans_is_pure_is_pure (App t1_1 t1_2)).
    { repeat econstructor; is_pure; eauto. }
    induction x; simpl in H.

  
    intros; simpl in *. is_pure.
    forwards bla: IHt1_1 H1 H7; eauto.
    2:{
      unzip.
      rewrite <- H0.
      simpl.
       
    { admit. }
    { unzip. rewrite <- H0. simpl. admit. }
  *  admit.
Admitted.

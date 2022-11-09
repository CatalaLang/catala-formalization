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
    induction a; simpl; eauto.
Admitted.

Definition bind2
  (m1: option monad)
  (m2: option monad)
  (cont: M.term -> M.term -> option monad)
: option monad :=
  bind m1 (fun t1 => bind m2 (fun t2 => cont t1 t2))
.



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
  simpl. repeat fequal.
Qed.

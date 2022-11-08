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

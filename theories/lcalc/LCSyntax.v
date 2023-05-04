Require Import Coq.Wellfounded.Inverse_Image.
Require Import MyTactics.
Require Export Autosubst.Autosubst.
Require Export AutosubstExtra.
Require Export Autosubst_IsRen.

Require Import Arith.
Require Import PeanoNat.
(* Require Export Autosubst_EOS. *)

Require Import Arith.Wf_nat.
Require Export Autosubst_FreeVars.

(* The syntax of the lambda-calculus. *)

Inductive term :=
| Var (x : var)
| Lam (t : {bind term})
| App (t1 t2 : term)
| Let (t1 : term) (t2 : {bind term})
| Match (tc t1: term) (t2 : {bind term})
| VariantNone
| VariantSome (t: term)
.

Definition monad_bind arg (body: {bind term}) :=
  Match arg VariantNone body.

Definition monad_return arg :=
  VariantSome arg.

Definition monad_empty :=
  VariantNone.

Definition monad_map arg (body: {bind term}):=
  monad_bind arg (monad_return body).

Definition monad_mbind (args: list term) (body: {bind term}): term :=
  List.fold_right (monad_bind) body args
  (* equivalent to 
  fix monad_mbind_aux (args : list B) : A :=
  match l with
  | nil => body
  | (arg :: args)%list => f arg (monad_mbind_aux args)
  end
 *)
.

Definition monad_mmap args (body: {bind term}): term :=
  (* unsure about this one, but it should work since the body bind is working. *)
  monad_mbind args (monad_return body)
.

#[export] Instance Ids_term : Ids term. derive. Defined.  
#[export] Instance Rename_term : Rename term. derive. Defined.
#[export] Instance Subst_term : Subst term. derive. Defined.
#[export] Instance SubstLemmas_term : SubstLemmas term. derive. Qed.
#[export] Instance IdsLemmas_term : IdsLemmas term.
Proof. econstructor. intros. injections. eauto. Qed.

(* If the image of [t] through a substitution is a variable, then [t] must
   itself be a variable. *)

Lemma subst_is_var:
  forall t sigma x,
  t.[sigma] = ids x ->
  exists y,
  t = ids y.
Proof.
  intros ? ? ? Heq. destruct t; compute in Heq; solve [ eauto | congruence ].
Qed.

(* The identity substitution [ids] is injective. *)

Lemma inj_ids:
  forall x y,
  ids x = ids y ->
  x = y.
Proof.
  intros ? ? Heq. compute in Heq. congruence.
Qed.

(* If the composition of two substitutions [sigma1] and [sigma2] is the
   identity substitution, then [sigma1] must be a renaming. *)

Lemma ids_implies_is_ren:
  forall sigma1 sigma2,
  sigma1 >> sigma2 = ids ->
  is_ren sigma1.
Proof.
  intros ? ? Hid.
  eapply prove_is_ren; [ eapply inj_ids | intros x ].
  eapply subst_is_var with (sigma := sigma2) (x := x).
  rewrite <- Hid. reflexivity.
Qed.

Global Hint Resolve ids_implies_is_ren : is_ren obvious.

(* The size of a term. *)

Fixpoint size (t : term) : nat :=
  match t with
  | Var _ => 0
  | Lam t => 1 + size t
  | App t1 t2
  | Let t1 t2 => 1 + size t1 + size t2
  | Match tc t1 t2 =>
    1 + size tc + size t1 + size t2
  | VariantNone => 0
  | VariantSome t => 1 + size t
  end.

(* The size of a term is preserved by renaming. *)

Lemma size_renaming:
  forall t sigma,
  is_ren sigma ->
  size t.[sigma] = size t.
Proof.
  induction t; intros sigma Hsigma; asimpl;
  repeat (match goal with h: forall sigma, _ |- _ => rewrite h by obvious; clear h end);
  try reflexivity.
  (* [Var] *)
  { destruct Hsigma as [ xi ? ]. subst. reflexivity. }
Qed.

(* The [size] function imposes a well-founded ordering on terms. *)

Lemma smaller_wf:
  well_founded (fun t1 t2 => size t1 < size t2).
Proof.
  eauto using wf_inverse_image, lt_wf.
Qed.

(* The tactic [size_induction] facilitates proofs by induction on the
   size of a term. The following lemmas are used in the construction
   of this tactic. *)

Lemma size_induction_intro:
  forall (P : term -> Prop),
  (forall n t, size t < n -> P t) ->
  (forall t, P t).
Proof.
  eauto. (* just instantiate [n] with [size t + 1] *)
Defined.

Lemma size_induction_induction:
  forall (P : term -> Prop),
  (forall n, (forall t, size t < n -> P t) -> (forall t, size t < S n -> P t)) ->
  (forall n t, size t < n -> P t).
Proof.
  intros P IH. induction n; intros.
  { false. eapply Nat.nlt_0_r. eauto. }
  { eauto. }
Defined.

Lemma size_induction:
  forall (P : term -> Prop),
  (forall n, (forall t, size t < n -> P t) -> (forall t, size t < S n -> P t)) ->
  (forall t, P t).
Proof.
  intros P IH.
  eapply size_induction_intro.
  eapply size_induction_induction.
  eauto.
Defined.

Ltac size_induction t :=
  (* We assume the goal is of the form [forall t, P t]. *)
  intro t; pattern t;
  match goal with |- ?P t =>
    simpl; eapply (@size_induction P); clear
  end;
  intros n IH t Htn.
  (* The goal should now be of the form [P t]
     with a hypothesis [IH: (forall t, size t < n -> P t]
     and a hypothesis [Htn: size t < S n]. *)

(* The tactic [size] proves goals of the form [size t < n]. The tactic
   [obvious] is also extended to prove such goals. *)

Global Hint Extern 1 (size ?t.[?sigma] < ?n) =>
  rewrite size_renaming by obvious
  : size obvious.

Global Hint Extern 1 (size ?t < ?n) =>
  simpl in *; lia
  : size obvious.

Ltac size :=
  eauto with size.

(* The following is a direct proof of [smaller_wf]. We do not use any
   preexisting lemmas, and end the proof with [Defined] instead of [Qed],
   so as to make the proof term transparent. Also, we avoid the tactic
   [lia], which produces huge proof terms. This allows Coq to compute
   with functions that are defined by well-founded recursion. *)

Lemma smaller_wf_transparent:
  well_founded (fun t1 t2 => size t1 < size t2).
Proof.
  unfold well_founded. size_induction t.
  constructor; intros u Hu.
  eapply IH. eauto with arith.
Defined.

(* The following lemmas can be useful in situations where the tactic
   [asimpl] performs too much simplification. *)

Lemma subst_var:
  forall x sigma,
  (Var x).[sigma] = sigma x.
Proof.
  autosubst.
Qed.

Lemma subst_lam:
  forall t sigma,
  (Lam t).[sigma] = Lam (t.[up sigma]).
Proof.
  autosubst.
Qed.

Lemma subst_app:
  forall t1 t2 sigma,
  (App t1 t2).[sigma] = App t1.[sigma] t2.[sigma].
Proof.
  autosubst.
Qed.

Lemma subst_let:
  forall t1 t2 sigma,
  (Let t1 t2).[sigma] = Let t1.[sigma] t2.[up sigma].
Proof.
  autosubst.
Qed.

Lemma subst_variant_none:
  forall sigma,
  VariantNone.[sigma] = VariantNone.
Proof.
  autosubst.
Qed.


Lemma subst_variant_some:
  forall t1 sigma,
  (VariantSome t1).[sigma] = VariantSome t1.[sigma].
Proof.
  autosubst.
Qed.


Lemma subst_match:
  forall tb t1 t2 sigma,
  (Match tb t1 t2).[sigma] = Match tb.[sigma] t1.[sigma] t2.[up sigma].
Proof.
  autosubst.
Qed.

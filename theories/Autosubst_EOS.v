Require Import Arith.
Require Import Psatz.
Require Import Autosubst.Autosubst.
Require Import AutosubstExtra. (* just for [upn_ren] *)
Require Import tactics.
Require Import Arith.Compare_dec.

(* This file defines the construction [eos x t], which can be understood as
   an end-of-scope mark for [x] in the term [t]. *)

(* It also defines the single-variable substitution t.[u // x], which is the
   substitution of [u] for [x] in [t]. *)

(* -------------------------------------------------------------------------- *)

Section EOS.

Context {A} `{Ids A, Rename A, Subst A, SubstLemmas A}.

(* The substitution [Var 0 .: Var 1 .: ... .: Var (x-1) .: Var (x+1) .: ...]
   does not have [Var x] in its codomain. Thus, applying this substitution
   to a term [t] can be understood as an end-of-scope construct: it means
   ``end the scope of [x] in [t]''. We write [eos x t] for this construct.
   It is also known as [adbmal]: see Hendriks and van Oostrom,
   https://doi.org/10.1007/978-3-540-45085-6_11 *)

(* There are at least two ways of defining the above substitution. One way
   is to define it in terms of AutoSubst combinators: *)

Definition eos_var x : var -> var :=
  (iterate upren x (+1)).

Definition eos x t :=
  t.[ren (eos_var x)].

Lemma eos_eq:
  forall x t,
  t.[upn x (ren (+1))] = eos x t.
Proof.
  intros. unfold eos, eos_var.
  erewrite upn_ren by eauto with typeclass_instances.
  reflexivity.
Qed.

(* Another way is to define directly as a function of type [var -> var]. *)

Definition lift_var x : var -> var :=
  fun y => if le_gt_dec x y then 1 + y else y.

(* The two definitions coincide: *)

Lemma upren_lift_var:
  forall x,
  upren (lift_var x) = lift_var (S x).
Proof.
  intros. f_ext; intros [|y].
  { reflexivity. }
  { simpl. unfold lift_var, var.
    induction (le_gt_dec x y);
    induction (le_gt_dec (S x) (S y));
    lia. }
Qed.

Lemma eos_var_eq_lift_var:
  eos_var = lift_var.
Proof.
  (* An uninteresting proof. *)
  f_ext; intros x.
  unfold eos_var.
  induction x.
  { reflexivity. }
  { rewrite iterate_S.
    rewrite IHx.
    rewrite upren_lift_var.
    reflexivity. }
Qed.

(* -------------------------------------------------------------------------- *)

(* [eos] enjoys certain commutation laws. *)

(* Ending the scope of variable [k], then the scope of variable [s], is the
   same as first ending the scope of variable [1 + s], then ending the scope
   of variable [k]. This holds provided [k <= s] is true, i.e., [k] is the
   most recently-introduced variable.*)

Lemma lift_var_lift_var:
  forall k s,
  k <= s ->
  lift_var s >>> lift_var k = lift_var k >>> lift_var (S s).
Proof.
  (* By case analysis. *)
  intros. f_ext; intros x. asimpl.
  unfold lift_var, var. dblib_by_cases; lia.
Qed.

Lemma eos_eos:
  forall k s t,
  k <= s ->
  eos k (eos s t) = eos (1 + s) (eos k t).
Proof.
  intros. unfold eos. asimpl.
  rewrite eos_var_eq_lift_var.
  rewrite lift_var_lift_var by eauto.
  reflexivity.
Qed.

(* What about the case where [k] is the least recently-introduced variable?
   It is obtained by symmetry, of course. *)

Lemma eos_eos_reversed:
  forall k s t,
  k >= s + 1 ->
  eos k (eos s t) = eos s (eos (k - 1) t).
Proof.
  intros.
  replace k with (1 + (k - 1)) by lia.
  rewrite <- eos_eos by lia.
  replace (1 + (k - 1) - 1) with (k - 1) by lia.
  reflexivity.
Qed.

(* -------------------------------------------------------------------------- *)

(* Single-variable substitutions. *)

(* [subst_var u x] is the substitution of [u] for [x]. *)

(* We give a direct definition of it as a function of type [var -> term],
   defined by cases. I don't know if it could also be nicely defined in
   terms of the basic combinators of de Bruijn algebra. Note that the
   candidate definition [upn x (t .: ids)] is WRONG when [x > 0]. *)

Definition subst_var (u : A) (x y : var) : A :=
  match lt_eq_lt_dec y x with
  | inleft (left _)  => ids y
  | inleft (right _) => u
  | inright _        => ids (y - 1)
end.

(* A nice notation: [t.[u // x]] is the substitution of [u] for [x] in [t]. *)

Notation "t .[ u // x ]" := (subst (subst_var u x) t)
  (at level 2, u at level 200, left associativity,
   format "t .[ u // x ]") : subst_scope.

(* The following laws serve as sanity checks: we got the definition right. *)

Lemma subst_var_miss_1:
  forall x y u,
  y < x ->
  (ids y).[u // x] = ids y.
Proof.
  intros. asimpl. unfold subst_var. dblib_by_cases. reflexivity.
Qed.

Lemma subst_var_match:
  forall x u,
  (ids x).[ u // x ] = u.
Proof.
  intros. asimpl. unfold subst_var. dblib_by_cases. reflexivity.
Qed.

Lemma subst_var_miss_2:
  forall x y u,
  x < y ->
  (ids y).[u // x] = ids (y - 1).
Proof.
  intros. asimpl. unfold subst_var. dblib_by_cases. reflexivity.
Qed.

(* In the special case where [x] is 0, the substitution [t // 0] can also
   be written [t/], which is an AutoSubst notation for [t .: ids]. *)

Lemma subst_var_0:
  forall t u,
  t.[u // 0] = t.[u/].
Proof.
  intros. f_equal. clear t.
  f_ext. intros [|x].
  { reflexivity. }
  { unfold subst_var. simpl. f_equal. lia. }
Qed.

(* -------------------------------------------------------------------------- *)

(* A cancellation law: substituting for a variable [x] that does not occur in
   [t] yields just [t]. In other words, a substitution for [x] vanishes when
   it reaches [eos x _]. *)

(* In informal syntax, this lemma would be written:

     t[u/x] = t

   under the hypothesis that x does not occur free in t.

   In de Bruijn style, the statement is just as short, and does not have a
   side condition. Instead, it requires an explicit [eos x _] to appear at the
   root of the term to which the substitution is applied; this may require
   rewriting before this lemma can be applied. *)

Lemma subst_eos:
  forall x t u,
  (eos x t).[u // x] = t.
Proof.
  intros.
  (* Again, let's simplify this first. *)
  unfold eos. asimpl.
  (* Aha! We can forget about [t], and focus on proving that two
     substitutions are equal. To do so, it is sufficient that
     their actions on a variable [y] are the same. *)
  rewrite <- subst_id.
  f_equal. clear t.
  f_ext. intro y.
  (* The proof is easy if we replace [eos_var] with [lift_var]. *)
  rewrite eos_var_eq_lift_var. simpl.
  unfold subst_var, lift_var. dblib_by_cases; f_equal; lia.
Qed.

(* The above property allows us to prove that [eos x _] is injective.
   Indeed, it has an inverse, namely [u // x], where [u] is arbitrary. *)

Lemma eos_injective:
  forall x t1 t2,
  eos x t1 = eos x t2 ->
  t1 = t2.
Proof.
  intros.
  pose (u := t1). (* dummy *)
  erewrite <- (subst_eos x t1 u).
  erewrite <- (subst_eos x t2 u).
  congruence.
Qed.

(* -------------------------------------------------------------------------- *)

(* More commutation laws. *)

Lemma eos_subst_1:
  forall k s t u,
  k <= s ->
  eos k (t.[u // s]) = (eos k t).[eos k u // s + 1].
Proof.
  intros. unfold eos. asimpl. f_equal. clear t.
  rewrite eos_var_eq_lift_var.
  f_ext. intros y.
  asimpl.
  unfold subst_var, lift_var.
  dblib_by_cases; asimpl; dblib_by_cases; solve [ eauto | f_equal; lia ].
Qed.

Lemma eos_subst_2:
  forall k s t u,
  s <= k ->
  eos k (t.[u // s]) = (eos (k + 1) t).[eos k u // s].
Proof.
  intros. unfold eos. asimpl. f_equal. clear t.
  rewrite eos_var_eq_lift_var.
  f_ext. intros y.
  asimpl.
  unfold subst_var, lift_var.
  dblib_by_cases; asimpl; dblib_by_cases; solve [ eauto | f_equal; lia ].
Qed.

Lemma subst_subst:
  forall t k v s w,
  k <= s ->
  t.[w // k].[v // s] =
  t.[eos k v // 1 + s].[w.[v // s] // k].
Proof.
  (* First, get rid of [t]. It is sufficient to consider the action of
     these substitutions at a variable [y]. *)
  intros. asimpl. f_equal. clear t. f_ext. intros y.
  (* Replace [eos_var] with [lift_var], whose definition is more direct. *)
  unfold eos. rewrite eos_var_eq_lift_var.
  (* Then, use brute force (case analysis) to prove that the goal holds. *)
  unfold subst_var. simpl.
  dblib_by_cases; asimpl; dblib_by_cases;
    (* This case analysis yields 5 cases, of which 4 are trivial... *)
    eauto.
  (* ... thus, one case remains. *)
  (* Now get rid of [v]. It is again sufficient to consider the action
     of these substitutions at a variable [z]. *)
  replace v with v.[ids] at 1 by autosubst.
  f_equal. f_ext. intros z. simpl.
  (* Again, use brute force. *)
  unfold lift_var. dblib_by_cases; f_equal. unfold var. lia.
  (* Not really proud of this proof. *)
Qed.

Lemma pun_1:
  forall t x,
  (eos x t).[ ids x // x + 1 ] = t.
Proof.
  (* First, get rid of [t]. It is sufficient to consider the action of
     these substitutions at a variable [y]. *)
  intros. unfold eos. asimpl.
  replace t with t.[ids] at 2 by autosubst.
  f_equal. clear t. f_ext. intros y.
  (* Replace [eos_var] with [lift_var], whose definition is more direct. *)
  rewrite eos_var_eq_lift_var.
  (* Then, use brute force (case analysis) to prove that the goal holds. *)
  simpl. unfold subst_var, lift_var. dblib_by_cases; f_equal; unfold var; lia.
Qed.

Lemma pun_2:
  forall t x,
  (eos (x + 1) t).[ ids x // x ] = t.
Proof.
  (* First, get rid of [t]. It is sufficient to consider the action of
     these substitutions at a variable [y]. *)
  intros. unfold eos. asimpl.
  replace t with t.[ids] at 2 by autosubst.
  f_equal. clear t. f_ext. intros y.
  (* Replace [eos_var] with [lift_var], whose definition is more direct. *)
  rewrite eos_var_eq_lift_var.
  (* Then, use brute force (case analysis) to prove that the goal holds. *)
  simpl. unfold subst_var, lift_var. dblib_by_cases; f_equal; unfold var; lia.
Qed.

End EOS.

(* Any notations defined in the above section must now be repeated. *)

Notation "t .[ u // x ]" := (subst (subst_var u x) t)
  (at level 2, u at level 200, left associativity,
   format "t .[ u // x ]") : subst_scope.

(* The tactic [subst_var] attempts to simplify applications of [subst_var]. *)

Ltac subst_var :=
  first [
    rewrite subst_var_miss_1 by lia
  | rewrite subst_var_match by lia
  | rewrite subst_var_miss_2 by lia
  ].

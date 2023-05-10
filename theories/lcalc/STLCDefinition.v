Require Import MyTactics.
Require Import LCSyntax.
Require Import LCValues.
Require Import LCReduction.
Require Import Arith.

(* for flip *)
Require Import Coq.Program.Basics.

Require Import LCFreeVars.

(*|

-----
Types
-----

Here is the syntax of simple types:

|*)

Inductive ty :=
| TyVar (x : var)
| TyFun (A B : ty)
| TyOption (T: ty)
| TyBool.

Fixpoint size (T: ty) { struct T } :=
  match T with
  | TyVar _ => 0
  | TyFun A B => 1 + size A + size B
  | TyOption A => 1 + size A
  | TyBool => 1
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

Notation "A @-> B" := (TyFun A B) (at level 49, right associativity).

Inductive jt_op : operator -> ty -> Prop :=
| TO_if: forall A, jt_op OIf (TyBool @-> A @-> A @-> A)
.


Inductive jt : tyenv -> term -> ty -> Prop :=
| JTVar:
    forall Gamma x T,
    Gamma x = T ->
    jt Gamma (EVar x) T
| JTLam:
    forall Gamma t T U,
    jt (T .: Gamma) t U ->
    jt Gamma (ELam t) (TyFun T U)
| JTApp:
    forall Gamma t1 t2 T U,
    jt Gamma t1 (TyFun T U) ->
    jt Gamma t2 T ->
    jt Gamma (EApp t1 t2) U
| JtNone:
  forall Gamma T,
  jt Gamma EVariantNone (TyOption T)
| JtSome:
  forall Gamma t T,
  jt Gamma t T ->
  jt Gamma (EVariantSome t) (TyOption T)
| JtMatch:
  forall Gamma tc t1 t2 T U,
  jt Gamma tc (TyOption U) ->
  jt Gamma t1 T ->
  jt ( U .: Gamma) t2 T ->
  jt Gamma (EMatch tc t1 t2) T
| JtPanic:
  forall Gamma exp T,
  jt Gamma (EPanic exp) T
| JtOp:
  forall Gamma op T,
  jt_op op T ->
  jt Gamma op T
.

Lemma jt_determ:
  forall Gamma x T,
  jt Gamma (EVar x) T ->
  forall U,
  jt Gamma (EVar x) U ->
  T = U.
Proof.
  intros Gamma t x Hjtx.
  inverts Hjtx.
  intros.
  now inverts H.
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


Global Hint Constructors jt_op : jt.
Global Hint Constructors jt : jt.


(*|
---------------------------
Renamings of term variables
---------------------------
|*)

(*|

The typing judgement is preserved by a renaming `xi` that maps
term variables to term variables. Note that `xi` need not be
injective.

|*)

Lemma jt_te_renaming:
  forall Gamma t U,
  jt Gamma t U ->
  forall Gamma' xi,
  Gamma = xi >>> Gamma' ->
  jt Gamma' t.[ren xi] U.
Proof.
  (* dup 2. {
    (* A detailed proof, where every case is dealt with explicitly: *)
    induction 1; intros; subst.
    (* JTVar *)
    { asimpl. econstructor. eauto. }
    (* JTLam *)
    { asimpl. econstructor. eapply IHjt. autosubst. }
    (* JTApp *)
    { asimpl. econstructor. eauto. eauto. }
    { asimpl. econstructor. }
    { asimpl. econstructor. eauto. }
    { asimpl. econstructor. eauto. eauto.
      eapply IHjt3. autosubst. }
  } *) 
  (* A shorter script, where all cases are dealt with uniformly: *)
  induction 1; intros; subst; asimpl;
  econstructor; eauto with autosubst.
Qed.

(*|

As a corollary, `jt` is preserved by the renaming `(+1)`.

|*)

Lemma jt_te_renaming_0:
  forall Gamma t T U,
  jt Gamma t U ->
  jt (T .: Gamma) (lift 1 t) U.
Proof.
  intros. eapply jt_te_renaming. eauto. autosubst.
Qed.

(*|
-----------------------------------------
Substitutions of terms for term variables
-----------------------------------------
|*)

(*|

The typing judgement is extended to substitutions of terms for term
variables.

With respect to a type environment `Gamma`, a substitution `sigma` has
type `Delta` if and only if, for every variable `x`, the term `sigma
x` has type `Delta x`.

This auxiliary judgement encourages us to think of terms of *total*
substitutions, where *every* variable is replaced by a term. This
concept turns out to be easier to understand and manipulate,
especially during proofs by induction. Of course one always later
consider the special case of a substitution that seems to affect just
one variable, say variable 0. (In reality, such a substitution affects
all variables, as the variables other than 0 are renumbered.)

|*)

Definition js Gamma sigma Delta :=
  forall x : var,
  jt Gamma (sigma x) (Delta x).

(*|

The following are basic lemmas about `js`.

The identity substitution has type `Gamma` in environment `Gamma`.

|*)

Lemma js_ids:
  forall Gamma,
  js Gamma ids Gamma.
Proof.
  unfold js. eauto with jt.
Qed.

(*|

The typing judgement `js` behaves like an infinite list of typing judgements
`jt`. So, one can prepend one more `jt` judgement in front of it.

|*)

Lemma js_cons:
  forall Gamma t sigma T Delta,
  jt Gamma t T ->
  js Gamma sigma Delta ->
  js Gamma (t .: sigma) (T .: Delta).
Proof.
  intros. intros [|x]; asimpl; eauto.
Qed.

(*|

The typing judgement `js` is preserved by the introduction of a new term
variable. That is, a typing judgement `js` can be pushed under a
lambda-abstraction.

|*)

Lemma js_up:
  forall Gamma sigma Delta T,
  js Gamma sigma Delta ->
  js (T .: Gamma) (up sigma) (T .: Delta).
Proof.
  intros. eapply js_cons.
  { eauto with jt. }
  { intro x. asimpl. eauto using jt_te_renaming_0. }
Qed.

(*|

The typing judgement is preserved by a well-typed substitution `sigma`
of (all) term variables to terms.

|*)

Lemma jt_te_substitution:
  forall Delta t U,
  jt Delta t U ->
  forall Gamma sigma,
  js Gamma sigma Delta ->
  jt Gamma t.[sigma] U.
Proof.
  (* A short script, where all cases are dealt with in the same way: *)
  induction 1; intros; subst; asimpl; eauto using js_up with jt.
  * econstructor; eauto.
    - eauto using js_up, IHjt3. 
Qed.

(*|

As a corollary, the typing judgement is preserved by a well-typed
substitution of one term for one variable, namely variable 0.

This property is exploited in the proof of subject reduction, in the
case of beta-reduction.

|*)

Lemma jt_te_substitution_0:
  forall Gamma t1 t2 T U,
  jt (T .: Gamma) t1 U ->
  jt Gamma t2 T ->
  jt Gamma t1.[t2/] U.
Proof.
(*
  (* One can do the proof step by step as follows: *)
  intros. eapply jt_te_substitution.
  { eauto. }
  { eapply js_cons.
    { eauto. }
    { eapply js_ids. } }
  (* Of course one can also let Coq find the proof by itself: *)
  Restart.*) eauto using jt_te_substitution, js_ids, js_cons.
Qed.



(*|
-----------------------------------------
Smart constructor for monadic constructs.
-----------------------------------------
|*)



Ltac unfold_monad :=
  unfold monad_handle;
  unfold monad_handle_one;
  unfold monad_handle_zero;
  unfold monad_mmap;
  unfold monad_mbind;

  unfold monad_map;
  unfold monad_bind;
  unfold monad_empty;
  unfold monad_return;
  eauto with jt.


Lemma JTmonad_return Gamma t T:
  jt Gamma t T -> jt Gamma (monad_return t) (TyOption T)
.
Proof.
  unfold_monad.
Qed.

Lemma JTmonad_empty Gamma T:
  jt Gamma (monad_empty) (TyOption T)
.
Proof.
  unfold_monad.
Qed.
Lemma JTmonad_bind Gamma arg body A B:
  jt Gamma arg (TyOption A) ->
  jt (A .: Gamma) body (TyOption B) ->
  jt Gamma (monad_bind arg body) (TyOption B)
.
Proof.
  unfold_monad.
Qed.

Lemma JTmonad_map Gamma arg body A B:
  jt Gamma arg (TyOption A) ->
  jt (A .: Gamma) body B ->
  jt Gamma (monad_map arg body) (TyOption B)
.
Proof.
  unfold_monad.
Qed.




Lemma JTmonad_mbind Gamma args body As B:
  List.Forall2 (fun arg A => jt Gamma arg (TyOption A)) args As ->
  jt (List.fold_left (flip scons) As Gamma) body (TyOption B) ->
  jt Gamma (monad_mbind args body) (TyOption B).
Proof.
  gen Gamma body As B.
  induction args.
  * introv HFA Hjt.
    inverts HFA.
    eauto.
  * intros.
    asimpl.
    inverts H.
    eapply JTmonad_bind.
    eapply H3.
    unfold monad_mbind in IHargs.
    eapply IHargs.
    2:{
      asimpl in *.
      unfold flip at 2 in H0.
      eauto.
    }
    { admit. }
Abort.


Lemma JTmonad_mmap Gamma args body As B:
  List.Forall2 (fun arg A => jt Gamma arg (TyOption A)) args As ->
  jt (List.fold_right scons Gamma As) body B ->
  jt Gamma (monad_mmap args body) (TyOption B).
Proof.
  unfold monad_mmap.
  intros; (* eapply JTmonad_mbind *)admit; eauto.
  (* * now eapply JTmonad_return. *)
Abort.

Lemma JTmonad_handle_one Gamma ts A:
  List.Forall (fun ti => jt Gamma ti (TyOption A)) ts ->
  jt (A .: Gamma) (monad_handle_one ts) (TyOption A)
.
Proof.
  induction 1; simpl.
  * eauto with jt.
  * econstructor; try eauto with jt.
    - eapply jt_te_renaming_0.
      eauto.
Qed.

Lemma JTmonad_handle_zero Gamma ts tj tc A:
  List.Forall (fun ti => jt Gamma ti (TyOption A)) ts ->
  jt Gamma tj (TyOption TyBool) ->
  jt Gamma tc (TyOption A) ->
  jt Gamma (monad_handle_zero ts tj tc) (TyOption A)
.
Proof.
  gen Gamma tj tc A.
  induction ts; asimpl.
  * intros.
    unfold_monad.
    eapply JtMatch; try eassumption.
    - econstructor.
    - assert (jt (TyBool .: Gamma) (lift 1 tc) (TyOption A)).
      { eapply jt_te_renaming_0. eauto. }
      repeat (econstructor; try eassumption).
  * intros; inverts_Forall.
    repeat econstructor; try eassumption.
    - eapply IHts; eauto.
    - eapply JTmonad_handle_one; eauto.
Qed.


Lemma JTmonad_handle Gamma ts tj tc A:
  List.Forall (fun ti => jt Gamma ti (TyOption A)) ts ->
  jt Gamma tj (TyOption TyBool) ->
  jt Gamma tc (TyOption A) ->
  jt Gamma (monad_handle ts tj tc) (TyOption A)
.
Proof.
  eapply JTmonad_handle_zero.
Qed.

Global Hint Resolve 
  JTmonad_return
  JTmonad_empty
  JTmonad_bind
  JTmonad_map
  (* JTmonad_mbind *)
  (* JTmonad_mmap *)
  JTmonad_handle_one
  JTmonad_handle_zero
  JTmonad_handle: jt.

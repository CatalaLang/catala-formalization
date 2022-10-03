Require Import List.
Require Import MyTactics.
Require Import MySequences.
Require Import DCSyntax.
Require Import DCFreeVars.
Require Import DCValues.
Require Import DCReduction.

(* -------------------------------------------------------------------------- *)
(* -------------------------------------------------------------------------- *)

(* A big-step call-by-value semantics. *)

Inductive bigcbv : term -> term -> Prop :=
| BigcbvValue:
    forall v,
    is_value v ->
    bigcbv v v
| BigcbvApp:
    forall t1 t2 u1 v2 v,
    bigcbv t1 (Lam u1) ->
    bigcbv t2 v2 ->
    bigcbv u1.[v2/] v ->
    bigcbv (App t1 t2) v
| BigcbvLet:
    forall t1 t2 v1 v,
    bigcbv t1 v1 ->
    bigcbv t2.[v1/] v ->
    bigcbv (Let t1 t2) v
.

Global Hint Constructors bigcbv : bigcbv.

(* The tactic [invert_bigcbv] looks for a hypothesis of the form [bigcbv t v]
   and inverts it. *)

Ltac invert_bigcbv :=
  pick bigcbv invert;
  try solve [ false; eauto 3 with obvious ].

(* -------------------------------------------------------------------------- *)

(* If [bigcbv t v] holds, then [v] must be a value. *)

Lemma bigcbv_is_value:
  forall t v,
  bigcbv t v ->
  is_value v.
Proof.
  induction 1; eauto.
Qed.

Global Hint Resolve bigcbv_is_value : is_value obvious.

(* -------------------------------------------------------------------------- *)

(* If [t] evaluates to [v] according to the big-step semantics,
   then [t] reduces to [v] according to the small-step semantics. *)

Lemma bigcbv_star_cbv:
  forall t v,
  bigcbv t v ->
  star cbv t v.
Proof.
(*
  (* A detailed proof: *)
  induction 1.
  (* BigcbvValue *)
  { eapply star_refl. }
  (* BigcbvApp *)
  { eapply star_trans. obvious.
    eapply star_trans. obvious.
    eapply star_step. obvious.
    eauto. }
  (* BigcbvLet *)
  { eapply star_trans. obvious.
    eapply star_step. obvious.
    eauto. }
Restart.*)
  (* A much shorter proof: *)
  induction 1; eauto 6 with sequences obvious.
Qed.

(* Conversely, if [t] reduces to [v] in the small-step semantics,
   then [t] evaluates to [v] in the big-step semantics. *)

Lemma cbv_bigcbv_bigcbv:
  forall t1 t2,
  cbv t1 t2 ->
  forall v,
  bigcbv t2 v ->
  bigcbv t1 v.
Proof.

  (* A detailed proof: *)
  induction 1; intros; subst; try solve [ false; tauto ].
  (* BetaV *)
  { econstructor; eauto with bigcbv. }
  (* LetV *)
  { econstructor; eauto with bigcbv. }
  (* AppL *)
  { invert_bigcbv. eauto with bigcbv. }
  (* AppR *)
  { invert_bigcbv. eauto with bigcbv. }
  (* LetL *)
  { invert_bigcbv. eauto with bigcbv. }
  { (* missing rule *) admit. }
  { invert_bigcbv. admit. (* missing rule *) }
  { invert_bigcbv. }
  { invert_bigcbv. }
  { admit. (* missing rule. *) }
  { admit. (* missing rule. *) }
Admitted.
(* Restart.
  (* A shorter proof: *)
  induction 1; intros; subst; try solve [ false; tauto
  | econstructor; eauto with bigcbv
  | invert_bigcbv; eauto with bigcbv
  ]. Qed. *)

Lemma star_cbv_bigcbv:
  forall t v,
  star cbv t v ->
  is_value v ->
  bigcbv t v.
Proof.
  induction 1; eauto using cbv_bigcbv_bigcbv with bigcbv.
Qed.

(* In conclusion, we have the following equivalence: *)

Lemma star_cbv_bigcbv_eq:
  forall t v,
  (star cbv t v /\ is_value v) <-> bigcbv t v.
Proof.
  split; intros; unpack;
  eauto using star_cbv_bigcbv, bigcbv_star_cbv with is_value.
Qed.

(* -------------------------------------------------------------------------- *)
(* -------------------------------------------------------------------------- *)

(* A big-step call-by-value semantics with explicit environments. *)

(* A closure is a pair of a term and an environment. A cvalue [cv] must be a
   closure, as we have no other forms of values. An environment [e] is a list
   of cvalues. *)

(* We break the mutual induction between [cvalue] and [cenv] by inlining the
   definition of [cenv] into the definition of [cvalue]. *)

Inductive cvalue :=
| Clo: {bind term} -> list cvalue -> cvalue.

Definition cenv :=
  list cvalue.

(* This dummy cvalue is passed below as an argument to [nth], but is really
   irrelevant, as the condition [x < length e] ensures that the dummy cvalue
   is never used. *)

Definition dummy_cvalue : cvalue :=
  Clo (Var 0) nil.

(* The judgement [ebigcbv e t cv] means that, under the environment [e], the
   term [t] evaluates to [cv]. *)

Inductive ebigcbv : cenv -> term -> cvalue -> Prop :=
| EBigcbvVar:
    forall e x cv,
    (* The variable [x] must be in the domain of [e]. *)
    x < length e ->
    (* This allows us to safely look up [e] at [x]. *)
    cv = nth x e dummy_cvalue ->
    ebigcbv e (Var x) cv
| EBigcbvLam:
    forall e t,
    (* The free variables of [t] must be less than or equal to [length e]. *)
    (forall cv, fv (length (cv :: e)) t) ->
    (* This allows us to build a closure that is indeed closed. *)
    ebigcbv e (Lam t) (Clo t e)
| EBigcbvApp:
    forall e e' t1 t2 u1 cv2 cv,
    (* Evaluate [t1] to a closure, *)
    ebigcbv e t1 (Clo u1 e') ->
    (* evaluate [t2] to a value, *)
    ebigcbv e t2 cv2 ->
    (* and evaluate the function body, in a suitable environment. *)
    ebigcbv (cv2 :: e') u1 cv ->
    ebigcbv e (App t1 t2) cv
| EBigcbvLet:
    forall e t1 t2 cv1 cv,
    (* Evaluate [t1] to a value, *)
    ebigcbv e t1 cv1 ->
    (* and evaluate [t2] under a suitable environment. *)
    ebigcbv (cv1 :: e) t2 cv ->
    ebigcbv e (Let t1 t2) cv
.

Global Hint Constructors ebigcbv : ebigcbv.

(* -------------------------------------------------------------------------- *)

(* To explain what the above semantics means, and to prove that it is
   equivalent to the big-step semantics, we first define a function that
   decodes a cvalue into a value. *)

(* Ideally, the function [decode] should be defined by the equation:

     decode (Clo t e) = (Lam t).[decode_cenv e]

   where the auxiliary function [decode_cenv] maps [decode] over the
   environment [e], and converts the result to a substitution, that
   is, a function of type [term -> term]:

     decode_cenv e = fun x => nth x (map decode e) (decode dummy_cvalue)

   The definitions below are a bit more awkward (as Coq does not support
   mutual induction very well), but mean the same thing. *)

Definition dummy_value : term :=
  Lam (Var 0).

Fixpoint decode (cv : cvalue) : term :=
  match cv with
  | Clo t e =>
      (Lam t).[fun x => nth x (map decode e) dummy_value]
  end.
  (* I am not even sure why this definition is accepted by Coq? *)

Definition decode_cenv e :=
  fun x => nth x (map decode e) (decode dummy_cvalue).

(* The first equation in the above comment is satisfied, as shown by
   the following lemma. The second equation in the above comment is
   satisfied too, by definition. *)

Lemma decode_eq:
  forall t e,
  decode (Clo t e) = (Lam t).[decode_cenv e].
Proof.
  reflexivity.
Qed.

(* This equation is useful, too. *)

Lemma decode_cenv_Var_eq:
  forall x e,
  (Var x).[decode_cenv e] = decode (nth x e dummy_cvalue).
Proof.
  intros. asimpl. unfold decode_cenv. rewrite map_nth. eauto.
Qed.

(* The tactic [decode] rewrites using the above two equations. *)

Global Hint Rewrite decode_eq decode_cenv_Var_eq : decode.
Ltac decode := autorewrite with decode in *.

(* We make [decode] opaque, so its definition is not unfolded by Coq. *)

Opaque decode.

(* [decode cv] is always a value. *)

Lemma is_value_decode:
  forall cv,
  is_value (decode cv).
Proof.
  intros. destruct cv. decode. asimpl. tauto.
Qed.

Lemma is_value_decode_cenv:
  forall x e,
  is_value (Var x).[decode_cenv e].
Proof.
  intros. decode. eauto using is_value_decode.
Qed.

Local Hint Resolve is_value_decode is_value_decode_cenv : is_value obvious.

(* A composition of two substitutions is the same thing as one substitution. *)

Lemma decode_cenv_cons:
  forall t e cv,
  t.[up (decode_cenv e)].[decode cv/] = t.[decode_cenv (cv :: e)].
Proof.
  intros. autosubst. (* wonderful *)
Qed.

(* The tactic [nonvalue_eq_decode] closes a subgoal when there is a hypothesis
   of the form [_ = decode_cenv e x], where the left-hand side of the equation
   clearly is not a value. This is a contradiction. *)

Ltac nonvalue_eq_decode :=
  match goal with
  | heq: _ = decode_cenv ?e ?x |- _ =>
      assert (hv: is_value (decode_cenv e x)); [
        solve [ obvious ]
      | rewrite <- heq in hv; false; is_value ]
  end.

(* -------------------------------------------------------------------------- *)

(* If [t] evaluates to [cv] under environment [e],
   then, in the big-step semantics,
   the term [t.[decode_cenv e]] evaluates to the value [decode cv]. *)

Lemma ebigcbv_bigcbv:
  forall e t cv,
  ebigcbv e t cv ->
  bigcbv t.[decode_cenv e] (decode cv).
Proof.
  induction 1; intros; subst.
  (* EBigcbvVar *)
  { decode. econstructor. obvious. }
  (* EBigcbvLam *)
  { econstructor. obvious. }
  (* EBigcbvApp *)
  { decode.
    asimpl. econstructor; eauto.
    asimpl. eauto. }
  (* EBigcbvLet *)
  { asimpl. econstructor; eauto.
    asimpl. eauto. }
Qed.

(* A simplified corollary, where [t] is closed and is therefore evaluated
   under the empty environment. *)

Lemma ebigcbv_bigcbv_nil:
  forall t cv,
  ebigcbv nil t cv ->
  closed t ->
  bigcbv t (decode cv).
Proof.
  intros.
  replace t with t.[decode_cenv nil] by eauto using closed_unaffected.
  eauto using ebigcbv_bigcbv.
Qed.

(* -------------------------------------------------------------------------- *)

(* The converse statement: if in the big-step semantics, the term
   [t.[decode_cenv e]] evaluates to the value [decode cv], then [t] evaluates
   to [cv] under environment [e]. *)

(* This proof does not work (and, in fact, the statement is wrong). A failed
   proof attempt reveals two problems... *)

Lemma bigcbv_ebigcbv_failed:
  forall e t cv,
  bigcbv t.[decode_cenv e] (decode cv) ->
  ebigcbv e t cv.
Proof.
  inversion 1; intros; subst.
  (* BigcbvValue *)
  (* { (* [t] must be a variable or a lambda-abstraction. *)
    destruct t; [ | | false; is_value | false; is_value ].
    (* Case: [t] is a variable. *)
    { econstructor.
      (* Here, we have two subgoals, neither of which can be proved. *)
      { (* Problem 1: we are unable to prove [x < length e]. In order
           to establish such a property, we would have to express the
           hypothesis that the free variables of [t] are in the domain
           of the environment [e]. And, for this hypothesis to be
           inductive, we have to further require every closure in
           the environment [e] to satisfy a similar condition. *)
        admit. }
      { (* Problem 2: we have [decode cv1 = decode cv2], and the goal
           is [cv1 = cv2]. This goal cannot be proved, as the function
           [decode] is not injective: multiple closures represent the
           same lambda-abstraction. *)
        decode.
        admit. } *)
Abort.

(* -------------------------------------------------------------------------- *)

(* In order to fix the above failed statement, we need to express the
   following well-formedness invariant: whenever a closure [Clo t e] is
   constructed, the free variables of the term [t] are in the domain of the
   environment [env], and, recursively, every value in [e] is well-formed. *)

Inductive wf_cvalue : cvalue -> Prop :=
| WfCvalue:
    forall t e,
    (forall cv, fv (length (cv :: e)) t) ->
    wf_cenv e ->
    wf_cvalue (Clo t e)

with wf_cenv : cenv -> Prop :=
| WfCenv:
    forall e,
    Forall wf_cvalue e ->
    wf_cenv e.

(* The following trivial lemmas (which repeat the definition) are provided as
   hints for [eauto with wf_cvalue]. *)

Lemma use_wf_cvalue_1:
  forall t e cv,
  wf_cvalue (Clo t e) ->
  fv (length (cv :: e)) t.
Proof.
  inversion 1; eauto.
Qed.

Lemma use_wf_cvalue_2:
  forall t e,
  wf_cvalue (Clo t e) ->
  wf_cenv e.
Proof.
  inversion 1; eauto.
Qed.

Lemma prove_wf_cenv_nil:
  wf_cenv nil.
Proof.
  econstructor. eauto.
Qed.

Lemma prove_wf_cenv_cons:
  forall cv e,
  wf_cvalue cv ->
  wf_cenv e ->
  wf_cenv (cv :: e).
Proof.
  inversion 2; intros; subst.
  econstructor.
  econstructor; eauto.
Qed.

Global Hint Resolve
  use_wf_cvalue_1 use_wf_cvalue_2 prove_wf_cenv_nil prove_wf_cenv_cons
: wf_cvalue.

(* The following lemma states that the invariant is preserved by [ebigcbv].
   That is, if the term [t] is successfully evaluated in the well-formed
   environment [e] to a cvalue [cv], then [cv] is well-formed. *)

Lemma ebigcbv_wf_cvalue:
  forall e t cv,
  ebigcbv e t cv ->
  wf_cenv e ->
  wf_cvalue cv.
Proof.
  induction 1; intros; subst.
  (* EBigcbvVar *)
  { pick wf_cenv invert. rewrite Forall_forall in *. eauto using nth_In. }
  (* EBigcbvLam *)
  { econstructor; eauto. }
  (* EBigcbvApp *)
  { eauto 6 with wf_cvalue. }
  (* EBigcbvLet *)
  { eauto 6 with wf_cvalue. }
Qed.

Global Hint Resolve ebigcbv_wf_cvalue : wf_cvalue.

(* -------------------------------------------------------------------------- *)

(* We can now make an amended statement: if in the big-step semantics, the
   term [t.[decode_cenv e]] evaluates to a value [v], if the environment [e]
   is well-formed, and if the free variables of [t] are in the domain of [e],
   then under environment [e] the term [t] evaluates to some cvalue [cv] such
   that [decode cv] is [v]. *)

Lemma bigcbv_ebigcbv:
  forall te v,
  bigcbv te v ->
  forall t e,
  te = t.[decode_cenv e] ->
  fv (length e) t ->
  wf_cenv e ->
  exists cv,
  ebigcbv e t cv /\ decode cv = v.
Proof.
  admit.
  (*
  induction 1; intros; subst.
  (* BigcbvValue *)
  { (* [t] must be a variable or a lambda-abstraction. *)
    destruct t; try solve [false; is_value]; try fv.
    (* Case: [t] is a variable. *)
    { eexists; split. econstructor; eauto. decode. eauto. }
    (* Case: [t] is a lambda-abstraction. *)
    { eexists; split. econstructor; eauto. reflexivity. }
  }
  (* BigcbvApp *)
  { (* [t] must be an application. *)
    destruct t;
    match goal with h: _ = _ |- _ => asimpl in h end;
    [ nonvalue_eq_decode | false; congruence | | false; congruence ].
    fv. unpack.
    (* The equality [App _ _ = App _ _] can be simplified. *)
    injections. subst.
    (* Exploit two of the induction hypotheses (forward). *)
    edestruct IHbigcbv1; eauto. unpack. clear IHbigcbv1.
    edestruct IHbigcbv2; eauto. unpack. clear IHbigcbv2.
    (* If [decode cv] is [Lam _], then [cv] must be a closure. This should
       be a lemma. Because (here) every cvalue is a closure, it is trivial. *)
    match goal with h: decode ?cv = Lam _ |- _ =>
      destruct cv as [ t' e' ];
      rewrite decode_eq in h;
      asimpl in h;
      injections; subst
    end.
    (* Now, exploit the third induction hypothesis (forward). *)
    edestruct IHbigcbv3; eauto using decode_cenv_cons with wf_cvalue.
    unpack. clear IHbigcbv3.
    (* The result follows. *)
    eauto with ebigcbv.
  }
  (* BigcbvLet *)
  { (* [t] must be a [Let] construct. *)
    destruct t;
    match goal with h: _ = _ |- _ => asimpl in h end;
    [ nonvalue_eq_decode | false; congruence | false; congruence | ].
    fv. unpack.
    injections. subst.
    (* Exploit the induction hypotheses (forward). *)
    edestruct IHbigcbv1; eauto. unpack. clear IHbigcbv1.
    edestruct IHbigcbv2; eauto using decode_cenv_cons with wf_cvalue.
    unpack. clear IHbigcbv2.
    (* The result follows. *)
    eauto with ebigcbv.
  } *)
Admitted.

(* A simplified corollary, where [t] is closed and is therefore evaluated
   under the empty environment. *)

Lemma bigcbv_ebigcbv_nil:
  forall t v,
  bigcbv t v ->
  closed t ->
  exists cv,
  ebigcbv nil t cv /\ decode cv = v.
Proof.
  intros. eapply bigcbv_ebigcbv; eauto with wf_cvalue.
  rewrite closed_unaffected by eauto. reflexivity.
Qed.

(* -------------------------------------------------------------------------- *)
(* -------------------------------------------------------------------------- *)

(* Suppose the big-step semantics [bigcbv] is taken as the primary definition
   of the meaning of terms. Then, in terms of [bigcbv], we can define a
   relation [sim] between terms, which has the flavor of a small-step
   reduction relation. *)

(* The definition is as follows: if, whenever [u] can produce the value [v],
   [t] can produce [v] as well, then [t] simulates [u]. *)

Definition sim t u :=
  forall v,
  bigcbv u v ->
  bigcbv t v.

(* This simulation relation is reflexive and transitive, hence a preorder. *)

Lemma reflexive_sim:
  forall t,
  sim t t.
Proof.
  unfold sim. eauto.
Qed.

Lemma transitive_sim:
  forall t1 t2 t3,
  sim t1 t2 ->
  sim t2 t3 ->
  sim t1 t3.
Proof.
  unfold sim. eauto.
Qed.

Global Hint Resolve reflexive_sim transitive_sim : sim.

(* This simulation relation includes the small-step relation [cbv]. *)

Lemma cbv_sim:
  forall t u,
  cbv t u ->
  sim t u.
Proof.
  (* This is a direct consequence of the fact that the composition
     [cbv . bigcbv] is a subset of [bigcbv] -- a fact that was proved above. *)
  unfold sim. eauto using cbv_bigcbv_bigcbv.
Qed.

(* As a consequence, [star cbv] is also a subset of [sim]. *)

Lemma star_cbv_sim:
  forall t u,
  star cbv t u ->
  sim t u.
Proof.
  induction 1; eauto using cbv_sim with sim.
Qed.

(* The converse is not true. Clearly, [star cbv] forbids all reductions under
   a lambda-abstraction, whereas (somewhat nonobviously) [sim] allows certain
   reductions under lambda-abstractions: intuitively, it allows all necessary
   reductions, in a certain sense (?). *)

(* For this reason, [sim] can be more comfortable to work with than [star cbv].
   The proof of correctness of the CPS transformation in CPSCorrectnessBigStep
   provides an example. *)

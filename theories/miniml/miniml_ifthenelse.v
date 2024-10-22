Require Export Autosubst.Autosubst.
Require Import String.
Require Import Coq.ZArith.ZArith.
Require Import tactics.
Import List.ListNotations.
Require Import common.
Require Import sequences.

Require Import Coq.Classes.SetoidClass.
Require Import Wellfounded.

From Equations Require Import Equations.

Set Default Goal Selector "!".


(*** Definitions of terms and continuations for mini-ML ***)


Inductive term :=
  (* Lambda calculus part of the language*)
  | Var (x: var)
  | App (t1 t2: term)
  | Lam (t: {bind term})
  | Value (v: value)

  | If (u t1 t2: term)

with value :=
  | Closure (t: {bind term}) (sigma: list value)
  | Bool (b: bool)
.

(* Declare and delimit the single LaTeX-compatible scope *)
Declare Scope latex_scope.

(* Notations for terms and values, LaTeX-friendly with minimal parentheses *)
Notation "'\#' x" := (Var x) (at level 55) : latex_scope.
Notation "t1 '\@' t2" := (App t1 t2) (at level 60, right associativity) : latex_scope.
Notation "'\synlambda' t '\syndot'" := (Lam t) (at level 65) : latex_scope.
Notation "'\synval' v" := (Value v) (at level 70) : latex_scope.

(* Notation for If expressions *)
Notation "'\synif' u '\synthen' t1 '\synelse' t2" := (If u t1 t2) (at level 80, right associativity) : latex_scope.

(* Notations for values *)
Notation "'\closure' t , sigma" := (Closure t sigma) (at level 75) : latex_scope.
Notation "'\bool' b" := (Bool b) (at level 75) : latex_scope.



#[export] Instance Ids_term : Ids term. derive. Defined.
#[export] Instance Rename_term : Rename term. derive. Defined.
#[export] Instance Subst_term : Subst term. derive. Defined.
#[export] Instance SubstLemmas_term : SubstLemmas term. derive. Qed.

Lemma ids_inj:
  forall x y, ids x = ids y -> x = y.
intros; inj; eauto.
Qed.


(*** Strong induction principle for terms ***)

Fixpoint size_term t := 
  match t with
  | Var _ => 0
  | App t1 t2 => S (size_term t1 + size_term t2)
  | Lam t => S (size_term t)
  | Value v => S (size_value v)
  | If u t1 t2 => S (size_term u + size_term t1 + size_term t2)
  end
with size_value v :=
  match v with
  | Closure t env => S (size_term t + (List.list_sum (List.map size_value env)))
  | Bool _ => 0
  end.

Definition size (x : term + value) :=
  match x with
  | inl t => size_term t
  | inr v => size_value v
  end.


Theorem term_value_induction
: forall {P : term -> Prop} {P0 : value -> Prop}
    {HVar: forall x : var, P (Var x)}
    {HApp: forall t1 : term, P t1 -> forall t2 : term, P t2 -> P (App t1 t2)}
    {HLam: forall t : {bind term}, P t -> P (Lam t)}
    {HValue: forall v : value, P0 v -> P (Value v)}
    {HIf: forall u, P u -> forall t1, P t1 -> forall t2, P t2 -> P (If u t1 t2)}
    {HClosure: forall t,
      P t -> forall sigma, (List.Forall P0 sigma) -> P0 (Closure t sigma)}
    {HBool: forall b, P0 (Bool b)},
    (forall x : term + value, match x with | inl t => P t | inr v => P0 v end).
Proof.
  induction x as [x IHx] using (
    well_founded_induction
      (wf_inverse_image _ nat _ size 
      PeanoNat.Nat.lt_wf_0)).
  { destruct x.
    { destruct t; try first [
        eapply HVar|
        eapply HApp|
        eapply HLam|
        eapply HValue|
        eapply HIf
      ].
      1: eapply (IHx (inl t1)).
      2: eapply (IHx (inl t2)).
      3: eapply (IHx (inl t)).
      4: eapply (IHx (inr v)).
      5: eapply (IHx (inl t1)).
      6: eapply (IHx (inl t2)).
      7: eapply (IHx (inl t3)).
      all: simpl; lia.
    }
    { destruct v; try first [
        eapply HClosure
      ].
      { eapply (IHx (inl t)); simpl; lia. }
      {
        induction sigma; econstructor; eauto.
        { eapply (IHx (inr a)); simpl; lia. }

        eapply IHsigma; intros.
        { eapply IHx. simpl in *; lia. }
      }
      eapply HBool.
    }
  }
Qed.

Theorem term_ind'
  : forall (P : term -> Prop) (P0 : value -> Prop),
      (forall x : var, P (Var x)) ->
      (forall t1 : term, P t1 -> forall t2 : term, P t2 -> P (App t1 t2)) ->
      (forall t : {bind term}, P t -> P (Lam t)) ->
      (forall v : value, P0 v -> P (Value v)) ->
      (forall t,
       P t -> forall sigma, (List.Forall P0 sigma) -> P0 (Closure t sigma)) ->
      (forall u, P u -> forall t1, P t1 -> forall t2, P t2 -> P (If u t1 t2)) ->
      (forall b, P0 (Bool b)) ->
      (forall t : term, P t) /\ (forall v : value, P0 v).
Proof.
  split; intros.
  unshelve eapply (term_value_induction (inl t)); eauto.
  unshelve eapply (term_value_induction (inr v)); eauto.
Qed.


(*** Syntax for continuations ***)

Inductive cont :=
  | CAppR (t2: term) (* [\square t2] *)
  | CClosure (t_cl: {bind term}) (sigma_cl: list value)
  (* [Clo(x, t_cl, sigma_cl) \square] Since we are using De Bruijn indices,
     there is no variable x. *)
  | CReturn (sigma: list value) (* call return *)
  | CIf (t1 t2: term) (* [if \square then t1 else t2]*)
.

Inductive result :=
  | RValue (v: value)
.


Inductive state :=
  | mode_eval (e: term) (kappa: list cont) (env: list value)
  | mode_cont (kappa: list cont) (env: list value) (result: result)
.


(*** Continuation step semantics ***)

Inductive cred: state -> state -> Prop :=
  (** Rules related to the lambda calculus *)
  | cred_var:
    forall x kappa sigma v,
    List.nth_error sigma x = Some v ->
    cred
      (mode_eval (Var x) kappa sigma)
      (mode_cont kappa sigma (RValue v))

  | cred_app:
    forall t1 t2 kappa sigma,
    cred
      (mode_eval (App t1 t2) kappa sigma)
      (mode_eval t1 ((CAppR t2) :: kappa) sigma)

  | cred_clo:
    forall t kappa sigma,
    cred
      (mode_eval (Lam t) kappa sigma)
      (mode_cont kappa sigma (RValue (Closure t sigma)))

  | cred_arg:
    forall t2 kappa sigma tcl sigmacl,
    cred
      (mode_cont ((CAppR t2)::kappa) sigma (RValue (Closure tcl sigmacl)))
      (mode_eval t2 ((CClosure tcl sigmacl)::kappa) sigma)

  | cred_value:
    forall v kappa sigma,
    cred
      (mode_eval (Value v) kappa sigma)
      (mode_cont kappa sigma (RValue v))

  | cred_beta:
    forall t_cl sigma_cl kappa sigma v,
    cred
      (mode_cont ((CClosure t_cl sigma_cl)::kappa) sigma (RValue v))
      (mode_eval t_cl (CReturn sigma::kappa)  (v :: sigma_cl))

  | cred_return:
    forall sigma_cl kappa sigma r,
    cred
      (mode_cont (CReturn sigma::kappa) sigma_cl r)
      (mode_cont kappa sigma r)

  | cred_if:
    forall u t1 t2 kappa sigma,
    cred
      (mode_eval (If u t1 t2) kappa sigma)
      (mode_eval u ((CIf t1 t2)::kappa) sigma)
  
  | cred_if_true:
    forall t1 t2 kappa sigma,
    cred
      (mode_cont ((CIf t1 t2):: kappa) sigma (RValue (Bool true)))
      (mode_eval t1 kappa sigma)
  
  | cred_if_false:
    forall t1 t2 kappa sigma,
    cred
      (mode_cont ((CIf t1 t2):: kappa) sigma (RValue (Bool false)))
      (mode_eval t2 kappa sigma)
.

Example example_of_reduction t1 t2:
  star cred
    (mode_eval (If (Value (Bool true)) t1 t2) [] [])
    (mode_eval t1 [] []).
Proof.
  eapply star_step;[econstructor|].
  eapply star_step;[econstructor|].
  eapply star_step;[econstructor|].
  eapply star_refl.
Qed.

(*** small step semantics ***)

Import List.ListNotations.
Open Scope list.

Definition subst_of_env sigma :=
  fun n =>
  match List.nth_error sigma n with
  | None => ids (n - List.length sigma)
  | Some t => Value t
  end
.




Inductive sred: term -> term -> Prop :=
  | sred_lam:
    forall t,
      sred
        (Lam t)
        (Value (Closure t []))
  | sred_beta:
    forall t v sigma',
      sred
        (App (Value (Closure t sigma')) (Value v))
        (t.[subst_of_env (v :: sigma')])
  | sred_app_right:
    forall t sigma u1 u2,
      sred (u1) (u2) ->
      sred
        (App (Value (Closure t sigma)) u1)
        (App (Value (Closure t sigma)) u2)
  | sred_app_left:
    forall t1 t2 u,
      sred (t1) (t2) ->
      sred
        (App t1 u)
        (App t2 u)
  | sred_if_true:
    forall t1 t2,
      sred (If (Value (Bool true)) t1 t2) t1
  
  | sred_if_false:
    forall t1 t2,
      sred (If (Value (Bool false)) t1 t2) t2
  
  | sred_if_cond:
    forall u1 u2 t1 t2,
      sred u1 u2 ->
      sred (If u1 t1 t2) (If u2 t1 t2)
.


(*** Typing ***)

Inductive type :=
  | TBool
  | TFun (T1 T2: type)
.

(* Standard typing rules for lambda calculus *)

Inductive jt_term:
  list type -> term -> type -> Prop :=
  | JTVar:
    forall Gamma x T,
      Some T = List.nth_error Gamma x ->
      jt_term Gamma (Var x) T
  | JTApp:
    forall Gamma t1 t2 T1 T2,
      jt_term Gamma t1 (TFun T1 T2) ->
      jt_term Gamma t2 T1 ->
      jt_term Gamma (App t1 t2) T2
  | JTLam:
    forall Gamma t T1 T2,
      jt_term (T1::Gamma) t T2 ->
      jt_term Gamma (Lam t) (TFun T1 T2)
  | JTValue:
    forall Gamma v T,
      jt_value v T ->
      jt_term Gamma (Value v) T
  | JTEIf:
    forall Gamma u ta tb T,
      jt_term Gamma u TBool ->
      jt_term Gamma ta T ->
      jt_term Gamma tb T ->
      jt_term Gamma (If u ta tb) T
with jt_value:
   value -> type -> Prop :=
  | JTValueClosure:
    forall  tcl sigma_cl Gamma_cl T1 T2,
      List.Forall2 jt_value sigma_cl Gamma_cl ->
      jt_term Gamma_cl (Lam tcl) (TFun T1 T2) ->
      jt_value (Closure tcl sigma_cl) (TFun T1 T2)
  | JTValueBool:
    forall b,
      jt_value (Bool b) TBool
.

(** Expanding the rules of typing to continuation-bases semantics requires to define the typing jugment for continuations. This typing judgement have two additional informations: the "hole" type, and the "environement" in the hole. Both are required with our presentation since the hole is filed when the jt_state judgement is defined. *)

Inductive jt_result: result -> type -> Prop := 
  | JTRValue:
    forall v T,
    jt_value v T ->
    jt_result (RValue v) T.

Inductive jt_cont:
  list type -> list type ->
  cont ->
  type -> type -> Prop :=
  | JTCAppR:
    forall {Gamma t2 T1 T2},
      jt_term Gamma t2 T1 ->
      jt_cont Gamma Gamma (CAppR t2) (TFun T1 T2) T2
  | JTCClosure:
    forall {Gamma Gamma_cl sigma_cl T1 T2 tcl},
      jt_term Gamma_cl (Lam tcl) (TFun T1 T2) ->
      List.Forall2 (jt_value) sigma_cl Gamma_cl ->
      jt_cont Gamma Gamma (CClosure tcl sigma_cl) T1 T2
  | JTCIf:
    forall Gamma T ta tb,
      jt_term Gamma ta T ->
      jt_term Gamma tb T ->
      jt_cont Gamma Gamma (CIf ta tb) (TBool) T
  | JTCReturn:
    forall {sigma Gamma1 Gamma2 T},
      (List.Forall2 (jt_value) sigma Gamma2) ->
      jt_cont Gamma1 Gamma2 (CReturn sigma) T T
.

Inductive jt_conts:  list type -> list type -> list cont -> type -> type -> Prop :=
| JTNil:
  forall {Gamma T},
    jt_conts Gamma Gamma nil T T
| JTCons:
  forall {Gamma1 Gamma2 Gamma3 cont kappa T1 T2 T3},
    jt_cont Gamma1 Gamma2 cont T1 T2 ->
    jt_conts Gamma2 Gamma3 kappa T2 T3 ->
    jt_conts Gamma1 Gamma3 (cont :: kappa) T1 T3
.

(** Finall well-typeness of the state. *)
Inductive jt_state:  list type -> state -> type -> Prop :=
| JTmode_eval:
  forall Gamma1 Gamma2 t T1 T2 kappa sigma,
    List.Forall2 (jt_value) sigma Gamma1 ->
    jt_term Gamma1 t T1 ->
    jt_conts Gamma1 Gamma2 kappa T1 T2 ->
    jt_state Gamma2 (mode_eval t kappa sigma) T2
| JTmode_cont:
  forall Gamma1 Gamma2 r T1 T2 kappa sigma,
    List.Forall2 (jt_value) sigma Gamma1 ->
    jt_result r T1 ->
    jt_conts Gamma1 Gamma2 kappa T1 T2 ->
    jt_state Gamma2 (mode_cont kappa sigma r) T2
. 


Require Import Ltac2.Ltac2.
Set Default Proof Mode "Classic".


(** Specialized tactics to invert typing judgement if one argument is a known constructor. *)
Ltac2 inv_jt () :=
  match! goal with
  | [ h: jt_term _ ?c _ |- _ ] => smart_inversion c h
  | [ h: jt_value ?c _ |- _ ] => smart_inversion c h
  | [ h: jt_value _ ?c |- _ ] => smart_inversion c h
  | [ h: jt_cont _ _ ?c _ _ |- _ ] => smart_inversion c h
  | [ h: jt_conts _ _ ?c _ _ |- _ ] => smart_inversion c h
  | [ h: jt_state _ ?c _ |- _ ] => smart_inversion c h
  | [ h: jt_result ?c _ |- _ ] => smart_inversion c h
  | [ h: List.Forall _ ?c |- _ ] => smart_inversion c h
  | [ h: List.Forall2 _ ?c _ |- _ ] => smart_inversion c h
  | [ h: List.Forall2 _ _ ?c |- _ ] => smart_inversion c h
end.

Ltac inv_jt := ltac2:(inv_jt ()).


(** Specialiazed tactic to apply econstructor when possible. *)
Ltac2 econs_jt () :=
  match! goal with
  | [ |- jt_term _ _ _] => econstructor
  | [ |- jt_value _ _] => econstructor
  | [ |- jt_cont _ _ _ _ _] => econstructor
  | [ |- jt_conts _ _ _ _ _] => econstructor
  | [ |- jt_state _ _ _] => econstructor
  | [ |- jt_result _ _] => econstructor
  | [ |- List.Forall _ _] => econstructor
  | [ |- List.Forall2 _ _ _] => econstructor
  end.
Ltac econs_jt := ltac2:(econs_jt ()).


Theorem Forall2_nth_error_Some {A B F l1 l2}:
  List.Forall2 F l1 l2 ->
  forall k (x: A) (y: B),
    List.nth_error l1 k = Some x ->
    List.nth_error l2 k = Some y ->
    F x y.
Proof.
  induction 1, k; simpl; intros; inj; eauto.
Qed.


(** Main preservation lemma for continuation-based semantics. *)
Theorem preservation_cont s1 s2:
  cred s1 s2 ->
  forall Gamma T,
  jt_state Gamma s1 T ->
  jt_state Gamma s2 T.
Proof.
  (* Case analysis over all possible rules *)
  induction 1.
  
  (* Most of the cases are easilly handle by the automation. *)
  all: intros; repeat inv_jt; repeat econs_jt; eauto.

  (** One case is left. It requires an external lemma. *)
  { pose proof (Forall2_nth_error_Some H5); eauto. }
Qed.

Definition is_mode_cont s :=
  match s with
  | mode_cont _ _ _ => true
  | _ => false
  end.

Definition stack s :=
  match s with
  | mode_eval _ k _ => k
  | mode_cont k _ _ => k
  end.

Theorem Forall2_nth_error_Some_right {A B F l1 l2}:
  List.Forall2 F l1 l2 ->
  forall {k} {y: A},
    List.nth_error l2 k = Some y ->
    exists (x: B), List.nth_error l1 k = Some x.
Proof.
  induction 1, k; simpl; intros; inj; eauto.
Qed.

(** Main progress lemma for continuation-based semantics. *)
Theorem progress_cont s1:
  forall Gamma T,
    jt_state Gamma s1 T ->
    (exists s2, cred s1 s2) \/ (is_mode_cont s1 = true /\ stack s1 = nil).
Proof.
  (* Precise case analysis. *)
  induction s1 as [t kappa env|kappa env r]; [induction t|(induction kappa as [|k kappa]; [|induction k]); induction r].

  

  (** Using inversion on each of the cases *)
  all: intros; repeat inv_jt.


  (** To add the boolean case, we need to further do a case analysis on b in the mode_cont case. *)
  all: try induction b.

  (** Most of the cases are easily handled using the automation *)
  all: try solve [left; eexists; econstructor; eauto].
  all: try solve [right; simpl; eauto].

  (* One case is left that requires an additional lemma on lists. *)
  { pose proof (Forall2_nth_error_Some_right H4 (eq_sym H1)); unpack.
    left; eexists; econstructor; eauto.
  }
Qed.


Definition fv k t :=
  t.[upn k (ren (+1))] = t.

Lemma fv_Lam_eq:
  forall k t,
  fv k (Lam t) <-> fv (S k) t.
Proof.
  unfold fv. intros. asimpl. split; intros.
  { injections. eauto. }
  { unpack. congruence. }
Qed.

Lemma fv_App_eq:
  forall k t1 t2,
  fv k (App t1 t2) <-> fv k t1 /\ fv k t2.
Proof.
  unfold fv. intros. asimpl. split; intros.
  { injections. eauto. }
  { unpack. congruence. }
Qed.

Lemma fv_If_eq:
  forall k u t1 t2,
  fv k (If u t1 t2) <-> fv k u /\ fv k t1 /\ fv k t2.
Proof.
  unfold fv. intros. asimpl. split; intros.
  { injections. eauto. }
  { unpack. congruence. }
Qed.

Hint Rewrite fv_Lam_eq fv_App_eq fv_If_eq : fv.


(** Main progress lemma for continuation-based semantics. *)
Theorem progress_trad t1:
  forall Gamma T,
    jt_term Gamma t1 T ->
    Gamma = [] ->
    (exists t2, sred t1 t2) \/ (exists v, t1 = Value v).
Proof.
  induction 1.

  (** Using inversion on each of the cases *)
  all: intros; repeat inv_jt.
  all: unzip; subst.
  
  (** Less cases than in the normal cases. *)
  all: try solve [left; eexists; econstructor; eauto].
  all: try solve [right; simpl; eauto].

  { (* Could be shown in a different lemma. *)
    exfalso.
    induction x; simpl in *; congruence. 
  } 

  { (** Manual handling of the proof here. *)
    pose proof (IHjt_term1 eq_refl).
    pose proof (IHjt_term2 eq_refl).
    unzip; subst.
    all: intros; repeat inv_jt.
    (* automation here depends on the order of the constructors. *)
    all: try solve [left; eexists; econstructor; eauto].
  }
  { (* applying left; eexists, econstructor leads to an unsolvable goal as we are not sure whenever u redices to t2 or is a value. *)
    (* left; eexists; econstructor. *)
    pose proof (IHjt_term1 eq_refl).
    unzip; subst.
    all: intros; repeat inv_jt.

    (* same case analysis as the continutation-based case before *)
    all: try induction b.

    (* the normal proof script can the resume. *)
    all: try solve [left; eexists; econstructor; eauto].
    all: try solve [right; simpl; eauto].
  }
Qed.


(*** Determinism of the relation *)

Theorem cred_deterministic:
  forall s1 s2, cred s1 s2 -> forall s2', cred s1 s2' -> s2 = s2'.
Proof.
  induction 1; inversion 1; subst; simpl in *; eauto.
  { rewrite H in H5; inj; eauto. }
Qed.

Theorem sred_deterministic:
  forall t1 t2, sred t1 t2 -> forall t2', sred t1 t2' -> t2 = t2'.
Proof.
  induction 1; inversion 1; subst; simpl in *; eauto.
  { inversion H4. }
  { inversion H3. }
  { inversion H. }
  { repeat f_equal. eapply IHsred. eauto. }
  { inversion H4. }
  { inversion H. }
  { inversion H. }
  { repeat f_equal. eapply IHsred. eauto. }
  { inversion H4. }
  { inversion H4. }
  { inversion H. }
  { inversion H. }
  { repeat f_equal. eapply IHsred. eauto. }
Qed.

(** Simple translation of [if t then ta else tb] into [if (if t then false else true) then tb else ta] *)

Module trans1.
Fixpoint trans_term t :=
  match t with
  | Var x => Var x
  | App t1 t2 => App (trans_term t1) (trans_term t2)
  | Lam t => Lam (trans_term t)
  | Value v => Value (trans_value v)
  | If u t1 t2 =>
    If (If (trans_term u) (Value (Bool false)) (Value (Bool true)))
       (trans_term t2) (trans_term t1)
  end
with trans_value v :=
  match v with
  | Closure t sigma =>
    Closure (trans_term t) (List.map trans_value sigma)
  | Bool b => Bool b
  end
.

Fixpoint trans_conts (kappa: list cont): list cont :=
  match kappa with
  | nil => nil
  | CAppR t2 :: kappa => CAppR (trans_term t2) :: trans_conts kappa
  | CClosure t sigma :: kappa =>
    CClosure (trans_term t) (List.map trans_value sigma) :: trans_conts kappa
  | CReturn sigma :: kappa =>
    CReturn (List.map trans_value sigma) :: trans_conts kappa
  | CIf t1 t2 :: kappa =>
    CIf (Value (Bool false)) (Value (Bool true))::
    CIf (trans_term t2) (trans_term t1) ::
    trans_conts kappa
  end
.

Definition trans_return (r: result): result:=
  match r with
  | RValue v => RValue (trans_value v)
  end.

Definition trans_state (s: state) : state :=
  match s with
  | mode_eval e kappa env =>
    mode_eval (trans_term e) (trans_conts kappa) (List.map trans_value env)
  | mode_cont kappa env r =>
    mode_cont (trans_conts kappa) (List.map trans_value env) (trans_return r)
  end
.

Theorem correction_continuations:
  forall s1 s2,
  cred s1 s2 ->

  star cred
    (trans_state s1) (trans_state s2).
Proof.
Local Ltac step := (
  try (eapply star_step; [solve
    [ econstructor; simpl; eauto using List.map_nth_error
  ]|]))
.
  induction 1; simpl; repeat step; try eapply star_refl.
Qed.

End trans1.

Module trans2.
Fixpoint trans_term t :=
  match t with
  | Var x => Var x
  | App t1 t2 => App (trans_term t1) (trans_term t2)
  | Lam t => Lam (trans_term t)
  | Value v => Value (trans_value v)
  | If (If u (Value (Bool false)) (Value (Bool true))) t1 t2 =>
    If (trans_term u) (trans_term t2) (trans_term t1)
  | If u t1 t2 =>
    If (trans_term u) (trans_term t1) (trans_term t2)
  end
with trans_value v :=
  match v with
  | Closure t sigma =>
    Closure (trans_term t) (List.map trans_value sigma)
  | Bool b => Bool b
  end
.

(* Generalized transformation for continuations *)
Fixpoint trans_conts (kappa: list cont): list cont :=
  match kappa with
  | nil => nil
  | CAppR t2 :: kappa => CAppR (trans_term t2) :: trans_conts kappa
  | CClosure t sigma :: kappa =>
    CClosure (trans_term t) (List.map trans_value sigma) :: trans_conts kappa
  | CReturn sigma :: kappa =>
    CReturn (List.map trans_value sigma) :: trans_conts kappa
  | CIf (Value (Bool false)) (Value (Bool true)) :: CIf t1 t2 :: kappa =>
    CIf (trans_term t1) (trans_term t2) :: trans_conts kappa
  | CIf  t1 t2 :: kappa =>
    CIf (trans_term t1) (trans_term t2) :: trans_conts kappa
  end.

(* Generalized transformation for results *)
Definition trans_return (r: result): result :=
  match r with
  | RValue v => RValue (trans_value v)
  end.

(* Generalized transformation for states with the special If case *)
Definition trans_state (s: state) : state :=
  match s with
  | mode_eval (If b (Value (Bool false)) (Value (Bool true))) (CIf t2 t1::kappa) env =>
    mode_eval (trans_term b) (CIf (trans_term t1) (trans_term t2)::trans_conts kappa) (List.map trans_value env)
  | mode_eval e kappa env =>
    mode_eval (trans_term e) (trans_conts kappa) (List.map trans_value env)
  | mode_cont kappa env r =>
    mode_cont (trans_conts kappa) (List.map trans_value env) (trans_return r)
    end.

End trans2.

(*

Equations f (l : list nat) : list nat :=
f []  := [];
f (cons a (cons b l)) := cons (a+b) (f l);
f (cons a l) := cons a (f l).

*)

Module trans3.

Definition with_stack s kappa :=
  match s with
  | mode_cont _ sigma v => mode_cont kappa sigma v
  | mode_eval t _ sigma => mode_eval t kappa sigma
  end.

Definition append_stack s kappa :=
  with_stack s (stack s ++ kappa).
Definition cons_stack s kappa :=
  with_stack s (kappa ++ stack s ).
Definition rev_state (s: state): state :=
  with_stack s (List.rev (stack s))
. 

Set Equations Transparent.

(* we define trans_state to be rev_state \circ trans_state_aux \circ rev_state
to permit more adapted pattern matching. *)
Require Import Coq.Program.Equality.
Definition total_relation {A : Type} : A -> A -> Prop := fun x y => True.
Axiom wf_total_init : forall {A}, WellFounded (@total_relation A).
#[local]
Remove Hints wf_total_init : typeclass_instances.

#[local]
Instance wf_total_init_compute : forall {A}, WellFounded (@total_relation A).
  exact (fun A => Acc_intro_generator 10 wf_total_init).
Defined.

Fixpoint trans_term t :=
  match t with
  | Var x => Var x
  | App t1 t2 => App (trans_term t1) (trans_term t2)
  | Lam t => Lam (trans_term t)
  | Value v => Value (trans_value v)
  | If (If u (Value (Bool false)) (Value (Bool true))) t1 t2 =>
    If (trans_term u) (trans_term t2) (trans_term t1)
  | If u t1 t2 =>
    If (trans_term u) (trans_term t1) (trans_term t2)
  end
with trans_value v :=
  match v with
  | Closure t sigma =>
    Closure (trans_term t) (List.map trans_value sigma)
  | Bool b => Bool b
  end
.

Definition trans_return (r: result): result :=
  match r with
  | RValue v => RValue (trans_value v)
  end.

Equations trans_cont_base (k: cont) : cont :=
  trans_cont_base (CAppR t2) := CAppR (trans_term t2);
  trans_cont_base (CClosure t sigma) := CClosure (trans_term t) (List.map trans_value sigma);
  trans_cont_base (CReturn sigma) := CReturn (List.map trans_value sigma);
  trans_cont_base (CIf t1 t2) := CIf (trans_term t1) (trans_term t2).

Equations? trans_state_aux (s: state) : state by wf s (@total_relation state) :=
trans_state_aux (mode_eval t (CIf t1 t2 :: CIf (Value (Bool false)) (Value (Bool true)) :: kappa) sigma) :=
  cons_stack (trans_state_aux (mode_eval t kappa sigma)) [trans_cont_base (CIf t2 t1)];
trans_state_aux (mode_eval (If b (Value (Bool false)) (Value (Bool true))) [CIf t1 t2] sigma) :=
  cons_stack (trans_state_aux (mode_eval b [] (List.map trans_value sigma))) [trans_cont_base (CIf t2 t1)];
trans_state_aux (mode_eval t (k::kappa) sigma) :=
  cons_stack (trans_state_aux (mode_eval t kappa sigma)) [trans_cont_base k];
trans_state_aux (mode_eval t [] sigma) :=
  (mode_eval (trans_term t) [] (List.map trans_value sigma));

trans_state_aux (mode_cont (CIf t1 t2 :: CIf (Value (Bool false)) (Value (Bool true)) :: kappa) sigma v) :=
  cons_stack (trans_state_aux (mode_cont kappa sigma v)) [trans_cont_base (CIf t2 t1)];
trans_state_aux (mode_cont (k::kappa) sigma v) :=
  cons_stack (trans_state_aux (mode_cont kappa sigma v)) [trans_cont_base k];
trans_state_aux (mode_cont [] sigma v) :=
  (mode_cont [] (List.map trans_value sigma) (trans_return v) )
.
Proof.
  all: constructor.
Defined.

Definition trans_state s := rev_state (trans_state_aux (rev_state s)).

Inductive trans_state' : state -> state -> Prop :=
  (* Case 1: Handle two nested CIf control units *)
  | trans_if_nested :
      forall t t1 t2 kappa sigma s',
      trans_state' (mode_eval t kappa sigma) s' ->
      trans_state' (mode_eval t (kappa ++ [CIf (Value (Bool false)) (Value (Bool true)); CIf t1 t2]) sigma)
                   (append_stack s' [CIf (trans_term t2) (trans_term t1)])

  (* Case 2: Handle If False True term with kappa ++ [CIf t2 t1] *)
  | trans_if_false_true :
      forall b t1 t2 sigma s',
      trans_state' (mode_eval b [] (List.map trans_value sigma)) s' ->
      trans_state' (mode_eval (If b (Value (Bool false)) (Value (Bool true))) [CIf t1 t2] sigma)
                   (mode_eval (trans_term b) [CIf t2 t1] (List.map trans_value sigma))

  (* Case 3: Handle mode_eval with non-empty continuation stack kappa ++ [k] *)
  | trans_mode_eval_non_empty :
      forall t k kappa sigma s',
      forall Hcond1:
        (* mode_eval
            (If b (Value (Bool false)) (Value (Bool true)))
            [CIf t1 t2]
            sigma
        *)
           match t with | If _ (Value (Bool false)) (Value (Bool true)) => False | _ => True end
        \/ (match kappa with | [] => False | _ => True end)
        \/ match k with | CIf _ _ => False | _ => True end,
      forall Hcond2:
          (* mode_eval
              t 
              (kappa ++ [CIf (Value (Bool false)) (Value (Bool true)); CIf t1 t2])
              sigma
          *)
           match List.rev kappa with | CIf (Value (Bool false)) (Value (Bool true)) ::_ => False | _ => True end
        \/ match k with | CIf _ _ => False | _ => True end,
      trans_state' (mode_eval t kappa sigma) s' ->
      trans_state' (mode_eval t (kappa ++ [k]) sigma)
                   (append_stack s' [trans_cont_base k])

  (* Case 4: Handle mode_eval with empty continuation stack kappa ++ [] *)
  | trans_mode_eval_empty :
      forall t sigma,
      trans_state' (mode_eval t [] sigma)
                   (mode_eval (trans_term t) [] (List.map trans_value sigma))

  (* Case 5: Handle two nested CIf statements in mode_cont with kappa ++ [CIf t2 t1] *)
  | trans_mode_cont_if_nested :
      forall t1 t2 kappa sigma v s',
      trans_state' (mode_cont kappa sigma v) s' ->
      trans_state' (mode_cont (kappa ++ [CIf (Value (Bool false)) (Value (Bool true)); CIf t1 t2]) sigma v)
                   (append_stack s' [CIf (trans_term t2) (trans_term t1)])

  (* Case 6: Handle mode_cont with non-empty continuation stack kappa ++ [k] *)
  | trans_mode_cont_non_empty :
      forall k kappa sigma v s',
      forall Hcond1: match List.rev kappa with |  CIf (Value (Bool false)) (Value (Bool true)) ::_ => False | _ => True end \/
       match k with CIf _ _ => False | _ => True end,
      trans_state' (mode_cont kappa sigma v) s' ->
      trans_state' (mode_cont (kappa ++ [k]) sigma v)
                   (append_stack s' [trans_cont_base k])

  (* Case 7: Handle mode_cont with empty continuation stack kappa ++ [] *)
  | trans_mode_cont_empty :
      forall sigma v,
      trans_state' (mode_cont [] sigma v)
                   (mode_cont [] (List.map trans_value sigma) (trans_return v)).

Lemma trans_state_deterministic:
  forall s s1,
    trans_state' s s1 ->
    forall s2,
    trans_state' s s2 ->
    s1 = s2.
Proof.
  induction 1; inversion 1; subst.
  all: try multimatch goal with
    | [h: _ = _ |- _] =>
      apply (f_equal (@List.rev _)) in h;
      repeat rewrite List.rev_app_distr in h;
      simpl in *;
      repeat injections; subst;
      repeat match goal with
      | [h: List.rev _ =  _ |- _] =>
        apply (f_equal (@List.rev _)) in h;
        repeat rewrite List.rev_involutive in h
      | [h: List.rev _ =  _ |- _] =>
        apply (f_equal (@List.rev _)) in h;
        repeat rewrite List.rev_involutive in h
      end;
      repeat injections; subst
    end.
  all: repeat rewrite List.rev_involutive in *.
  all: try solve [eapply f_equal2; eauto | unzip; tryfalse | congruence].
  { exfalso; induction kappa using List.rev_ind; intros; simpl in *.
    { congruence. }
    { rewrite List.rev_app_distr in *; simpl in *.
      injections; subst.
      unzip; tryfalse.
    }
  }
  { apply (f_equal (@List.rev _)) in H1;
    repeat rewrite List.rev_involutive in H1;
    simpl in H1. subst. 
    unzip; tryfalse.
  }
  { exfalso; induction kappa using List.rev_ind; intros; simpl in *.
    { congruence. }
    { rewrite List.rev_app_distr in *; simpl in *.
      injections; subst.
      unzip; tryfalse.
    }
  }
Qed.

Lemma trans_correct:
  forall s,
    trans_state' s (trans_state s).
Proof.
  (* trop pénible *)
Admitted.

Theorem cred_append_stack s s':
  (* If you can do a transition, then you can do the same transition with additional informations on the stack. *)
  cred s s' ->
  forall k,
  cred (append_stack s k) (append_stack s' k).
Proof.
  induction 1; intros; asimpl; try econstructor; eauto.
Qed.

Theorem star_cred_append_stack s s':
  star cred s s'
  ->
  forall k,
  star cred (append_stack s k) (append_stack s' k).
Proof.
  induction 1; intros.
  * eauto with sequences.
  * eapply star_step; eauto using cred_append_stack.
Qed.


Lemma append_left_and_right {s1 s2 kappa}:
  (exists tgt, star cred s1 tgt /\ star cred s2 tgt) ->
  exists tgt, star cred (append_stack s1 kappa) tgt /\ star cred (append_stack s2 kappa) tgt.
Proof.
  intros; unpack.
  eexists; split; eapply star_cred_append_stack; eauto.
Qed.


Ltac list_simpl_base h := 
  learn (f_equal (@List.rev _) h);
    repeat multimatch goal with
    | [h: _ |- _] =>
      let P := typeof h in
      match P with
      | @Learnt _ =>
        idtac
      | _ =>
        repeat rewrite List.rev_involutive in h;
        repeat rewrite List.rev_app_distr in h;
        simpl in h
      end
    end;
    injections;
    subst;
    try congruence
.
Ltac list_simpl0 := 
  (try multimatch goal with
  | [h: _ = _ |- _] =>
    list_simpl_base h
  end)
  .

Lemma list_append_decompose: forall {A} {kappa1 kappa2} {k1 k2: A} ,
  k1 :: kappa1 = kappa2 ++ [k2] ->
  (k1 = k2 /\ kappa1 = nil /\ kappa2 = nil)
  \/ (exists kappa, kappa1 = kappa ++ [k2] /\ kappa2 = k1 :: kappa).
Proof.
  induction kappa1 as [|a1 kappa1]; intros.
  { repeat list_simpl0.
    left; unzip; eauto.
  }
  {
    induction kappa2 as [|a2 kappa2]; repeat list_simpl0.
    destruct IHkappa1 with kappa2 a1 k2; eauto.
  }
Qed.



Ltac list_simpl := 
  (try multimatch goal with
  | [h: _ = _ |- _] =>
    list_simpl_base h
  | [h: _ :: _ = _ ++ [_] |- _] =>
    learn (list_append_decompose h); unzip
  end)
  .

Ltac decompose h :=

  let kappa := fresh "kappa" in
  first
    [ destruct (list_append_decompose h) as [?|[kappa ?]]; unpack; repeat list_simpl0; repeat cleanup
    | destruct (list_append_decompose (eq_sym h)) as [?|[kappa ?]]; unpack; repeat list_simpl0; repeat cleanup
  ].


Theorem correction_continuations:
  forall s1 s2,
  cred s1 s2 ->
  forall s1',
  trans_state' s1 s1' ->
  forall s2',
  trans_state' s2 s2' ->
  exists s3,
    star cred s1' s3 /\ star cred s2' s3.
Proof.
  (* induction s1 using (
    well_founded_induction
      (wf_inverse_image
        _
        nat
        _
        (fun s => List.length (stack s))
        PeanoNat.Nat.lt_wf_0)
  ). *)
  intros s1 s2 Hcred ? Htrans1.
  generalize dependent s2.
  induction Htrans1; inversion 1; subst; inversion 1; subst.
  all: repeat list_simpl0.
  all: try solve [repeat rewrite List.app_comm_cons in *; repeat rewrite List.rev_app_distr in *; simpl in *; unzip; tryfalse].
  all: try solve [
    eapply append_left_and_right;
    eapply IHHtrans1; [|solve [eauto]]; econstructor; eauto
  ].
  all: repeat cleanup.
  all: simpl; repeat (eapply confluent_star_step_left; [solve [econstructor]|]).
  all: try solve [eapply confluence_star_refl].
  { admit "need that b reduces". }
  { admit "need that b reduces". }
  { destruct (list_append_decompose (eq_sym H3)) as [?|[kappa' ?]]; unpack; repeat list_simpl0.
    all: repeat cleanup; unzip; tryfalse.
  }
  { eapply confluent_star_step_left. {
      econstructor.
      rewrite List.nth_error_map.
      rewrite H3. reflexivity.
    }
    eapply confluence_star_refl.
  }
  { eapply confluence_star_refl_eq.
    inversion H4.
    all: repeat list_simpl; simpl; list_simpl0; repeat cleanup.
    reflexivity.
  }
  { admit "need that b reduces". }
  { admit "need that u reduces". }
  { decompose H7.
    decompose H1.
    eapply append_left_and_right.
    eapply IHHtrans1; [econstructor|].
    eauto.
  }
  { decompose H4.
    decompose H24.
    unzip; tryfalse.
  }
  { decompose H1.
    decompose H1.
    eapply append_left_and_right.
    eapply IHHtrans1; [econstructor|].
    eauto.
  }
  { decompose H3.
    decompose H24.
    unzip; tryfalse.
  }
  { decompose H3.
    unzip; tryfalse.
  }
  { decompose H3.
    { inversion H5; repeat list_simpl0; repeat cleanup.
      inversion Htrans1; repeat list_simpl0; repeat cleanup.
      simpl.
      repeat (eapply confluent_star_step_left; [solve[econstructor]|]).
      repeat (eapply confluent_star_step_right; [solve[econstructor]|]).
      eapply confluence_star_refl.
    }
    { unzip; tryfalse. }
  }
  { decompose H3.
    { inversion H5; repeat list_simpl0; repeat cleanup.
      inversion Htrans1; repeat list_simpl0; repeat cleanup.
      simpl.
      repeat (eapply confluent_star_step_left; [solve[econstructor]|]).
      repeat (eapply confluent_star_step_right; [solve[econstructor]|]).
      eapply confluence_star_refl.
    }
    { unzip; tryfalse. }
  }
  {
    decompose H11.
    decompose H0.
    unzip; tryfalse.
  }
  { decompose H0.
    {
      inversion H5; repeat list_simpl0; repeat cleanup.
      inversion Htrans1; repeat list_simpl0; repeat cleanup.
      simpl.
      repeat (eapply confluent_star_step_left; [solve[econstructor]|]).
      repeat (eapply confluent_star_step_right; [solve[econstructor]|]).
      eapply confluence_star_refl.
    }
    { eapply append_left_and_right.
      eapply IHHtrans1; [econstructor|].
      eauto.
    }
  }
  { decompose H7.
    decompose H18.
    unzip; tryfalse.
  }
  { decompose H9.
    { inversion H5; repeat list_simpl0; repeat cleanup.
      inversion Htrans1; repeat list_simpl0; repeat cleanup.
      simpl.
      repeat (eapply confluent_star_step_left; [solve[econstructor]|]).
      repeat (eapply confluent_star_step_right; [solve[econstructor]|]).
      eapply confluence_star_refl.
    }
    { eapply append_left_and_right.
      eapply IHHtrans1; [econstructor|].
      eauto.
    }
  }
  {
    inversion Htrans1; repeat list_simpl0; repeat cleanup.
    simpl.
    repeat (eapply confluent_star_step_left; [solve[econstructor]|]).
    repeat (eapply confluent_star_step_right; [solve[econstructor]|]).
    eapply confluence_star_refl.
  }
  { inversion H5; repeat list_simpl0; repeat cleanup.
    inversion Htrans1; repeat list_simpl0; repeat cleanup.
    inversion H9; repeat list_simpl0; repeat cleanup.
    simpl.
    repeat (eapply confluent_star_step_left; [solve[econstructor]|]).
    repeat (eapply confluent_star_step_right; [solve[econstructor]|]).
    admit "need to reduce b".
  }
  { inversion Htrans1; repeat list_simpl0; repeat cleanup.
    simpl.
    repeat (eapply confluent_star_step_left; [solve[econstructor]|]).
    repeat (eapply confluent_star_step_right; [solve[econstructor]|]).
    eapply confluence_star_refl.
  }
  { inversion Htrans1; repeat list_simpl0; repeat cleanup.
    inversion H5; repeat list_simpl0; repeat cleanup.
    inversion H7; repeat list_simpl0; repeat cleanup.
    simpl.
    repeat (eapply confluent_star_step_left; [solve[econstructor]|]).
    repeat (eapply confluent_star_step_right; [solve[econstructor]|]).
    admit "require to reduce b".
  }
  { inversion Htrans1; repeat list_simpl0; repeat cleanup.
    simpl.
    repeat (eapply confluent_star_step_left; [solve[econstructor]|]).
    apply confluence_star_refl.
  }
Admitted.

Theorem correction_traditional:
  forall s1 s2,
  sred s1 s2 ->

  star sred
    (trans_term s1) (trans_term s2).
Proof.
  Local Ltac step := (
    try (eapply star_step; [solve
      [ econstructor; simpl; eauto using List.map_nth_error
    ]|]))
  .
  induction 1; simpl; repeat step; try eapply star_refl.
  4: { admit "abort". }
  all: admit.
Admitted.


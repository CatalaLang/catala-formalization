Require Import syntax.
Require Import Sorting.Permutation.
Import List.ListNotations.
Open Scope list_scope.
Require Import sequences common.
Require Import Coq.Arith.Arith.
Require Import Coq.ZArith.ZArith.
Require Import Bool.

Require Import String.


(* Proof automation. ZifyBool is needed for operators such as [_ <=? _] *)
Require Import Lia ZifyBool.

From Catala Require Import tactics.


(* Definition of continuaton semantics for the catala programming language. *)

Inductive result :=
  | RValue (v: value)
  | REmpty
  | RConflict
.

Theorem result_eq_dec: forall (x y : result), {x = y}+{x <> y}.
  decide equality.
  eapply value_eq_dec.
Qed.

Inductive is_hole :=
  | Hole
  | NoHole
.

Theorem is_hole_eq_dec: forall (x y : is_hole), {x = y}+{x <> y}.
  decide equality.
Qed.


(* App (Var 0) (up t2) *)

Inductive cont :=
  | CAppR (t2: term) (* [\square t2] *)
  | CClosure (t_cl: {bind term}) (sigma_cl: list value)
  (* [Clo(x, t_cl, sigma_cl) \square] Since we are using De Bruijn indices,
     there is no variable x. *)

  | CBinopL (op: op) (v1: value) (* [op t1 \square] *)
  | CBinopR (op: op) (t2: term) (* [op \square t2] *)
  | CReturn (sigma: list value) (* call return *)
  | CDefault (b: is_hole) (o: option value) (ts: list term) (tj: term) (tc: term)
    (* [Def(o, ts, tj, tc)] *)
  | CDefaultBase (tc: term)
    (* [ <| \square :- tc >] *)
  | CMatch (t1: term) (t2: {bind term})
    (* [ match \square with None -> t1 | Some -> t2 end ] *)
  | CIf (ta: term) (tb: term)
  | CSome
  | CErrorOnEmpty
  | CDefaultPure
  | CFold (f: term) (ts: list term)
.

Theorem option_eq_dec
	 : forall A : Type,
       (forall x y : A, {x = y} + {x <> y}) ->
       forall o o' : option A, {o = o'} + {o <> o'}.
Proof.
  intros.
  destruct o, o'; finish.
  epose proof (X a a0); finish.
Qed.



Theorem cont_eq_dec: forall (x y : cont), {x = y}+{x <> y}.
  decide equality.
  all: try eapply List.list_eq_dec.
  all: try eapply option_eq_dec.
  all: try solve
    [ eapply term_eq_dec
    | eapply value_eq_dec
    | eapply op_eq_dec
    | eapply is_hole_eq_dec].
Qed.

Inductive state :=
  | mode_eval (e: term) (kappa: list cont) (env: list value)
  | mode_cont (kappa: list cont) (env: list value) (result: result)
.

Theorem state_eq_dec: forall (x y : state), {x = y}+{x <> y}.
  decide equality.
  all: try eapply List.list_eq_dec.
  all: try eapply option_eq_dec.
  all: try solve
    [ eapply term_eq_dec
    | eapply value_eq_dec
    | eapply op_eq_dec
    | eapply is_hole_eq_dec
    | eapply result_eq_dec
    | eapply cont_eq_dec].
Qed.


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


  (** Rules related to the defaults *)

  | cred_defaultpure_intro:
    forall e kappa sigma,
    cred
      (mode_eval (DefaultPure e) kappa sigma)
      (mode_eval e (CDefaultPure::kappa) sigma)
  | cred_defaultpure_elim:
    forall kappa sigma v,
    cred
      (mode_cont (CDefaultPure::kappa) sigma (RValue v))
      (mode_cont kappa sigma (RValue (VPure v)))

  | cred_erroronempty_intro:
    forall e kappa sigma,
    cred
      (mode_eval (ErrorOnEmpty e) kappa sigma)
      (mode_eval e (CErrorOnEmpty::kappa) sigma)
  | cred_erroronempty_elim_empty:
    forall kappa sigma,
    cred
      (mode_cont (CErrorOnEmpty::kappa) sigma REmpty)
      (mode_cont kappa sigma RConflict)
  | cred_erroronempty_elim_other:
    forall kappa sigma v,
    cred
      (mode_cont (CErrorOnEmpty::kappa) sigma (RValue (VPure v)))
      (mode_cont kappa sigma (RValue v))

  | cred_default:
    forall ts tj tc kappa sigma,
    cred
      (mode_eval (Default ts tj tc) kappa sigma)
      (mode_cont ((CDefault Hole None ts tj tc)::kappa) sigma REmpty)

  | cred_default_unpack:
    forall o th ts tj tc kappa sigma,
    cred
      (mode_cont ((CDefault Hole o (th::ts) tj tc)::kappa) sigma REmpty)
      (mode_eval th ((CDefault NoHole o ts tj tc)::kappa) sigma)

  | cred_default_value:
    forall o ts tj tc kappa sigma v,
    cred
      (mode_cont ((CDefault NoHole o ts tj tc)::kappa) sigma (RValue (VPure v)))
      (mode_cont ((CDefault Hole o ts tj tc)::kappa) sigma (RValue (VPure v)))

  | cred_default_value_none_to_some:
    forall ts tj tc kappa sigma v,
    cred
      (mode_cont ((CDefault Hole None ts tj tc)::kappa) sigma (RValue (VPure v)))
      (mode_cont ((CDefault Hole (Some v) ts tj tc)::kappa) sigma REmpty)

  | cred_default_value_conflict:
    forall ts tj tc kappa sigma v v',
    cred
      (mode_cont ((CDefault Hole (Some v) ts tj tc)::kappa) sigma (RValue (VPure v')))
      (mode_cont kappa sigma RConflict)

  | cred_default_value_return:
    forall v tj tc kappa sigma,
    cred
      (mode_cont ((CDefault Hole (Some v) [] tj tc)::kappa) sigma REmpty)
      (mode_cont kappa sigma (RValue (VPure v)))

  (* empty *)
  | cred_default_empty:
    forall o ts tj tc kappa sigma,
    cred
      (mode_cont ((CDefault NoHole o ts tj tc)::kappa) sigma REmpty)
      (mode_cont ((CDefault Hole o ts tj tc)::kappa) sigma REmpty)

  | cred_defaultbase:
    forall tj tc kappa sigma,
    cred
      (mode_cont ((CDefault Hole None [] tj tc)::kappa) sigma REmpty)
      (mode_eval tj ((CDefaultBase tc)::kappa) sigma)

  | cred_defaultbasetrue:
    forall tc kappa sigma,
    cred
      (mode_cont ((CDefaultBase tc)::kappa) sigma (RValue (Bool true)))
      (mode_eval tc kappa sigma)

  | cred_defaultbasefalse:
    forall tc kappa sigma,
    cred
      (mode_cont ((CDefaultBase tc)::kappa) sigma (RValue (Bool false)))
      (mode_cont kappa sigma REmpty)

  (* Conflict panics and stop the execution of the program.
     We only pop the stack one at the time to ensure the size of kappa
     is changed by one at most. *)
  | cred_conflict:
    forall phi kappa sigma,
    (forall sigma', phi <> CReturn sigma') ->
    cred
      (mode_cont (phi::kappa) sigma RConflict)
      (mode_cont kappa sigma RConflict)

  | cred_confict_intro:
    forall kappa sigma,
    cred
      (mode_eval Conflict kappa sigma)
      (mode_cont kappa sigma RConflict)

  | cred_empty_intro:
    forall kappa sigma,
    cred
      (mode_eval Empty kappa sigma)
      (mode_cont kappa sigma REmpty)

  | cred_value_intro:
    forall v kappa sigma,
    cred
      (mode_eval (Value v) kappa sigma)
      (mode_cont kappa sigma (RValue v))

  | cred_op_intro:
    forall op e1 e2 kappa sigma,
    cred
      (mode_eval (Binop op e1 e2) kappa sigma)
      (mode_eval e1 (CBinopR op e2::kappa) sigma)

  | cred_op_mid:
    forall op e2 kappa sigma v,
    cred
      (mode_cont (CBinopR op e2 :: kappa) sigma (RValue v))
      (mode_eval e2 (CBinopL op v :: kappa) sigma)

  | cred_op_final:
    forall op v v1 v2 kappa sigma,
    Some v = get_op op v1 v2 ->
    cred
      (mode_cont (CBinopL op v1 :: kappa) sigma (RValue v2))
      (mode_cont kappa sigma (RValue v))

  | cred_match:
    forall u t1 t2 kappa sigma,
    cred
      (mode_eval (Match_ u t1 t2) kappa sigma)
      (mode_eval u ((CMatch t1 t2)::kappa) sigma)
  | cred_match_none:
    forall t1 t2 kappa sigma,
    cred
      (mode_cont ((CMatch t1 t2)::kappa) sigma (RValue VNone))
      (mode_eval t1 kappa sigma)
  | cred_match_some:
    forall t1 t2 kappa sigma v,
    cred
      (mode_cont ((CMatch t1 t2) :: kappa) sigma (RValue (VSome (v))))
      (mode_eval t2 (CReturn sigma :: kappa) (v::sigma))
  | cred_enone:
    forall kappa sigma,
    cred
      (mode_eval ENone kappa sigma)
      (mode_cont kappa sigma (RValue VNone))
  | cred_esome_intro:
    forall t kappa sigma,
    cred
      (mode_eval (ESome t) kappa sigma)
      (mode_eval t (CSome::kappa) sigma)
  | cred_esome_elim:
    forall v kappa sigma,
    cred
      (mode_cont (CSome::kappa) sigma (RValue v))
      (mode_cont kappa sigma (RValue (VSome v)))
  | cred_if:
    forall u t1 t2 kappa sigma,
    cred
      (mode_eval (If u t1 t2) kappa sigma)
      (mode_eval u ((CIf t1 t2)::kappa) sigma)
  | cred_if_none:
    forall t1 t2 kappa sigma,
    cred
      (mode_cont ((CIf t1 t2)::kappa) sigma (RValue (Bool true)))
      (mode_eval t1 kappa sigma)
  | cred_if_some:
    forall t1 t2 kappa sigma,
    cred
      (mode_cont ((CIf t1 t2) :: kappa) sigma (RValue (Bool false)))
      (mode_eval t2 kappa sigma)

  | cred_fold_intro:
    forall f ts acc kappa sigma,
    cred
      (mode_eval (Fold f ts acc) kappa sigma)
      (mode_eval acc (CFold f ts :: kappa) sigma)
  | cred_fold_rec:
    forall f h ts v kappa sigma,
    cred
      (mode_cont (CFold f (h::ts) :: kappa) sigma (RValue v))
      (mode_eval (App (App f h) (Value v)) (CFold f ts :: kappa) sigma)
  | cred_fold_init:
    forall f v kappa sigma,
    cred
      (mode_cont (CFold f [] :: kappa) sigma (RValue v))
      (mode_cont kappa sigma (RValue v))
  | cred_fold_conflict:
    forall f ts kappa sigma,
    cred
      (mode_cont (CFold f ts :: kappa) sigma RConflict)
      (mode_cont kappa sigma RConflict)
.

Notation "'cred' t1 t2" :=
  (cred t1 t2) (
  at level 50,
  t1 at level 3,
  t2 at level 3,
  only printing,
  format "'cred'  '[hv' t1  '/' t2 ']'"
).
Notation "'star' 'cred' t1 t2" :=
  (star cred t1 t2) (
  at level 50,
  t1 at level 3,
  t2 at level 3,
  only printing,
  format "'star'  'cred'  '[hv' t1  '/' t2 ']'"
).
Notation "'plus' 'cred' t1 t2" :=
  (plus cred t1 t2) (
  at level 50,
  t1 at level 3,
  t2 at level 3,
  only printing,
  format "'plus'  'cred'  '[hv' t1  '/' t2 ']'"
).


(* Declare Custom Entry latex.
Declare Scope latex.

  (* Base coq *)
  Notation "'<LATEX>' e '</LATEX>'" := e (e custom latex): latex.
  Notation "'<COQERROR>' x '</COQERROR>'" := x (in custom latex, x constr): latex.

  Notation "'\ident{' x '}'" := (x) (x ident, in custom latex at level 0): latex.

  Notation "'\synpunct{[]}'" := (@nil _) (in custom latex): latex.
  Notation " x '\syncons' l " := (@cons _ x l) (in custom latex at level 20): latex.
  Notation " '[' ']' " := ([]) (in custom latex): latex.
  Notation " '[' x ']' " := ([x]) (in custom latex): latex.
  Notation " '[' x ';'  y ']' " := ([x; y]) (in custom latex): latex.
  Notation " '[' x ';'  y ']' " := ([x; y]) (in custom latex): latex.
  Notation " '[' x ';'  y ';' z ']' " := ([x; y; z]) (in custom latex): latex.
  Notation " '[' x ';'  y ';' z ';' w ']' " := ([x; y; z; w]) (in custom latex): latex.

  Notation " \synnone " := None (in custom latex): latex.
  Notation " '\synsome\left(' v '\right)' " := (Some v) (in custom latex): latex.

  (* Terms *)
  Notation " '\overline{\synvar{' x '}}' " := (Var x) (in custom latex, x constr ): latex.
  Notation " '\synvar{' x '}' " := (FreeVar x) (in custom latex): latex.
  Notation " t1  t2 " := (App t1 t2) (in custom latex at level 15): latex.
  Notation " '\synlambda.' t " := (Lam t) (in custom latex at level 25): latex.
  Notation " \synlet t2 \synin t1 " := (App (Lam t1) t2) (in custom latex at level 17): latex.

  Notation " '\synlangle' ts '\synmid' tj '\synjust' tc '\synrangle' " :=  (Default ts tj tc) (in custom latex): latex.
  Notation " '\ghostvalue{' v '}'" := (Value (v)) (in custom latex): latex.
  Notation " t1 '\synpunct{' op '}' t2 " := (Binop op t1 t2) (in custom latex at level 19): latex.

  Notation "'if' a 'then' b 'else' c 'end'" := (If a b c) (in custom latex).
  Notation "'match' a 'with' 'None' => b 'Some' => c 'end'" := (Match_ a b c) (in custom latex).


  (* Closures *)
  Notation " '\square' '\synpunct{' op '}' e2 " := (CBinopR op e2) (in custom latex at level 0): latex.
  Notation " '\square' e2 " := (CAppR e2) (in custom latex at level 0): latex.
  Notation " v1 '\synpunct{' op '}' '\square' " := (CBinopL op v1) (in custom latex at level 0): latex.
  Notation " '\synCClo(' t_cl ','  sigma_cl ')' '\square' " := (CClosure t_cl sigma_cl) (in custom latex at level 0): latex.
  Notation " '\synDef(' o ',' ts ','  tj ','  tc ')' " := (CDefault o ts tj tc) (in custom latex at level 0): latex.
  Notation " '\synReturn(' sigma ')' " := (CReturn sigma) (in custom latex at level 0): latex.
  Notation " '\synlangle' '\square' '\synjust' tc '\synrangle' " := (CDefaultBase tc) (in custom latex at level 0): latex.


  (* Runtime Values *)
  Notation "\syntrue" := (Bool true) (in custom latex at level 0): latex.
  Notation "\synfalse" := (Bool false) (in custom latex at level 0): latex.

  Notation " \ghostint i " := (Int i) (in custom latex at level 0, i constr): latex.
  Notation " '\synClo(' t ','  sigma ')' " := (Closure t sigma) (in custom latex): latex.
  (* Notation " '\ghostvvalue'  v " := (VValue v) (in custom latex): latex. *)

  (* Notation "+" := Add (in custom latex): latex. *)


  (* Results *)
  Notation "'\synempty'" := REmpty (in custom latex): latex.
  Notation "'\synconflict'" := RConflict (in custom latex): latex.
  Notation " v " := (RValue v) (in custom latex at level 0): latex.

  (* continuation mode *)
  Notation "'{\leval'  t ,  kappa ,  sigma  '\reval}'" := (mode_eval t kappa  sigma) (in custom latex at level 150): latex.
  Notation "'{\lcont'  kappa ,  sigma ,  v  '\rcont}'" := (mode_cont kappa sigma  v) (in custom latex): latex.
  Notation " s1  '\leadsto^*' s2 " := (star cred s1 s2) (in custom latex at level 20): latex.
  Notation " s1  '\leadsto' s2 " := (cred s1 s2) (in custom latex at level 200): latex. *)

(** STACK MANIPULATION *)

Definition stack s :=
  match s with
  | mode_eval _ k _ => k
  | mode_cont k _ _ => k
  end.

Definition with_stack s kappa :=
  match s with
  | mode_eval t _ sigma => mode_eval t kappa sigma
  | mode_cont _ sigma v => mode_cont kappa sigma v
  end.

Definition is_mode_eval s :=
  match s with
  | mode_eval _ _ _ => true
  | _ => false
  end.

Definition is_mode_cont s :=
  match s with
  | mode_cont _ _ _ => true
  | _ => false
  end.

Definition append_stack s kappa2 :=
  match s with
  | mode_eval t kappa1 sigma =>
    mode_eval t (kappa1++kappa2) sigma
  | mode_cont kappa1 sigma v =>
    mode_cont (kappa1++kappa2) sigma v
  end
.

Lemma append_stack_all {s}:
  s = append_stack (with_stack s []) (stack s).
Proof.
  induction s; intros; simpl in *; subst; reflexivity.
Qed.

Lemma append_stack_app {s kappa1 kappa2}:
  stack s = kappa1 ++ kappa2 ->
  s = append_stack (with_stack s kappa1) kappa2.
Proof.
  induction s; intros; simpl in *; subst; reflexivity.
Qed.


(** Reductions are stable if stack is append. *)

Theorem cred_append_stack s s':
  (* If you can do a transition, then you can do the same transition with additional informations on the stack. *)
  cred s s' ->
  forall k,
  cred (append_stack s k) (append_stack s' k).
Proof.
  induction 1; intros; asimpl; try econstructor; eauto.
  repeat intro; inj.
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

Theorem plus_cred_append_stack s s':
  plus cred s s'
  ->
  forall k,
  plus cred (append_stack s k) (append_stack s' k).
Proof.
  induction 1; intros.
  econstructor; try eapply cred_append_stack; try eapply star_cred_append_stack; eauto.
Qed.


(* PROPERTIES OF CRED *)

Theorem cred_deterministic (s s1' s2': state):
  cred s s1' -> cred s s2' -> s1' = s2'.
Proof.
  induction 1; inversion 1; subst; try solve [eauto|congruence].
  (* What is left is cases involving the [cred_empty] and [cred_conflict] rules. Since congrugence don't go inside the forall, it does not handle those cases correctly. *)
  all: try match goal with
    [h: context [CReturn _ <> CReturn _] |- _ ] =>
      epose proof h _ as tmp; exfalso; apply tmp; eauto
    end.
  all: try match goal with
    [h: context [CDefault _ _ _ _ _ <> CDefault _ _ _ _ _] |- _ ] =>
    epose proof h _ _ _ _ _ as tmp; exfalso; apply tmp; eauto
    end.
Qed.


(** Our reduction sequences should have the folowing shape:
* The head of kappa, if it exists can have any possible shape.
* Each member of the tail should however not contain "Hole" inside their default terms.
* This is explained by the invariant `inv_state`.

*)

Inductive inv_conts_no_hole: cont -> Prop :=
| inv_CAppR (t2: term):
  inv_conts_no_hole (CAppR (t2: term))
| inv_CClosure (t_cl: {bind term}) (sigma_cl: list value):
  inv_conts_no_hole (CClosure (t_cl: {bind term}) (sigma_cl: list value))
| inv_CBinopL (op: op) (v1: value):
  inv_conts_no_hole (CBinopL (op) (v1: value))
| inv_CBinopR (op: op) (t2: term):
  inv_conts_no_hole (CBinopR (op) (t2: term))
| inv_CReturn (sigma: list value):
  inv_conts_no_hole (CReturn (sigma: list value))
| inv_CDefault (o: option value) (ts: list term) (tj: term) (tc: term):
  inv_conts_no_hole (CDefault (NoHole) (o: option value) (ts: list term) (tj: term) (tc: term))
| inv_CDefaultBase (tc: term):
  inv_conts_no_hole (CDefaultBase (tc: term))
| inv_CMatch (t1: term) (t2: {bind term}):
  inv_conts_no_hole (CMatch (t1: term) (t2: {bind term}))
| inv_CSome:
  inv_conts_no_hole (CSome)
| inv_If (ta tb: term):
  inv_conts_no_hole (CIf ta tb)
| inv_ErrorOnEmpty:
  inv_conts_no_hole CErrorOnEmpty
| inv_CDefaultPure:
  inv_conts_no_hole CDefaultPure
| inv_CFold:
  forall f ts,
  inv_conts_no_hole (CFold f ts)
.

Inductive inv_state: state -> Prop :=
| inv_mode_eval t kappa env:
  List.Forall inv_conts_no_hole kappa ->
  inv_state (mode_eval t kappa env)
| inv_mode_cont_cons k kappa env r:
  List.Forall inv_conts_no_hole kappa ->
  inv_state (mode_cont (k::kappa) env r)
| inv_mode_cont_nil env r:
  inv_state (mode_cont [] env r)
.

Lemma inv_state_append_stack {s kappa}:
  inv_state s ->
  List.Forall inv_conts_no_hole kappa ->
  inv_state (append_stack s kappa).
Proof.
  inversion 1; simpl; intros.
  econstructor; eapply List.Forall_app; eauto.
  econstructor; eapply List.Forall_app; eauto.
  { induction kappa; unpack.
    all: econstructor; eauto.
  }
Qed.
  

(* This property is indeed conserved by the cred relation. *)

Theorem cred_inv_state_stable:
  forall s1 s2,
    cred s1 s2 ->
    inv_state s1 ->
    inv_state s2.
Proof.
  induction 1; inversion 1; subst; repeat econstructor; eauto.
  all: destruct kappa; econstructor; unpack; eauto.
Qed.

Theorem star_cred_inv_state_stable:
  forall s1 s2,
    star cred s1 s2 ->
    inv_state s1 ->
    inv_state s2.
Proof.
  induction 1.
  { eauto. }
  { intros; eapply IHstar; eapply cred_inv_state_stable; eauto. }
Qed.


Theorem cred_stack_empty_irred:
  forall sigma v,
    irred cred (mode_cont [] sigma v)
.
Proof.
  repeat intro.
  inversion H.
Qed.

Lemma cred_stack_sub:
  forall a b k,
    cred a b ->
    lastn 1 (stack a) = [k] ->
    lastn 1 (stack a) = lastn 1 (stack b) ->
    cred
      (with_stack a (droplastn 1 (stack a)))
      (with_stack b (droplastn 1 (stack b))).
Proof.
  (* By induction on [cred a b]. *)
  induction 1.
  (* First filter: rules that don't modify the stack. *)
  all: simpl; try econstructor; eauto; intros.
  all: induction kappa.

  (* Get rid of empty stacks when it is not supposed to be empty. *)
  all: try solve [repeat rewrite lastn_def_firstn in *; simpl in *; inj].

  all: repeat rewrite lastn_cons in * by (simpl; lia).
  all: try remember (a::kappa) as kappa'.
  all: repeat rewrite droplastn_cons by (subst; simpl; lia).
  all: try solve [econstructor; eauto].
  {
    repeat rewrite lastn_def_firstn in *; simpl in *.
    inj.
    exfalso; eapply list_diagonal; eauto.
  }
Qed.

Theorem creds_stack_sub:
  forall s1 s2,
    star (fun s1 s2 => cred s1 s2 /\ lastn 1 (stack s1) = lastn 1 (stack s2))
      s1 s2
    ->
      star cred
        (with_stack s1 (droplastn 1 (stack s1)))
        (with_stack s2 (droplastn 1 (stack s2))).
Proof.
  intros s1 s2.
  induction 1; unpack; econstructor.
  { eapply cred_stack_sub; eauto. }
  { eapply IHstar.
  }
Qed.

Lemma cred_stack_lastn1_change_is_mode_cont:
  forall a b k,
    lastn 1 (stack a) = [k] ->
    lastn 1 (stack a) <> lastn 1 (stack b) ->
    cred a b ->
    is_mode_cont a = true.
Proof.
  intros a b k Hk Hab Hred.
  pose proof lastn1_length1 _ _ Hk.
  revert Hred Hab; induction 1.
  all: simpl; subst; eauto; rewrite lastn_cons; eauto.
Qed.

Lemma cred_stack_lastn1_change_sizeone:
  forall a b k,
    cred a b ->
    lastn 1 (stack a) = [k] ->
    lastn 1 (stack a) <> lastn 1 (stack b) ->
    stack a = [k].
Proof.
  induction 1.
  all: simpl; subst; eauto.
  all: induction kappa using List.rev_ind.
  all: repeat rewrite List.app_comm_cons.
  all: repeat rewrite lastn1_append.
  all: repeat rewrite lastn1_one.
  all: repeat rewrite lastn1_nil.
  all: intros; solve [ inj | tryfalse | eauto].
Qed.

Theorem cred_stack_drop:
  forall t k env env'' r'',
    star cred
      (mode_eval t [k] env)
      (mode_cont [] env'' r'')
    ->
    exists env' r',
    star cred
      (mode_eval t [] env)
      (mode_cont [] env' r').
Proof.
  intros.

  (* Let s1 be the starting state, and s3 the ending state. The goal is find s2, the first state before there is a change on the last continuation of the stack.  *)
  remember (mode_eval t [k] env) as s1.
  remember (mode_cont [] env'' r'') as s3.
  destruct (takewhile (fun s s' => RMicromega.sumboolb (List.list_eq_dec cont_eq_dec (lastn 1 (stack s1)) (lastn 1 (stack s')))) H)
  as [Htakewhile| (s2 & s2' & Hs1s2 & Hs2's3 & Hs2s2' & Hs2')].
  { (* This state does exists since s1 and s3 have different stacks. *)
    exfalso.
    induction Htakewhile using star_ind_n1.
    { subst; inj. }
    { unpack; subst; simpl in *; inj. }
  }
  { (* There is no modification of the last continuation between s1 and s2. We already have this fact, but in bool format. *)
    assert (Hs2: lastn 1 (stack s2) = lastn 1 (stack s1)). {
      induction Hs1s2 using star_ind_n1.
      { eauto. }
      { unpack.
        remember (List.list_eq_dec cont_eq_dec (lastn 1 (stack s1)) (lastn 1 (stack z))) as b; induction b; simpl in *; tryfalse; eauto.
      }
    }

    (* There is indead an modification between s2 and s2'. *)
    assert (Hs2'_tmp: lastn 1 (stack s2) <> lastn 1 (stack s2')). {
      clear - Hs2 Hs2'.
      remember (List.list_eq_dec cont_eq_dec (lastn 1 (stack s1)) (lastn 1 (stack s2'))) as b; induction b; simpl in *; tryfalse; eauto.
      rewrite Hs2; eauto.
    }
    clear Hs2'; rename Hs2'_tmp into Hs2'.

    assert (Hs1s2_tmp: star (fun s s' => cred s s' /\ lastn 1 (stack s1) = lastn 1 (stack s')) s1 s2). {
      clear -Hs1s2.
      induction Hs1s2 using star_ind_n1.
      { econstructor. }
      { eapply star_step_n1.
        2: { eapply IHHs1s2. }
        { unpack.
          remember (List.list_eq_dec cont_eq_dec (lastn 1 (stack s1)) (lastn 1 (stack z))) as cond; induction cond; simpl in *; inj.
          repeat split; eauto.
        }
      }
    }
    clear Hs1s2; rename Hs1s2_tmp into Hs1s2.

    assert (Hs1s2_tmp: star (fun s1 s2 => cred s1 s2 /\ lastn 1 (stack s1) = lastn 1 (stack s2)) s1 s2). {
      clear -Hs1s2.
      induction Hs1s2 using star_ind_n1.
      { econstructor. }
      { eapply star_step_n1.
        2: { eapply IHHs1s2. }
        { unpack.
          assert (Hy: (lastn 1 (stack s1)) = (lastn 1 (stack y))).
          { clear - Hs1s2.
            induction Hs1s2 using star_ind_n1; unpack; eauto.
          }
          repeat split; congruence.
        }
      }
    }
    clear Hs1s2; rename Hs1s2_tmp into Hs1s2.

    rewrite Heqs1 in Hs2; simpl in Hs2; rewrite lastn1_one in Hs2.
    epose proof (cred_stack_lastn1_change_is_mode_cont _ _ _ Hs2 Hs2' Hs2s2').
    epose proof (cred_stack_lastn1_change_sizeone _ _ _ Hs2s2' Hs2 Hs2').
    induction s2; subst; simpl in *. { tryfalse. }

    subst.
    exists env0, result0.
    remember (mode_eval t [k] env) as s1.
    remember (mode_cont [k] env0 result0) as s2.
    replace (mode_eval t [] env) with (with_stack s1 (droplastn 1 (stack s1))).
    replace (mode_cont [] env0 result0) with (with_stack s2 (droplastn 1 (stack s2))).
    all: try solve [unfold with_stack; unfold droplastn; subst; simpl; eauto].

    assert (lastn 1 (stack s1) = [k]).
    { subst; simpl; rewrite lastn1_one; eauto. }
    eapply creds_stack_sub; eauto.
  }
Qed.

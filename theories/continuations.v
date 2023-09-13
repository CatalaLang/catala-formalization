Require Import syntax.
Require Import Sorting.Permutation.
Import List.ListNotations.
Open Scope list_scope.
Require Import sequences common.
Require Import Coq.Arith.Arith.
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

(* App (Var 0) (up t2) *)

Inductive cont :=
  | CAppR (t2: term) (* [\square t2] *)
  | CClosure (t_cl: {bind term}) (sigma_cl: list value)
  (* [Clo(x, t_cl, sigma_cl) \square] Since we are using De Bruijn indices,
     there is no variable x. *)

  | CBinopL (op: op) (v1: value) (* [op t1 \square] *)
  | CBinopR (op: op) (t2: term) (* [op \square t2] *)
  | CReturn (sigma: list value) (* call return *)
  | CDefault (o: option value) (ts: list term) (tj: term) (tc: term)
    (* [Def(o, ts, tj, tc)] *)
  | CDefaultBase (tc: term)
    (* [ <| \square :- tc >] *)
  | CMatch (t1: term) (t2: {bind term})
    (* [ match \square with None -> t1 | Some -> t2 end ] *)
  | CSome
.

Inductive state :=
  | mode_eval (e: term) (kappa: list cont) (env: list value)
  | mode_cont (kappa: list cont) (env: list value) (result: result)
.

Inductive cred: state -> state -> Prop :=
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

  | cred_default:
    forall ts tj tc kappa sigma,
    cred
      (mode_eval (Default ts tj tc) kappa sigma)
      (mode_cont ((CDefault None ts tj tc)::kappa) sigma REmpty)

  | cred_defaultunpack:
    forall o th ts tj tc kappa sigma,
    cred
      (mode_cont ((CDefault o (th::ts) tj tc)::kappa) sigma REmpty)
      (mode_eval th ((CDefault o ts tj tc)::kappa) sigma)

  | cred_defaultnone:
    forall ts tj tc kappa sigma v,
    cred
      (mode_cont ((CDefault None ts tj tc)::kappa) sigma (RValue v))
      (mode_cont ((CDefault (Some v) ts tj tc)::kappa) sigma REmpty)

  | cred_defaultconflict:
    forall ts tj tc kappa sigma v v',
    cred
      (mode_cont ((CDefault (Some v) ts tj tc)::kappa) sigma (RValue v'))
      (mode_cont kappa sigma RConflict)

  | cred_defaultvalue:
    forall v tj tc kappa sigma,
    cred
      (mode_cont ((CDefault (Some v) [] tj tc)::kappa) sigma REmpty)
      (mode_cont kappa sigma (RValue v))

  (* | cred_defaultnonefinal: (* not needed *)
    todo *)

  | cred_defaultbase:
    forall tj tc kappa sigma,
    cred
      (mode_cont ((CDefault None [] tj tc)::kappa) sigma REmpty)
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

  (* REmpty is catched by CDefault in the rule cdefaultbase. *)
  | cred_empty:
    forall phi kappa sigma,
    (forall o ts tj tc, phi <> CDefault o ts tj tc) ->
    (forall sigma', phi <> CReturn sigma') ->
    cred
      (mode_cont (phi::kappa) sigma REmpty)
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
.


Declare Custom Entry latex.
Declare Scope latex.

  (* Base coq *)
  Notation "'<LATEX>' e '</LATEX>'" := e (e custom latex): latex.
  Notation "'<COQERROR>' x '</COQERROR>'" := x (in custom latex, x constr): latex.

  Notation "'\ident{' x '}'" := (x) (x ident, in custom latex at level 0): latex.

  Notation "'\synpunct{[]}'" := (@nil _) (in custom latex): latex.
  Notation "'{' x '\syncons' l '}'" := (@cons _ x l) (in custom latex): latex.
  Notation "'{' '[' x ']' '}'" := ([x]) (in custom latex): latex.
  Notation "'{' '[' x ';'  y ']' '}'" := ([x; y]) (in custom latex): latex.
  Notation "'{' '[' x ';'  y ']' '}'" := ([x; y]) (in custom latex): latex.
  Notation "'{' '[' x ';'  y ';' z ']' '}'" := ([x; y; z]) (in custom latex): latex.
  Notation "'{' '[' x ';'  y ';' z ';' w ']' '}'" := ([x; y; z; w]) (in custom latex): latex.

  Notation "'{' \synnone '}'" := None (in custom latex): latex.
  Notation "'{' '\synsome(' v ')' '}'" := (Some v) (in custom latex): latex.

  (* Terms *)
  Notation "'{' '\overline{\synvar{' x '}}' '}'" := (Var x) (in custom latex, x constr ): latex.
  Notation "'{' '\synvar{' x '}' '}'" := (FreeVar x) (in custom latex): latex.
  Notation "'{' t1  t2 '}'" := (App t1 t2) (in custom latex): latex.
  Notation "'{' ( '\synlambda.' t ) '}'" := (Lam t) (in custom latex): latex.
  Notation "'{' \synlet t2 \synin t1 '}'" := (App (Lam t1) t2) (in custom latex): latex.

  Notation "'{' '\synlangle' ts '\synmid' tj '\synjust' tc '\synrangle' '}'" :=  (Default ts tj tc) (in custom latex): latex.
  Notation "'{' '\ghostvalue' v '}'" := (Value (v)) (in custom latex): latex.
  Notation "'{' t1 '\synpunct{' op '}' t2 '}'" := (Binop op t1 t2) (in custom latex): latex.


  (* Closures *)
  Notation "'{' '\square' '\synpunct{' op '}' e2 '}'" := (CBinopR op e2) (in custom latex): latex.
  Notation "'{' '\square' e2 '}'" := (CAppR e2) (in custom latex): latex.
  Notation "'{' v1 '\synpunct{' op '}' '\square' '}'" := (CBinopL op v1) (in custom latex): latex.
  Notation "'{' '\synCClo(' t_cl ','  sigma_cl ')' '\square' '}'" := (CClosure t_cl sigma_cl) (in custom latex): latex.
  Notation "'{' '\synDef(' o ',' ts ','  tj ','  tc ')' '}'" := (CDefault o ts tj tc) (in custom latex): latex.
  Notation "'{' '\synReturn(' sigma ')' '}'" := (CReturn sigma) (in custom latex): latex.
  Notation "'{' '\synlangle' '\square' '\synjust' tc '\synrangle' '}'" := (CDefaultBase tc) (in custom latex): latex.


  (* Runtime Values *)
  Notation "\syntrue" := true (in custom latex): latex.
  Notation "\synfalse" := false (in custom latex): latex.
  Notation "'{' \ghostbool b '}'" := (Bool b) (in custom latex): latex.
  Notation "'{' \ghostint i '}'" := (Int i) (in custom latex, i constr): latex.
  Notation "'{' '\synClo(' t ','  sigma ')' '}'" := (Closure t sigma) (in custom latex): latex.
  (* Notation "'{' '\ghostvvalue'  v '}'" := (VValue v) (in custom latex): latex. *)

  Notation "+" := Add (in custom latex): latex.


  (* Results *)
  Notation "'\synempty'" := REmpty (in custom latex): latex.
  Notation "'\synconflict'" := RConflict (in custom latex): latex.
  Notation "'{' v '}'" := (RValue v) (in custom latex): latex.

  (* continuation mode *)
  Notation "'{\leval'  t ,  kappa ,  sigma  '\reval}'" := (mode_eval t kappa  sigma) (in custom latex): latex.
  Notation "'{\lcont'  kappa ,  sigma ,  v  '\rcont}'" := (mode_cont kappa sigma  v) (in custom latex): latex.
  Notation "'{' s1  '\leadsto^*' s2 '}'" := (star cred s1 s2) (in custom latex): latex.
  Notation "'{' s1  '\leadsto' s2 '}'" := (cred s1 s2) (in custom latex): latex.


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

Section CRED_EXAMPLES.
  Require Import Coq.ZArith.ZArith.
  Example wtf:
  exists sigma',
    star cred
    (mode_eval
      (* \synlet 5 \synin (\synlet 3 \synin \bar 0) +\ bar 0*)
      (App
        (Lam
          (Binop
            Add
            (App (Lam (Var 0)) (Value (Int 3%Z)))
            (Var 0)
          )
        )
        (Value (Int 5%Z))
      )
      []
      []
    )
    (mode_cont [] sigma' (RValue (Int 8%Z)))
    .
  Proof.
    repeat econstructor.
    (* (* step by step for demonstration purpose. *)
    try eapply star_step; [econstructor; simpl; eauto|].
    try eapply star_step; [econstructor; simpl; eauto|].
    try eapply star_step; [econstructor; simpl; eauto|].
    try eapply star_step; [econstructor; simpl; eauto|].
    try eapply star_step; [econstructor; simpl; eauto|].
    try eapply star_step; [econstructor; simpl; eauto|].
    try eapply star_step; [econstructor; simpl; eauto|].
    try eapply star_step; [econstructor; simpl; eauto|].
    try eapply star_step; [econstructor; simpl; eauto|].
    try eapply star_step; [econstructor; simpl; eauto|].
    try eapply star_step; [econstructor; simpl; eauto|].
    try eapply star_step; [econstructor; simpl; eauto|].
    try eapply star_step; [econstructor; simpl; eauto|].
    try eapply star_step; [econstructor; simpl; eauto|].
    try eapply star_step; [econstructor; simpl; eauto|].
    try eapply star_step; [econstructor; simpl; eauto|].
    eapply star_refl. *)
  Qed.

End CRED_EXAMPLES.

Section CRED_PROPERTIES.

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

Definition append_env s sigma2 :=
  match s with
  | mode_eval t kappa sigma1 =>
    mode_eval t kappa (sigma1 ++ sigma2)
  | mode_cont kappa sigma1 v =>
    mode_cont kappa (sigma1 ++ sigma2) v
  end
.

Lemma append_stack_def s kappa:
  append_stack s kappa = with_stack s (stack s ++ kappa).
Proof.
  induction s; simpl; eauto.
Qed.


(** Reductions are stable if stack is append. *)

Theorem append_stack_stable s s':
  (* If you can do a transition, then you can do the same transition with additional informations on the stack. *)
  cred s s' ->
  forall k,
  cred (append_stack s k) (append_stack s' k).
Proof.
  induction 1; intros; asimpl; try econstructor; eauto.
Qed.

Theorem append_stack_stable_star s s':
  star cred s s'
  ->
  forall k,
  star cred (append_stack s k) (append_stack s' k).
Proof.
  induction 1; intros.
  * eauto with sequences.
  * eapply star_step; eauto using append_stack_stable.
Qed.

Theorem append_stack_all_cont kappa sigma r:
  mode_cont kappa sigma r = append_stack (mode_cont [] sigma r) kappa.
Proof.
  simpl; eauto.
Qed.

Theorem append_stack_all_eval t kappa sigma:
  mode_eval t kappa sigma = append_stack (mode_eval t [] sigma) kappa.
Proof.
  simpl; eauto.
Qed.

Theorem cred_append_stack_inv s s' n:
  cred s s' ->
  (fun x y => lastn n (stack x) = lastn n (stack y)) s s'->
  cred
    (with_stack s (droplastn n (stack s)))
    (with_stack s' (droplastn n (stack s')))
.
Proof.
  induction 1; simpl; intros; try econstructor.
  all: repeat rewrite droplastn_cons; try econstructor.
  all: try solve [eapply lastn_cons_length; eauto].
  all: try eapply lastn_cons_cons_length; eauto; try congruence.
  all: intro; injections; eapply fuck_stdlib; eauto.
Qed.

Theorem cred_star_append_stack_inv s s' n:
  star (fun x y => cred x y /\ lastn n (stack x) = lastn n (stack y)) s s' ->
  star cred
    (with_stack s (droplastn n (stack s)))
    (with_stack s' (droplastn n (stack s'))).
Proof.
  induction 1; unpack; econstructor.
  { eapply cred_append_stack_inv; eauto. }
  { eauto. }
Qed.

Theorem cred_stack_stack_inv_one s s' k:
  star (fun x y => cred x y /\ lastn 1 (stack x) = lastn 1 (stack y)) s s' ->
  stack s = [k] ->
  stack s' = [k] ->
  star cred (with_stack s []) (with_stack s' []).
Proof.
  intros Hcred Hs Hs'.
  replace ([]) with (droplastn 1 (stack s)) at 1.
  2:{ rewrite Hs; unfold droplastn; simpl; eauto. }
  replace ([]) with (droplastn 1 (stack s')) at 1.
  2:{ rewrite Hs'; unfold droplastn; simpl; eauto. }
  eapply cred_star_append_stack_inv; eauto.
Qed.


(** Reduction don't modify the stack too much *)

Lemma cred_stack_lenght_at_most_one s1 s2:
  cred s1 s2 ->
  let n1 := List.length (stack s1) in
  let n2 := List.length (stack s2) in
  n1 = n2 \/ n1 = S n2 \/ S n1 = n2.
Proof.
  induction 1; simpl; lia.
Qed.

Lemma cred_stack_lenght_at_most_one_precise s1 s2:
  cred s1 s2 ->
  let n1 := List.length (stack s1) in
  let n2 := List.length (stack s2) in
  False
  \/ n1 = n2 /\ is_mode_cont s1 = true
  \/ n1 = n2 /\ is_mode_eval s1 = true /\ is_mode_cont s2 = true /\ stack s1 = stack s2
  \/ n1 = S n2 /\ is_mode_cont s1 = true
  \/ S n1 = n2 /\ is_mode_eval s1 = true.
Proof.
  induction 1; try solve [ idtac
    | simpl; left; repeat split
    | simpl; right; left; repeat split
    | simpl; right; right; left; repeat split
    | simpl; right; right; right; left; repeat split
    | simpl; right; right; right; right; left; repeat split
    | simpl; lia]. 
Qed.

Lemma cred_lastn_stable_n_minus_one s1 s2 n:
  List.length (stack s1) > n ->
  List.length (stack s2) > n ->
  cred s1 s2 ->
  lastn n (stack s1) = lastn n (stack s2).
Proof.
  intros Hs1 Hs2.
  induction 1; try solve [unfold lastn; case n; simpl in *; eauto];
    simpl in *; repeat rewrite lastn_cons in *; eauto; try lia.
Qed.

Lemma cred_lastn_different s1 s2:
  let n1 := List.length (stack s1) in
  let n2 := List.length (stack s2) in
  cred s1 s2 ->
  lastn n1 (stack s1) <> lastn n1 (stack s2) ->
  (n1 = S n2 /\ is_mode_cont s1 = true /\ lastn n2 (stack s1) = lastn n2 (stack s2))
  \/ (n1 = n2 /\ is_mode_cont s1 = true /\ forall k, n1 = S k -> lastn k (stack s1) = lastn k (stack s2))
  \/ (S n1 = n2 /\ False).
Proof.
  Ltac finish := try solve [repeat split; intros; injections; subst;
      repeat rewrite lastn_length in *;
      repeat rewrite lastn_length_cons in *;
      eauto; tryfalse lia].
  simpl.
  induction 1; simpl; intros;
  solve [ left; finish | right; left; finish | right; right finish].
Qed.

(* specialized versions of the previous lemma *)


Lemma cred_stack_same_length_unmodified s1 s2:
  cred s1 s2 ->
  List.length (stack s1) = List.length (stack s2) ->
  is_mode_cont s1 = true \/ stack s1 = stack s2 /\ is_mode_eval s1 = true /\ is_mode_cont s2 = true.
Proof.
  induction 1; try solve [simpl; try lia; eauto].
Qed.

Lemma cred_lastn_stable s1 s2 n:
  List.length (stack s1) >= n ->
  List.length (stack s2) >= n ->
  cred s1 s2 ->
  lastn n (stack s1) = lastn n (stack s2).
Proof.
  intros Hs1 Hs2.
  induction 1;
    try solve [ idtac
      | unfold lastn; case n; simpl in *; eauto
      | simpl in *; repeat rewrite lastn_cons in *; eauto
    ].
Abort.

Lemma cred_lastn_stable s1 s2 n:
  List.length (stack s1) > n ->
  List.length (stack s2) > n ->
  cred s1 s2 ->
  lastn n (stack s1) = lastn n (stack s2).
Proof.
  intros Hs1 Hs2.
  induction 1; try solve [unfold lastn; case n; simpl in *; eauto];
    simpl in *; repeat rewrite lastn_cons in *; eauto; try lia.
Qed.

Lemma creds_lastn_stable_aux s1 s2 n:
  star (fun a b => cred a b /\ List.length (stack a) > n /\ List.length (stack b) > n) s1 s2 ->
  star (fun a b => cred a b /\ lastn n (stack a) = lastn n (stack b)) s1 s2.
Proof.
  induction 1; econstructor; unpack; eauto using cred_lastn_stable.
Qed.

Lemma creds_lastn_stable s1 s2 n:
  n <? List.length (stack s2) = true ->
  star (fun a b => cred a b /\ n <? List.length (stack a) = true) s1 s2 ->
  star (fun a b => cred a b /\ lastn n (stack a) = lastn n (stack b)) s1 s2.
Proof.
  intros.
  destruct creds_lastn_stable_aux with s1 s2 n; try solve [econstructor; eauto].
  match goal with |[h: star _ _ _ |- _ ] => induction h using star_ind_n1 end.
  unpack.
  { econstructor. }
  { eapply star_step_n1; unpack; repeat split; eauto; try lia. }
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
    [h: context [CDefault _ _ _ _ <> CDefault _ _ _ _] |- _ ] =>
    epose proof h _ _ _ _ as tmp; exfalso; apply tmp; eauto
    end.
Qed.

Theorem cred_stack_empty_irred:
  forall sigma v,
    irred cred (mode_cont [] sigma v)
.
Proof.
  repeat intro.
  inversion H.
Qed.

Theorem cred_stack_sub:
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
  all: induction kappa;
    try solve [
    repeat rewrite lastn_def_firstn in *; simpl in *; inj
    | repeat rewrite lastn_cons in * by (simpl; lia);
      remember (a::kappa) as kappa';
      repeat rewrite droplastn_cons by (subst; simpl; lia);
      try solve [econstructor; eauto|eapply lastn1_length1; eauto]
    ].
  { inj; exfalso; eapply fuck_stdlib; eauto. }
Qed.

Theorem creds_stack_sub:
  forall s1 s2 k,
    lastn 1 (stack s1) = [k] ->
    star (fun s1 s2 => cred s1 s2 /\ lastn 1 (stack s1) = lastn 1 (stack s2))
      s1 s2
    ->
      star cred
        (with_stack s1 (droplastn 1 (stack s1)))
        (with_stack s2 (droplastn 1 (stack s2))).
Proof.
  intros s1 s2 k Hk.
  induction 1; unpack; econstructor.
  { eapply cred_stack_sub; eauto. }
  { eapply IHstar.
    rewrite Hk in *; eauto.
  }
Qed.

Theorem cred_stack_:
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

Theorem cred_stack_drop:
  forall t k env env' env'' r' r'',
    star cred
      (mode_eval t [k] env)
      (mode_cont [] env' r')
    ->
    star cred
      (mode_eval t [] env)
      (mode_cont [] env'' r'').
Proof.
Abort.


End CRED_PROPERTIES.


(* Decreasing measure *)

Hypothesis measure: state -> nat.
Hypothesis measure_decrease: forall s1 s2, cred s1 s2 -> measure s2 < measure s1.

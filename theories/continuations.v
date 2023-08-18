Require Import syntax.
Require Import Sorting.Permutation.
Import List.ListNotations.
Open Scope list_scope.
Require Import sequences common.
Require Import Coq.Arith.Arith.
Require Import Bool.


(* Proof automation. ZifyBool is needed for operators such as [_ <=? _] *)
Require Import Lia ZifyBool.

From Catala Require Import tactics.


(* Definition of continuaton semantics for the catala programming language. *)

Inductive result :=
  | RValue (v: value)
  | REmpty
  | RConflict
.

Inductive cont :=
  (* | CAppL (t1: term) (* [t1 \square] *) *) (* cannot happend*)
  | CAppR (t2: term) (* [\square t2] *)
  | CBinopL (op: op) (v1: value) (* [op t1 \square] *)
  | CBinopR (op: op) (t2: term) (* [op \square t2] *)
  | CClosure (t_cl: {bind term}) (sigma_cl: list value)
    (* [Clo(x, t_cl, sigma_cl) \sigma] Since we are using De Bruijn indices, there is no variable x. *)
  | CReturn (sigma: list value) (* call return *)
  | CDefault (o: option value) (ts: list term) (tj: term) (tc: term)
    (* [Def(o, ts, tj, tc)] *)
  | CDefaultBase (tc: term)
    (* [ <| \square :- tc >] *)
  
  | CMatch (t1 t2: term)
    (* [ match \square with None -> t1 | Some -> t2 end ] *)
  | CSome
.

Inductive state :=
  | mode_eval (e: term) (stack: list cont) (env: list value)
  | mode_cont (stack: list cont) (env: list value) (result: result)
.

Inductive cred: state -> state -> Prop :=
  | cred_var:
    (* $\leval \synvar x, \kappa, \sigma \reval \leadsto \lcont\kappa, \sigma, \sigma(x) \rcont$ *)

    forall x kappa sigma v,
    List.nth_error sigma x = Some v ->
    cred
      (mode_eval (Var x) kappa sigma)
      (mode_cont kappa sigma (RValue v))

  | cred_app:
    (* $\leval e_1\ e_2, \kappa, \sigma \reval \leadsto \leval e_1, (\square\ e_2) \cons \kappa, \sigma \reval $ *)
    forall t1 t2 kappa sigma,
    cred
      (mode_eval (App t1 t2) kappa sigma)
      (mode_eval t1 ((CAppR t2) :: kappa) sigma)
  
  | cred_clo:
    (* $\leval \lambda x. t, \kappa, \sigma \reval \leadsto \lcont\kappa, \sigma, Clo (x, t, \sigma) \rcont$ *)
    forall t kappa sigma,
    cred
      (mode_eval (Lam t) kappa sigma)
      (mode_cont kappa sigma (RValue (Closure t sigma)))

  | cred_arg:
    (* $\lcont (\square\ e_2) \cons \kappa, \sigma, Clo (x, t_{cl}, \sigma_{cl}) \rcont \leadsto \leval e_2, (Clo(x, t_{cl}, \sigma_{cl})\ \square) \cons \kappa, \sigma \reval$ *)
    forall t2 kappa sigma tcl sigmacl,
    cred
      (mode_cont ((CAppR t2)::kappa) sigma (RValue (Closure tcl sigmacl)))
      (mode_eval t2 ((CClosure tcl sigmacl)::kappa) sigma)

  | cred_beta:
    (* $\lcont(Clo(x, t_{cl}, \sigma_{cl})\ \square) \cons \kappa, \sigma, v \rcont \leadsto \leval t_{cl}, \kappa, (x\mapsto v) \cons\sigma_{cl} \reval$ *)
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
    (* $\leval \synlangle es \synmid e_j \synjust e_c \synrangle, \kappa, \sigma \reval \leadsto \lcont (\mathtt{Def}(\synnone, es, e_j, e_c)) \cons \kappa, \sigma, \synempty \rcont$ *)
    forall ts tj tc kappa sigma,
    cred
      (mode_eval (Default ts tj tc) kappa sigma)
      (mode_cont ((CDefault None ts tj tc)::kappa) sigma REmpty)

  | cred_defaultunpack:
    (* $\lcont \mathtt{Def}(o, e_h \cons es, e_j, e_c) \cons \kappa, \sigma, \synempty \rcont \leadsto \leval e_h, \mathtt{Def}(o, es, e_j, e_c) \cons \kappa, \sigma \reval$ *)
    forall o th ts tj tc kappa sigma,
    cred
      (mode_cont ((CDefault o (th::ts) tj tc)::kappa) sigma REmpty)
      (mode_eval th ((CDefault o ts tj tc)::kappa) sigma)

  | cred_defaultnone:
    (* $\lcont \mathtt{Def}(\synnone, e_h \cons es, e_j, e_c) \cons \kappa, \sigma, v \rcont \leadsto \leval e_h, \mathtt{Def}(\synsome(v), es, e_j, e_c) \cons \kappa, \sigma \reval$ *)
    forall ts tj tc kappa sigma v,
    cred
      (mode_cont ((CDefault None ts tj tc)::kappa) sigma (RValue v))
      (mode_cont ((CDefault (Some v) ts tj tc)::kappa) sigma REmpty)

  | cred_defaultconflict:
    (* $\lcont \mathtt{Def}(\synsome(v), es, e_j, e_c) \cons \kappa, \sigma, v' \rcont \leadsto \lcont \mathtt{Def}(\synsome(v), es, e_j, e_c)  \cons \kappa, \sigma, \synconflict \rcont$ *)
    forall ts tj tc kappa sigma v v',
    cred
      (mode_cont ((CDefault (Some v) ts tj tc)::kappa) sigma (RValue v'))
      (mode_cont kappa sigma RConflict)

  | cred_defaultvalue:
    (* $\lcont \mathtt{Def}(\synsome(v), [], e_j, e_c) \cons \kappa, \sigma, \synempty \rcont \leadsto \lcont \kappa, \sigma, v \rcont$ *)
    forall v tj tc kappa sigma,
    cred
      (mode_cont ((CDefault (Some v) [] tj tc)::kappa) sigma REmpty)
      (mode_cont kappa sigma (RValue v))

  (* | cred_defaultnonefinal: (* not needed *)
    (* $\lcont \mathtt{Def}(\synnone, [], e_j, e_c) \cons \kappa, \sigma, v \rcont \leadsto \lcont \kappa, \sigma, v \rcont$ \hfill $v \neq \synempty, \synconflict$ *)
    todo *)

  | cred_defaultbase:
    (* $\lcont \mathtt{Def}(\synnone, [], e_j, e_c) \cons \kappa, \sigma, \synempty \rcont \leadsto \leval e_j, \synlanglemid \square \synjust e_c \synrangle \cons \kappa, \sigma \reval$ *)
    forall tj tc kappa sigma,
    cred
      (mode_cont ((CDefault None [] tj tc)::kappa) sigma REmpty)
      (mode_eval tj ((CDefaultBase tc)::kappa) sigma)

  | cred_defaultbasetrue:
    (* $\lcont \synlanglemid \square \synjust e_c \synrangle \cons \kappa, \sigma, \syntrue \rcont \leadsto \leval e_c, \kappa, \sigma \reval$ *)
    forall tc kappa sigma,
    cred
      (mode_cont ((CDefaultBase tc)::kappa) sigma (RValue (Bool true)))
      (mode_eval tc kappa sigma)

  | cred_defaultbasefalse:
    (* $\lcont \synlanglemid \square \synjust e_c \synrangle \cons \kappa, \sigma, \synfalse \rcont \leadsto \lcont \kappa, \sigma, \synempty \rcont$ *)
    forall tc kappa sigma,
    cred
      (mode_cont ((CDefaultBase tc)::kappa) sigma (RValue (Bool false)))
      (mode_cont kappa sigma REmpty)

  | cred_empty:
    (* $\lcont \phi \cons \kappa, \sigma, \synempty \rcont \leadsto \lcont \kappa, \sigma, \synempty \rcont$ \hfill $\forall o\ es\ e_j\ e_c,\ \phi \neq \mathtt{Def}(o, es, e_j, ec)$ *)
    forall phi kappa sigma,
    (forall o ts tj tc, phi <> CDefault o ts tj tc) ->
    (forall sigma', phi <> CReturn sigma') ->
    cred
      (mode_cont (phi::kappa) sigma REmpty)
      (mode_cont kappa sigma REmpty)

  | cred_conflict:
    (* $\lcont \phi \cons \kappa, \sigma, \synconflict \rcont \leadsto \lcont \kappa, \sigma, \synconflict \rcont$ *)
    forall phi kappa sigma,
    (forall sigma', phi <> CReturn sigma') ->
    cred
      (mode_cont (phi::kappa) sigma RConflict)
      (mode_cont kappa sigma RConflict)

  (* | cred_confict_intro:
    forall kappa sigma,
    cred
      (mode_eval Conflict kappa sigma)
      (mode_cont kappa sigma RConflict)

  | cred_empty_intro:
    forall kappa sigma,
    cred
      (mode_eval Empty kappa sigma)
      (mode_cont kappa sigma REmpty) *)

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
      (mode_cont ((CMatch t1 t2)::kappa) sigma (RValue (VSome (v))))
      (mode_eval t2 (CReturn sigma:: kappa) (v::sigma))
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

  Notation "'{' \synnone '}'" := None (in custom latex): latex.
  Notation "'{' '\synsome(' v ')' '}'" := (Some v) (in custom latex): latex.

  (* Terms *)
  Notation "'{' '\overline{\synvar{' x '}}' '}'" := (Var x) (in custom latex, x constr ): latex.
  Notation "'{' '\synvar{' x '}' '}'" := (FreeVar x) (in custom latex): latex.
  Notation "'{' t1  t2 '}'" := (App t1 t2) (in custom latex): latex.
  Notation "'{' ( '\synlambda.' t ) '}'" := (Lam t) (in custom latex): latex.
  Notation "'{' \synlet t2 \syn in t1 '}'" := (App (Lam t1) t2) (in custom latex): latex.

  Notation "'{' '\synlangle' ts '\synmid' tj '\synjust' tc '\synrangle' '}'" :=  (Default ts tj tc) (in custom latex): latex.
  Notation "'{' '\ghostvalue' v '}'" := (Value (v)) (in custom latex): latex.
  Notation "'{' t1 '\synpunct{' op '}' t2 '}'" := (Binop op t1 t2) (in custom latex): latex.


  (* Closures *)
  Notation "'{' '\square' '\synpunct{' op '}' e2 '}'" := (CBinopR op e2) (in custom latex): latex.
  Notation "'{' '\square' e2 '}'" := (CAppR e2) (in custom latex): latex.
  Notation "'{' v1 '\synpunct{' op '}' '\square' '}'" := (CBinopL op v1) (in custom latex): latex.
  Notation "'{' '\synCClo(' t_cl ','  sigma_cl ')' '}'" := (CClosure t_cl sigma_cl) (in custom latex): latex.
  Notation "'{' '\synDef(' o ',' ts ','  tj ','  tc ')' '}'" := (CDefault o ts tj tc) (in custom latex): latex.
  Notation "'{' '\synReturn(' sigma ')' '}'" := (CReturn sigma) (in custom latex): latex.
  Notation "'{' '\synlangle' '\square' '\synjust' tc '\synrangle' '}'" := (CDefaultBase tc) (in custom latex): latex.


  (* Runtime Values *)
  Notation "\syntrue" := true (in custom latex): latex.
  Notation "\synfalse" := false (in custom latex): latex.
  Notation "'{' \ghostbool b '}'" := (Bool b) (in custom latex): latex.
  Notation "'{' \ghostint i '}'" := (Int i) (in custom latex, i constr): latex.
  (* Notation "'{' '\synClo(' t ','  sigma ')' '}'" := (VClosure t sigma) (in custom latex): latex. *)
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
Qed.


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

Theorem append_stack_def s kappa:
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


(* Theorem cred_progress s:
  (exists s', cred s s') \/ stack s = [].
Proof.
  induction s.
  * induction e; try solve [left; eexists; econstructor].
    - admit alain "If a variable is not defined, then it might be an issue".
    - admit alain "todo: add an interpretation for free variables".
  * match goal with [v: list cont |- _] => induction v; try solve [left; eexists; econstructor|simpl; eauto] | _ => idtac end;
    match goal with [v: cont |- _] => induction v; try solve [left; eexists; econstructor|simpl; eauto] | _ => idtac end;
    match goal with [v: result |- _] => induction v; try solve [left; eexists; econstructor|simpl; eauto] | _ => idtac end;
    match goal with [v: option value |- _] => induction v; try solve [left; eexists; econstructor|simpl; eauto] | _ => idtac end;
    match goal with [v: list term |- _] => induction v; try solve [left; eexists; econstructor|simpl; eauto] | _ => idtac end;
    repeat match goal with [v: value |- _] => induction v; try solve [left; eexists; econstructor|simpl; eauto] | _ => idtac end;
    match goal with [v: bool |- _] => induction v; try solve [left; eexists; econstructor|simpl; eauto] | _ => idtac end;
    match goal with [v: op |- _] => induction v; try solve [left; eexists; econstructor|simpl; eauto] | _ => idtac end.
    all: try solve[left; eexists; econstructor; repeat intro; discriminate].
    all: match goal with [ |- context[CBinopL] ] => left; eexists; econstructor; try solve [simpl; eauto]; admit alain "typing error on the operator"| _ => idtac end.
    - admit alain "typing error on the function application.".
    - admit alain "typing error on the function application.".
    - admit alain "typing error on the function application.".
    - admit alain "typing error on the justification".
    - admit alain "typing error on the justification".
Abort. *)

Theorem cred_deterministic (s s1' s2': state):
  cred s s1' -> cred s s2' -> s1' = s2'.
Proof.
  induction 1; inversion 1; subst; eauto.
  (* All the cases are quite the same: we know the top of the stack is not an Default, but the top of the stack is a default. Hence there is a contradiction. *)
  * rewrite H in H5; inj; eauto.
  * now pose proof H6 sigma.
  * now pose proof H5 sigma.
  * specialize H4 with o (th::ts) tj tc. destruct H4. eauto.
  * specialize H4 with (Some v) ([]) tj tc. destruct H4. eauto.
  * specialize H4 with None [] tj tc. destruct H4. eauto.
  * now pose proof H0 sigma0.
  * specialize H with o (th::ts) tj tc. destruct H. eauto.
  * specialize H with (Some v) ([]) tj tc. destruct H. eauto.
  * specialize H with None [] tj tc. destruct H. eauto.
  * now pose proof H sigma0.
  * rewrite <- H in H7.
    injection H7; intros; subst; eauto.
Qed.

Theorem cred_stack_empty_irred:
  forall sigma v,
    irred cred (mode_cont [] sigma v)
.
Proof.
  repeat intro.
  inversion H.
Qed.


End CRED_PROPERTIES.

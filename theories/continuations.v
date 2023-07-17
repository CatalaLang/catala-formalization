Require Import syntax.
Require Import Sorting.Permutation.
Import List.ListNotations.
Open Scope list_scope.
Require Import sequences.
Require Import Lia.

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
  | CClosure (t_cl: {bind term}) (sigma_cl: var -> value)
    (* [Clo(x, t_cl, sigma_cl) \sigma] Since we are using De Bruijn indices, there is no variable x. *)
  | CDefault (o: option value) (ts: list term) (tj: term) (tc: term)
    (* [Def(o, ts, tj, tc)] *)
  | CDefaultBase (tc: term)
    (* [ <| \square :- tc >] *)
.

Inductive state :=
  | mode_eval (e: term) (stack: list cont) (env: var -> value)
  | mode_cont (stack: list cont) (env: var -> value) (result: result)
.

Inductive cred: state -> state -> Prop :=
  | cred_var:
    (* $\leval \synvar x, \kappa, \sigma \reval \leadsto \lcont\kappa, \sigma, \sigma(x) \rcont$ *)

    forall x kappa sigma,
    cred
      (mode_eval (Var x) kappa sigma)
      (mode_cont kappa sigma (RValue (sigma x)))

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
    forall tcl sigmacl kappa sigma v, 
    cred
      (mode_cont ((CClosure tcl sigmacl)::kappa) sigma (RValue v))
      (mode_eval tcl kappa  (v .: sigmacl))


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
    cred
      (mode_cont (phi::kappa) sigma REmpty)
      (mode_cont kappa sigma REmpty)

  | cred_conflict:
    (* $\lcont \phi \cons \kappa, \sigma, \synconflict \rcont \leadsto \lcont \kappa, \sigma, \synconflict \rcont$ *)
    forall phi kappa sigma,
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
.



Tactic Notation "admit" := admit.
Tactic Notation "admit" string(x) := admit.

Section CRED_PROPERTIES.

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

Theorem cred_progress s:
  (exists s', cred s s') \/ stack s = [].
Proof.
  induction s.
  * induction e; try solve [left; eexists; econstructor].
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
    all: match goal with [ |- context[CBinopL] ] => left; eexists; econstructor; try solve [simpl; eauto]; admit "typing error on the operator"| _ => idtac end.
    - admit alain "typing error on the function application.".
    - admit alain "typing error on the function application.".
    - admit alain "typing error on the function application.".
    - admit alain "typing error on the justification".
    - admit alain "typing error on the justification".
Admitted.

Theorem cred_deterministic (s s1' s2': state):
  cred s s1' -> cred s s2' -> s1' = s2'.
Proof.
  induction 1; inversion 1; subst; eauto.
  (* All the cases are quite the same: we know the top of the stack is not an Default, but the top of the stack is a default. Hence there is a contradiction. *)
  * specialize H4 with o (th::ts) tj tc. destruct H4. eauto.
  * specialize H4 with (Some v) ([]) tj tc. destruct H4. eauto.
  * specialize H4 with None [] tj tc. destruct H4. eauto.
  * specialize H with o (th::ts) tj tc. destruct H. eauto.
  * specialize H with (Some v) ([]) tj tc. destruct H. eauto.
  * specialize H with None [] tj tc. destruct H. eauto.
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




Theorem cred_star_deterministic s1 s2 s2':
  star cred s1 s2 ->
  star cred s1 s2' ->
  irred cred s2 ->
  irred cred s2' ->
  s2 = s2'.
Proof.
  intros; eapply finseq_unique; eauto using cred_deterministic.
Qed.


Theorem cred_star_deterministic_contempty s sigma v :
  star cred s (mode_cont [] sigma v) ->
  forall sigma' v', star cred s (mode_cont [] sigma' v') ->
  sigma = sigma' /\ v = v'.
Proof.
  intros.
  assert (mode_cont [] sigma v = (mode_cont [] sigma' v')).
  { eapply cred_star_deterministic; eauto using cred_stack_empty_irred. }
  match goal with [h: mode_cont _ _ _ = mode_cont _ _ _ |- _] =>
  injection h end; eauto.
Qed.


Definition append_stack s kappa2 :=
  match s with
  | mode_eval t kappa1 sigma =>
    mode_eval t (kappa1++kappa2) sigma
  | mode_cont kappa1 sigma v =>
    mode_cont (kappa1++kappa2) sigma v
  end
.

(* Properties of append_stack *)

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

Lemma append_stack_inv:
  forall s1 s2 kappa2,
  s1 = append_stack s2 (kappa2) ->
  exists kappa1, stack s1 = kappa1 ++ kappa2.
Proof.
  induction s1; induction s2; simpl; intros.
  all: try solve [injection H; intros; subst; eexists; eauto ].
  all: try solve [discriminate].
Qed.


Search "skipn" "length". 

Definition lastn {A} n (l: list A) := List.skipn ((List.length l) - n) l.

Lemma lastn_length {A} n:
  forall l: list A, List.length (lastn n l) = min n (List.length l).
Proof.
  unfold lastn.
  setoid_rewrite List.skipn_length; lia.
Qed.

Lemma lastn_cons {A} n:
  forall a (l: list A), length l >= n -> lastn n (a::l) = lastn n l.
Proof.
  unfold lastn.
  intros.
  simpl length.
  replace (S (length l) - n) with (S (length l - n)); eauto.
  lia.
Qed.


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

Lemma fuck_stdlib {A} (x: A) l :
  l <> x :: l.
Proof.
  induction l; intro; inj; contradiction.
Qed.


Lemma cred_stack_inv s1 s2:
  stack s1 = stack s2 ->
  cred s1 s2 ->
  cred (with_stack s1 []) (with_stack s2 []).
Proof.
  intros Heq. induction 1; simpl in *; inj;
  try solve
    [econstructor
    |exfalso; eapply fuck_stdlib; eauto
  ].
Qed.




Open Scope nat.

Require Import Lia.

From Catala Require Import tactics.

Lemma cred_stack_descreasing_mode_cont:
  forall s1 s2,
  cred s1 s2 ->
  Nat.ltb (List.length (stack s2)) (List.length (stack s1)) = true ->
  exists kappa sigma v,
  s1 = mode_cont kappa sigma v
  .
Proof.
  induction 1; simpl; eauto.
  all: admit alain "All cases are trivially true by computation".
Admitted.

Lemma cred_stack_descreasing_mode_cont_0:
  forall s1 s2 k,
  cred s1 s2 ->
  stack s1 = [k] ->
  stack s2 = [] ->
  exists sigma v,
  s1 = mode_cont [k] sigma v.
Proof.
  induction 1; simpl; intros; subst; inj; eauto.
Qed.

Open Scope nat_scope.

Search List.length.

Lemma general_inversion_lemma:
  forall t k_1 sigma_1 sigma_3 v_3,
  star cred
    (mode_eval t [k_1] sigma_1)
    (mode_cont [] sigma_3 v_3)
  ->
  exists sigma_2 v_2,
  star cred 
    (mode_eval t [] sigma_1)
    (mode_cont [] sigma_2 v_2).
Proof.
  intros ? ? ? ? ? Hstar13.
  destruct (takewhile (fun s => Nat.ltb 0 (List.length (stack s)) ) Hstar13)
  as [[H1 H2]|[s_2' [Hs2'a [Hs2'b Hs2'c]]]].
  - eauto.
  - simpl in *; exfalso; discriminate.
  - induction Hs2'a using star_ind_n1.
    * simpl in *; exfalso; discriminate.
    * rename y into s2, z into s2'.
      assert (Hassert: exists k_2 sigma_2 v_2, s2 = mode_cont [k_2] sigma_2 v_2).
      { admit "Since [List.length (stack s2') = 0] and [cred s2 s2'] ". }
      destruct Hassert as [k_2 [sigma_2 [v_2 Hs_2]]]; subst.

      admit "since [s1 ~> s2] and stack length is always greater than one, k1 = k2 and [cred (mode_eval t [] sigma_1) (mode_cont [] sigma_2 v_2)].".
Abort.    


Lemma inversion_lemma:
  forall x o l tj tc sigma v,
  star cred
    (mode_eval x [CDefault o l tj tc] sigma)
    (mode_cont [] sigma v)
  ->
  exists v',
  star cred
    (mode_eval x [CDefault o l tj tc] sigma)
    (mode_cont [CDefault o l tj tc] sigma v').
Proof.
Abort.


Lemma thing1:
  forall o x l tj tc sigma v,
  star cred
    (mode_cont ((CDefault o (x :: l) tj tc)::[]) sigma REmpty)
    (mode_cont [] sigma v)
  ->
  star cred
    (mode_cont ((CDefault o l tj tc)::[]) sigma REmpty)
    (mode_eval (Default l tj tc) [] sigma).
Proof.
  intros.
  inversion H; subst.
  inversion H0; subst.
  econstructor.
  { admit "wip". } 
  do 2 econstructor.
  { econstructor.
    admit "wip".
    admit "wip". }
Abort.

Notation "'{\leval'  t ,  kappa ,  sigma  '\reval}'" := (mode_eval t kappa sigma).
Notation "'{\lcont'  kappa ,  sigma ,  v  '\rcont}'" := (mode_cont kappa sigma v).
Notation "'{' s1  '\leadsto^*' s2 '}'" := (star cred s1 s2).

Lemma technical3:
  forall x k s1 s3 v3,
    star cred (mode_eval x [k] s1) (mode_cont [] s3 v3) ->
    exists v2 s2,
      star cred (mode_eval x [] s1) (mode_cont [] s2 v2).
Proof.
  intros.
  (* *)
  inversion H; subst.

  induction H0; inversion H; subst; inversion H0.  


(* semantics does no changes when permuting the differents exceptions *)

Theorem default_permut_stable ts1 ts2 tj tc sigma sigma1 sigma2 v1 v2:
  Permutation ts1 ts2 ->
  star cred 
    (mode_eval (Default ts1 tj tc) [] sigma)
    (mode_cont [] sigma1 v1)
  ->
  star cred 
    (mode_eval (Default ts2 tj tc) [] sigma)
    (mode_cont [] sigma2 v2)
  ->
  (* The more general [irred cred s1 /\ irred cred s2] does not holds: indeed, in the swap case [Default (t1::t2::ts) tj tc] the terms [t1] and [t2] could be stuck for differents reasons. *)
  (mode_cont [] sigma1 v1) = (mode_cont [] sigma2 v2).
Proof.
  induction 1.
  * intros.
    eapply finseq_unique; eauto using cred_deterministic, cred_stack_empty_irred.
  * intros.
    eapply IHPermutation; eauto.
    - inversion H0; subst.
      inversion H2; subst.
      inversion H3; subst.
      inversion H4; subst.
       { econstructor. }

      admit "computation using previous lemmas".
    - admit "same computation".
  * admit "
    we only need to unrool [mode_eval x [] sigma] and [mode_eval y [] sigma]

    Then there is 3*3 distinct cases: [x] can returns REmpty, RConflict or RValue, same for [y]. wlog, we can suppose x <= y for a any order on return. We can now consider all the cases:

    * RConflict, _ -> we return Rconflict in both cases.
    * REmpty, REmpty -> we can use finseq_unique to after the computation of both [x] and [y]
    * RValue, REmpty -> we can use finseq_unique to after the computation of both [x] and [y]
    * RValue, RValue -> we can use finseq_unique to after the computation of both [x] and [y]

    /!\ It is not possible to add an other kind of error and have this theorem: conflict and empty must be the only one. Else, the following terms are counter example: [Default [Error1; Error2] false false] [Default [Error2; Error1] false false].
    
  ".
Abort.

Require Import syntax.
Require Import Sorting.Permutation.
Import List.ListNotations.
Open Scope list_scope.
Require Import sequences.
Require Import Lia.


(* Definition of continuaton semantics for the catala programming language. *)

Inductive result :=
  | RValue (v: value)
  | REmpty
  | RConflict
.

Inductive cont :=
  (* | CAppL (t1: term) (* [t1 \square] *) *) (* cannot happend*)
  | CAppR (t2: term) (* [\square t2] *)
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
  
  | cred_value_intr:
    forall v kappa sigma,
    cred
      (mode_eval (Value v) kappa sigma)
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

Theorem cred_progress s:
  (exists s', cred s s') \/ stack s = [].
Proof.
  induction s.
  * induction e; try solve [left; eexists; econstructor].
    - admit "todo: add an interpretation for free variables".
    - admit "todo: add an interpretation of binary operators".
  * match goal with [v: list cont |- _] => induction v; try solve [left; eexists; econstructor|simpl; eauto] | _ => idtac end;
    match goal with [v: cont |- _] => induction v; try solve [left; eexists; econstructor|simpl; eauto] | _ => idtac end;
    match goal with [v: result |- _] => induction v; try solve [left; eexists; econstructor|simpl; eauto] | _ => idtac end;
    match goal with [v: value |- _] => induction v; try solve [left; eexists; econstructor|simpl; eauto] | _ => idtac end;
    match goal with [v: option value |- _] => induction v; try solve [left; eexists; econstructor|simpl; eauto] | _ => idtac end;
    match goal with [v: list term |- _] => induction v; try solve [left; eexists; econstructor|simpl; eauto] | _ => idtac end;
    match goal with [v: bool |- _] => induction v; try solve [left; eexists; econstructor|simpl; eauto] | _ => idtac end.
    all: try solve[left; eexists; econstructor; repeat intro; discriminate].
    - admit "typing error on the function application.".
    - admit "typing error on the function application.".
    - admit "typing error on the function application.".
    - admit "typing error on the justification".
    - admit "typing error on the justification".
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

(* conversly, if we have a transition *)
Theorem bottom_stack_unmodified_cred s1 s2 kappa:
  cred (append_stack s1 kappa) s2 ->
  List.length (stack (append_stack s1 kappa)) >= List.length kappa ->
  exists s2', s2 = append_stack s2' kappa.
Proof.
  remember (append_stack s1 kappa) as s1'.
  induction 1; subst; simpl; intros Hlen; match goal with [h: (_ = append_stack _ _) |- _] => pose proof append_stack_inv _ _ _ h as [kappa']; simpl in *; subst end.
  all: try match goal with [ |- context [_ ++ _]] => admit end.
Qed.

Theorem bottom_stack_unmodified s1 s2 kappa p:
  star
    (fun a b => cred a b /\ p a)
    s1 s2
  -> 
  exists s1', s1 = append_stack s1' kappa ->
  exists s2', s1 = append_stack s2' kappa.
Proof.
  induction 1 as [|a b c [Hred Hp] Hstar IHstar].
  * eauto.
  * induction H.


Open Scope nat.

Require Import Lia.

From Catala Require Import tactics.

Lemma technical_lemma:
  forall s1 s2,
  cred s1 s2 ->
  Nat.ltb (stack_length s2) (stack_length s1) = true ->
  exists kappa sigma v,
  s1 = mode_cont kappa sigma v
  .
Proof.
  induction 1; simpl; eauto.
  all: admit alain "All cases are trivially true by computation".
Admitted.

Open Scope nat_scope.

Lemma general_inversion_lemma:
  forall x k sigma v',
  star cred
    (mode_eval x [k] sigma)
    (mode_cont [] sigma v')
  ->
  exists v,
  star cred 
    (mode_eval x [k] sigma)
    (mode_cont [] sigma v).
Proof.
  intros.
  destruct (takewhile (fun s => Nat.ltb 0  (stack_length s) ) H).
  - eauto.
  - destruct H0.
    simpl in H1.
    exfalso; discriminate.
  - destruct H0 as [s [Hs1 [Hs2 Hs3]]].
    induction Hs1 using star_ind_n1.
    * eauto.
    *  
      (* I know cred y z and stack_length y > stack_length z and stack_elngth z = 0. Hence y = mode_cont [k'] sigma v.*)
    induction .


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
  { eapply cred_defaultunpack. } 
  do 2 econstructor.
  { econstructor. }
  - 
  eapply star_step.




(* semantics does no changes when permuting the differents exceptions *)

Theorem default_permut_stable ts1 ts2 tj tc sigma s1 s2:
  Permutation ts1 ts2 ->
  star cred 
    (mode_eval (Default ts1 tj tc) [] sigma)
    s1
  ->
  star cred 
    (mode_eval (Default ts2 tj tc) [] sigma)
    s2
  ->
  irred cred s1 ->
  irred cred s2 ->
  s1 = s2.
Proof.
  induction 1.
  * intros.
    eapply finseq_unique; eauto using cred_deterministic.
  * intros.
    eapply IHPermutation; eauto.
    - 

Qed.

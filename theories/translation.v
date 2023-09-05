Require Import syntax.

Inductive pure := Pure | Impure.

Notation monad_bind t1 t2 := (Match_ t1 ENone t2).


Fixpoint monad_handle_one (ts: list term) : term :=
  match ts with
  | nil => ESome (Var 0)
  | cons thead ttail =>
    Match_ (lift 1 thead)
      (monad_handle_one ttail)
      (Conflict)
  end.

Fixpoint monad_handle_zero ts tj tc: term :=
  match ts with
  | nil => monad_bind tj (App (App (App (Var 0) (Var 0)) (lift 1 tc)) ENone)
  | cons thead ttail =>
    Match_ thead
      (monad_handle_zero ttail tj tc)
      (monad_handle_one ttail)
  end.



Definition monad_handle ts tj tc: term :=
  monad_handle_zero ts tj tc
.

Fixpoint trans (Delta: list pure) t { struct t } :=
  match t with
  | Var x =>
    match List.nth_error Delta x with
    | Some Impure => ESome (Var x)
    | Some Pure => Var x
    | None => Conflict
    end
  | Lam t =>
    ESome (Lam (trans (Pure :: Delta) t))
  | App (Lam body) arg => (* let arg in body *)
    monad_bind (trans Delta arg) (trans (Pure :: Delta) body)
  (* | D.App () =>
    MBind (trans Delta arg) (ESome (L.EOp op) ) *)
  | App (Var f) arg =>
    match List.nth_error Delta f with
    | Some b =>
      if b then
        (monad_bind (trans Delta arg)
          (App (lift 1 (Var f)) (Var 0))
        )
      else
        (monad_bind (Var f)
          (monad_bind (lift 1 (trans Delta arg))
            (App (lift 1 (Var 0)) (Var 0))
          )
        )
    | None => Conflict
    end
  | Binop op e1 e2 =>
    monad_bind (trans Delta e1)
      (monad_bind (trans Delta e2)
        (Binop op (Var 1) (Var 0))
      )

  (* | D.App f arg =>
    monad_bind (trans Delta f) (monad_bind (lift 1 (trans Delta arg)) (L.App (lift 1 (L.Var 0)) (L.Var 0))) *)
  | Default es ej ec =>
    monad_handle
      (List.map (trans Delta) es)
      (trans Delta ej)
      (trans Delta ec)
  | Value v =>
    ESome (Value v)
  | Empty =>
    ENone
  (* incompatible *)
  | Conflict => Conflict
  | FreeVar _ => Conflict
  | App _ _ => Conflict
  | Match_ _ _ _ => Conflict
  | ENone => Conflict
  | ESome _ => Conflict
  (* | D.BinOp op t1 t2 => L..ECompile*)
  end.

Require Import continuations.


Definition subst_of_env sigma :=
  fun n =>
  match List.nth_error sigma n with
  | None => ids n
  | Some t => Value t
  end
.
Search (?x = S ?x).

Require Import tactics.
Require Import sequences typing.

Theorem correction_continuations:
  forall s1 s2,
  (exists GGamma Gamma T, jt_state GGamma Gamma s1 T) ->
  cred s1 s2 ->
  forall Delta,
  exists target,
    star cred
      (mode_eval (trans Delta (apply_state s1)) nil nil) target /\
    star cred
      (mode_eval (trans Delta (apply_state s2)) nil nil) target.
Proof.
  intros s1 s2 [GGamma [Gamma [T Htyped]]] Hcred.
  pose proof (cred_stack_lenght_at_most_one_precise _ _ Hcred);
  simpl in *;
  repeat match goal with
    | [h: _ \/ _ |- _] => destruct h
    | [h: False |- _] => destruct h
    | [h: _ /\ _ |- _] => destruct h
  end.
  { induction Hcred; try solve [simpl in *; tryfalse (eapply n_Sn; eauto)].
    6:{
      induction kappa.
      { simpl in *.
        eexists; split.
        { eapply star_step. econstructor.
          eapply star_step. econstructor.
          eapply star_step. econstructor.
          eapply star_step. econstructor.
          eapply star_step. econstructor.
          eapply star_step. econstructor.
          edestruct (typing.correct (mode_eval (trans Delta e2.[subst_of_env sigma]) nil (v :: nil))). { admit alain. }
          eapply star_trans.
          { rewrite append_stack_all_eval.
            rewrite append_env_all_eval.
            eapply append_stack_stable_star.
            unpack. eauto.
          }
          unpack.
          induction x; simpl in *; subst; try congruence; simpl.
          assert (exists Delta Gamma T, jt_state Delta Gamma (mode_cont nil env result) (TOption T)). { admit alain. }
          unpack.
          induction result; repeat inv_jt.
          { eapply star_step. econstructor.
            eapply star_step. econstructor.
            eapply star_step. econstructor.
            eapply star_refl.
          }
          { eapply star_step. econstructor.
            eapply star_step. econstructor.
            eapply star_step.
            eapply star_refl.
          }

            eapply H2.
            eapply 


      simpl monad_bind.


      simpl.

    }
    all: admit alain.
  }
  { induction Hcred; simpl in *; tryfalse (eapply n_Sn; eauto).
    all: admit alain.
  }
  { induction Hcred; simpl in *; tryfalse (eapply n_Sn; eauto).
    all: admit alain.
  }
  { induction Hcred; simpl in *; tryfalse (eapply n_Sn; eauto).
    all: admit alain.
  }
Admitted.
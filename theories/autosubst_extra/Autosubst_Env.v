Require Import List.
Require Import MyTactics. (* TEMPORARY *)
Require Import Autosubst.Autosubst.
Require Import Autosubst_EOS. (* [eos_var] *)

(* Environments are sometimes represented as finite lists. This file
   provides a few notions that helps deal with this representation. *)

Section Env.

Context {A} `{Ids A, Rename A, Subst A, SubstLemmas A}.

(* -------------------------------------------------------------------------- *)

(* The function [env2subst default], where [default] is a default value,
   converts an environment (a finite list) to a substitution (a total
   function). *)

Definition env2subst (default : A) (e : list A) (x : var) : A :=
  nth x e default.

(* -------------------------------------------------------------------------- *)

(* [env_ren_comp e xi e'] means (roughly) that the environment [e] is equal to
   the composition of the renaming [xi] and the environment [e'], that is,
   [e = xi >>> e']. We also explicitly require the environments [e] and [e']
   to have matching lengths, up to [xi], as this is *not* a consequence of
   the other premise. *)

Inductive env_ren_comp : list A -> (var -> var) -> list A -> Prop :=
| EnvRenComp:
    forall e xi e',
    (forall x, x < length e -> xi x < length e') ->
    (forall x default, nth x e default = nth (xi x) e' default) ->
    env_ren_comp e xi e'.

(* A reformulation of the second premise in the above definition. *)

Lemma env_ren_comp_eq:
  forall e xi e',
  (forall default, env2subst default e = xi >>> env2subst default e') <->
  (forall x default, nth x e default = nth (xi x) e' default).
Proof.
  unfold env2subst. split; intros h; intros.
  { change (nth x e default) with ((fun x => nth x e default) x).
    rewrite h. reflexivity. }
  { f_ext; intro x. eauto. }
Qed.

(* -------------------------------------------------------------------------- *)

(* Initialization: [e = id >>> e]. *)

Lemma env_ren_comp_id:
  forall e,
  env_ren_comp e (fun x => x) e.
Proof.
  econstructor; eauto.
Qed.

(* -------------------------------------------------------------------------- *)

(* The relation [e = xi >>> e'] can be taken under a binder, as follows. *)

Lemma env_ren_comp_up:
  forall e xi e' v,
  env_ren_comp e xi e' ->
  env_ren_comp (v :: e) (upren xi) (v :: e').
Proof.
  inversion 1; intros; subst; econstructor;
  intros [|x]; intros; simpl in *; eauto with lia.
Qed.

(* -------------------------------------------------------------------------- *)

(* One element can be prepended to [e'], provided [xi] is adjusted. *)

Lemma env_ren_comp_prepend:
  forall e xi e' v,
  env_ren_comp e xi e' ->
  env_ren_comp e (xi >>> (+1)) (v :: e').
Proof.
  inversion 1; intros; subst.
  econstructor; intros; simpl; eauto with lia.
Qed.

(* -------------------------------------------------------------------------- *)

(* A consequence of [env_ren_comp_id] and [env_ren_comp_prepend]. The renaming
   (+1) will eat away the first entry in [v :: e]. *)

Lemma env_ren_comp_plus1:
  forall e v,
  env_ren_comp e (+1) (v :: e).
Proof.
  econstructor; intros; simpl; eauto with lia.
Qed.

(* -------------------------------------------------------------------------- *)

(* More generally, the renaming [eos_var x], which means that [x] goes out of
   scope, will eat away the entry at index [x] in [e1 ++ v :: e2]. *)

Lemma env_ren_comp_eos_var:
  forall x e1 v e2,
  x = length e1 ->
  env_ren_comp (e1 ++ e2) (eos_var x) (e1 ++ v :: e2).
Proof.
  rewrite eos_var_eq_lift_var. unfold lift_var.
  econstructor; intros y; dblib_by_cases.
  { rewrite app_length in *. simpl. lia. }
  { rewrite app_length in *. simpl. lia. }
  { do 2 (rewrite app_nth2 by lia).
    replace (1 + y - length e1) with (1 + (y - length e1)) by lia.
    reflexivity. }
  { do 2 (rewrite app_nth1 by lia).
    reflexivity. }
Qed.

(* -------------------------------------------------------------------------- *)

End Env.

Global Hint Resolve
  env_ren_comp_id
  env_ren_comp_up
  env_ren_comp_prepend
  env_ren_comp_plus1
  env_ren_comp_eos_var
: env_ren_comp.

(* 2022-06-08 *)

Require Import DCSyntax.
Require Import LCSyntax.

Require Import MyTactics.

Require Import DCReduction.
Require Import LCReduction.

Require Import MySequences.
Require Import Simulation.

Definition dterm := DCSyntax.term.
Definition lterm := LCSyntax.term.




(* map fragment *)
Hypothesis ctx: Type.



Inductive translate_and_hoist (ctx: ctx) :
  dterm -> lterm -> (nat -> dterm) -> Prop :=
  | THVar:
    forall x, ctx x.is_pure ->
      translate_and_hoist ctx (Var x) (Var x) 
    (Var x) (Var y) 
.



(* bind fragment *)
(* complex fragment *)


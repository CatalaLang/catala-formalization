Require dpdgraph.dpdgraph.


(* This file exists only to export the fine-grain dependency graph between lemmas, definitions and theorems. It makes it possible for dead-lemmas elimination from a set of results in the paper. *)

From Catala Require
  common
  continuations
  sequences
  syntax
  tactics
  trans
  typing
.

Set DependGraph File "catala.dpd".
Print FileDependGraph
  common
  continuations
  sequences
  syntax
  tactics
  trans
  typing
.

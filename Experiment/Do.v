From Semantics Require Import FunctionRepresentation EquateValues FindValue.
From CausalDiagrams Require Import Assignments Interventions.
From DAGs Require Import Basics.
From Utils Require Import Lists.
Import ListNotations.

Definition do_graphfun {X: Type} (a: node) (alpha: X) (g: graphfun): graphfun :=
  fun w => if (w =? a)
           then f_constant X alpha  (* ignore parents and unobs term *)
           else g w.


Definition semantic_do {X: Type} (a: node) (alpha: X)
  (G: graph) (g: graphfun) (u: node) (U: assignments X): option X :=
  find_value (do a G) (do_graphfun a alpha g) u U [].

Definition rct_graph (G:graph) (a r:node) (H: member r (nodes_in_graph G) = false) : graph :=
    match G with
    | (V,E) => (r::V, (r,a)::remove_edges_into a E)
    end.

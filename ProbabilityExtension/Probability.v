From DAGs Require Import Basics_Constr.
From CausalDiagrams Require Import Assignments.
From Stdlib Require Import Reals.

Import ListNotations.
Open Scope R_scope.

(* A finite space of values (simplified to nat) each node can take on *)
Definition node_domains : Type := node -> list nat.

(* A world is a complete assignment where each node gets a value from its domain *)
Definition world (dom : node_domains) (G : graph) : Type :=
  { A : assignments nat |
      is_exact_assignment_for A (nodes_in_graph G)
    /\ forall u val, In (u, val) A -> In val (dom u) }.

(* Enumerate all assignments where each node gets a value from its domain *)
Fixpoint enum_assignments (dom : node_domains) (V : nodes) : list (assignments nat) :=
  match V with
  | [] => [ [] ]
  | u :: rest =>
      flat_map (fun res_assignments => map (fun val => (u, val) :: res_assignments) (dom u))
               (enum_assignments dom rest)
  end.


Section Examples.
Local Open Scope nat_scope.

(* Example: graph 1->2->3, dom 1 = {0}, dom 2 = {0,1}, dom 3 = {0,1} *)
Definition G_ex : graph := ([1;2;3],[(1,2);(2,3)]).

Definition dom_ex : node_domains := fun n =>
  match n with
  | 1 => [0]
  | 2 => [0; 1]
  | 3 => [0; 1]
  | _ => []
  end.

Example enum_ex :
  enum_assignments dom_ex (nodes_in_graph G_ex) =
  [ [(1,0); (2,0); (3,0)];
    [(1,0); (2,1); (3,0)];
    [(1,0); (2,0); (3,1)];
    [(1,0); (2,1); (3,1)] ].
Proof. reflexivity. Qed.

End Examples.

(* Correctness: enum_assignments produces exactly the valid complete assignments *)
Theorem enum_assignments_correct (dom : node_domains) (G : graph) :
  forall A : assignments nat,
  In A (enum_assignments dom (nodes_in_graph G))
  <->
  is_exact_assignment_for A (nodes_in_graph G) /\ forall u val, In (u, val) A -> In val (dom u).
Proof. Admitted.

Fixpoint map_with_In {A B : Type} (l : list A) (f : forall a, In a l -> B) : list B :=
  match l as l' return (forall a, In a l' -> B) -> list B with
  | [] => fun _  => []
  | h :: t => fun f' =>
      f' h (in_eq h t) ::
      map_with_In t (fun a Ha => f' a (in_cons h a t Ha))
  end f.

Definition enum_worlds (dom : node_domains) (G : graph) : list (world dom G) :=
  let As := enum_assignments dom (nodes_in_graph G) in
  map_with_In As (fun A HA => exist _ A (proj1 (enum_assignments_correct dom G A) HA)).


Theorem enum_worlds_sound (dom : node_domains) (G : graph) :
  forall w, In w (enum_worlds dom G) <->
  is_exact_assignment_for (proj1_sig w) (nodes_in_graph G)
  /\ forall u val, In (u, val) (proj1_sig w) -> In val (dom u).
Proof.
    constructor.
    - intros. exact (proj2_sig w).
    - admit.
Admitted.

Definition Rsum (l : list R) : R := fold_right Rplus 0 l.

(* An event is a set of worlds, represented as a characteristic function *)
Definition event (dom : node_domains) (G : graph) : Type := world dom G -> bool.

(* Probability of an event: sum pmf over all worlds in the event *)
Definition prob_event {dom : node_domains} {G : graph}
    (P : (world dom G -> R)) (E : event dom G) : R :=
  Rsum (map P (filter E (enum_worlds dom G))).

(* A probability measure over worlds satisfying non-negativity, normalization, and additivity *)
Record prob_measure (dom : node_domains) (G : graph) : Type := mkProbMeasure {
  pmf :> world dom G -> R;
  pmf_nonneg     : forall w : world dom G, 0 <= pmf w;
  pmf_normalized : Rsum (map pmf (enum_worlds dom G)) = 1;
  pmf_additive   : forall (E1 E2 : event dom G),
    (forall w, E1 w = true -> E2 w = false) ->   (* E1 and E2 are disjoint *)
    prob_event pmf (fun w => E1 w || E2 w) =
    prob_event pmf E1 + prob_event pmf E2
}.

From DAGs Require Import Basics.
From DAGs Require Import CycleDetection.
Import ListNotations.

(*
"Universal Assumptions:
1. there's no measurement error
2. all exogenous variables are mutually independent
3. An experiment is measuring the treatment vector's effect on the reponse vector
4. Every node (including unmeasurable) has a declared finite domain;
    Unmeasurable restricts observation, not existence.
5. dag's are finite

"
*)



Inductive node_label : Type :=
  | Treatment
  | Response      (* sometimes a proxy *)
  | Unmeasurable  (* nodes that can't be measured *)
  | Unlabeled.    (* default label *)
(* the causal query in an experiment will be list Treatment -> list Response *)

Definition node_label_eqb (r1 r2 : node_label) : bool :=
  match r1, r2 with
  | Treatment,          Treatment          => true
  | Response,           Response           => true
  | Unmeasurable,       Unmeasurable       => true
  | Unlabeled,          Unlabeled          => true
  | _,                  _                  => false
  end.

Lemma node_label_eqb_refl : forall r, node_label_eqb r r = true.
Proof. intros []; reflexivity. Qed.

Lemma node_label_eqb_eq : forall r1 r2, node_label_eqb r1 r2 = true <-> r1 = r2.
Proof. intros [] []; simpl; split; intro H; try reflexivity; try discriminate; try congruence. Qed.

(* specify size of the node domain so that we can abstract it to be [n] *)
Definition node_card : Type := node -> nat.

(* The values of node n's domain, as a list: [0; ...; dom n - 1] *)
Definition node_dom (d : node_card) (n : node) : list nat := seq 0 (d n).


Record aug_graph : Type := mk_aug_graph {
  dag      : graph;
  label_of : node -> node_label;
  dom      : node_card;
}.

(* Example: x -> y and x <- z -> y, where x:Treatment, y:Response.
   Node ids: x = 1, y = 2, z = 3. z is an (unlabeled) confounder of x and y. *)
Definition G_3 : aug_graph :=
  mk_aug_graph
    ([1; 2; 3], [(1, 2); (3, 1); (3, 2)])
    (fun n => match n with
              | 1 => Treatment
              | 2 => Response
              | _ => Unlabeled
              end)
    (fun n => match n with
              | 1 => 2   (* x: values {0,1} = no treatment / treatment *)
              | 2 => 3   (* y: values {0,1,2} = three outcome levels *)
              | _ => 2   (* z (and any other node): binary *)
              end).

Definition nodes_with_label (ag : aug_graph) (r : node_label) : nodes :=
  filter (fun n => node_label_eqb (label_of ag n) r) (nodes_in_graph (dag ag)).

Definition treatment_nodes (ag : aug_graph) : nodes :=
  nodes_with_label ag Treatment.

Definition response_nodes (ag : aug_graph) : nodes :=
  nodes_with_label ag Response.

Definition is_unmeasurable (ag : aug_graph) (n : node) : bool :=
  node_label_eqb (label_of ag n) Unmeasurable.

Definition measurable_nodes (ag : aug_graph) : nodes :=
  filter (fun n => negb (is_unmeasurable ag n)) (nodes_in_graph (dag ag)).

(* a well-formed aug_graph contains >=1 treatment and response nodes,
   and every node in the graph has a nonempty value domain *)
Definition wf_aug_graph (ag : aug_graph) : Prop :=
  G_well_formed (dag ag) = true /\
  contains_cycle (dag ag) = false /\
  treatment_nodes ag <> [] /\
  response_nodes ag <> [] /\
  (forall n, node_in_graph n (dag ag) = true -> 0 < dom ag n).

Example wf_G_3 : wf_aug_graph G_3.
Proof.
  repeat split; try reflexivity; try discriminate.
  intros n _. destruct n as [| [| [| n']]]; apply Nat.lt_0_succ.
Qed.

Lemma wf_has_treatment : forall ag,
  wf_aug_graph ag ->
  exists t, In t (treatment_nodes ag).
Proof.
  intros ag [_ [_ [Hne _]]].
  destruct (treatment_nodes ag) as [| t rest] eqn:Heq.
  - contradiction.
  - exists t. left. reflexivity.
Qed.

Lemma wf_has_response : forall ag,
  wf_aug_graph ag ->
  exists r, In r (response_nodes ag).
Proof.
  intros ag [_ [_ [_ [Hne _]]]].
  destruct (response_nodes ag) as [| r rest] eqn:Heq.
  - contradiction.
  - exists r. left. reflexivity.
Qed.

(* Values are nat codes in 0 .. dom n - 1 (Universal Assumption 4). *)
Inductive operation : Type :=
  | Intervene (n : node) (v : nat)   (* do(n=v): set n to a specific value *)
  | Randomize (n : node) (r : node)  (* RCT: remove incoming edges to n, add fresh r → n *)
(*  | Control  (n : node) (v : nat)  *)
  | Measure   (n : node).            (* record n's current value into the log *)
  (* | Wait. *)

Definition program : Type := list operation.

Definition wf_operation (ag : aug_graph) (op : operation) : Prop :=
  match op with
  | Intervene n v =>
      node_in_graph n (dag ag) = true /\ v < dom ag n
  | Randomize n r =>
      node_in_graph n (dag ag) = true /\ node_in_graph r (dag ag) = false
  (* | Stratify n _ => node_in_graph n (dag ag) = true*)
  | Measure n =>
      node_in_graph n (dag ag) = true /\ label_of ag n <> Unmeasurable
  (* | Wait => True *)
  end.

Definition wf_program (ag : aug_graph) (prog : program) : Prop :=
  Forall (wf_operation ag) prog.

From DAGs Require Import Basics.
From DAGs Require Import CycleDetection.
Import ListNotations.


Inductive node_label : Type :=
  | Treatment
  | Response
  | Unmeasurable
  | Unlabeled.
(* the causal query in an experiment will be Treatment -> Response *)

Definition node_label_eqb (r1 r2 : node_label) : bool :=
  match r1, r2 with
  | Treatment,          Treatment          => true
  | Response,           Response           => true
  | Unmeasurable,         Unmeasurable         => true (* nodes that can't be measured *)
  | Unlabeled,          Unlabeled          => true
  | _,                  _                  => false
  end.

Lemma node_label_eqb_refl : forall r, node_label_eqb r r = true.
Proof. intros []; reflexivity. Qed.

Lemma node_label_eqb_eq : forall r1 r2, node_label_eqb r1 r2 = true <-> r1 = r2.
Proof. intros [] []; simpl; split; intro H; try reflexivity; try discriminate; try congruence. Qed.

(* An aug_graph pairs an underlying causal DAG with a total function assigning each node a role.
    Nodes not explicitly labeled by the researcher default to Unlabeled. *)
Record aug_graph : Type := mk_aug_graph {
  dag     : graph;
  label_of : node -> node_label;
}.

Definition nodes_with_label (ag : aug_graph) (r : node_label) : nodes :=
  filter (fun n => node_label_eqb (label_of ag n) r) (nodes_in_graph (dag ag)).

Definition treatment_node (ag : aug_graph) : option node :=
  match nodes_with_label ag Treatment with
  | [t] => Some t
  | _   => None
  end.

Definition response_node (ag : aug_graph) : option node :=
  match nodes_with_label ag Response with
  | [r] => Some r
  | _   => None
  end.

Definition is_unmeasurable (ag : aug_graph) (n : node) : bool :=
  node_label_eqb (label_of ag n) Unmeasurable.

Definition observed_nodes (ag : aug_graph) : nodes :=
  filter (fun n => negb (is_unmeasurable ag n)) (nodes_in_graph (dag ag)).

Definition wf_aug_graph (ag : aug_graph) : Prop :=
  G_well_formed (dag ag) = true /\
  contains_cycle (dag ag) = false /\
  length (nodes_with_label ag Treatment) = 1 /\
  length (nodes_with_label ag Response)  = 1 /\
  treatment_node ag <> response_node ag.
(* "what if treatment/response are a function of other nodes.
    should there be other node types, like proxy? or other edge types like definitional? " *)

Lemma wf_has_treatment : forall ag,
  wf_aug_graph ag ->
  exists t, treatment_node ag = Some t.
Proof.
  intros ag [_ [_ [Hlen _]]].
  unfold treatment_node.
  destruct (nodes_with_label ag Treatment) as [| t [| t' rest]] eqn:Heq.
  - simpl in Hlen. discriminate.
  - exists t. reflexivity.
  - simpl in Hlen. discriminate.
Qed.

Lemma wf_has_response : forall ag,
  wf_aug_graph ag ->
  exists r, response_node ag = Some r.
Proof.
  intros ag [_ [_ [_ [Hlen _]]]].
  unfold response_node.
  destruct (nodes_with_label ag Response) as [| r [| r' rest]] eqn:Heq.
  - simpl in Hlen. discriminate.
  - exists r. reflexivity.
  - simpl in Hlen. discriminate.
Qed.

Inductive operation (X : Type) : Type :=
  | Intervene (n : node) (v : X)   (* do(n=v): set n to a specific value *)
  | Randomize (n : node) (r : node)      (* RCT: remove incoming edges to n, add fresh r → n *)
(*  | Control  (n : node) (v : X)  *)
  | Measure   (n : node).            (* record n's current value into the log *)
  (* | Wait. *)

Arguments Intervene {X}.
Arguments Randomize {X}.
(* Arguments Stratify  {X}. *)
Arguments Measure   {X}.
(* Arguments Wait      {X}. *)

(* temporary name until I found a better name *)
Definition program (X : Type) : Type := list (operation X).

Definition wf_operation {X : Type} (ag : aug_graph) (op : operation X) : Prop :=
  match op with
  | Intervene n _ =>
      node_in_graph n (dag ag) = true
  | Randomize n r =>
      node_in_graph n (dag ag) = true /\
      node_in_graph r (dag ag) = false
  (* | Stratify n _ =>
      node_in_graph n (dag ag) = true*)
  | Measure n =>
      node_in_graph n (dag ag) = true /\
      label_of ag n <> Unmeasurable
  (* | Wait => True *)
  end.

Definition wf_program {X : Type} (ag : aug_graph) (prog : program X) : Prop :=
  Forall (wf_operation ag) prog.

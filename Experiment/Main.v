From DAGs Require Import Basics Descendants CycleDetection.
From Stdlib Require Import Lia Bool List.
From CausalDiagrams Require Import Assignments Interventions DSeparation.
From Semantics Require Import FunctionRepresentation FindValue EquateValues SemanticSeparationDef SemanticDSepEquiv.
From Utils Require Import Lists EqType List_Relations Logic.
Import ListNotations.

(*
"
Universal Assumptions:
1. there's no measurement error
2. all exogenous variables are mutually independent
3. An experiment is measuring the treatment vector's effect on the reponse vector
4. Every node (including unmeasurable) has a declared finite domain;
    Unmeasurable restricts observation, not existence.
    - this means we only deal with finite probability. no measure theory.
5. dag's are finite
6. (for now) population is finite
"
*)

(* ===================================================================== *)
(* Node labels                                                           *)
(* ===================================================================== *)

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

(* ===================================================================== *)
(* Augmented graph                                                       *)
(* ===================================================================== *)

(* The structural layer is value-free: it carries only the DAG and the labels
   needed to locate T / R / Unmeasurable.  Node domains ([node_card]) are
   value-space metadata and belong to the denotation -- [Prob.v] already takes
   [dom : node_card] as its own parameter -- so they are NOT a field here. *)
Record aug_graph : Type := mk_aug_graph {
  dag      : graph;
  label_of : node -> node_label;
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

(* a well-formed aug_graph is an acyclic, well-formed DAG with >=1 treatment and
   response node.  (The old "every node has a nonempty domain" clause moved out
   with [dom]: it is a value-space condition for the denotation layer.) *)
Definition wf_aug_graph (ag : aug_graph) : Prop :=
  G_well_formed (dag ag) = true /\
  contains_cycle (dag ag) = false /\
  treatment_nodes ag <> [] /\
  response_nodes ag <> [].

Example wf_G_3 : wf_aug_graph G_3.
Proof.
  repeat split; try reflexivity; try discriminate.
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
  intros ag [_ [_ [_ Hne]]].
  destruct (response_nodes ag) as [| r rest] eqn:Heq.
  - contradiction.
  - exists r. left. reflexivity.
Qed.

(* ===================================================================== *)
(* Operations and operationss                                               *)
(* ===================================================================== *)

(* Values are nat codes in 0 .. dom n - 1 (Universal Assumption 4); the range
   check [v < dom n] is a value-space condition and now lives with the
   denotation layer, not in the structural [wf_operation] below. *)
Inductive operation : Type :=
  | Intervene (n : node) (v : nat)   (* do(n=v): set n to a specific value *)
  | Randomize (n : node)             (* RCT: n's value is drawn by the experimenter's coin *)
  | Measure   (n : node).            (* record n's current value into the log *)


Definition operations : Type := list operation.

Definition wf_operation (ag : aug_graph) (op : operation) : Prop :=
  match op with
  | Intervene n v =>
      node_in_graph n (dag ag) = true
  | Randomize n =>
      node_in_graph n (dag ag) = true
  | Measure n =>
      node_in_graph n (dag ag) = true /\ label_of ag n <> Unmeasurable
  end.

Definition wf_operations (ag : aug_graph) (prog : operations) : Prop :=
  Forall (wf_operation ag) prog.

(* ===================================================================== *)
(* Graph- and function-surgery helpers                                   *)
(* ===================================================================== *)

Definition do_graphfun {X: Type} (a: node) (alpha: X) (g: graphfun): graphfun :=
  fun w => if (w =? a)
           then f_constant X alpha  (* ignore parents and unobs term *)
           else g w.

Definition semantic_do {X: Type} (a: node) (alpha: X)
  (G: graph) (g: graphfun) (u: node) (U: assignments X): option X :=
  find_value (do a G) (do_graphfun a alpha g) u U [].

(* ===================================================================== *)
(* Total node evaluation (M2)                                             *)
(* --------------------------------------------------------------------- *)
(* [find_value] is total under well-formedness -- dsep-core's              *)
(* [find_value_existence]: a well-formed acyclic graph with a COMPLETE     *)
(* exogenous assignment [U] assigns every in-graph node a value.  [eval]   *)
(* packages that as an OPTION-FREE evaluator.  The [0] default is provably *)
(* dead code under wf (see [eval_find_value]) -- it is NOT a clamp; it     *)
(* only names the value [find_value] already computes.  This is the total  *)
(* "solve" the distribution semantics (M4) wraps in [fdistmap], so the     *)
(* outcome law ranges over worlds, not option-worlds. *)
Definition eval (G : graph) (g : @graphfun nat) (u : node) (U : assignments nat) : nat :=
  match find_value G g u U [] with
  | Some v => v
  | None   => 0
  end.

Lemma eval_find_value :
  forall (G : graph) (g : @graphfun nat) (u : node) (U : assignments nat),
  G_well_formed G = true ->
  contains_cycle G = false ->
  is_assignment_for U (nodes_in_graph G) = true ->
  node_in_graph u G = true ->
  find_value G g u U [] = Some (eval G g u U).
Proof.
  intros G g u U Hwf Hcyc HU Hu.
  destruct (find_value_existence nat G g U [] u
              (conj Hwf Hcyc) (conj HU Hu)) as [v Hv].
  unfold eval. rewrite Hv. reflexivity.
Qed.

Definition remove_incoming (n : node) (G : graph) : graph :=
  (fst G, remove_edges_into n (snd G)).

(* dag and nodefun are compatible iff |domain of nodefun n| <= |pa(n)| for all n in G *)
Definition dag_fun_compatible (G : graph) (g : @graphfun nat) : Prop :=
  forall (n : node) (u : nat) (pa1 pa2 : list nat),
    node_in_graph n G = true ->
    (forall i, i < length (find_parents n G) -> nth_error pa1 i = nth_error pa2 i) ->
    g n (u, pa1) = g n (u, pa2).

Definition remove_edges_out_of (n : node) (E : edges) : edges :=
  filter (fun edg => negb (fst edg =? n)) E.

Definition remove_outgoing (n : node) (G : graph) : graph :=
  (fst G, remove_edges_out_of n (snd G)).

Definition no_descendant_of_b (T : node) (G : graph) (Z : nodes) : bool :=
  forallb (fun z => negb (member z (find_descendants T G))) Z.

(* ---- Edge removal (remove_outgoing) preserves well-formedness/acyclicity ---- *)

Lemma remove_outgoing_pair : forall (T : node) (V : nodes) (E : edges),
  remove_outgoing T (V, E) = (V, filter (fun edg => negb (fst edg =? T)) E).
Proof. reflexivity. Qed.

Lemma G_well_formed_filter_edges : forall (V : nodes) (E : edges) (P : edge -> bool),
  G_well_formed (V, E) = true -> G_well_formed (V, filter P E) = true.
Proof.
  intros V E P H.
  cbn [G_well_formed] in *.
  apply split_and_true in H. destruct H as [HAB HC].
  apply split_and_true in HAB. destruct HAB as [HA HB].
  apply split_and_true. split. apply split_and_true. split.
  - apply forallb_forall. intros e He.
    apply filter_In in He. destruct He as [HeE _].
    rewrite forallb_forall in HA. apply HA. exact HeE.
  - exact HB.
  - apply forallb_forall. intros e He.
    apply filter_In in He as He'. destruct He' as [HeE HPe].
    rewrite <- (count_edge_filter E e P HPe).
    rewrite forallb_forall in HC. apply HC. exact HeE.
Qed.

Lemma G_well_formed_remove_outgoing : forall (T : node) (G : graph),
  G_well_formed G = true -> G_well_formed (remove_outgoing T G) = true.
Proof.
  intros T [V E] H. rewrite remove_outgoing_pair.
  apply G_well_formed_filter_edges. exact H.
Qed.

Lemma is_edge_remove_outgoing : forall (T : node) (G : graph) (e : edge),
  is_edge e (remove_outgoing T G) = true -> is_edge e G = true.
Proof.
  intros T [V E] [u v] H.
  rewrite remove_outgoing_pair in H. cbn [is_edge] in H |- *.
  apply split_and_true in H. destruct H as [Huv Hme].
  rewrite Huv. simpl.
  apply member_edge_In_equiv. apply member_edge_In_equiv in Hme.
  apply filter_In in Hme. destruct Hme as [Hme _]. exact Hme.
Qed.

Lemma dir_path_helper_remove_outgoing : forall (L : nodes) (T : node) (G : graph),
  is_dir_path_in_graph_helper L (remove_outgoing T G) = true ->
  is_dir_path_in_graph_helper L G = true.
Proof.
  intros L T G. induction L as [| h t IH].
  - intros _. reflexivity.
  - destruct t as [| h' t'].
    + intros _. reflexivity.
    + intros H. simpl in H. apply split_and_true in H. destruct H as [He Hrest].
      simpl. apply split_and_true. split.
      * apply is_edge_remove_outgoing with (T := T). exact He.
      * apply IH. exact Hrest.
Qed.

Lemma is_directed_path_remove_outgoing : forall (p : path) (T : node) (G : graph),
  is_directed_path_in_graph p (remove_outgoing T G) = true ->
  is_directed_path_in_graph p G = true.
Proof.
  intros [[u v] l] T G H.
  unfold is_directed_path_in_graph in *.
  apply dir_path_helper_remove_outgoing with (T := T). exact H.
Qed.

Lemma contains_cycle_remove_outgoing : forall (T : node) (G : graph),
  G_well_formed G = true -> contains_cycle G = false ->
  contains_cycle (remove_outgoing T G) = false.
Proof.
  intros T G Hwf Hcyc.
  apply contains_cycle_false_complete.
  - apply G_well_formed_remove_outgoing. exact Hwf.
  - intros p Hp.
    apply (contains_cycle_false_correct G p Hwf Hcyc).
    apply is_directed_path_remove_outgoing with (T := T). exact Hp.
Qed.

(* 3 node example
     - g(z) = U_z
     - g(x) = if z = 1 then 0 else 1
     - g(y) = x + z *)
Definition g_3 : @graphfun nat :=
  fun n =>
    match n with
    | 1 => fun val => if nth_default (fst val) (snd val) 0 =? 1 then 0 else 1
    (* val is (unobs, list parents) *)
    | 2 => fun val => nth_default (fst val) (snd val) 0
                    + nth_default (fst val) (snd val) 1
    | 3 => f_unobs nat
    | _ => f_unobs nat
    end.

Lemma nth_default_agree : forall (l1 l2 : list nat) (i d : nat),
  nth_error l1 i = nth_error l2 i -> nth_default d l1 i = nth_default d l2 i.
Proof. intros l1 l2 i d H. unfold nth_default. rewrite H. reflexivity. Qed.

Example g_3_compatible : dag_fun_compatible (dag G_3) g_3.
Proof.
  unfold dag_fun_compatible.
  intros n u pa1 pa2 Hin Hagree.
  destruct n as [| [| [| [| n']]]]; simpl in Hin; try discriminate; simpl in Hagree.
  - assert (H0 : nth_default u pa1 0 = nth_default u pa2 0)
      by (apply nth_default_agree, Hagree; lia).
    change (g_3 1 (u, pa1)) with (if nth_default u pa1 0 =? 1 then 0 else 1).
    change (g_3 1 (u, pa2)) with (if nth_default u pa2 0 =? 1 then 0 else 1).
    rewrite H0. reflexivity.
  - change (g_3 2 (u, pa1)) with (nth_default u pa1 0 + nth_default u pa1 1).
    change (g_3 2 (u, pa2)) with (nth_default u pa2 0 + nth_default u pa2 1).
    f_equal; apply nth_default_agree, Hagree; lia.
  - reflexivity.
Qed.

(* ===================================================================== *)
(* Experiment record                                                     *)
(* ===================================================================== *)

(* an experimental unit is a concrete instantiation of all "unobservables" *)
Definition individual : Type := assignments nat.

Record experiment : Type := mk_experiment {
  init_graph : aug_graph;
  init_fun   : @graphfun nat;
  sample     : list individual;
  ops        : operations;
}.

Definition experiment_wf (e : experiment) : Prop :=
  wf_aug_graph (init_graph e) /\
  wf_operations (init_graph e) (ops e) /\
  dag_fun_compatible (dag (init_graph e)) (init_fun e).

(* ===================================================================== *)
(* Concrete (per-unit) semantics                                         *)
(* ===================================================================== *)

Record unit_state : Type := mk_unit_state {
  cur_fun : @graphfun nat;
  log     : assignments nat;
}.

Definition unit_state_wf (G0 : graph) (st : unit_state) : Prop :=
  dag_fun_compatible G0 (cur_fun st).

Definition randomize_graphfun (n : node) (g : @graphfun nat) : @graphfun nat :=
  fun w => if w =? n then f_unobs nat else g w.

Definition apply_op (G0 : graph) (U : individual) (st : unit_state) (op : operation)
    : option unit_state :=
  match op with
  | Intervene n v =>
      Some (mk_unit_state (do_graphfun n v (cur_fun st)) (log st))
  | Randomize n =>
      Some (mk_unit_state (randomize_graphfun n (cur_fun st)) (log st))
  | Measure n =>
      match find_value G0 (cur_fun st) n U [] with
      | Some v => Some (mk_unit_state (cur_fun st) (log st ++ [(n, v)]))
      | None   => None
      end
  end.

(* --------------------------------------------------------------------- *)
(* Structural (abstract) counterpart of [apply_op]                        *)
(* --------------------------------------------------------------------- *)

(* The same three operations read on the OTHER layer.  [apply_op] above
   rewrites the mechanism F (and emits the log); [abs_apply_op] below rewrites
   the DAG (and records the measured footprint).  The two layers AGREE
   structurally: [Intervene] and [Randomize] both cut n loose from its parents
   (remove_incoming), exactly mirroring the mechanism side where f_n stops
   reading them (constant resp. exogenous draw).  [Measure] is the odd one
   out: the only op that changes nothing on either state, yet the only one
   that produces data. *)
Record abs_state : Type := mk_abs_state {
  abs_graph : aug_graph;
  measured  : nodes;
}.

Definition abs_apply_op (st : abs_state) (op : operation) : abs_state :=
  match op with
  | Intervene n _ =>
      mk_abs_state
        (mk_aug_graph
          (remove_incoming n (dag (abs_graph st)))
          (label_of (abs_graph st)))
        (measured st)
  | Randomize n =>
      mk_abs_state
        (mk_aug_graph
          (remove_incoming n (dag (abs_graph st)))
          (label_of (abs_graph st)))
        (measured st)
  | Measure n =>
      mk_abs_state (abs_graph st) (measured st ++ [n])
  end.

(* ---- Helper lemmas: how find_parents/node_in_graph interact with surgery ---- *)

Lemma find_parents_from_edges_remove_neq : forall (n w : node) (E : edges),
  w <> n ->
  find_parents_from_edges w (remove_edges_into n E) = find_parents_from_edges w E.
Proof.
  intros n w E Hneq.
  induction E as [| [u v] t IH].
  - reflexivity.
  - simpl. destruct (v =? n) eqn:Hvn.
    + simpl. assert (Hvw: (v =? w) = false).
      { apply Nat.eqb_eq in Hvn. subst v. apply Nat.eqb_neq. auto. }
      rewrite Hvw. apply IH.
    + simpl. destruct (v =? w) eqn:Hvw.
      * f_equal. apply IH.
      * apply IH.
Qed.

Lemma find_parents_from_edges_remove_self : forall (n : node) (E : edges),
  find_parents_from_edges n (remove_edges_into n E) = [].
Proof.
  intros n E.
  induction E as [| [u v] t IH].
  - reflexivity.
  - simpl. destruct (v =? n) eqn:Hvn.
    + apply IH.
    + simpl. rewrite Hvn. apply IH.
Qed.

Lemma find_parents_remove_incoming_neq : forall (n w : node) (G : graph),
  w <> n ->
  find_parents w (remove_incoming n G) = find_parents w G.
Proof.
  intros n w [V E] Hneq. unfold remove_incoming, find_parents. simpl.
  apply find_parents_from_edges_remove_neq. exact Hneq.
Qed.

Lemma find_parents_remove_incoming_self : forall (n : node) (G : graph),
  find_parents n (remove_incoming n G) = [].
Proof.
  intros n [V E]. unfold remove_incoming, find_parents. simpl.
  apply find_parents_from_edges_remove_self.
Qed.

Lemma node_in_graph_remove_incoming : forall (n w : node) (G : graph),
  node_in_graph w (remove_incoming n G) = node_in_graph w G.
Proof.
  intros n w [V E]. reflexivity.
Qed.

Lemma apply_op_preserves_wf : forall (G0 : graph) (U : individual) (st st' : unit_state) (op : operation),
  unit_state_wf G0 st ->
  apply_op G0 U st op = Some st' ->
  unit_state_wf G0 st'.
Proof.
  intros G0 U st st' op Hwf Hop.
  destruct op as [n v | n | n]; simpl in Hop.
  - (* Intervene n v *)
    inversion Hop; subst; clear Hop.
    unfold unit_state_wf, dag_fun_compatible in *. cbn [cur_fun log].
    intros w u pa1 pa2 Hin Hagree.
    unfold do_graphfun.
    destruct (w =? n) eqn:Hwn.
    + reflexivity.
    + apply Hwf; assumption.
  - (* Randomize n *)
    inversion Hop; subst; clear Hop.
    unfold unit_state_wf, dag_fun_compatible in *. cbn [cur_fun log].
    intros w u pa1 pa2 Hin Hagree.
    unfold randomize_graphfun.
    destruct (w =? n) eqn:Hwn.
    + reflexivity.
    + apply Hwf; assumption.
  - (* Measure n *)
    destruct (find_value G0 (cur_fun st) n U []) eqn:Hfv.
    + inversion Hop; subst; clear Hop.
      unfold unit_state_wf in *. simpl. apply Hwf.
    + discriminate Hop.
Qed.

Fixpoint run_unit (G0 : graph) (U : individual) (st : unit_state) (p : operations)
    : option unit_state :=
  match p with
  | []       => Some st
  | op :: p' =>
      match apply_op G0 U st op with
      | Some st' => run_unit G0 U st' p'
      | None     => None
      end
  end.

Lemma run_unit_preserves_wf : forall (G0 : graph) (U : individual) (p : operations) (st st' : unit_state),
  unit_state_wf G0 st ->
  run_unit G0 U st p = Some st' ->
  unit_state_wf G0 st'.
Proof.
  intros G0 U p.
  induction p as [| op p' IH]; intros st st' Hwf Hrun.
  - simpl in Hrun. inversion Hrun; subst. exact Hwf.
  - simpl in Hrun. destruct (apply_op G0 U st op) as [st_mid|] eqn:Hop.
    + apply (IH st_mid st').
      * exact (apply_op_preserves_wf G0 U st st_mid op Hwf Hop).
      * exact Hrun.
    + discriminate Hrun.
Qed.

Lemma run_unit_app : forall (G0 : graph) (U : individual) (p1 p2 : operations) (st st' : unit_state),
  run_unit G0 U st (p1 ++ p2) = Some st' <->
  exists st_mid, run_unit G0 U st p1 = Some st_mid /\ run_unit G0 U st_mid p2 = Some st'.
Proof.
  intros G0 U p1.
  induction p1 as [| op p1' IH]; intros p2 st st'.
  - simpl. split.
    + intros H. exists st. split; [reflexivity | exact H].
    + intros [st_mid [Heq H]]. inversion Heq; subst. exact H.
  - simpl. destruct (apply_op G0 U st op) as [st1|] eqn:Hop.
    + apply IH.
    + split.
      * discriminate.
      * intros [st_mid [H1 _]]. discriminate H1.
Qed.

Lemma measure_total : forall (G0 : graph) (U : individual) (p : operations) (st st' : unit_state),
  run_unit G0 U st p = Some st' ->
  length (log st') =
    length (log st) +
    length (filter (fun op => match op with Measure _ => true | _ => false end) p).
Proof.
  intros G0 U p.
  induction p as [| op p' IH]; intros st st' Hrun.
  - simpl in Hrun. inversion Hrun; subst. simpl. lia.
  - simpl in Hrun.
    destruct (apply_op G0 U st op) as [st1|] eqn:Hop; [| discriminate Hrun].
    specialize (IH st1 st' Hrun).
    destruct op as [n v | n | n]; simpl in Hop.
    + inversion Hop; subst. simpl in IH. simpl. lia.
    + inversion Hop; subst. simpl in IH. simpl. lia.
    + destruct (find_value G0 (cur_fun st) n U []) as [v|] eqn:Hfv; [| discriminate Hop].
      inversion Hop; subst. simpl in IH.
      rewrite length_app in IH. simpl in IH.
      simpl. lia.
Qed.

Fixpoint run_all (e : experiment) (us : list individual)
    : option (list (assignments nat)) :=
  match us with
  | [] => Some []
  | U :: rest =>
      let init_st := mk_unit_state (init_fun e) [] in
      match run_unit (dag (init_graph e)) U init_st (ops e) with
      | None     => None
      | Some st' =>
          match run_all e rest with
          | None      => None
          | Some logs => Some (log st' :: logs)
          end
      end
  end.

Definition concrete_logs (e : experiment) : option (list (assignments nat)) :=
  run_all e (sample e).

(* ===================================================================== *)
(* Abstract (graph-surgical) semantics                                   *)
(* ===================================================================== *)

Fixpoint abs_run (st : abs_state) (p : operations) : abs_state :=
  match p with
  | []       => st
  | op :: p' => abs_run (abs_apply_op st op) p'
  end.

Definition abs_init (e : experiment) : abs_state :=
  mk_abs_state (init_graph e) [].

Definition post_experiment_dag (e : experiment) : graph :=
  dag (abs_graph (abs_run (abs_init e) (ops e))).

(* ===================================================================== *)
(* Simulation invariant: concrete log tracks the abstract measured set   *)
(* ===================================================================== *)

Lemma apply_op_measured_agree : forall (G0 : graph) (U : individual) (st st1 : unit_state)
    (a : abs_state) (op : operation),
  map fst (log st) = measured a ->
  apply_op G0 U st op = Some st1 ->
  map fst (log st1) = measured (abs_apply_op a op).
Proof.
  intros G0 U st st1 a op Heq Hop.
  destruct op as [n v | n | n]; simpl in Hop.
  - inversion Hop; subst. simpl. exact Heq.
  - inversion Hop; subst. simpl. exact Heq.
  - destruct (find_value G0 (cur_fun st) n U []) as [v0|] eqn:Hfv; [| discriminate Hop].
    inversion Hop; subst. simpl.
    unfold assignment in *.
    rewrite map_app. simpl. rewrite Heq. reflexivity.
Qed.

Lemma measured_agree : forall (G0 : graph) (U : individual) (p : operations)
    (st st' : unit_state) (a : abs_state),
  map fst (log st) = measured a ->
  run_unit G0 U st p = Some st' ->
  map fst (log st') = measured (abs_run a p).
Proof.
  intros G0 U p.
  induction p as [| op p' IH]; intros st st' a Heq Hrun.
  - simpl in Hrun. inversion Hrun; subst. simpl. exact Heq.
  - simpl in Hrun.
    destruct (apply_op G0 U st op) as [st1|] eqn:Hop; [| discriminate Hrun].
    simpl.
    apply (IH st1 st' (abs_apply_op a op)).
    + apply (apply_op_measured_agree G0 U st st1 a op Heq Hop).
    + exact Hrun.
Qed.



(* ===================================================================== *)
(* Backdoor criterion — syntactic and semantic                           *)
(* ===================================================================== *)

Definition dedup (Z : nodes) : nodes := nodup Nat.eq_dec Z.

Lemma In_dedup : forall (x : node) (Z : nodes), In x (dedup Z) <-> In x Z.
Proof. intros x Z. unfold dedup. apply nodup_In. Qed.

Lemma member_dedup : forall (x : node) (Z : nodes), member x (dedup Z) = member x Z.
Proof.
  intros x Z. destruct (member x Z) eqn:HZ.
  - apply member_In_equiv in HZ. apply member_In_equiv. apply In_dedup. exact HZ.
  - apply member_In_equiv_F in HZ. apply member_In_equiv_F. rewrite In_dedup. exact HZ.
Qed.

Lemma subset_dedup : forall (Z L : nodes), subset Z L = true -> subset (dedup Z) L = true.
Proof.
  intros Z L H. unfold subset in *. apply forallb_forall. intros x Hx.
  rewrite In_dedup in Hx. rewrite forallb_forall in H. apply H. exact Hx.
Qed.

Lemma NoDup_each_node_appears_once : forall (l : nodes),
  NoDup l -> each_node_appears_once l.
Proof.
  intros l. induction l as [| h t IH]; intros Hnd.
  - intros u Hin. inversion Hin.
  - apply NoDup_cons_iff in Hnd. destruct Hnd as [Hnh Hndt].
    intros u Hin. simpl in Hin. simpl. destruct (h =? u) eqn:Hhu.
    + apply Nat.eqb_eq in Hhu. subst h.
      rewrite (not_member_count_0 t u (proj2 (member_In_equiv_F t u) Hnh)).
      reflexivity.
    + apply Nat.eqb_neq in Hhu. destruct Hin as [Heq | Hin'].
      * exfalso. apply Hhu. exact Heq.
      * specialize (IH Hndt). apply IH. exact Hin'.
Qed.

Lemma each_node_appears_once_dedup : forall (Z : nodes),
  each_node_appears_once (dedup Z).
Proof.
  intros Z. apply NoDup_each_node_appears_once. unfold dedup. apply NoDup_nodup.
Qed.

Definition syntactic_backdoor (G : graph) (T R : node) (Z : nodes) : bool :=
  no_descendant_of_b T G (dedup Z)
  && d_separated_bool T R (remove_outgoing T G) (dedup Z).

Definition semantic_backdoor (X : Type) `{EqType X}
    (G : graph) (T R : node) (Z : nodes) : Prop :=
  no_descendant_of_b T G (dedup Z) = true /\
  semantically_separated X (remove_outgoing T G) T R (dedup Z).

(* [each_node_appears_once] is discharged internally now, because both
   predicates condition on [dedup Z], which is duplicate-free by construction. *)
Theorem backdoor_correspondence {X : Type} `{EqType X} :
  forall (G : graph) (T R : node) (Z : nodes),
    node_in_graph R G = true -> T <> R ->
    generic_graph_and_type_properties_hold X G ->
    subset Z (nodes_in_graph G) = true ->
    member T Z = false -> member R Z = false ->
    syntactic_backdoor G T R Z = true <-> semantic_backdoor X G T R Z.
Proof.
  intros G T R Z HRin HTR Hgen HZsub HTZ HRZ.
  destruct Hgen as [Hxy [Hwf Hcyc]].
  assert (Hnodes : nodes_in_graph (remove_outgoing T G) = nodes_in_graph G)
    by (destruct G as [V E]; reflexivity).
  assert (HRin' : node_in_graph R (remove_outgoing T G) = true)
    by (destruct G as [V E]; exact HRin).
  assert (HZsub' : subset (dedup Z) (nodes_in_graph (remove_outgoing T G)) = true).
  { rewrite Hnodes. apply subset_dedup. exact HZsub. }
  assert (Hwf' : G_well_formed (remove_outgoing T G) = true)
    by (apply G_well_formed_remove_outgoing; exact Hwf).
  assert (Hcyc' : contains_cycle (remove_outgoing T G) = false)
    by (apply contains_cycle_remove_outgoing; [ exact Hwf | exact Hcyc ]).
  assert (HTZ' : member T (dedup Z) = false) by (rewrite member_dedup; exact HTZ).
  assert (HRZ' : member R (dedup Z) = false) by (rewrite member_dedup; exact HRZ).
  pose proof (semantic_and_d_separation_equivalent (X := X)
                (remove_outgoing T G) T R
                (conj HTR (conj (conj Hxy (conj Hwf' Hcyc')) HRin'))
                (dedup Z)
                (conj HZsub' (conj (each_node_appears_once_dedup Z) (conj HTZ' HRZ')))) as Hequiv.
  unfold syntactic_backdoor, semantic_backdoor.
  split.
  - intro Hsyn. apply andb_prop in Hsyn. destruct Hsyn as [Hnd Hdsep].
    split; [ exact Hnd | apply (proj2 Hequiv); exact Hdsep ].
  - intros [Hnd Hsem].
    apply andb_true_intro.
    split; [ exact Hnd | apply (proj1 Hequiv); exact Hsem ].
Qed.

(* ===================================================================== *)
(* Simplified randomized controlled trial (RCT)                          *)
(* ===================================================================== *)

(* A [simple_rct] is an experiment over ANY causal DAG [G], graphfun [F] and
   sample [S] whose program randomizes the treatment node [T] and then measures
   the response node [R].  For now we take a single treatment and a single
   response node.  The correctness statement is in [Correctness.v]
   ([simple_rct_syntactically_correct]). *)
Definition simple_rct (G : aug_graph) (F : @graphfun nat) (S : list individual)
    (T R : node) : experiment :=
  mk_experiment G F S [Randomize T; Measure R].

(* The post-experiment DAG of a [simple_rct]: randomizing [T] deletes [T]'s
   incoming edges -- the same surgery as an intervention on [T]; measuring is
   inert on the structural layer. *)
Lemma post_dag_simple_rct : forall (G : aug_graph) (F : @graphfun nat)
    (S : list individual) (T R : node),
  post_experiment_dag (simple_rct G F S T R)
  = remove_incoming T (dag G).
Proof. reflexivity. Qed.

(* Membership in [nodes_with_label] recovers both graph-membership and the
   label of the node -- lets a caller say "T is the treatment node" with one
   hypothesis. *)
Lemma In_nodes_with_label_inv : forall (ag : aug_graph) (r : node_label) (n : node),
  In n (nodes_with_label ag r) ->
  node_in_graph n (dag ag) = true /\ label_of ag n = r.
Proof.
  intros ag r n Hin. unfold nodes_with_label in Hin.
  apply filter_In in Hin. destruct Hin as [Hin Hlab].
  split.
  - destruct (dag ag) as [V E]. unfold nodes_in_graph in Hin.
    unfold node_in_graph. apply member_In_equiv. exact Hin.
  - apply node_label_eqb_eq. exact Hlab.
Qed.

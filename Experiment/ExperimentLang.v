From DAGs Require Import Basics Descendants.
From CausalDiagrams Require Import Assignments Interventions.
From Semantics Require Import FunctionRepresentation FindValue EquateValues.
From Experiment Require Import Exp_Basics Do.
Import ListNotations.

(* Graph surgery helpers *)
Definition remove_incoming (n : node) (G : graph) : graph :=
  (fst G, remove_edges_into n (snd G)).

Definition add_fresh_source (src tgt : node) (G : graph) : graph :=
  (src :: fst G, (src, tgt) :: snd G).

Definition fun_graph_compat {X : Type} (G : graph) (g : @graphfun X) : Prop :=
  forall (n : node) (u : X) (pa1 pa2 : list X),
    node_in_graph n G = true ->
    (forall i, i < length (find_parents n G) -> nth_error pa1 i = nth_error pa2 i) ->
    g n (u, pa1) = g n (u, pa2).

(* Experiment record  *)

Definition individual (X : Type) : Type := assignments X.

Record experiment (X : Type) : Type := mk_experiment {
  init_graph : aug_graph;
  init_fun   : @graphfun X;
  sample     : list (individual X);
  ops        : program X;
}.
Arguments init_graph {X}.
Arguments init_fun   {X}.
Arguments sample     {X}.
Arguments ops        {X}.

Definition experiment_wf {X : Type} (e : experiment X) : Prop :=
  wf_aug_graph (init_graph e) /\
  wf_program (init_graph e) (ops e) /\
  fun_graph_compat (dag (init_graph e)) (init_fun e).

(* Concrete (per-unit) semantics *)
Record unit_state (X : Type) : Type := mk_unit_state {
  cur_graph : graph;
  cur_fun   : @graphfun X;
  log       : assignments X;
}.
Arguments cur_graph {X}.
Arguments cur_fun   {X}.
Arguments log       {X}.

(* A unit_state is well-formed when its graphfun is compatible with its graph. *)
Definition unit_state_wf {X : Type} (st : unit_state X) : Prop :=
  fun_graph_compat (cur_graph st) (cur_fun st).

Definition apply_op {X : Type} (U : individual X) (st : unit_state X) (op : operation X)
    : option (unit_state X) :=
  match op with
  | Intervene n v =>
      Some (mk_unit_state X
        (remove_incoming n (cur_graph st))
        (do_graphfun n v (cur_fun st))
        (log st))
  | Randomize n r =>
      Some (mk_unit_state X
        (add_fresh_source r n (remove_incoming n (cur_graph st)))
        (fun w => if w =? n then f_parent_i X 0 (* only take the value of r *)
                  else if w =? r then f_unobs X (* only take the value of the unobservable*)
                  else cur_fun st w)
        (log st))
  | Measure n =>
      match find_value (cur_graph st) (cur_fun st) n U [] with
      | Some v => Some (mk_unit_state X (cur_graph st) (cur_fun st) (log st ++ [(n, v)]))
      | None   => None
      end
  end.

(* apply_op preserves unit_state_wf: each case installs equations that only
   read from the node's new parent set. *)
Lemma apply_op_preserves_wf : forall {X : Type} (U : individual X) (st st' : unit_state X) (op : operation X),
  unit_state_wf st ->
  apply_op U st op = Some st' ->
  unit_state_wf st'.
Proof.
Admitted.

Fixpoint run_unit {X : Type} (U : individual X) (st : unit_state X) (p : program X)
    : option (unit_state X) :=
  match p with
  | []       => Some st
  | op :: p' =>
      match apply_op U st op with
      | Some st' => run_unit U st' p'
      | None     => None
      end
  end.

Lemma run_unit_preserves_wf : forall {X : Type} (U : individual X) (st st' : unit_state X) (p : program X),
  unit_state_wf st ->
  run_unit U st p = Some st' ->
  unit_state_wf st'.
Proof.
Admitted.

Lemma run_unit_app : forall {X : Type} (U : individual X) (st : unit_state X) (p1 p2 : program X) (st' : unit_state X),
  run_unit U st (p1 ++ p2) = Some st' <->
  exists st_mid, run_unit U st p1 = Some st_mid /\ run_unit U st_mid p2 = Some st'.
Proof.
Admitted.

Lemma measure_total : forall {X : Type} (U : individual X) (st st' : unit_state X) (p : program X),
  run_unit U st p = Some st' ->
  length (log st') =
    length (log st) +
    length (filter (fun op => match op with Measure _ => true | _ => false end) p).
Proof.
Admitted.

Fixpoint run_all {X : Type} (e : experiment X) (us : list (individual X))
    : option (list (assignments X)) :=
  match us with
  | [] => Some []
  | U :: rest =>
      let init_st := mk_unit_state X (dag (init_graph e)) (init_fun e) [] in
      match run_unit U init_st (ops e) with
      | None     => None
      | Some st' =>
          match run_all e rest with
          | None      => None
          | Some logs => Some (log st' :: logs)
          end
      end
  end.

Definition concrete_logs {X : Type} (e : experiment X) : option (list (assignments X)) :=
  run_all e (sample e).

(* ================================================================ *)
(* Abstract (graph-surgical) semantics                              *)
(* ================================================================ *)

Record abs_state : Type := mk_abs_state {
  abs_graph : aug_graph;
  measured  : nodes;
}.

Definition abs_apply_op {X : Type} (st : abs_state) (op : operation X) : abs_state :=
  match op with
  | Intervene n _ =>
      mk_abs_state
        (mk_aug_graph
          (remove_incoming n (dag (abs_graph st)))
          (label_of (abs_graph st)))
        (measured st)
  | Randomize n r =>
      mk_abs_state
        (mk_aug_graph
          (add_fresh_source r n (remove_incoming n (dag (abs_graph st))))
          (fun m => if m =? r then Unlabeled else label_of (abs_graph st) m))
        (measured st)
  | Measure n =>
      mk_abs_state (abs_graph st) (measured st ++ [n])
  end.

Fixpoint abs_run {X : Type} (st : abs_state) (p : program X) : abs_state :=
  match p with
  | []       => st
  | op :: p' => abs_run (abs_apply_op st op) p'
  end.

Definition abs_init {X : Type} (e : experiment X) : abs_state :=
  mk_abs_state (init_graph e) [].

Definition post_experiment_dag {X : Type} (e : experiment X) : graph :=
  dag (abs_graph (abs_run (abs_init e) (ops e))).

(* Agreement lemmas *)

Lemma graphs_agree : forall {X : Type} (U : individual X) (p : program X)
    (st st' : unit_state X) (a : abs_state),
  cur_graph st = dag (abs_graph a) ->
  run_unit U st p = Some st' ->
  cur_graph st' = dag (abs_graph (abs_run a p)).
Proof.
Admitted.

Lemma measured_agree : forall {X : Type} (U : individual X) (p : program X)
    (st st' : unit_state X) (a : abs_state),
  map fst (log st) = measured a ->
  run_unit U st p = Some st' ->
  map fst (log st') = measured (abs_run a p).
Proof.
Admitted.

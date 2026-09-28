Set Warnings "-notation-overridden,-deprecated-library-file,-ambiguous-paths".
From HB Require Import structures.
From mathcomp Require Import all_ssreflect.
From DAGs Require Import Basics_Constr Descendants.
From CausalDiagrams Require Import Assignments.
From Semantics Require Import FunctionRepresentation FindValue.
From Experiment Require Main.
From Experiment Require Import Prob.

Set Implicit Arguments.
Unset Strict Implicit.

(* ===================================================================== *)
(* Typed experiment surface                                              *)
(* --------------------------------------------------------------------- *)
(* [Main.operation] speaks dsep-core's untyped language: node ids are raw *)
(* nats and [Intervene n v] carries a nat CODE.  That is the right        *)
(* language for the semantics -- the abstract layer rewrites the dag, and *)
(* [operation] must stay graph-free for that to typecheck -- but it is a  *)
(* poor language to WRITE a protocol in.                                  *)
(*                                                                        *)
(* So this file adds a typed surface and compiles it down, exactly as     *)
(* [Prob.elab] does for mechanisms:                                       *)
(*                                                                        *)
(*     tgraphfun  --[elab]-->     graphfun        (mechanisms, Prob.v)    *)
(*     toperation --[elab_op]-->  operation       (protocols, here)       *)
(*                                                                        *)
(* An author writes [TIntervene x3 drug], not [Intervene 1 1]: the value  *)
(* is given in ITS OWN domain, so an out-of-range value is unrepresentable *)
(* rather than a side condition to discharge.  Half of [wf_operation]     *)
(* comes for free too -- a [Node G] cannot name a node outside G, so      *)
(* [elab_op_wf] only has the LABEL obligations left to check.             *)
(*                                                                        *)
(* Why compile rather than retype [Main.operation]: surgery changes the   *)
(* graph, so a graph-indexed operation type would need [operation         *)
(* (remove_incoming n G)] after each step.  The node set never changes    *)
(* (D1), but [nodes_in_graph (remove_incoming n G)] reduces to [fst G]    *)
(* while [nodes_in_graph G] is stuck on an abstract G, so the two index   *)
(* types are NOT convertible and every step would carry a transport.      *)
(* Elaboration erases the index and the problem with it.                  *)
(* ===================================================================== *)

Section TypedOps.
Variable G : graph.

Unset Implicit Arguments.
Variable dom : Node G -> finType.
Variable enc : forall n : Node G, dom n -> nat.
Variable dec : forall n : Node G, nat -> dom n.
Set Implicit Arguments.

(* A typed operation.  [TFilter] carries its read set [ns] separately from
   its rule [keep] for the reason [Main.Filter] does: the read set is the
   conditioning set Z the static checks consume, so it must stay visible.
   [keep] receives a view that answers only for nodes of [ns] -- the same
   ticket discipline as [Prob.parent_view], so a rule cannot read what it
   was not given, and cannot depend on the order [ns] was written in. *)
Inductive toperation : Type :=
  | TIntervene (n : Node G) (v : dom n)
  | TRandomize (n : Node G)
  | TMeasure   (n : Node G)
  | TFilter    (ns : list (Node G))
               (keep : (forall n : Node G, n \in ns -> dom n) -> bool).

(* the typed view handed to a filter's rule: look each node of the read set
   up BY ID in the nat-valued assignment, then decode into its own domain *)
Definition decode_at (ns : list (Node G)) (a : assignments nat)
    : forall n : Node G, n \in ns -> dom n :=
  fun n _ =>
    dec n (match get_assigned_value a (ssval n) with
           | Some x => x
           | None   => 0
           end).

Definition elab_op (op : toperation) : Main.operation :=
  match op with
  | TIntervene n v  => Main.Intervene (ssval n) (enc n v)
  | TRandomize n    => Main.Randomize (ssval n)
  | TMeasure n      => Main.Measure   (ssval n)
  | TFilter ns keep => Main.Filter (map (fun n => ssval n) ns)
                                   (fun a => keep (@decode_at ns a))
  end.

Definition elab_ops (p : list toperation) : Main.operations :=
  map elab_op p.

(* --- well-formedness: only the LABEL half survives typing -------------- *)

(* [Main.wf_operation] asks two things of a node: that it is in the graph,
   and (for reads) that it is not Unmeasurable.  The first is structural
   here -- a [Node G] IS a node of G -- so a typed operation only has to
   promise the second.  Labels are not part of [Node], which is why this
   obligation cannot be typed away as well. *)
Definition twf_operation (ag : Main.aug_graph) (op : toperation) : Prop :=
  match op with
  | TIntervene _ _ => True
  | TRandomize _   => True
  | TMeasure n     => Main.label_of ag (ssval n) <> Main.Unmeasurable
  | TFilter ns _   =>
      List.Forall (fun n => Main.label_of ag (ssval n) <> Main.Unmeasurable) ns
  end.

Lemma elab_op_wf (ag : Main.aug_graph) (op : toperation) :
  Main.dag ag = G ->
  twf_operation ag op ->
  Main.wf_operation ag (elab_op op).
Proof.
move=> Hag; case: op => /=.
- by move=> n v _; rewrite Hag; exact: node_in_graph_ssval.
- by move=> n _; rewrite Hag; exact: node_in_graph_ssval.
- by move=> n Hl; split; [rewrite Hag; exact: node_in_graph_ssval|].
- (* [keep] is irrelevant to well-formedness -- and its type mentions [ns],
     so it has to go before [ns] can be generalised *)
  move=> ns _ /=; elim: ns => [|n ns IH] /=; first by move=> _; constructor.
  move=> Hl; constructor.
  + by split; [rewrite Hag; exact: node_in_graph_ssval
              | exact: (List.Forall_inv Hl)].
  + by apply: IH; exact: (List.Forall_inv_tail Hl).
Qed.

Lemma elab_ops_wf (ag : Main.aug_graph) (p : list toperation) :
  Main.dag ag = G ->
  List.Forall (twf_operation ag) p ->
  List.Forall (Main.wf_operation ag) (elab_ops p).
Proof.
move=> Hag; elim: p => [|op p IH] /= Hl; first by constructor.
constructor.
- by apply: elab_op_wf => //; exact: (List.Forall_inv Hl).
- by apply: IH; exact: (List.Forall_inv_tail Hl).
Qed.

(* --- the ordering discipline transfers verbatim ----------------------- *)
(* [elab_op] preserves which KIND each operation is, so [Main.measures_last]
   on the elaborated program is the typed check on the typed one. *)

Definition tis_surgery (op : toperation) : bool :=
  match op with TIntervene _ _ | TRandomize _ => true | _ => false end.

Definition tis_measure (op : toperation) : bool :=
  match op with TMeasure _ => true | _ => false end.

Fixpoint tmeasures_last (p : list toperation) : bool :=
  match p with
  | nil => true
  | op :: rest =>
      if tis_measure op
      then List.forallb (fun o => negb (tis_surgery o)) rest
      else tmeasures_last rest
  end.

Lemma is_measure_elab op : Main.is_measure (elab_op op) = tis_measure op.
Proof. by case: op. Qed.

Lemma is_surgery_elab op : Main.is_surgery (elab_op op) = tis_surgery op.
Proof. by case: op. Qed.

Lemma forallb_surgery_elab (p : list toperation) :
  List.forallb (fun o => negb (Main.is_surgery o)) (elab_ops p)
  = List.forallb (fun o => negb (tis_surgery o)) p.
Proof. by elim: p => [|op p IH] //=; rewrite is_surgery_elab IH. Qed.

Lemma measures_last_elab (p : list toperation) :
  Main.measures_last (elab_ops p) = tmeasures_last p.
Proof.
elim: p => [|op p IH] //=.
rewrite is_measure_elab; case: (tis_measure op); last exact: IH.
exact: forallb_surgery_elab.
Qed.

(* --- the typed experiment --------------------------------------------- *)
(* Graph, domains and codes are fixed by the section; a typed experiment
   adds the labels, the typed mechanism and the typed protocol. *)

Record texperiment : Type := mk_texperiment {
  te_labels : node -> Main.node_label;
  te_mech   : tgraphfun dom;
  te_ops    : list toperation;
}.

Definition te_aug (te : texperiment) : Main.aug_graph :=
  Main.mk_aug_graph G (te_labels te).

Definition elab_exp (te : texperiment) : Main.experiment :=
  Main.mk_experiment (te_aug te)
                     (elab enc dec (te_mech te))
                     (elab_ops (te_ops te)).

(* Elaborating a well-formed typed experiment gives a well-formed untyped
   one.  Note what is NOT a hypothesis: [dag_fun_compatible] comes free from
   [elab_compatible], and every node-membership side condition is discharged
   by typing.  What remains are the genuinely semantic obligations -- the
   graph is a wf dag with treatments and responses, reads are measurable,
   and measurements come after surgery. *)
Theorem elab_exp_wf (te : texperiment) :
  Main.wf_aug_graph (te_aug te) ->
  List.Forall (twf_operation (te_aug te)) (te_ops te) ->
  tmeasures_last (te_ops te) = true ->
  Main.experiment_wf (elab_exp te).
Proof.
move=> Hag Hops Hml; split; first exact: Hag.
split; last exact: elab_compatible.
split.
- by apply: elab_ops_wf.
- by rewrite measures_last_elab.
Qed.

End TypedOps.

(* ===================================================================== *)
(* Worked example: the drug trial's protocol, written typed              *)
(* --------------------------------------------------------------------- *)
(* G3, its domains and its mechanism all come from [Prob.v]; only the     *)
(* protocol is new.  The elaboration checks below are [reflexivity]:      *)
(* unlike anything routed through [to_assign], [elab_op] computes.        *)
(* ===================================================================== *)

(* randomize the treatment, then measure the response -- the typed twin of
   [Main.simple_rct]'s program *)
Definition trct_3 : list (toperation dom_3) :=
  @TRandomize G3 dom_3 x3 :: @TMeasure G3 dom_3 y3 :: nil.

Example trct_3_elaborates :
  elab_ops enc_3 dec_3 trct_3
  = (Main.Randomize 1 :: Main.Measure 2 :: nil)%N.
Proof. reflexivity. Qed.

(* the ordering discipline is satisfied, checked on the typed side *)
Example trct_3_measures_last : tmeasures_last trct_3 = true.
Proof. reflexivity. Qed.

(* a typed intervention: the value is a [treatment], not a code.  [drug]
   encodes to 1, but the author never writes the 1. *)
Example tintervene_elaborates :
  elab_op enc_3 dec_3 (@TIntervene G3 dom_3 x3 drug) = Main.Intervene 1 1.
Proof. reflexivity. Qed.

(* and the point of the exercise: [TIntervene x3 cured] does not typecheck,
   because [cured : outcome] is not in [dom_3 x3 = treatment].  Under
   [Main.Intervene 1 3] the same mistake is a well-typed nat. *)
Fail Example tintervene_ill_typed :
  elab_op enc_3 dec_3 (@TIntervene G3 dom_3 x3 cured) = Main.Intervene 1 3.

(* a typed filter: keep the units whose confounder reads [old].  The rule
   reads Z by name out of the view it is given. *)
Definition tfilter_old : toperation dom_3 :=
  @TFilter G3 dom_3 (z3 :: nil) (fun v => v z3 (mem_head _ _) == old).

Example tfilter_reads_z :
  elab_op enc_3 dec_3 tfilter_old
  = Main.Filter (3 :: nil)%N
      (fun a => dec_3 z3 (match get_assigned_value a 3 with
                          | Some x => x
                          | None => 0
                          end) == old).
Proof. reflexivity. Qed.

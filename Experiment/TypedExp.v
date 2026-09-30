Set Warnings "-notation-overridden,-deprecated-library-file,-ambiguous-paths".
From HB Require Import structures.
From mathcomp Require Import all_ssreflect ssralg ssrnum finalg reals matrix.
From mathcomp Require boolp.
From infotheo Require Import ssr_ext ssralg_ext fdist proba.
From DAGs Require Import Basics_Constr Descendants CycleDetection.
From CausalDiagrams Require Import Assignments.
From Semantics Require Import FunctionRepresentation FindValue.
From Experiment Require Main.
From Experiment Require Import Prob.

Set Implicit Arguments.
Unset Strict Implicit.

Local Open Scope fdist_scope.

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

(* A typed operation: the same three the untyped layer has, with node ids
   replaced by [Node G] and intervention values by elements of [dom n]. *)
Inductive toperation : Type :=
  | TIntervene (n : Node G) (v : dom n)
  | TRandomize (n : Node G)
  | TMeasure   (n : Node G).

Definition elab_op (op : toperation) : Main.operation :=
  match op with
  | TIntervene n v  => Main.Intervene (ssval n) (enc n v)
  | TRandomize n    => Main.Randomize (ssval n)
  | TMeasure n      => Main.Measure   (ssval n)
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
  elab_ops enc_3 trct_3
  = (Main.Randomize 1 :: Main.Measure 2 :: nil)%N.
Proof. reflexivity. Qed.

(* the ordering discipline is satisfied, checked on the typed side *)
Example trct_3_measures_last : tmeasures_last trct_3 = true.
Proof. reflexivity. Qed.

(* a typed intervention: the value is a [treatment], not a code.  [drug]
   encodes to 1, but the author never writes the 1. *)
Example tintervene_elaborates :
  elab_op enc_3 (@TIntervene G3 dom_3 x3 drug) = Main.Intervene 1 1.
Proof. reflexivity. Qed.

(* and the point of the exercise: [TIntervene x3 cured] does not typecheck,
   because [cured : outcome] is not in [dom_3 x3 = treatment].  Under
   [Main.Intervene 1 3] the same mistake is a well-typed nat. *)
Fail Example tintervene_ill_typed :
  elab_op enc_3 (@TIntervene G3 dom_3 x3 cured) = Main.Intervene 1 3.

(* ===================================================================== *)
(* The experiment's outcome law                                          *)
(* --------------------------------------------------------------------- *)
(* The concrete semantics runs a protocol on ONE unit and produces a log. *)
(* The population is not a field of the experiment (D7), so the law over  *)
(* outcomes is the pushforward of the exogenous law along that run --     *)
(* the same move [fdist_world] makes for a model, one level up.           *)
(*                                                                        *)
(* [log_val e w n] reads node n's entry out of the log produced by        *)
(* running [e] on the unit [w], decoded into n's own domain.  It lands in *)
(* a finType, which a whole log does not (a log is a list), so this is    *)
(* what can carry a distribution today.  A general log law needs a finite *)
(* log type indexed by the [Measure] positions -- deferred until a        *)
(* protocol measures more than one node.                                  *)
(* ===================================================================== *)

Section ExperimentLaw.
Variable G : graph.

Unset Implicit Arguments.
Variable dom : Node G -> finType.
Variable enc : forall n : Node G, dom n -> nat.
Variable dec : forall n : Node G, nat -> dom n.
Set Implicit Arguments.
Hypothesis encK : forall n : Node G, cancel (enc n) (dec n).

Variable R : realType.
Variable P : forall n : Node G, R.-fdist (dom n).

(* node n's logged value after running [e] on the unit [w] *)
Definition log_val (e : Main.experiment) (w : context dom) (n : Node G) : dom n :=
  dec n (odflt 0
    (get_assigned_value
       (Main.log (Main.run_unit_total (Main.dag (Main.init_graph e))
                    (to_assign enc w)
                    (Main.mk_unit_state (Main.init_fun e) nil)
                    (Main.ops e)))
       (ssval n))).

(* the law of that value across the population *)
Definition fdist_log_val (e : Main.experiment) (n : Node G) : R.-fdist (dom n) :=
  dmap (fun w : context dom => log_val e w n) (fdist_context P).

(* a protocol that only measures n logs exactly n's solved value *)
Lemma log_val_measure (te : texperiment dom) (w : context dom) (n : Node G) :
  te_ops te = @TMeasure G dom n :: nil ->
  log_val (elab_exp enc dec te) w n = solve enc dec (te_mech te) w n.
Proof.
move=> Hops; rewrite /log_val /elab_exp /elab_ops Hops /= Nat.eqb_refl /=.
by rewrite /solve.
Qed.

(* HELLO WORLD.  Run a protocol that measures one parentless node whose
   mechanism echoes its own noise.  The law of what gets logged is exactly
   the law that node was given: what you put in is what you get out.

   This is the end-to-end smoke test of the whole stack -- enc/dec,
   to_assign, find_value, eval, solve, run_unit_total, fdist_context --
   and it is an EXACT equality of laws, not a limit statement. *)
Theorem measure_source_law (te : texperiment dom) (n : Node G) :
  G_well_formed G = true ->
  contains_cycle G = false ->
  find_parents (ssval n) G = nil ->
  te_ops te = @TMeasure G dom n :: nil ->
  (forall u pa, (te_mech te : tgraphfun dom) n u pa = u) ->
  fdist_log_val (elab_exp enc dec te) n = P n.
Proof.
move=> Hwf Hcyc Hnp Hops Hecho.
have Hs : forall w0 : context dom, solve enc dec (te_mech te) w0 n = w0 n.
  by move=> w0; apply: solve_source.
rewrite /fdist_log_val.
transitivity (dmap (fun w : context dom => w n) (fdist_context P));
  last exact: fdist_context_marginal.
apply: dmap_eq => w.
by rewrite (log_val_measure w Hops) Hs.
Qed.

(* ===================================================================== *)
(* The concrete log over a sample vs the abstract law                    *)
(* --------------------------------------------------------------------- *)
(* [measure_source_law] is about the population law.  An experimenter     *)
(* sees a finite sample, so here is the finite-sample counterpart: run    *)
(* the protocol on every unit of [us], tabulate the logged values, and    *)
(* you get back the abstract law -- PROVIDED the sample is representative *)
(* ([emp us = fdist_context P]).  That hypothesis is the honest form of   *)
(* "exhaustive": it says the sample already carries the right law, and it *)
(* is stated rather than assumed away.                                    *)
(*                                                                        *)
(* The work is done by [Prob.emp_map]: tabulating and then pushing        *)
(* through the protocol is the same as running the protocol on every unit *)
(* and then tabulating.  Everything is finite -- no limits anywhere.      *)
(* ===================================================================== *)

Theorem measure_source_empirical (te : texperiment dom) (n : Node G)
    (N : nat) (us : list (context dom))
    (Hus : size us = N.+1)
    (Hlog : size (map (fun w => log_val (elab_exp enc dec te) w n) us) = N.+1) :
  G_well_formed G = true ->
  contains_cycle G = false ->
  find_parents (ssval n) G = nil ->
  te_ops te = @TMeasure G dom n :: nil ->
  (forall u pa, (te_mech te : tgraphfun dom) n u pa = u) ->
  emp Hus = fdist_context P ->
  emp Hlog = P n.
Proof.
move=> Hwf Hcyc Hnp Hops Hecho Hrep.
rewrite (emp_map Hus Hlog) Hrep.
exact: measure_source_law.
Qed.

(* NEXT: the law of large numbers for this.  [Prob.sum_iidE] (the generic
   n-iid-copies sum, which infotheo only instantiates for one specific
   random variable) plus infotheo's [wlln] give a quantitative Chebyshev
   bound on the empirical frequency.  Blocked only on wiring the outcome
   indicator into [Ex]: [Ex] ranges over an [lmodType], and the [{RV P -> R}]
   phantom does not unify there without help. *)

End ExperimentLaw.

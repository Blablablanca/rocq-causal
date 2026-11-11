Set Warnings "-notation-overridden,-deprecated-library-file,-ambiguous-paths".
From HB Require Import structures.
From mathcomp Require Import all_ssreflect all_algebra finalg reals matrix.
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

(* the nodes a protocol measures, in program order.  These are the only
   nodes a run can produce data for, so they index the dataset below. *)
Fixpoint tmeasured (p : list toperation) : list (Node G) :=
  match p with
  | nil => nil
  | op :: rest =>
      match op with
      | TMeasure n => n :: tmeasured rest
      | _ => tmeasured rest
      end
  end.

(* --- the typed experiment --------------------------------------------- *)
(* Graph, domains and codes are fixed by the section; a typed experiment
   adds the labels, the typed mechanism, the typed protocol, and the SAMPLE
   SIZE it is run at.

   [te_size] is a hyperparameter, not data: it says how many units the
   protocol draws, never which ones.  That is what keeps it clear of D7.
   The field D7 removed was [sample : list raw_context] on
   [Main.experiment], which held the units themselves and served as the
   input LAW ("uniform over these"), so the same protocol over a second
   cohort was a different experiment.  A SIZE says nothing about who is in
   the study: the population stays [fdist_context P], which does not
   mention [te_size], and two cohorts of the same size give the SAME
   [texperiment].  What it does distinguish is N = 400 from N = 1000, which
   is the point of recording it -- a trial's sample size is pre-registered
   design, fixed before any data exists, exactly like the choice of which
   node to randomize.

   It lives on the TYPED record only.  [elab_exp] discards it, because the
   untyped semantics runs one unit at a time and has no notion of a sample
   at all; the size is consumed by the sample-level laws at the end of this
   file, where it sets the RATE of convergence. *)

Record texperiment : Type := mk_texperiment {
  te_labels : node -> Main.node_label;
  te_mech   : tgraphfun dom;
  te_ops    : list toperation;
  te_size   : nat;              (* how many units the protocol runs on *)
}.

(* n is a node this protocol measures -- a computable test, so on a concrete
   protocol the ticket below is discharged by [isT] *)
Definition is_measured (te : texperiment) (n : Node G) : bool :=
  n \in tmeasured (te_ops te).

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
   graph is a wf dag with treatments and responses, and reads are
   measurable. *)
Theorem elab_exp_wf (te : texperiment) :
  Main.wf_aug_graph (te_aug te) ->
  List.Forall (twf_operation (te_aug te)) (te_ops te) ->
  Main.experiment_wf (elab_exp te).
Proof.
move=> Hag Hops; split; first exact: Hag.
split; last exact: elab_compatible.
by apply: elab_ops_wf.
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
   mechanism reads only its own noise, [tF n u pa = g u].  The law of what
   gets logged is exactly the PUSHFORWARD of that node's noise law through
   its mechanism: what you put in is what you get out, modulo [g].

   [g] is arbitrary -- the mechanism need not be the identity, only
   parent-free.  [measure_source_law_echo] below is the [g = id] case.

   This is the end-to-end smoke test of the whole stack -- enc/dec,
   to_assign, find_value, eval, solve, run_unit_total, fdist_context --
   and it is an EXACT equality of laws, not a limit statement. *)
Theorem measure_source_law (te : texperiment dom) (n : Node G)
    (g : dom n -> dom n) :
  G_well_formed G = true ->
  contains_cycle G = false ->
  find_parents (ssval n) G = nil ->
  te_ops te = @TMeasure G dom n :: nil ->
  (forall u pa, (te_mech te : tgraphfun dom) n u pa = g u) ->
  fdist_log_val (elab_exp enc dec te) n = dmap g (P n).
Proof.
move=> Hwf Hcyc Hnp Hops Hmech.
have Hs : forall w0 : context dom, solve enc dec (te_mech te) w0 n = g (w0 n).
  by move=> w0; apply: solve_source.
rewrite /fdist_log_val -fdist_context_marginal dmap_comp.
apply: dmap_eq => w.
by rewrite /comp (log_val_measure w Hops) Hs.
Qed.

(* the original hello world: a pure echo logs the noise law untouched *)
Corollary measure_source_law_echo (te : texperiment dom) (n : Node G) :
  G_well_formed G = true ->
  contains_cycle G = false ->
  find_parents (ssval n) G = nil ->
  te_ops te = @TMeasure G dom n :: nil ->
  (forall u pa, (te_mech te : tgraphfun dom) n u pa = u) ->
  fdist_log_val (elab_exp enc dec te) n = P n.
Proof.
move=> Hwf Hcyc Hnp Hops Hecho.
rewrite (@measure_source_law te n id Hwf Hcyc Hnp Hops Hecho).
by rewrite /dmap fdistmap_id.
Qed.

(* ===================================================================== *)
(* Weak law of large numbers for the outcome                             *)
(* --------------------------------------------------------------------- *)
(* [measure_source_empirical_rV] (below) needs the sample to be EXACTLY   *)
(* representative.  A real sample never is, so the honest question is how *)
(* far off it can be.  Chebyshev answers it: for the indicator of a single *)
(* outcome value [v], the empirical frequency over N+1 INDEPENDENT units  *)
(* is within [eps] of the true probability [dmap g (P n) v] except with   *)
(* probability at most [V / ((N+1) eps^2)].                               *)
(*                                                                        *)
(* The bound is finite-N, not a limit -- which is what makes this         *)
(* provable here at all: [fdist] is finite-support only, so the infinite  *)
(* product space that almost-sure convergence needs is not expressible.   *)
(* A 1/N bound gives convergence in probability without mentioning one.   *)
(*                                                                        *)
(* Note the [R^o] ascriptions: [`E]/[`V] need the codomain seen through   *)
(* an lmodType, and [Ind]'s codomain [R] otherwise resolves via the       *)
(* realType route, which carries no module structure.  [R^o] is R as a    *)
(* module over itself, and it is what [wlln] unifies with.                *)
(* ===================================================================== *)

Local Open Scope proba_scope.
Local Open Scope ring_scope.
Import Num.Def.

(* the event "this unit's logged value is v" *)
Definition outcome_set (e : Main.experiment) (n : Node G) (v : dom n)
  : {set context dom} := [set w : context dom | log_val e w n == v].

(* its indicator's mean IS the outcome law -- this is where
   [measure_source_law] enters *)
Lemma E_outcome (te : texperiment dom) (n : Node G) (v : dom n)
    (g : dom n -> dom n) :
  G_well_formed G = true ->
  contains_cycle G = false ->
  find_parents (ssval n) G = nil ->
  te_ops te = @TMeasure G dom n :: nil ->
  (forall u pa, (te_mech te : tgraphfun dom) n u pa = g u) ->
  `E (Ind (@outcome_set (elab_exp enc dec te) n v)
      : {RV (fdist_context P) -> R^o}) = dmap g (P n) v.
Proof.
move=> Hwf Hcyc Hnp Hops Hmech.
rewrite E_Ind /Pr -(measure_source_law Hwf Hcyc Hnp Hops Hmech).
rewrite /fdist_log_val /dmap fdistmapE.
by apply: eq_bigl => w; rewrite !inE.
Qed.

Theorem measure_source_lln (te : texperiment dom) (n : Node G) (v : dom n)
    (g : dom n -> dom n) (N : nat) (eps : R) :
  G_well_formed G = true ->
  contains_cycle G = false ->
  find_parents (ssval n) G = nil ->
  te_ops te = @TMeasure G dom n :: nil ->
  (forall u pa, (te_mech te : tgraphfun dom) n u pa = g u) ->
  0 < eps ->
  `Pr[ (normr `o
        ((@sum_iid R (context dom) (fdist_context P) N.+1
            (Ind (@outcome_set (elab_exp enc dec te) n v)) `/ N.+1)
         `-cst (dmap g (P n) v))) >= eps ]
  <= `V (Ind (@outcome_set (elab_exp enc dec te) n v)
         : {RV (fdist_context P) -> R^o})
     / (N.+1%:R * eps ^+ 2).
Proof.
move=> Hwf Hcyc Hnp Hops Hmech Heps.
set Xv := Ind (@outcome_set (elab_exp enc dec te) n v).
apply: (@wlln _ _ _ _ (\row_(i < N.+1) Xv) (dmap g (P n) v) _ (`V Xv) _ _
               (sum_iidE N Xv) _ Heps).
- by move=> i; rewrite mxE /Xv (@E_outcome te n v g Hwf Hcyc Hnp Hops Hmech).
- by move=> i; rewrite mxE.
Qed.

(* ===================================================================== *)
(* The sample: one protocol, N units                                     *)
(* --------------------------------------------------------------------- *)
(* Everything above is per-unit.  [log_val] runs the protocol on ONE       *)
(* context, and the sample in [measure_source_lln] is anonymous -- it is   *)
(* only the domain of [sum_iid]'s random variable, named nowhere and       *)
(* connected to nothing.  This block names it.                            *)
(*                                                                        *)
(* A sample must be LENGTH-INDEXED; see the note at [Prob.emp_rV].  Hence  *)
(* [sample N], and hence a sample SIZE is a hyperparameter: it is needed   *)
(* to name the space the probability is on, before the statement exists.   *)
(*                                                                        *)
(* [fdist_sample] is where IID SAMPLING is assumed, and naming it puts two *)
(* independent assumptions side by side: [fdist_context] is a product over *)
(* NODES (UA2, a claim about the model), [`^ N] a product over UNITS (a    *)
(* claim about the design).  Both were previously implicit in the single   *)
(* step that reached for [sum_iid].                                       *)
(*                                                                        *)
(* [log_sample] is the payoff.  The protocol still contains exactly ONE    *)
(* [TMeasure n]; the [\row_i] runs that one-op program at each of the N    *)
(* units.  Measuring N units is not expressible by REPEATING the op --     *)
(* [run_unit_total] takes one context, so N copies of [TMeasure n] would   *)
(* log one unit's value N times -- which is why the sample belongs here,   *)
(* in the denotation, rather than in the op list.                         *)
(*                                                                        *)
(* Scope: [log_sample] is node n's COLUMN of the dataset.  The whole       *)
(* dataset -- every measured node at once -- still needs the finite log    *)
(* type that multi-[Measure] protocols are waiting on.                    *)
(* ===================================================================== *)

Local Open Scope vec_ext_scope.
Import GRing.Theory.

(* a SAMPLE of size N: N exogenous draws, length-indexed so it has a law *)
Definition sample (N : nat) := 'rV[context dom]_N.

Definition fdist_sample (N : nat) : R.-fdist (sample N) :=
  (fdist_context P) `^ N.

(* run the protocol ONCE, over the whole sample *)
Definition log_sample (e : Main.experiment) (n : Node G) (N : nat)
    (s : sample N) : 'rV[dom n]_N :=
  \row_i log_val e (s ``_ i) n.

(* the estimator an experimenter actually reports: the empirical frequency
   of the value [v] in the dataset, as a random variable OF THE SAMPLE *)
Definition emp_freq (e : Main.experiment) (n : Node G) (v : dom n) (N : nat)
  : {RV (fdist_sample N.+1) -> R^o} :=
  fun s => emp_rV (log_sample e n s) v.

(* THE EXACT-SAMPLE LAW.  [measure_source_law] is about the population law;
   an experimenter sees a finite sample, and this is the counterpart: run
   the protocol on every unit of [s], tabulate the logged values, and you
   get back the abstract law [dmap g (P n)] -- PROVIDED [s] is
   representative ([emp_rV s = fdist_context P]).  That is the honest form
   of "exhaustive": the sample already carries the right law, and the
   assumption is stated rather than assumed away.  All of it is finite --
   no limits anywhere.  The work is done by [Prob.emp_rV_map]: tabulating
   and then pushing through the protocol is the same as running the protocol
   on every unit and then tabulating.

   Note what is NOT a hypothesis.  No size proofs: the length is in the
   type.  And no [te_size] -- this conclusion quotes no rate, so the
   declared size has no business appearing in it, and a [te_size]
   hypothesis here would be one the proof never uses.

   CAVEAT, and the reason this is a warm-up rather than the result: the
   representativeness premise silently restricts [P] to rational values
   with denominator dividing N+1, because an empirical distribution can
   only land on that grid ([Prob.emp_rV_grid]).  Against an irrational
   truth it is vacuous.  [measure_source_emp_lln] below carries no such
   premise. *)
Theorem measure_source_empirical_rV (te : texperiment dom) (n : Node G)
    (g : dom n -> dom n) (N : nat) (s : sample N.+1) :
  G_well_formed G = true ->
  contains_cycle G = false ->
  find_parents (ssval n) G = nil ->
  te_ops te = @TMeasure G dom n :: nil ->
  (forall u pa, (te_mech te : tgraphfun dom) n u pa = g u) ->
  emp_rV s = fdist_context P ->
  emp_rV (log_sample (elab_exp enc dec te) n s) = dmap g (P n).
Proof.
move=> Hwf Hcyc Hnp Hops Hmech Hrep.
rewrite /log_sample (emp_rV_map (fun w => log_val (elab_exp enc dec te) w n)).
by rewrite Hrep; exact: measure_source_law.
Qed.

(* THE LAW OF LARGE NUMBERS, stated about the program's own output.  The
   protocol contains one [TMeasure n]; [emp_freq] is the frequency of [v]
   among the N+1 values it produced; and this says that frequency is within
   [eps] of the true probability [dmap g (P n) v] except with probability
   at most [V / (declared size * eps^2)].

   This is where [te_size] earns its keep: the PRE-REGISTERED sample size
   sets the rate.  Drop [Hsz] and the statement is false, because the bound
   would quote a size with no relation to the sample -- so the field is
   load-bearing here, not bookkeeping.

   The sample type is indexed by a free [N] rather than by [te_size te],
   with [Hsz] carrying the link propositionally.  Indexing it by [te_size
   te] would catch a size mismatch by typing, but [te_size te] is stuck on
   an abstract [te], so every use of a sample would carry a transport --
   the same cost D12 refused for graph-indexed operations.

   The proof is a rewrite: [emp_freq] IS [sum_iid]'s average, by
   [Prob.emp_rV_sum_iid], so [measure_source_lln] does all the work and no
   new probability theory is needed. *)
Theorem measure_source_emp_lln (te : texperiment dom) (n : Node G) (v : dom n)
    (g : dom n -> dom n) (N : nat) (eps : R) :
  G_well_formed G = true ->
  contains_cycle G = false ->
  find_parents (ssval n) G = nil ->
  te_ops te = @TMeasure G dom n :: nil ->
  (forall u pa, (te_mech te : tgraphfun dom) n u pa = g u) ->
  te_size te = N.+1 ->
  0 < eps ->
  `Pr[ (normr `o
        ((@emp_freq (elab_exp enc dec te) n v N)
         `-cst (dmap g (P n) v))) >= eps ]
  <= `V (Ind (@outcome_set (elab_exp enc dec te) n v)
         : {RV (fdist_context P) -> R^o})
     / ((te_size te)%:R * eps ^+ 2).
Proof.
move=> Hwf Hcyc Hnp Hops Hmech Hsz Heps.
have Hrv :
  (@emp_freq (elab_exp enc dec te) n v N)
  = ((@sum_iid R (context dom) (fdist_context P) N.+1
        (Ind (@outcome_set (elab_exp enc dec te) n v))) `/ N.+1).
  apply: boolp.funext => s.
  rewrite /emp_freq /log_sample.
  rewrite (emp_rV_sum_iid (fdist_context P)
             (fun w => log_val (elab_exp enc dec te) w n) v s).
  by rewrite /GRing.scale /= mulrC.
rewrite Hrv Hsz.
exact: measure_source_lln.
Qed.

(* ===================================================================== *)
(* THE SAME BOUND, FOR AN ARBITRARY PROTOCOL                              *)
(* --------------------------------------------------------------------- *)
(* [measure_source_emp_lln] above carries five structural hypotheses: the *)
(* graph is a dag, the measured node is a SOURCE, the protocol is exactly *)
(* one measurement, and that node's mechanism is [g].  They are all there *)
(* to identify the TARGET of the convergence, via [measure_source_law].   *)
(* None of them is needed by the probability.                            *)
(*                                                                        *)
(* Factoring them out gives the general statement: for ANY experiment and *)
(* ANY node, the empirical frequency of a logged value concentrates on    *)
(* [fdist_log_val], the population law of that same logged value.  The    *)
(* two semantics are compared at their own level of generality, and the   *)
(* protocol-specific work is pushed entirely into COMPUTING               *)
(* [fdist_log_val] for the protocol at hand -- which is what each worked  *)
(* example does.                                                          *)
(*                                                                        *)
(* The pivot is [E_outcome_any], which is [E_outcome] with the appeal to  *)
(* [measure_source_law] deleted: the mean of the indicator of the event   *)
(* that this unit logged v is the law of the logged value AT v, by        *)
(* unfolding alone.                                                      *)
(* This is the precise sense in which the empirical/population comparison *)
(* is independent of the experiment: the estimator's target is READ OFF   *)
(* the abstract semantics, not derived from the protocol.                *)
(* ===================================================================== *)

(* ELABORATION IGNORES THE DECLARED SIZE.  [te_size] is a hyperparameter
   of the protocol, not part of the model it elaborates to, so two records
   differing only in their declared size elaborate to the SAME experiment --
   by conversion, hence a one-line proof.  This is what lets a statement
   quantified over sample sizes keep its constants at a fixed index: the
   variance of an indicator of a logged value cannot depend on the declared
   size, because the experiment it is computed from does not. *)
Lemma elab_exp_size (labels : node -> Main.node_label) (F : tgraphfun dom)
    (ops : list (@toperation G dom)) (M M' : nat) :
  elab_exp enc dec (mk_texperiment labels F ops M)
  = elab_exp enc dec (mk_texperiment labels F ops M').
Proof. by []. Qed.

(* ===================================================================== *)
(* JOINT AND CONDITIONAL LOGGED LAWS                                      *)
(* --------------------------------------------------------------------- *)
(* [fdist_log_val] is one node's column law, and every result up to here  *)
(* is about one such marginal.  A causal query such as the outcome law in  *)
(* the arm X = x is not a marginal: it needs two columns of the SAME       *)
(* units, which is what [joint_at] provides on the data side.  This block  *)
(* is the population counterpart.                                         *)
(*                                                                        *)
(* No conditioning machinery is introduced.  infotheo's [cPr E F =         *)
(* Pr (E :&: F) / Pr F] already applies, because our events are sets of    *)
(* CONTEXTS -- one finType, one law [fdist_context P] -- so a conditional  *)
(* logged probability is a ratio of two unconditional ones and nothing     *)
(* more.  What has to be proved is only that the two unconditional ones    *)
(* are the joint and the marginal logged laws, which is [Pr_outcome] and   *)
(* [Pr_outcome_pair].  Both are true by unfolding: like                    *)
(* [E_outcome_any], they assume nothing about the experiment, the nodes,   *)
(* or the graph.                                                          *)
(*                                                                        *)
(* Positivity appears exactly once, in [cPr_outcome_eq], and it is a       *)
(* condition on the NUMBERS -- no well-formedness discipline can discharge *)
(* it.  That is why it is a hypothesis on the one lemma that divides,      *)
(* rather than a side condition baked into a conditional-distribution      *)
(* type.                                                                  *)
(* ===================================================================== *)

(* the joint law of two nodes' logged values, over the same unit *)
Definition fdist_log_pair (e : Main.experiment) (m n : Node G)
  : R.-fdist (dom m * dom n)%type :=
  dmap (fun w : context dom => (log_val e w m, log_val e w n)) (fdist_context P).

(* its marginals are the per-node logged laws *)
Lemma fdist_log_pair_fst (e : Main.experiment) (m n : Node G) :
  dmap (fun p : dom m * dom n => p.1) (fdist_log_pair e m n) = fdist_log_val e m.
Proof.
rewrite /fdist_log_pair /fdist_log_val dmap_comp; exact: dmap_eq.
Qed.

Lemma fdist_log_pair_snd (e : Main.experiment) (m n : Node G) :
  dmap (fun p : dom m * dom n => p.2) (fdist_log_pair e m n) = fdist_log_val e n.
Proof.
rewrite /fdist_log_pair /fdist_log_val dmap_comp; exact: dmap_eq.
Qed.

(* the mass of "this unit logged v at n" IS the logged law at v *)
Lemma Pr_outcome (e : Main.experiment) (n : Node G) (v : dom n) :
  Pr (fdist_context P) (@outcome_set e n v) = fdist_log_val e n v.
Proof.
rewrite /Pr /fdist_log_val /dmap fdistmapE.
by apply: eq_bigl => w; rewrite !inE.
Qed.

(* and the mass of the CELL "logged u at m and v at n" is the joint law *)
Lemma Pr_outcome_pair (e : Main.experiment) (m n : Node G)
    (u : dom m) (v : dom n) :
  Pr (fdist_context P) (@outcome_set e m u :&: @outcome_set e n v)
  = fdist_log_pair e m n (u, v).
Proof.
rewrite /Pr /fdist_log_pair /dmap fdistmapE.
by apply: eq_bigl => w; rewrite !inE xpair_eqE.
Qed.

(* THE CONDITIONAL LOGGED LAW, as a ratio.  Hypothesis-free: this is just
   [cPr]'s definition with the two masses named. *)
Lemma cPr_outcomeE (e : Main.experiment) (m n : Node G)
    (u : dom m) (v : dom n) :
  cPr (fdist_context P) (@outcome_set e n v) (@outcome_set e m u)
  = fdist_log_pair e m n (u, v) / fdist_log_val e m u.
Proof.
by rewrite /cPr setIC Pr_outcome_pair Pr_outcome.
Qed.

(* the mass a factorised joint puts on one cell: arm mass times the
   outcome mass that arm's kernel assigns *)
Lemma dbind_pair_cell (m n : Node G) (d : R.-fdist (dom m))
    (k : dom m -> R.-fdist (dom n)) (u : dom m) (v : dom n) :
  dbind d (fun a => dmap (fun b => (a, b)) (k a)) (u, v) = d u * k u v.
Proof.
rewrite /dbind fdistbindE (bigD1 u) //= big1; last first.
  move=> i Hiu; rewrite /dmap fdistmapE big_pred0 ?mulr0 // => b.
  by rewrite !inE xpair_eqE (negbTE Hiu).
rewrite addr0 /dmap fdistmapE (eq_bigl (fun a => a == v)); last first.
  by move=> a; rewrite !inE xpair_eqE eqxx.
by rewrite big_pred1_eq.
Qed.

(* ...and when the conditioning arm has positive mass, a factorised joint
   gives the conditional outright.  This is the shape every per-arm claim
   in the development will take: show the joint draws the arm and then
   draws the outcome from that arm kernel, and the conditional in arm u is
   the kernel at u.  The division is the only place positivity is used. *)
Lemma cPr_outcome_eq (e : Main.experiment) (m n : Node G)
    (u : dom m) (v : dom n) (k : dom m -> R.-fdist (dom n)) :
  fdist_log_val e m u != 0 ->
  fdist_log_pair e m n
  = dbind (fdist_log_val e m) (fun a => dmap (fun b => (a, b)) (k a)) ->
  cPr (fdist_context P) (@outcome_set e n v) (@outcome_set e m u) = k u v.
Proof.
move=> Hpos Hjoint; rewrite cPr_outcomeE Hjoint dbind_pair_cell.
by rewrite mulrAC (divff Hpos) mul1r.
Qed.

(* ===================================================================== *)
(* THE GENERAL PER-ARM FACTORISATION                                      *)
(* --------------------------------------------------------------------- *)
(* Everything above is general in the protocol.  This block is general in
   the MODEL: any well-formed acyclic graph, any mechanisms, any exogenous
   law, any two distinct nodes.  rct3's results become instances.

   Three facts carry it, and all three are already proved:
     [solve_randE]     randomizing a and solving = intervening at a's draw
     [solve_do_off]    setting a makes the solve ignore a's own slot
     [dmap_split_off]  so a's slot splits off the product law
   What is left is to read the two logged columns off the runner. *)

(* --- the two columns ---------------------------------------------------
   A [Measure] step leaves the mechanism family alone and only appends to
   the log, so both reads happen in the SAME randomized model.  The
   engine's first-match lookup is why the a column cannot shadow the n
   column. *)

Lemma log_val_rand_fst (te : texperiment dom) (a n : Node G)
    (w : context dom) :
  te_ops te = @TRandomize G dom a :: @TMeasure G dom a
                :: @TMeasure G dom n :: nil ->
  log_val (elab_exp enc dec te) w a = solve_rand enc dec (te_mech te) a w a.
Proof.
move=> Hops; rewrite /log_val /elab_exp /elab_ops Hops /= Nat.eqb_refl /=.
by rewrite /solve_rand.
Qed.

Lemma log_val_rand_snd (te : texperiment dom) (a n : Node G)
    (w : context dom) :
  te_ops te = @TRandomize G dom a :: @TMeasure G dom a
                :: @TMeasure G dom n :: nil ->
  log_val (elab_exp enc dec te) w n = solve_rand enc dec (te_mech te) a w n.
Proof.
move=> Hops.
(* [n = a] is not an exception: the log then carries a's entry twice, and
   first-match returns the first, whose value is the same one -- so the
   claim collapses to the first column. *)
have [Hna|Hna] := altP (n =P a).
  rewrite Hna in Hops *; exact: (@log_val_rand_fst te a a w Hops).
have Han : (ssval a =? ssval n) = false.
  apply/Nat.eqb_neq => E.
  by move/eqP: Hna; apply; exact: (esym (val_inj E)).
rewrite /log_val /elab_exp /elab_ops Hops /= Han Nat.eqb_refl /=.
by rewrite /solve_rand.
Qed.

(* the randomized column IS the coin: its law is a's own exogenous law,
   whatever the mechanism it displaced said *)
Lemma rand_full_fst_law (te : texperiment dom) (a n : Node G) :
  G_well_formed G = true -> contains_cycle G = false ->
  te_ops te = @TRandomize G dom a :: @TMeasure G dom a
                :: @TMeasure G dom n :: nil ->
  fdist_log_val (elab_exp enc dec te) a = P a.
Proof.
move=> Hwf Hcyc Hops; rewrite /fdist_log_val.
rewrite -(fdist_context_marginal P a); apply: dmap_eq => w.
rewrite (@log_val_rand_fst te a n w Hops).
exact: (solve_rand_self encK (te_mech te) a w Hwf Hcyc).
Qed.

(* THE THEOREM.  The pair the protocol logs is drawn by first drawing a's
   slot from its own law and then drawing n's value from the
   INTERVENTIONAL law at that value.  No positivity is needed: this is an
   identity of laws, not an estimate. *)
Theorem rand_full_joint (te : texperiment dom) (a n : Node G) :
  G_well_formed G = true -> contains_cycle G = false ->
  te_ops te = @TRandomize G dom a :: @TMeasure G dom a
                :: @TMeasure G dom n :: nil ->
  fdist_log_pair (elab_exp enc dec te) a n
  = dbind (P a) (fun x => dmap (fun y => (x, y))
                   (fdist_do enc dec (te_mech te) P a x n)).
Proof.
move=> Hwf Hcyc Hops.
have HF : forall (x : dom a) (w w' : context dom),
    (forall m : Node G, m != a -> w m = w' m) ->
    solve_do enc dec (te_mech te) a x w n
    = solve_do enc dec (te_mech te) a x w' n.
  by move=> x w w' Hoff; exact: (solve_do_off enc dec (te_mech te) x n Hoff).
rewrite /fdist_log_pair.
transitivity (dmap (fun w : context dom =>
    (w a, solve_do enc dec (te_mech te) a (w a) w n)) (fdist_context P)).
  apply: dmap_eq => w.
  rewrite (@log_val_rand_fst te a n w Hops) (@log_val_rand_snd te a n w Hops).
  rewrite (solve_rand_self encK (te_mech te) a w Hwf Hcyc).
  by rewrite (solve_randE enc dec (te_mech te) a w n Hwf Hcyc).
by rewrite (@dmap_split_off G dom R P a (dom n)
              (fun x w => solve_do enc dec (te_mech te) a x w n) HF).
Qed.

(* ...and therefore, in any arm the coin actually fills, conditioning on
   the recorded treatment gives the interventional law.  This is the
   general form of identification by randomization. *)
Corollary rand_full_cond (te : texperiment dom) (a n : Node G)
    (x : dom a) (y : dom n) :
  G_well_formed G = true -> contains_cycle G = false ->
  te_ops te = @TRandomize G dom a :: @TMeasure G dom a
                :: @TMeasure G dom n :: nil ->
  P a x != 0 ->
  cPr (fdist_context P)
      (@outcome_set (elab_exp enc dec te) n y)
      (@outcome_set (elab_exp enc dec te) a x)
  = fdist_do enc dec (te_mech te) P a x n y.
Proof.
move=> Hwf Hcyc Hops Hpos.
apply: (@cPr_outcome_eq (elab_exp enc dec te) a n x y
          (fun z => fdist_do enc dec (te_mech te) P a z n)).
- by rewrite (@rand_full_fst_law te a n Hwf Hcyc Hops).
- rewrite (@rand_full_joint te a n Hwf Hcyc Hops).
  by rewrite (@rand_full_fst_law te a n Hwf Hcyc Hops).
Qed.

(* ===================================================================== *)
(* MANY COLUMNS: "randomize a, then measure any list of nodes"            *)
(* --------------------------------------------------------------------- *)
(* A real trial does not log two columns.  It logs the treatment, the
   response, and every covariate, mediator and repeated reading the
   protocol asks for.  This block says that logging them breaks nothing
   and buys the JOINT: the whole table is drawn by flipping the
   randomizer's coin and then observing the ENTIRE measured list in a
   world where the treatment was forced to that value.

   The measured list carries no side conditions.  Its nodes need not be
   distinct, [a] itself may appear in it, the order is free, and no node
   need be a descendant of [a].  Duplicates are harmless because the
   engine's log read is first-match and every occurrence of a node carries
   the same evaluated value. *)

(* [\in] on a mathcomp seq, as dsep-core's [List.In] *)
Lemma mem_In (T : eqType) (x : T) (s : list T) : x \in s -> List.In x s.
Proof.
elim: s => [|y s IH] //; rewrite inE => /orP[/eqP->|/IH H]; [by left|by right].
Qed.

(* a measured list elaborates to the raw measures of its nodes' ids.
   Phrased over [map (elab_op _)] rather than [elab_ops] so it applies
   both before and after [elab_ops] is unfolded. *)
Lemma elab_measures (ns : list (Node G)) :
  map (elab_op enc) (map (@TMeasure G dom) ns)
  = map Main.Measure (map (fun m : Node G => ssval m) ns).
Proof. by elim: ns => [|m ns IH] //=; rewrite IH. Qed.

(* THE READING LEMMA.  Under "randomize a, then measure ns", every node of
   ns logs the value the RANDOMIZED model gives it.  This is the only
   place the runner is touched; everything after it is distribution
   algebra.  [Correctness.log_run_measures] carries the per-unit content:
   a [Measure] step leaves [cur_fun] alone, so a whole run of measures
   evaluates against the one randomized mechanism family, and first-match
   hands each node its own entry. *)
Lemma log_val_randomized (te : texperiment dom) (a n : Node G)
    (ns : list (Node G)) (w : context dom) :
  te_ops te = @TRandomize G dom a :: map (@TMeasure G dom) ns ->
  n \in ns ->
  log_val (elab_exp enc dec te) w n = solve_rand enc dec (te_mech te) a w n.
Proof.
move=> Hops Hn.
have Hin : List.In (ssval n) (map (fun m : Node G => ssval m) ns).
  by apply: List.in_map; apply: mem_In; exact: Hn.
rewrite /log_val /elab_exp /elab_ops Hops /= elab_measures.
rewrite (Correctness.log_run_measures _ _ _ _ _ Hin).
by rewrite /solve_rand.
Qed.

(* --- the table a unit produces ----------------------------------------
   One cell per measured POSITION, so the type is a dependent ffun over
   ['I_k] -- exactly as [context] is one over [Node G].  Indexing by
   position rather than by node is what lets the measured list repeat a
   node and still have a well-typed table.  Being a dependent ffun over a
   finType it is a finType, which is what [dmap_split_off] needs of its
   target. *)
Definition logrec (k : nat) (ms : k.-tuple (Node G)) : finType :=
  {dffun forall i : 'I_k, dom (tnth ms i)}.

(* the table unit [w] produces under [e] *)
Definition log_rec (e : Main.experiment) (k : nat) (ms : k.-tuple (Node G))
    (w : context dom) : logrec ms :=
  [ffun i => log_val e w (tnth ms i)].

(* the joint law of the arm column and the whole table *)
Definition fdist_log_arm_rec (e : Main.experiment) (a : Node G)
    (k : nat) (ms : k.-tuple (Node G)) : R.-fdist (dom a * logrec ms)%type :=
  dmap (fun w : context dom => (log_val e w a, log_rec e ms w))
       (fdist_context P).

(* the INTERVENTIONAL joint law of the measured list at [do(a := x)]:
   [fdist_do]'s many-node twin, built from the same [solve_do] *)
Definition fdist_do_rec (tF : tgraphfun dom) (a : Node G) (x : dom a)
    (k : nat) (ms : k.-tuple (Node G)) : R.-fdist (logrec ms) :=
  dmap (fun w : context dom =>
          [ffun i => solve_do enc dec tF a x w (tnth ms i)] : logrec ms)
       (fdist_context P).

(* THE MANY-COLUMN THEOREM.  The table the protocol logs is drawn by first
   drawing a's slot from its own law and then drawing the WHOLE table from
   the interventional joint at that value.  Same three facts as the
   two-column case -- [solve_randE], [solve_do_off], [dmap_split_off] --
   and no positivity: this is an identity of laws. *)
Theorem rand_many_joint (te : texperiment dom) (a : Node G)
    (k : nat) (ms : k.-tuple (Node G)) :
  G_well_formed G = true -> contains_cycle G = false ->
  te_ops te = @TRandomize G dom a :: @TMeasure G dom a
                :: map (@TMeasure G dom) ms ->
  fdist_log_arm_rec (elab_exp enc dec te) a ms
  = dbind (P a) (fun x => dmap (fun y => (x, y))
                   (fdist_do_rec (te_mech te) x ms)).
Proof.
move=> Hwf Hcyc Hops.
have HF : forall (x : dom a) (w w' : context dom),
    (forall m : Node G, m != a -> w m = w' m) ->
    ([ffun i : 'I_k => solve_do enc dec (te_mech te) a x w (tnth ms i)]
       : logrec ms)
    = [ffun i : 'I_k => solve_do enc dec (te_mech te) a x w' (tnth ms i)].
  move=> x w w' Hoff; apply/ffunP => i; rewrite !ffunE.
  exact: (solve_do_off enc dec (te_mech te) x (tnth ms i) Hoff).
rewrite /fdist_log_arm_rec.
transitivity (dmap (fun w : context dom =>
    (w a, ([ffun i : 'I_k =>
              solve_do enc dec (te_mech te) a (w a) w (tnth ms i)]
             : logrec ms))) (fdist_context P)).
  apply: dmap_eq => w.
  rewrite (@log_val_randomized te a a (a :: ms) w Hops (mem_head a ms)).
  rewrite (solve_rand_self encK (te_mech te) a w Hwf Hcyc).
  congr (_, _); apply/ffunP => i; rewrite /log_rec !ffunE.
  rewrite (@log_val_randomized te a (tnth ms i) (a :: ms) w Hops);
    last by rewrite inE mem_tnth orbT.
  by rewrite (solve_randE enc dec (te_mech te) a w (tnth ms i) Hwf Hcyc).
rewrite /fdist_do_rec.
by rewrite (@dmap_split_off G dom R P a (logrec ms)
   (fun x w => [ffun i : 'I_k =>
                  solve_do enc dec (te_mech te) a x w (tnth ms i)]) HF).
Qed.

(* --- generic observables ----------------------------------------------
   [outcome_set] and [cPr_outcome_eq] are phrased for ONE node's column.
   The algebra they package never looks at what the column is, only that
   it is something computed from a unit, and the many-column table is
   another such thing.  So the generic form below is what makes the table
   reachable at all; the column versions are its instances. *)

Definition obs_set (B : finType) (f : context dom -> B) (u : B)
  : {set context dom} := [set w : context dom | f w == u].

Lemma obs_set_outcome (e : Main.experiment) (n : Node G) (v : dom n) :
  obs_set (fun w : context dom => log_val e w n) v = @outcome_set e n v.
Proof. by apply/setP => w; rewrite !inE. Qed.

Lemma Pr_obs (B : finType) (f : context dom -> B) (u : B) :
  Pr (fdist_context P) (@obs_set B f u) = dmap f (fdist_context P) u.
Proof.
rewrite /Pr /dmap fdistmapE.
by apply: eq_bigl => w; rewrite !inE.
Qed.

Lemma Pr_obs_pair (B C : finType) (f : context dom -> B) (g : context dom -> C)
    (u : B) (v : C) :
  Pr (fdist_context P) (@obs_set B f u :&: @obs_set C g v)
  = dmap (fun w : context dom => (f w, g w)) (fdist_context P) (u, v).
Proof.
rewrite /Pr /dmap fdistmapE.
by apply: eq_bigl => w; rewrite !inE xpair_eqE.
Qed.

Lemma cPr_obsE (B C : finType) (f : context dom -> B) (g : context dom -> C)
    (u : B) (v : C) :
  cPr (fdist_context P) (@obs_set C g v) (@obs_set B f u)
  = dmap (fun w : context dom => (f w, g w)) (fdist_context P) (u, v)
    / dmap f (fdist_context P) u.
Proof. by rewrite /cPr setIC Pr_obs_pair Pr_obs. Qed.

(* the generic per-arm factorisation: a joint that draws [f] and then
   draws [g] from a kernel has that kernel as its conditional.  The
   division is the only place positivity is used. *)
Lemma cPr_obs_eq (B C : finType) (f : context dom -> B) (g : context dom -> C)
    (u : B) (v : C) (k : B -> R.-fdist C) :
  dmap f (fdist_context P) u != 0 ->
  dmap (fun w : context dom => (f w, g w)) (fdist_context P)
  = dbind (dmap f (fdist_context P)) (fun b => dmap (fun c => (b, c)) (k b)) ->
  cPr (fdist_context P) (@obs_set C g v) (@obs_set B f u) = k u v.
Proof.
move=> Hpos Hjoint; rewrite cPr_obsE Hjoint dbind_pair_cell_gen.
by rewrite mulrAC (divff Hpos) mul1r.
Qed.

(* --- identification, many columns ------------------------------------- *)

(* the event "this unit's whole table is y" *)
Definition record_set (e : Main.experiment) (k : nat) (ms : k.-tuple (Node G))
    (y : logrec ms) : {set context dom} := obs_set (log_rec e ms) y.

(* the arm column is still the coin, however many columns follow it *)
Lemma rand_many_fst_law (te : texperiment dom) (a : Node G)
    (k : nat) (ms : k.-tuple (Node G)) :
  G_well_formed G = true -> contains_cycle G = false ->
  te_ops te = @TRandomize G dom a :: @TMeasure G dom a
                :: map (@TMeasure G dom) ms ->
  fdist_log_val (elab_exp enc dec te) a = P a.
Proof.
move=> Hwf Hcyc Hops; rewrite /fdist_log_val.
rewrite -(fdist_context_marginal P a); apply: dmap_eq => w.
rewrite (@log_val_randomized te a a (a :: ms) w Hops (mem_head a ms)).
exact: (solve_rand_self encK (te_mech te) a w Hwf Hcyc).
Qed.

(* ...so in any arm the coin actually fills, conditioning on the recorded
   treatment gives the INTERVENTIONAL JOINT over everything measured.
   Not one outcome marginal at a time: the whole table at once, which is
   what licenses any quantity computed from it. *)
Corollary rand_many_cond (te : texperiment dom) (a : Node G)
    (k : nat) (ms : k.-tuple (Node G)) (x : dom a) (y : logrec ms) :
  G_well_formed G = true -> contains_cycle G = false ->
  te_ops te = @TRandomize G dom a :: @TMeasure G dom a
                :: map (@TMeasure G dom) ms ->
  P a x != 0 ->
  cPr (fdist_context P) (@record_set (elab_exp enc dec te) k ms y)
                        (@outcome_set (elab_exp enc dec te) a x)
  = fdist_do_rec (te_mech te) x ms y.
Proof.
move=> Hwf Hcyc Hops Hpos.
rewrite /record_set -obs_set_outcome.
apply: (@cPr_obs_eq (dom a) (logrec ms)
          (fun w : context dom => log_val (elab_exp enc dec te) w a)
          (log_rec (elab_exp enc dec te) ms) x y
          (fun z => fdist_do_rec (te_mech te) z ms)).
- by rewrite -/(fdist_log_val _ a) (@rand_many_fst_law te a k ms Hwf Hcyc Hops).
- rewrite -/(fdist_log_arm_rec _ a ms)
          (@rand_many_joint te a k ms Hwf Hcyc Hops).
  by rewrite -/(fdist_log_val _ a) (@rand_many_fst_law te a k ms Hwf Hcyc Hops).
Qed.

(* --- one column at a time: adding columns cannot break identification --
   The many-column protocol still factorises against ANY ONE of its
   columns.  That is the precise sense in which logging covariates is
   free: the two-column conclusion is unchanged by the extra columns
   standing next to it.  Same proof as the two-column case, with
   [log_val_randomized] in place of the two hand-rolled reads -- which is
   why [rand_full_joint] is now an instance (checked just below). *)
Theorem rand_many_pair (te : texperiment dom) (a n : Node G)
    (k : nat) (ms : k.-tuple (Node G)) :
  G_well_formed G = true -> contains_cycle G = false ->
  te_ops te = @TRandomize G dom a :: @TMeasure G dom a
                :: map (@TMeasure G dom) ms ->
  n \in a :: ms ->
  fdist_log_pair (elab_exp enc dec te) a n
  = dbind (P a) (fun x => dmap (fun y => (x, y))
                   (fdist_do enc dec (te_mech te) P a x n)).
Proof.
move=> Hwf Hcyc Hops Hn.
have HF : forall (x : dom a) (w w' : context dom),
    (forall m : Node G, m != a -> w m = w' m) ->
    solve_do enc dec (te_mech te) a x w n
    = solve_do enc dec (te_mech te) a x w' n.
  by move=> x w w' Hoff; exact: (solve_do_off enc dec (te_mech te) x n Hoff).
rewrite /fdist_log_pair.
transitivity (dmap (fun w : context dom =>
    (w a, solve_do enc dec (te_mech te) a (w a) w n)) (fdist_context P)).
  apply: dmap_eq => w.
  rewrite (@log_val_randomized te a a (a :: ms) w Hops (mem_head a ms)).
  rewrite (@log_val_randomized te a n (a :: ms) w Hops Hn).
  rewrite (solve_rand_self encK (te_mech te) a w Hwf Hcyc).
  by rewrite (solve_randE enc dec (te_mech te) a w n Hwf Hcyc).
by rewrite (@dmap_split_off G dom R P a (dom n)
              (fun x w => solve_do enc dec (te_mech te) a x w n) HF).
Qed.

(* ...so every single column of the table, read on its own, still gives
   the interventional MARGINAL inside each arm *)
Corollary rand_many_cond_col (te : texperiment dom) (a n : Node G)
    (k : nat) (ms : k.-tuple (Node G)) (x : dom a) (v : dom n) :
  G_well_formed G = true -> contains_cycle G = false ->
  te_ops te = @TRandomize G dom a :: @TMeasure G dom a
                :: map (@TMeasure G dom) ms ->
  n \in a :: ms -> P a x != 0 ->
  cPr (fdist_context P)
      (@outcome_set (elab_exp enc dec te) n v)
      (@outcome_set (elab_exp enc dec te) a x)
  = fdist_do enc dec (te_mech te) P a x n v.
Proof.
move=> Hwf Hcyc Hops Hn Hpos.
apply: (@cPr_outcome_eq (elab_exp enc dec te) a n x v
          (fun z => fdist_do enc dec (te_mech te) P a z n)).
- by rewrite (@rand_many_fst_law te a k ms Hwf Hcyc Hops).
- rewrite (@rand_many_pair te a n k ms Hwf Hcyc Hops Hn).
  by rewrite (@rand_many_fst_law te a k ms Hwf Hcyc Hops).
Qed.

(* SUBSUMPTION.  [rand_full_joint]'s statement, re-derived from the
   many-column theorem at the one-element list.  Nothing was deleted --
   the two-column proof stays on record -- but this says the general
   result really does cover it, rather than merely resembling it. *)
Example rand_full_joint_is_many (te : texperiment dom) (a n : Node G) :
  G_well_formed G = true -> contains_cycle G = false ->
  te_ops te = @TRandomize G dom a :: @TMeasure G dom a
                :: @TMeasure G dom n :: nil ->
  fdist_log_pair (elab_exp enc dec te) a n
  = dbind (P a) (fun x => dmap (fun y => (x, y))
                   (fdist_do enc dec (te_mech te) P a x n)).
Proof.
move=> Hwf Hcyc Hops.
apply: (@rand_many_pair te a n _ (in_tuple (n :: nil))).
- exact: Hwf.
- exact: Hcyc.
- exact: Hops.
- by rewrite inE mem_head orbT.
Qed.


(* ===================================================================== *)
(* CONCENTRATION FOR AN ARBITRARY EVENT ABOUT A UNIT                      *)
(* --------------------------------------------------------------------- *)
(* [measure_lln_any] below is indexed by a node and a value, but its      *)
(* proof never uses what [outcome_set e n v] IS -- only that it is a set  *)
(* of contexts whose mass is the target.  So the indexing is about naming *)
(* the event, exactly as the five structural hypotheses it already shed   *)
(* were about naming the target.  Strip it too and the statement covers   *)
(* every event an experimenter can tabulate from a unit's log:            *)
(*                                                                        *)
(*   - one cell of one column,    [outcome_set e n v]                     *)
(*   - the ARM of a trial,        [outcome_set e X x]                     *)
(*   - a CELL OF THE JOINT,       [outcome_set e X x :&: outcome_set e Y y]*)
(*                                                                        *)
(* The last two are what a per-arm or conditional estimate is built from,  *)
(* and they are not of the form "node n logged v", so the general form is  *)
(* what makes them reachable at all.  [emp_freq] is recovered as the       *)
(* instance [A := outcome_set e n v], so nothing is lost.                 *)
(* ===================================================================== *)

(* the fraction of the sample's units lying in A: the estimator for any
   tabulated event, and definitionally the scaled i.i.d. sum *)
Definition emp_event (A : {set context dom}) (N : nat)
  : {RV (fdist_sample N.+1) -> R^o} :=
  (@sum_iid R (context dom) (fdist_context P) N.+1 (Ind A)) `/ N.+1.

(* THE WEAK LAW, with nothing named but the event.  [E_Ind] replaces
   [E_outcome_any]: the mean of an indicator is the mass of its event, and
   that is the whole structural input. *)
Theorem emp_event_lln (A : {set context dom}) (N : nat) (eps : R) :
  0 < eps ->
  `Pr[ (normr `o ((@emp_event A N) `-cst (Pr (fdist_context P) A))) >= eps ]
  <= `V (Ind A : {RV (fdist_context P) -> R^o}) / (N.+1%:R * eps ^+ 2).
Proof.
move=> Heps.
set XA := Ind A.
apply: (@wlln _ _ _ _ (\row_(i < N.+1) XA) (Pr (fdist_context P) A) _ (`V XA)
               _ _ (sum_iidE N XA) _ Heps).
- by move=> i; rewrite mxE /XA E_Ind.
- by move=> i; rewrite mxE.
Qed.

(* --- and the node-and-value form as an instance ----------------------- *)

Lemma E_outcome_any (e : Main.experiment) (n : Node G) (v : dom n) :
  `E (Ind (@outcome_set e n v) : {RV (fdist_context P) -> R^o})
  = fdist_log_val e n v.
Proof. by rewrite E_Ind Pr_outcome. Qed.

(* [emp_freq], the per-column estimator, IS [emp_event] at that column's
   cell -- so every event-level result above applies to it *)
Lemma emp_freqE (e : Main.experiment) (n : Node G) (v : dom n) (N : nat) :
  @emp_freq e n v N = @emp_event (@outcome_set e n v) N.
Proof.
apply: boolp.funext => s.
rewrite /emp_freq /log_sample.
rewrite (emp_rV_sum_iid (fdist_context P) (fun w => log_val e w n) v s).
by rewrite /emp_event /GRing.scale /= mulrC.
Qed.

(* the sample-mean form, hypothesis-free *)
Theorem measure_lln_any (e : Main.experiment) (n : Node G) (v : dom n)
    (N : nat) (eps : R) :
  0 < eps ->
  `Pr[ (normr `o
        ((@sum_iid R (context dom) (fdist_context P) N.+1
            (Ind (@outcome_set e n v)) `/ N.+1)
         `-cst (fdist_log_val e n v))) >= eps ]
  <= `V (Ind (@outcome_set e n v) : {RV (fdist_context P) -> R^o})
     / (N.+1%:R * eps ^+ 2).
Proof.
move=> Heps; rewrite -Pr_outcome.
exact: (emp_event_lln (@outcome_set e n v) N Heps).
Qed.

(* THE EXPERIMENT-LEVEL COMPARISON.  The empirical frequency that an
   experimenter reports from a run of [e] on [N+1] units is within [eps] of
   the population law of the same logged value, except on an event of
   probability at most [V / ((N+1) eps^2)].  No hypothesis on [e], on [n],
   or even on the graph: this is the concrete semantics meeting the
   abstract one, with nothing about the protocol assumed. *)
Theorem emp_lln_any (e : Main.experiment) (n : Node G) (v : dom n)
    (N : nat) (eps : R) :
  0 < eps ->
  `Pr[ (normr `o ((@emp_freq e n v N) `-cst (fdist_log_val e n v))) >= eps ]
  <= `V (Ind (@outcome_set e n v) : {RV (fdist_context P) -> R^o})
     / (N.+1%:R * eps ^+ 2).
Proof.
move=> Heps; rewrite emp_freqE -Pr_outcome.
exact: (emp_event_lln (@outcome_set e n v) N Heps).
Qed.


(* ===================================================================== *)
(* THE CONDITIONAL ESTIMATOR                                              *)
(* --------------------------------------------------------------------- *)
(* [emp_cond A B] is the number an experimenter reports when asked for a  *)
(* conditional frequency: among the units in B, the fraction also in A.    *)
(* It is a quotient of two [emp_event]s, so both halves are i.i.d.         *)
(* averages that [emp_event_lln] already controls, and the division is     *)
(* paid for separately by [ratio_close] -- which is the point of that      *)
(* formulation, since conditioning itself would break the i.i.d.           *)
(* structure (the number of units in B is random).                         *)
(*                                                                        *)
(* Positivity of the conditioning event is needed and is exactly OVERLAP:  *)
(* an arm no unit was assigned to has nothing to condition on.  Note what  *)
(* it is NOT needed for -- the population conditional [cPr] is defined     *)
(* regardless, and so is an interventional law (see [Prob.fdist_do]).      *)
(* Overlap is about ESTIMATING a conditional, not about its existence.     *)
(* ===================================================================== *)

Import Order.TTheory Num.Theory.

(* applying a pointwise-subtracted random variable.  True by conversion;
   named only so that [rewrite] can use it, since unification will not
   unfold the function-space ring on its own. *)
Lemma trans_sub_RV_appE (U : finType) (d : R.-fdist U)
    (X : {RV d -> R^o}) (m : R) (u : U) :
  (X `-cst m) u = X u - m.
Proof. by []. Qed.

Definition emp_cond (A B : {set context dom}) (N : nat)
  : {RV (fdist_sample N.+1) -> R^o} :=
  fun s => @emp_event (A :&: B) N s / @emp_event B N s.

(* CHEBYSHEV FOR THE QUOTIENT.  If both halves are within [del] of their
   targets then the quotient is within [4*del/Pr B] of [cPr]; so the event
   that the quotient is OFF by [eps] is contained in the union of the two
   events that a half is off by [del], and a union bound finishes it. *)
Theorem emp_cond_bound (A B : {set context dom}) (N : nat) (eps del : R) :
  0 < del -> 2 * del <= Pr (fdist_context P) B ->
  4 * del / Pr (fdist_context P) B < eps ->
  `Pr[ (normr `o ((@emp_cond A B N) `-cst (cPr (fdist_context P) A B)))
       >= eps ]
  <= `V (Ind (A :&: B) : {RV (fdist_context P) -> R^o}) / (N.+1%:R * del ^+ 2)
   + `V (Ind B : {RV (fdist_context P) -> R^o}) / (N.+1%:R * del ^+ 2).
Proof.
move=> Hdel Hdb Heps.
have Hb : 0 < Pr (fdist_context P) B
  by apply: lt_le_trans Hdb; rewrite mulr_gt0.
have Hab : Pr (fdist_context P) (A :&: B) <= Pr (fdist_context P) B
  by apply: subset_Pr; exact: subsetIr.
have Ha0 : 0 <= Pr (fdist_context P) (A :&: B) by exact: Pr_ge0.
apply: le_trans (_ : Pr (fdist_sample N.+1)
     ([set s | del <= `|@emp_event (A :&: B) N s
                        - Pr (fdist_context P) (A :&: B)|]
      :|: [set s | del <= `|@emp_event B N s - Pr (fdist_context P) B|])
     <= _).
  apply: subset_Pr; apply/subsetP => s.
  rewrite !inE /comp_RV trans_sub_RV_appE => Hs.
  apply/orP.
  have [H1|H1] := lerP del `|@emp_event (A :&: B) N s
                             - Pr (fdist_context P) (A :&: B)|;
    first by left.
  have [H2|H2] := lerP del `|@emp_event B N s - Pr (fdist_context P) B|;
    first by right.
  move: Hs; rewrite leNgt => /negP []; apply: le_lt_trans Heps.
  rewrite /emp_cond /cPr.
  exact: (ratio_close Ha0 Hab Hb Hdb (ltW H1) (ltW H2)).
apply: (le_trans (le_Pr_setU _ _ _)).
by apply: lerD; [exact: (emp_event_lln (A :&: B) N Hdel)
                | exact: (emp_event_lln B N Hdel)].
Qed.

(* CONVERGENCE OF THE CONDITIONAL ESTIMATOR.  For any tolerance and any
   confidence there is a sample size beyond which the reported conditional
   frequency is within [eps] of the population conditional with probability
   at least [1 - delta].  The [del] that does the work is
   [min (Pr B / 2) (eps * Pr B / 8)]: the first argument keeps the
   estimated denominator away from zero, the second makes the quotient
   bound beat [eps]. *)
Corollary emp_cond_converges (A B : {set context dom}) (eps delta : R) :
  0 < eps -> 0 < delta -> 0 < Pr (fdist_context P) B ->
  exists N0 : nat, forall N : nat, (N0 <= N)%N ->
    `Pr[ (normr `o ((@emp_cond A B N) `-cst (cPr (fdist_context P) A B)))
         >= eps ]
    <= delta.
Proof.
move=> Heps Hdelta Hb.
set b := Pr (fdist_context P) B.
set del := Order.min (b / 2) (eps * b / 8).
have H2 : (0 : R) < 2 by rewrite ltr0n.
have H8 : (0 : R) < 8 by rewrite ltr0n.
have Hdel : 0 < del.
  rewrite lt_min; apply/andP; split; first exact: (divr_gt0 Hb H2).
  exact: (divr_gt0 (mulr_gt0 Heps Hb) H8).
have Hdb : 2 * del <= b.
  rewrite mulrC -ler_pdivlMr //; by rewrite ge_min lexx.
have Hq : 4 * del / b < eps.
  apply: le_lt_trans (_ : 4 * (eps * b / 8) / b < eps).
    apply: ler_wpM2r; first by rewrite invr_ge0 ltW.
    apply: ler_wpM2l; first by rewrite ler0n.
    by rewrite ge_min lexx orbT.
  have Hb0 : b != 0 by rewrite gt_eqF.
  rewrite quarter_of_eighth mulrAC (mulfK Hb0).
  by rewrite ltr_pdivrMr // ltr_pMr // ltr1n.
set C := `V (Ind (A :&: B) : {RV (fdist_context P) -> R^o})
       + `V (Ind B : {RV (fdist_context P) -> R^o}).
have Hpos : 0 < delta * del ^+ 2 by rewrite mulr_gt0 // exprn_gt0.
exists (truncn (C / (delta * del ^+ 2))) => N HN.
apply: (le_trans (@emp_cond_bound A B N eps del Hdel Hdb Hq)).
rewrite -mulrDl -/C.
have Hx : C / (delta * del ^+ 2) < N.+1%:R.
  apply: (lt_le_trans (truncnS_gt _)).
  by rewrite ler_nat ltnS.
move: Hx; rewrite ltr_pdivrMr // => Hlt.
rewrite ler_pdivrMr; last by rewrite mulr_gt0 // exprn_gt0.
by rewrite mulrCA; exact: ltW.
Qed.

(* ===================================================================== *)
(* UNIFORM OVER A FAMILY: THE REPORTED DISTRIBUTION                      *)
(* --------------------------------------------------------------------- *)
(* Everything above is per VALUE.  The [N0] of [emp_cond_converges]       *)
(* depends on which value is asked about, so the per-value statements do  *)
(* not add up to "the reported conditional DISTRIBUTION is close to the   *)
(* target" -- that needs one sample size good for every value at once.    *)
(*                                                                       *)
(* Boole's inequality closes the gap, and cheaply, for a reason worth     *)
(* naming: the [del] that [emp_cond_bound] runs on is                     *)
(* [min (Pr B / 2) (eps * Pr B / 8)], which depends only on the           *)
(* CONDITIONING event and [eps] -- not on which member of the family is   *)
(* being estimated.  So one [del] and one [N0] serve the whole family,    *)
(* and the only price is that the variances add.                         *)
(*                                                                       *)
(* The target is a parameter here rather than [cPr] itself, with the      *)
(* identification supplied as a hypothesis.  That is the same shape       *)
(* [cPr_outcome_eq] takes, and it is what lets a caller state the         *)
(* conclusion about an INTERVENTIONAL law: the estimator converges to     *)
(* whatever the conditional has been proved equal to.                     *)
(* ===================================================================== *)

(* the event that the family member [A] is misreported by [eps], against
   a target [theta] the caller names *)
Definition cond_off (A B : {set context dom}) (N : nat) (theta eps : R)
  : {set sample N.+1} :=
  [set s | eps <= `|@emp_cond A B N s - theta|].

(* [pr_geq] of the deviation IS the mass of that set; the two differ only
   by the RV combinators, which do not reduce under unification *)
Lemma pr_cond_off (A B : {set context dom}) (N : nat) (theta eps : R) :
  `Pr[ (normr `o ((@emp_cond A B N) `-cst theta)) >= eps ]
  = Pr (fdist_sample N.+1) (@cond_off A B N theta eps).
Proof.
rewrite /pr_geq /cond_off /Pr; apply: eq_bigl => s.
by rewrite !inE /comp_RV trans_sub_RV_appE.
Qed.

(* CHEBYSHEV FOR THE WHOLE FAMILY.  One [del], so one bound; the sum is
   over the family and the conditioning variance is paid once per member. *)
Theorem emp_cond_bound_fam (I : finType) (Af : I -> {set context dom})
    (B : {set context dom}) (N : nat) (eps del : R) :
  0 < del -> 2 * del <= Pr (fdist_context P) B ->
  4 * del / Pr (fdist_context P) B < eps ->
  Pr (fdist_sample N.+1)
     (\bigcup_(i : I) @cond_off (Af i) B N (cPr (fdist_context P) (Af i) B) eps)
  <= (\sum_(i : I) (`V (Ind (Af i :&: B) : {RV (fdist_context P) -> R^o})
                    + `V (Ind B : {RV (fdist_context P) -> R^o})))
     / (N.+1%:R * del ^+ 2).
Proof.
move=> Hdel Hdb Heps.
apply: (le_trans (Pr_bigcup _ _ _)).
rewrite mulr_suml; apply: ler_sum => i _.
rewrite mulrDl -pr_cond_off.
exact: (@emp_cond_bound (Af i) B N eps del Hdel Hdb Heps).
Qed.

(* ...and the eps-delta form: with confidence [1 - delta], EVERY member of
   the family is reported within [eps] of its target, from one sample
   size on.  This is the statement that says a reported conditional
   DISTRIBUTION is close, rather than one of its values. *)
Corollary emp_cond_converges_fam (I : finType) (Af : I -> {set context dom})
    (B : {set context dom}) (th : I -> R) (eps delta : R) :
  0 < eps -> 0 < delta -> 0 < Pr (fdist_context P) B ->
  (forall i : I, th i = cPr (fdist_context P) (Af i) B) ->
  exists N0 : nat, forall N : nat, (N0 <= N)%N ->
    Pr (fdist_sample N.+1)
       (\bigcup_(i : I) @cond_off (Af i) B N (th i) eps) <= delta.
Proof.
move=> Heps Hdelta Hb Hth.
have Hset : forall M : nat,
    \bigcup_(i : I) @cond_off (Af i) B M (th i) eps
    = \bigcup_(i : I) @cond_off (Af i) B M
        (cPr (fdist_context P) (Af i) B) eps.
  by move=> M; apply: eq_bigr => i _; rewrite Hth.
set b := Pr (fdist_context P) B.
set del := Order.min (b / 2) (eps * b / 8).
have H2 : (0 : R) < 2 by rewrite ltr0n.
have H8 : (0 : R) < 8 by rewrite ltr0n.
have Hdel : 0 < del.
  rewrite lt_min; apply/andP; split; first exact: (divr_gt0 Hb H2).
  exact: (divr_gt0 (mulr_gt0 Heps Hb) H8).
have Hdb : 2 * del <= b.
  rewrite mulrC -ler_pdivlMr //; by rewrite ge_min lexx.
have Hq : 4 * del / b < eps.
  apply: le_lt_trans (_ : 4 * (eps * b / 8) / b < eps).
    apply: ler_wpM2r; first by rewrite invr_ge0 ltW.
    apply: ler_wpM2l; first by rewrite ler0n.
    by rewrite ge_min lexx orbT.
  have Hb0 : b != 0 by rewrite gt_eqF.
  rewrite quarter_of_eighth mulrAC (mulfK Hb0).
  by rewrite ltr_pdivrMr // ltr_pMr // ltr1n.
set C := \sum_(i : I) (`V (Ind (Af i :&: B) : {RV (fdist_context P) -> R^o})
                       + `V (Ind B : {RV (fdist_context P) -> R^o})).
have Hpos : 0 < delta * del ^+ 2 by rewrite mulr_gt0 // exprn_gt0.
exists (truncn (C / (delta * del ^+ 2))) => N HN.
rewrite Hset.
apply: (le_trans (@emp_cond_bound_fam I Af B N eps del Hdel Hdb Hq)).
rewrite -/C.
have Hx : C / (delta * del ^+ 2) < N.+1%:R.
  apply: (lt_le_trans (truncnS_gt _)).
  by rewrite ler_nat ltnS.
move: Hx; rewrite ltr_pdivrMr // => Hlt.
rewrite ler_pdivrMr; last by rewrite mulr_gt0 // exprn_gt0.
by rewrite mulrCA; exact: ltW.
Qed.

(* ===================================================================== *)
(* THE GENERAL CHAIN, END TO END                                          *)
(* --------------------------------------------------------------------- *)
(* [rand_full_cond] identifies the per-arm conditional with the
   interventional law for EVERY well-formed acyclic model; the two
   concentration results above are already general in the events.  So the
   composition needs no new probability: what a trial reports in an arm
   converges to P(n = y | do(a := x)), in any model.

   Note what replaces rct3's declared-size bookkeeping: there [e3] had to
   be pinned at size 1 so the events stayed fixed while N was quantified,
   because the protocol [te_rct3_full N] mentioned N.  Here [te] is a
   parameter, so its elaboration is one fixed term and the question does
   not arise. *)

Theorem rand_full_emp_cond_converges (te : texperiment dom) (a n : Node G)
    (x : dom a) (y : dom n) (eps delta : R) :
  G_well_formed G = true -> contains_cycle G = false ->
  te_ops te = @TRandomize G dom a :: @TMeasure G dom a
                :: @TMeasure G dom n :: nil ->
  0 < eps -> 0 < delta -> 0 < P a x ->
  exists N0 : nat, forall N : nat, (N0 <= N)%N ->
    `Pr[ (normr `o ((@emp_cond
              (@outcome_set (elab_exp enc dec te) n y)
              (@outcome_set (elab_exp enc dec te) a x) N)
           `-cst (fdist_do enc dec (te_mech te) P a x n y))) >= eps ]
    <= delta.
Proof.
move=> Hwf Hcyc Hops Heps Hdelta Hx.
have HB : Pr (fdist_context P) (@outcome_set (elab_exp enc dec te) a x) = P a x.
  by rewrite Pr_outcome (@rand_full_fst_law te a n Hwf Hcyc Hops).
rewrite -(@rand_full_cond te a n x y Hwf Hcyc Hops (lt0r_neq0 Hx)).
apply: emp_cond_converges => //.
by rewrite HB.
Qed.

(* ...and uniformly over the outcome values: with confidence [1 - delta],
   the whole reported table for arm x is within [eps] of the
   interventional law.  This is the general form of the statement rct3
   gets in [rct3_full_emp_cond_converges_all]. *)
Theorem rand_full_emp_cond_converges_all (te : texperiment dom) (a n : Node G)
    (x : dom a) (eps delta : R) :
  G_well_formed G = true -> contains_cycle G = false ->
  te_ops te = @TRandomize G dom a :: @TMeasure G dom a
                :: @TMeasure G dom n :: nil ->
  0 < eps -> 0 < delta -> 0 < P a x ->
  exists N0 : nat, forall N : nat, (N0 <= N)%N ->
    Pr (fdist_sample N.+1)
       (\bigcup_(y : dom n)
          @cond_off (@outcome_set (elab_exp enc dec te) n y)
                    (@outcome_set (elab_exp enc dec te) a x)
                    N (fdist_do enc dec (te_mech te) P a x n y) eps)
    <= delta.
Proof.
move=> Hwf Hcyc Hops Heps Hdelta Hx.
have HB : Pr (fdist_context P) (@outcome_set (elab_exp enc dec te) a x) = P a x.
  by rewrite Pr_outcome (@rand_full_fst_law te a n Hwf Hcyc Hops).
apply: emp_cond_converges_fam => //.
  by rewrite HB.
move=> y.
exact: (esym (@rand_full_cond te a n x y Hwf Hcyc Hops (lt0r_neq0 Hx))).
Qed.

(* ...and the many-column version: with confidence [1 - delta], EVERY
   cell of arm x's whole reported table -- one cell per joint record of
   the measured list, not one per outcome value -- is within [eps] of its
   interventional value, simultaneously.  The union bound costs nothing
   extra here because [emp_cond_bound_fam]'s Chebyshev slack depends only
   on the conditioning arm and [eps], never on which cell. *)
Theorem rand_many_emp_cond_converges_all (te : texperiment dom) (a : Node G)
    (k : nat) (ms : k.-tuple (Node G)) (x : dom a) (eps delta : R) :
  G_well_formed G = true -> contains_cycle G = false ->
  te_ops te = @TRandomize G dom a :: @TMeasure G dom a
                :: map (@TMeasure G dom) ms ->
  0 < eps -> 0 < delta -> 0 < P a x ->
  exists N0 : nat, forall N : nat, (N0 <= N)%N ->
    Pr (fdist_sample N.+1)
       (\bigcup_(y : logrec ms)
          @cond_off (@record_set (elab_exp enc dec te) k ms y)
                    (@outcome_set (elab_exp enc dec te) a x)
                    N (fdist_do_rec (te_mech te) x ms y) eps)
    <= delta.
Proof.
move=> Hwf Hcyc Hops Heps Hdelta Hx.
have HB : Pr (fdist_context P) (@outcome_set (elab_exp enc dec te) a x) = P a x.
  by rewrite Pr_outcome (@rand_many_fst_law te a k ms Hwf Hcyc Hops).
apply: emp_cond_converges_fam => //.
  by rewrite HB.
move=> y.
exact: (esym (@rand_many_cond te a k ms x y Hwf Hcyc Hops (lt0r_neq0 Hx))).
Qed.


(* ===================================================================== *)
(* The dataset: every measured node's column at once                     *)
(* --------------------------------------------------------------------- *)
(* [log_sample] is ONE node's column.  A dataset is all of them, and the  *)
(* interesting thing about having them together is that unit i's JOINT    *)
(* observation becomes available -- which is what a query like            *)
(* [P(R | do(T))] needs, and what a per-node marginal cannot express.     *)
(*                                                                        *)
(* Columns are addressed BY NODE with an [is_measured] ticket, exactly as *)
(* [Prob.parent_view] addresses parents with an [is_parent] ticket: no    *)
(* ticket, no read, so a node the protocol never measured is UNASKABLE    *)
(* rather than answered with junk.  (Without the ticket the column would  *)
(* still typecheck and would return [dec n 0], since [log_val] reads an    *)
(* absent log entry through [odflt 0] -- data that looks real and is not.) *)
(*                                                                        *)
(* The ticket costs nothing here, which is worth recording because it     *)
(* normally would.  A ticketed type is a function out of a [Prop], so it  *)
(* is NOT a finType and cannot carry an [fdist].  That would be fatal if  *)
(* the dataset needed its own law -- but it does not: a dataset is a       *)
(* deterministic function of the sample, and every probabilistic statement *)
(* here is already phrased over [fdist_sample].  The concrete side holds   *)
(* DATA, the abstract side holds the law ([Prob.fdist_node]), and the two  *)
(* are compared through [emp_rV].  So the law lives where the randomness   *)
(* is, and the dataset is free to be faithful instead of enumerable.      *)
(* ===================================================================== *)

Definition dataset (te : texperiment dom) (N : nat) : Type :=
  forall n : Node G, is_measured te n -> 'rV[dom n]_N.

(* what a run produces: each measured node's column, over the whole sample *)
Definition log_dataset (te : texperiment dom) (N : nat) (s : sample N)
  : dataset te N :=
  fun n _ => log_sample (elab_exp enc dec te) n s.

(* unit i's joint observation at two measured nodes.  The pairing is a real
   index [i : 'I_N], not a positional convention that could drift. *)
Definition joint_at (te : texperiment dom) (N : nat) (x y : Node G)
    (Hx : is_measured te x) (Hy : is_measured te y)
    (d : dataset te N) (i : 'I_N) : dom x * dom y :=
  ((d x Hx) ``_ i, (d y Hy) ``_ i).

(* a protocol that measures n does have a ticket for n -- this is what
   discharges the ticket for the one-[Measure] protocols below *)
Lemma is_measured_single (te : texperiment dom) (n : Node G) :
  te_ops te = @TMeasure G dom n :: nil -> is_measured te n.
Proof. by rewrite /is_measured => ->; rewrite /= inE eqxx. Qed.

(* and the exact-sample law transfers to the dataset's column verbatim:
   [log_dataset]'s column at n IS [log_sample] at n, so everything already
   proved about columns applies to the dataset unchanged *)
Corollary measure_source_dataset (te : texperiment dom) (n : Node G)
    (g : dom n -> dom n) (N : nat) (s : sample N.+1)
    (Hm : is_measured te n) :
  G_well_formed G = true ->
  contains_cycle G = false ->
  find_parents (ssval n) G = nil ->
  te_ops te = @TMeasure G dom n :: nil ->
  (forall u pa, (te_mech te : tgraphfun dom) n u pa = g u) ->
  emp_rV s = fdist_context P ->
  emp_rV (@log_dataset te N.+1 s n Hm) = dmap g (P n).
Proof.
move=> Hwf Hcyc Hnp Hops Hmech Hrep.
exact: measure_source_empirical_rV.
Qed.

End ExperimentLaw.

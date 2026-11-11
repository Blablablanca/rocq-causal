Set Warnings "-notation-overridden,-deprecated-library-file,-ambiguous-paths".
From HB Require Import structures.
From mathcomp Require Import all_ssreflect all_algebra finalg reals matrix.
From infotheo Require Import ssr_ext ssralg_ext fdist proba.
From DAGs Require Import Basics_Constr Descendants CycleDetection.
From CausalDiagrams Require Import Assignments.
(* Require-only: [Interventions] imports [Nat] and [Lists], whose names
   would shadow mathcomp's.  Only the qualified [Interventions.do] is used. *)
From CausalDiagrams Require Interventions.
From Semantics Require Import FunctionRepresentation FindValue.
From Experiment Require Main.
From Experiment Require Import Prob TypedExp.

Set Implicit Arguments.
Unset Strict Implicit.

Local Open Scope fdist_scope.

(* ===================================================================== *)
(* A CONFOUNDED RANDOMIZED TRIAL                                          *)
(* --------------------------------------------------------------------- *)
(* [Rct2.v] randomizes a treatment whose natural assignment was merely    *)
(* BIASED.  This file does the case randomization actually exists for: a  *)
(* CONFOUNDER.  The graph is Main.v's G_3,                                *)
(*                                                                        *)
(*        Z (age)                                                         *)
(*        /    \                 X = treatment, Y = outcome,              *)
(*       v      v                Z = age, a common cause of both          *)
(*       X ---> Y                                                         *)
(*                                                                        *)
(* with the protocol "randomize X, then measure Y".  Everything except    *)
(* the protocol is reused from [Prob.v]: the graph, the three categorical *)
(* domains, the codes, and the mechanism family [tF_3] -- whose X         *)
(* mechanism is confounded on purpose ("the old get treated").           *)
(*                                                                        *)
(* WHAT IS NEW HERE, beyond Rct2.                                        *)
(*                                                                        *)
(* 1. DEPTH.  Y has TWO parents, and its positional parent list is        *)
(*    [X; Z], so the keyed reads [pa x3] and [pa z3] must resolve to      *)
(*    positions 0 and 1 of that list.  Rct2 only ever had a one-element   *)
(*    parent list, where any lookup discipline would have worked.         *)
(*                                                                        *)
(* 2. RANDOMIZATION BREAKS CONFOUNDING, and the theorem shows it.  In     *)
(*    [tF_3] the treatment READS the confounder                           *)
(*    (X = if Z is old then drug else placebo), so in the untouched model *)
(*    X and Z are dependent.  [TRandomize x3] cuts that: X takes its own  *)
(*    exogenous slot instead, and the two become independent -- which is  *)
(*    exactly why [rct3_correct]'s conclusion FACTORISES into a mixture   *)
(*    over X's law of laws depending only on Z's own law.  The confounder *)
(*    still influences the outcome; it is just no longer correlated with  *)
(*    the treatment.  That is the whole point of an RCT, and here it is   *)
(*    the difference between a law that factorises and one that does not. *)
(* ===================================================================== *)

Example G3_wf : G_well_formed G3 = true.
Proof. reflexivity. Qed.
Example G3_acyc : contains_cycle G3 = false.
Proof. reflexivity. Qed.
Example G3_pa_X : find_parents 1 G3 = (3 :: nil)%N.
Proof. reflexivity. Qed.
Example G3_pa_Y : find_parents 2 G3 = (1 :: 3 :: nil)%N.
Proof. reflexivity. Qed.
Example G3_pa_Z : find_parents 3 G3 = nil.
Proof. reflexivity. Qed.

(* the response table [tF_3] uses at Y, named so the theorems can quote it *)
Definition h3 (t : treatment) (a : age) : outcome :=
  match t, a with
  | drug,    young => cured
  | drug,    _     => better
  | placebo, old   => worse
  | placebo, _     => same
  end.

(* the protocol: randomize the treatment, then measure the response *)
Definition te_rct3 (N : nat) : texperiment dom_3 :=
  mk_texperiment
    (Main.label_of Main.G_3)
    tF_3
    (@TRandomize G3 dom_3 x3 :: @TMeasure G3 dom_3 y3 :: nil)
    N.

Example te_rct3_elaborates (N : nat) :
  Main.ops (elab_exp enc_3 dec_3 (te_rct3 N))
  = (Main.Randomize 1 :: Main.Measure 2 :: nil)%N.
Proof. reflexivity. Qed.

(* --- the solve, node by node ------------------------------------------ *)

Section Rct3Solve.
Let F' := Main.randomize_graphfun 1 (elab enc_3 dec_3 tF_3).

Let Hx (w : context dom_3) :
  get_assigned_value (to_assign enc_3 w) 1 = Some (@enc_3 x3 (w x3))
  := to_assign_get enc_3 w x3.
Let Hy (w : context dom_3) :
  get_assigned_value (to_assign enc_3 w) 2 = Some (@enc_3 y3 (w y3))
  := to_assign_get enc_3 w y3.
Let Hz (w : context dom_3) :
  get_assigned_value (to_assign enc_3 w) 3 = Some (@enc_3 z3 (w z3))
  := to_assign_get enc_3 w z3.

Let Hoy : @o_node G3 2 = Some y3 := o_node_self y3.
Let Hoz : @o_node G3 3 = Some z3 := o_node_self z3.

(* Z is a source and echoes its own noise -- untouched by the protocol *)
Lemma rct3_Z (w : context dom_3) :
  find_value G3 F' 3 (to_assign enc_3 w) nil = Some (@enc_3 z3 (w z3)).
Proof.
have [Q [_ Hfv]] :=
  find_value_gives_value_of_node G3 F' (to_assign enc_3 w) 3
    (conj G3_wf G3_acyc)
    (conj (to_assign_complete enc_3 w) (node_in_graph_ssval z3)).
rewrite Hfv /get_value_of_node /= (Hz w) /=.
rewrite /F' /Main.randomize_graphfun /= /elab Hoz /=.
by rewrite enc_3K.
Qed.

(* X, after randomization, hands back its own slot -- and in particular
   STOPS READING Z.  Note the parent list [3] is still built and passed,
   and simply ignored: that is the confounding being cut. *)
Lemma rct3_X (w : context dom_3) :
  find_value G3 F' 1 (to_assign enc_3 w) nil = Some (@enc_3 x3 (w x3)).
Proof.
have [Q [HQ Hfv]] :=
  find_value_gives_value_of_node G3 F' (to_assign enc_3 w) 1
    (conj G3_wf G3_acyc)
    (conj (to_assign_complete enc_3 w) (node_in_graph_ssval x3)).
move: HQ; rewrite /= (rct3_Z w) => /Some_inj HQ2.
rewrite -HQ2 in Hfv.
by rewrite Hfv /get_value_of_node /= (Hx w) /=.
Qed.

(* Y reads BOTH parents, positionally [X; Z], keyed as [pa x3] / [pa z3] *)
Lemma rct3_Y (w : context dom_3) :
  find_value G3 F' 2 (to_assign enc_3 w) nil
  = Some (@enc_3 y3 (h3 (w x3) (w z3))).
Proof.
have [Q [HQ Hfv]] :=
  find_value_gives_value_of_node G3 F' (to_assign enc_3 w) 2
    (conj G3_wf G3_acyc)
    (conj (to_assign_complete enc_3 w) (node_in_graph_ssval y3)).
move: HQ; rewrite /= (rct3_X w) (rct3_Z w) => /Some_inj HQ2.
rewrite -HQ2 in Hfv.
rewrite Hfv /get_value_of_node /= (Hy w) /=.
rewrite /F' /Main.randomize_graphfun /= /elab Hoy /=.
by rewrite !enc_3K.
Qed.

End Rct3Solve.

(* --- the logged value, and the outcome law ----------------------------- *)

Lemma log_val_rct3 (N : nat) (w : context dom_3) :
  log_val enc_3 dec_3 (elab_exp enc_3 dec_3 (te_rct3 N)) w y3
  = h3 (w x3) (w z3).
Proof.
rewrite /log_val /elab_exp /elab_ops /= /Main.eval (rct3_Y w) /=.
by rewrite enc_3K.
Qed.

Section Rct3Law.
Import GRing.Theory.
Local Open Scope ring_scope.
Variable R : realType.
Variable P : forall n : Node G3, R.-fdist (dom_3 n).

Theorem rct3_log_law (N : nat) :
  fdist_log_val enc_3 dec_3 P (elab_exp enc_3 dec_3 (te_rct3 N)) y3
  = dmap (fun w : context dom_3 => h3 (w x3) (w z3)) (fdist_context P).
Proof.
rewrite /fdist_log_val; apply: dmap_eq => w; exact: log_val_rct3.
Qed.

Example x3_neq_z3 : x3 != z3.
Proof. by []. Qed.

(* CORRECTNESS OF THE CONFOUNDED TRIAL.  The outcome law is the mixture,
   over the RANDOMIZED treatment, of outcome laws that depend only on the
   confounder's OWN exogenous law.  The confounder is still in the model and
   still moves the outcome -- what randomization removed is the CORRELATION
   between it and the treatment, and the factorisation is the formal trace
   of that removal.  Without [TRandomize x3] the treatment would read Z
   through [tF_3], the two would be dependent, and no such factorisation
   would be available. *)
Theorem rct3_correct (N : nat) :
  fdist_log_val enc_3 dec_3 P (elab_exp enc_3 dec_3 (te_rct3 N)) y3
  = dbind (P x3) (fun t => dmap (h3 t) (P z3)).
Proof.
rewrite rct3_log_law -(dmap_uncurry_prod (P x3) (P z3) h3).
rewrite -(fdist_context_pair P x3_neq_z3) dmap_comp.
by apply: dmap_eq => w.
Qed.

End Rct3Law.

(* ===================================================================== *)
(* THE INTERVENTIONAL LAW, AND WHAT THE TRIAL EARNS                       *)
(* --------------------------------------------------------------------- *)
(* [rct3_correct] says the trial's outcome law factorises as a mixture    *)
(*                                                                        *)
(*       dbind (P x3) (fun t => dmap (h3 t) (P z3)).                      *)
(*                                                                        *)
(* That is a statement about PUSHFORWARDS: nothing in it mentions do().   *)
(* This block identifies the mixand.  [fdist_do] (Prob.v) is the law of Y *)
(* in the model SURGERED at X -- X's mechanism replaced by a constant,    *)
(* X's incoming edge from Z cut -- which is P(Y | do(X := t)) and has     *)
(* nothing to do with any protocol.  The three solves below compute it,   *)
(* and [fdist_do_rct3_Y] shows it is exactly the mixand above.            *)
(*                                                                        *)
(* [rct3_is_mixture_of_do] is then the causal reading of the trial:        *)
(*                                                                        *)
(*    the law the RANDOMIZED protocol logs at Y                           *)
(*      = the P(x3)-mixture of the INTERVENTIONAL laws P(Y | do(X := t)). *)
(*                                                                        *)
(* Both sides are computed, so this needs no general randomize/do bridge  *)
(* (Correctness.v's [randomize_semantic_do], whose distributional lift is *)
(* still open).  What it does need is that the two routes agree on this   *)
(* model: randomizing X and then logging Y, versus setting X by fiat and  *)
(* reading Y off the surgered model.                                      *)
(*                                                                        *)
(* Note which pieces of the surgery each side uses.  Randomization cuts   *)
(* X's READ of Z but leaves the edge Z -> X in the graph (see [rct3_X]:    *)
(* the parent list is still built, and ignored).  The do-surgery removes   *)
(* the edge outright.  They agree at Y because what Y sees is the VALUE    *)
(* at X, and under both readings that value is free of Z.                 *)
(* ===================================================================== *)

Section Do3Solve.
Variable t : treatment.

Let Gd : graph := Interventions.do (ssval x3) G3.
Let Fd : @graphfun nat :=
  Main.do_graphfun (ssval x3) (@enc_3 x3 t) (elab enc_3 dec_3 tF_3).

(* the surgery in one line: X's parent list is gone, Y's is not *)
Example Gd_pa_X : find_parents 1 Gd = nil.
Proof. reflexivity. Qed.
Example Gd_pa_Y : find_parents 2 Gd = (1 :: 3 :: nil)%N.
Proof. reflexivity. Qed.

Let Gd_wf : G_well_formed Gd = true := erefl.
Let Gd_acyc : contains_cycle Gd = false := erefl.

Let Hx (w : context dom_3) :
  get_assigned_value (to_assign enc_3 w) 1 = Some (@enc_3 x3 (w x3))
  := to_assign_get enc_3 w x3.
Let Hy (w : context dom_3) :
  get_assigned_value (to_assign enc_3 w) 2 = Some (@enc_3 y3 (w y3))
  := to_assign_get enc_3 w y3.
Let Hz (w : context dom_3) :
  get_assigned_value (to_assign enc_3 w) 3 = Some (@enc_3 z3 (w z3))
  := to_assign_get enc_3 w z3.

Let Hoy : @o_node G3 2 = Some y3 := o_node_self y3.
Let Hoz : @o_node G3 3 = Some z3 := o_node_self z3.

(* Z is untouched by the surgery: still a source, still its own noise *)
Lemma do3_Z (w : context dom_3) :
  find_value Gd Fd (ssval z3) (to_assign enc_3 w) nil
  = Some (@enc_3 z3 (w z3)).
Proof.
have [Q [_ Hfv]] :=
  find_value_gives_value_of_node Gd Fd (to_assign enc_3 w) (ssval z3)
    (conj Gd_wf Gd_acyc)
    (conj (to_assign_complete enc_3 w) (node_in_graph_ssval z3)).
rewrite Hfv /get_value_of_node /= (Hz w) /=.
rewrite /Fd /Main.do_graphfun /= /elab Hoz /=.
by rewrite enc_3K.
Qed.

(* X is the CONSTANT t.  Not "its own slot" as under randomization, and
   not a function of Z as in the untouched model: the mechanism is gone,
   and so is the parent list -- [Gd_pa_X] is nil. *)
Lemma do3_X (w : context dom_3) :
  find_value Gd Fd (ssval x3) (to_assign enc_3 w) nil = Some (@enc_3 x3 t).
Proof.
have [Q [_ Hfv]] :=
  find_value_gives_value_of_node Gd Fd (to_assign enc_3 w) (ssval x3)
    (conj Gd_wf Gd_acyc)
    (conj (to_assign_complete enc_3 w) (node_in_graph_ssval x3)).
by rewrite Hfv /get_value_of_node /= (Hx w) /= /Fd /Main.do_graphfun /=.
Qed.

(* Y still reads both parents, positionally [X; Z] -- the surgery did not
   touch Y's parent list, only the value arriving at X *)
Lemma do3_Y (w : context dom_3) :
  find_value Gd Fd (ssval y3) (to_assign enc_3 w) nil
  = Some (@enc_3 y3 (h3 t (w z3))).
Proof.
have [Q [HQ Hfv]] :=
  find_value_gives_value_of_node Gd Fd (to_assign enc_3 w) (ssval y3)
    (conj Gd_wf Gd_acyc)
    (conj (to_assign_complete enc_3 w) (node_in_graph_ssval y3)).
move: HQ; rewrite /= (do3_X w) (do3_Z w) => /Some_inj HQ2.
rewrite -HQ2 in Hfv.
rewrite Hfv /get_value_of_node /= (Hy w) /=.
rewrite /Fd /Main.do_graphfun /= /elab Hoy /=.
by rewrite !enc_3K.
Qed.

End Do3Solve.

(* the typed surgered solve, per unit: Y's value when X is HELD at t *)
Lemma solve_do_rct3_Y (t : treatment) (w : context dom_3) :
  solve_do enc_3 dec_3 tF_3 x3 t w y3 = h3 t (w z3).
Proof.
rewrite /solve_do /Main.semantic_do (do3_Y t w) /=.
by rewrite enc_3K.
Qed.

Section Do3Law.
Import GRing.Theory.
Local Open Scope ring_scope.
Variable R : realType.
Variable P : forall n : Node G3, R.-fdist (dom_3 n).

(* P(Y | do(X := t)).  Note which law survives: Z's OWN exogenous law.
   Setting X kills X's draw, so the only randomness left upstream of Y is
   the confounder's own noise -- and the answer is Z's law pushed through
   the response table with the treatment held fixed. *)
Theorem fdist_do_rct3_Y (t : treatment) :
  fdist_do enc_3 dec_3 tF_3 P x3 t y3 = dmap (h3 t) (P z3).
Proof.
rewrite /fdist_do.
transitivity (dmap (fun w : context dom_3 => h3 t (w z3)) (fdist_context P)).
  by apply: dmap_eq => w; exact: solve_do_rct3_Y.
rewrite -(fdist_context_marginal P z3) dmap_comp.
by apply: dmap_eq => w.
Qed.

(* THE CAUSAL READING OF THE TRIAL.  The law the protocol [Randomize X,
   Measure Y] logs at Y is the mixture, over the randomization law, of the
   INTERVENTIONAL laws P(Y | do(X := t)).  Randomizing is not identified
   with intervening here -- the protocol performs no [TIntervene], and
   do() is a denotation, not an operation.  What is proved is that on this
   model the two readings coincide, which is what makes the trial an
   instrument for a causal quantity. *)
Theorem rct3_is_mixture_of_do (N : nat) :
  fdist_log_val enc_3 dec_3 P (elab_exp enc_3 dec_3 (te_rct3 N)) y3
  = dbind (P x3) (fun t => fdist_do enc_3 dec_3 tF_3 P x3 t y3).
Proof.
rewrite (rct3_correct P N); apply: dbind_eq => t.
by rewrite fdist_do_rct3_Y.
Qed.

(* --- the experiment level: the concrete run against the causal law ----- *)
(* Everything above compares DISTRIBUTIONS.  This block states the         *)
(* comparison an experimenter cares about, and it is the first time the    *)
(* chain closes end to end on a confounded model:                          *)
(*                                                                        *)
(*    the numbers a concrete run of [Randomize X, Measure Y] writes into   *)
(*    the log at Y  -->  converge to  -->  the P(x3)-mixture of the        *)
(*    INTERVENTIONAL laws P(Y | do(X := t)).                              *)
(*                                                                        *)
(* The right-hand side is a causal quantity, not a pushforward dressed up  *)
(* as one: [rct3_is_mixture_of_do] put it there.  So this is the sense in  *)
(* which the trial MEASURES something causal -- the limit of what it       *)
(* reports is the do-mixture, and by [obs3_is_not_do_mixture] the          *)
(* observational protocol's limit is not.                                  *)
(*                                                                        *)
(* Declared size = sample size, exactly as in [Rct2.v]: the protocol is    *)
(* [te_rct3 N.+1] run on a sample of length [N.+1], and the rate is quoted *)
(* as [te_size].  [rct3_varE] is the [elab_exp_size] trick again -- the    *)
(* elaborated experiment does not mention the declared size, so the        *)
(* variance constant can be named once at a fixed index and stays fixed    *)
(* while the sample size is quantified. *)

Import Order.TTheory Num.Def Num.Theory.
Local Open Scope proba_scope.

(* the variance of the indicator "this unit logged v at Y", named at a
   fixed declared size so it is a constant of the protocol *)
Definition rct3_var (v : dom_3 y3) : R :=
  `V (Ind (@outcome_set G3 dom_3 enc_3 dec_3
             (elab_exp enc_3 dec_3 (te_rct3 1)) y3 v)
      : {RV (fdist_context P) -> R^o}).

Lemma rct3_varE (v : dom_3 y3) (M : nat) :
  `V (Ind (@outcome_set G3 dom_3 enc_3 dec_3
             (elab_exp enc_3 dec_3 (te_rct3 M)) y3 v)
      : {RV (fdist_context P) -> R^o})
  = rct3_var v.
Proof. rewrite /rct3_var /te_rct3; reflexivity. Qed.

(* CHEBYSHEV FORM.  The empirical frequency of [v] in the logged column at
   Y is within [eps] of the do-mixture, except on an event of probability
   at most V / (te_size * eps^2).  Nothing is assumed about the allocation
   law [P x3] or the confounder's law [P z3]: the structural work was done
   by [rct3_is_mixture_of_do] and the probabilistic work by [emp_lln_any],
   which knows nothing about this protocol. *)
Theorem rct3_emp_converges (N : nat) (v : dom_3 y3) (eps : R) :
  0 < eps ->
  `Pr[ (normr `o
        ((@emp_freq G3 dom_3 enc_3 dec_3 R P
            (elab_exp enc_3 dec_3 (te_rct3 N.+1)) y3 v N)
         `-cst (dbind (P x3)
                  (fun t => fdist_do enc_3 dec_3 tF_3 P x3 t y3) v))) >= eps ]
  <= rct3_var v / ((te_size (te_rct3 N.+1))%:R * eps ^+ 2).
Proof.
move=> Heps.
rewrite -(rct3_is_mixture_of_do N.+1) -(rct3_varE v N.+1).
exact: emp_lln_any.
Qed.

(* CONVERGENCE PROPER.  For any tolerance [eps] and confidence [delta]
   there is a pre-registrable sample size beyond which the frequency the
   trial reports at Y is within [eps] of the interventional mixture with
   probability at least [1 - delta].  This is the development's full arc on
   a confounded model: a concrete program run, a weak law, and a causal
   quantity, with the randomization doing the work in the middle. *)
Corollary rct3_emp_converges_eps_delta (v : dom_3 y3) (eps delta : R) :
  0 < eps -> 0 < delta ->
  exists N0 : nat, forall N : nat, (N0 <= N)%N ->
    `Pr[ (normr `o
          ((@emp_freq G3 dom_3 enc_3 dec_3 R P
              (elab_exp enc_3 dec_3 (te_rct3 N.+1)) y3 v N)
           `-cst (dbind (P x3)
                    (fun t => fdist_do enc_3 dec_3 tF_3 P x3 t y3) v))) >= eps ]
    <= delta.
Proof.
move=> Heps Hdelta.
have Hpos : 0 < delta * eps ^+ 2 by rewrite mulr_gt0 // exprn_gt0.
exists (truncn (rct3_var v / (delta * eps ^+ 2))) => N HN.
apply: (le_trans (@rct3_emp_converges N v eps Heps)).
have Hsz : te_size (te_rct3 N.+1) = N.+1 by [].
rewrite Hsz.
have Hx : rct3_var v / (delta * eps ^+ 2) < N.+1%:R.
  apply: (lt_le_trans (truncnS_gt _)).
  by rewrite ler_nat ltnS.
move: Hx; rewrite ltr_pdivrMr // => Hlt.
rewrite ler_pdivrMr; last by rewrite mulr_gt0 // exprn_gt0.
by rewrite mulrCA; exact: ltW.
Qed.

End Do3Law.

(* ===================================================================== *)
(* THE CONTRAST: the same measurement WITHOUT randomizing                 *)
(* --------------------------------------------------------------------- *)
(* [rct3_correct] on its own does not show that randomizing CHANGED       *)
(* anything.  So here is the observational protocol -- measure Y and      *)
(* nothing else -- on the same model.  Now X's confounded mechanism is    *)
(* live, so the chain is Z -> X -> Y and the solve is three deep: the     *)
(* first genuinely 3-deep solve in the development.                      *)
(*                                                                        *)
(* The resulting law is a function of Z ALONE, and it does NOT factorise  *)
(* as a mixture over any treatment law -- the treatment is not free to    *)
(* vary independently of the confounder, which is precisely the bias.     *)
(* [rct3_differs_from_obs3] closes the argument on Prob.v's concrete      *)
(* [P_3]: the two laws disagree, so randomization is not a no-op.         *)
(* ===================================================================== *)

(* X's confounded assignment, as [tF_3] has it: the old get treated *)
Definition bias (a : age) : treatment := if a is old then drug else placebo.

Definition te_obs3 (N : nat) : texperiment dom_3 :=
  mk_texperiment
    (Main.label_of Main.G_3)
    tF_3
    (@TMeasure G3 dom_3 y3 :: nil)
    N.

Section Obs3Solve.
Let F0 := elab enc_3 dec_3 tF_3.

Let Hx (w : context dom_3) :
  get_assigned_value (to_assign enc_3 w) 1 = Some (@enc_3 x3 (w x3))
  := to_assign_get enc_3 w x3.
Let Hy (w : context dom_3) :
  get_assigned_value (to_assign enc_3 w) 2 = Some (@enc_3 y3 (w y3))
  := to_assign_get enc_3 w y3.
Let Hz (w : context dom_3) :
  get_assigned_value (to_assign enc_3 w) 3 = Some (@enc_3 z3 (w z3))
  := to_assign_get enc_3 w z3.

Let Hox : @o_node G3 1 = Some x3 := o_node_self x3.
Let Hoy : @o_node G3 2 = Some y3 := o_node_self y3.
Let Hoz : @o_node G3 3 = Some z3 := o_node_self z3.

Lemma obs3_Z (w : context dom_3) :
  find_value G3 F0 3 (to_assign enc_3 w) nil = Some (@enc_3 z3 (w z3)).
Proof.
have [Q [_ Hfv]] :=
  find_value_gives_value_of_node G3 F0 (to_assign enc_3 w) 3
    (conj G3_wf G3_acyc)
    (conj (to_assign_complete enc_3 w) (node_in_graph_ssval z3)).
rewrite Hfv /get_value_of_node /= (Hz w) /= /F0 /elab Hoz /=.
by rewrite enc_3K.
Qed.

(* X READS Z here -- this is the edge randomization cut *)
Lemma obs3_X (w : context dom_3) :
  find_value G3 F0 1 (to_assign enc_3 w) nil
  = Some (@enc_3 x3 (bias (w z3))).
Proof.
have [Q [HQ Hfv]] :=
  find_value_gives_value_of_node G3 F0 (to_assign enc_3 w) 1
    (conj G3_wf G3_acyc)
    (conj (to_assign_complete enc_3 w) (node_in_graph_ssval x3)).
move: HQ; rewrite /= (obs3_Z w) => /Some_inj HQ2.
rewrite -HQ2 in Hfv.
rewrite Hfv /get_value_of_node /= (Hx w) /= /F0 /elab Hox /=.
by rewrite enc_3K.
Qed.

(* and Y reads the confounded X together with Z: three deep *)
Lemma obs3_Y (w : context dom_3) :
  find_value G3 F0 2 (to_assign enc_3 w) nil
  = Some (@enc_3 y3 (h3 (bias (w z3)) (w z3))).
Proof.
have [Q [HQ Hfv]] :=
  find_value_gives_value_of_node G3 F0 (to_assign enc_3 w) 2
    (conj G3_wf G3_acyc)
    (conj (to_assign_complete enc_3 w) (node_in_graph_ssval y3)).
move: HQ; rewrite /= (obs3_X w) (obs3_Z w) => /Some_inj HQ2.
rewrite -HQ2 in Hfv.
rewrite Hfv /get_value_of_node /= (Hy w) /= /F0 /elab Hoy /=.
by rewrite !enc_3K.
Qed.

End Obs3Solve.

Lemma log_val_obs3 (N : nat) (w : context dom_3) :
  log_val enc_3 dec_3 (elab_exp enc_3 dec_3 (te_obs3 N)) w y3
  = h3 (bias (w z3)) (w z3).
Proof.
rewrite /log_val /elab_exp /elab_ops /= /Main.eval (obs3_Y w) /=.
by rewrite enc_3K.
Qed.

Section Obs3Law.
Import GRing.Theory.
Local Open Scope ring_scope.
Variable R : realType.
Variable P : forall n : Node G3, R.-fdist (dom_3 n).

(* The observational law is a function of the CONFOUNDER ALONE: Z fixes the
   treatment, which fixes the response.  There is no treatment law left to
   mix over -- which is exactly the sense in which the design is biased. *)
Theorem obs3_log_law (N : nat) :
  fdist_log_val enc_3 dec_3 P (elab_exp enc_3 dec_3 (te_obs3 N)) y3
  = dmap (fun a : age => h3 (bias a) a) (P z3).
Proof.
rewrite /fdist_log_val.
transitivity (dmap (fun w : context dom_3 => h3 (bias (w z3)) (w z3))
                   (fdist_context P)).
  by apply: dmap_eq => w; exact: log_val_obs3.
rewrite -(fdist_context_marginal P z3) dmap_comp.
by apply: dmap_eq => w.
Qed.

End Obs3Law.

(* --- randomizing is not a no-op --------------------------------------- *)

Section Rct3VsObs3.
Import GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Variable R : realType.

(* Under the trial, [worse] has mass 1/3: the placebo arm reaches it
   whenever the unit is old, and randomization makes "old" and "placebo"
   co-occur. *)
Lemma rct3_P3_worse (N : nat) :
  fdist_log_val enc_3 dec_3 (@P_3 R) (elab_exp enc_3 dec_3 (te_rct3 N)) y3 worse
  = (3%:R)^-1.
Proof.
rewrite (rct3_correct (@P_3 R) N) /dbind /dret /= fdist1bind /dmap fdistmapE.
rewrite (eq_bigl (fun a : age => a == old)); last first.
  by move=> a; rewrite inE; case: a.
by rewrite big_pred1_eq /dunif fdist_uniformE card_age.
Qed.

(* Under the observational protocol it has mass 0: the only age that would
   produce [worse] is [old], and [old] is exactly the age the confounded
   mechanism treats -- so no unit can ever be both. *)
Lemma obs3_P3_worse (N : nat) :
  fdist_log_val enc_3 dec_3 (@P_3 R) (elab_exp enc_3 dec_3 (te_obs3 N)) y3 worse
  = 0.
Proof.
rewrite (obs3_log_law (@P_3 R) N) /dmap fdistmapE big_pred0 // => a.
by rewrite inE; case: a.
Qed.

(* Hence the two protocols denote DIFFERENT outcome laws on the same model:
   randomizing changed the answer, and the confounding was real. *)
Theorem rct3_differs_from_obs3 (N : nat) :
  fdist_log_val enc_3 dec_3 (@P_3 R) (elab_exp enc_3 dec_3 (te_rct3 N)) y3
  <> fdist_log_val enc_3 dec_3 (@P_3 R) (elab_exp enc_3 dec_3 (te_obs3 N)) y3.
Proof.
move=> Heq; move: (rct3_P3_worse N).
rewrite Heq (obs3_P3_worse N) => /esym/eqP.
by rewrite invr_eq0 pnatr_eq0.
Qed.

(* CONFOUNDING, FORMALLY: seeing is not doing on this model.  The trial's
   law at Y IS the mixture of interventional laws [rct3_is_mixture_of_do];
   the observational law differs from the trial's [rct3_differs_from_obs3];
   so the observational law is not the interventional mixture.  This is the
   bias an RCT exists to remove, stated as an inequation between a law the
   confounded design produces and the causal quantity it is mistaken for. *)
Corollary obs3_is_not_do_mixture (N : nat) :
  fdist_log_val enc_3 dec_3 (@P_3 R) (elab_exp enc_3 dec_3 (te_obs3 N)) y3
  <> dbind (@P_3 R x3) (fun t => fdist_do enc_3 dec_3 tF_3 (@P_3 R) x3 t y3).
Proof.
move=> Heq; apply: (@rct3_differs_from_obs3 N).
by rewrite Heq; exact: (rct3_is_mixture_of_do (@P_3 R) N).
Qed.

End Rct3VsObs3.

(* ===================================================================== *)
(* PER ARM: MEASURING THE TREATMENT TOO                                   *)
(* --------------------------------------------------------------------- *)
(* [te_rct3] logs only Y, so its law is the P(x3)-MIXTURE of the           *)
(* interventional laws [rct3_is_mixture_of_do].  A mixture has already     *)
(* averaged over the arms and cannot be un-averaged, so P(Y | do(X := x))  *)
(* for a PARTICULAR x is not recoverable from it.  To separate the arms    *)
(* one has to know which arm each unit was in, which is an X column --     *)
(* and in the typed layer that is not merely practical but enforced:       *)
(* [joint_at] and [fdist_log_pair] need an [is_measured] ticket for both   *)
(* nodes, so without [TMeasure x3] the conditional cannot even be STATED.  *)
(*                                                                        *)
(* This is a NEW protocol rather than an edit to [te_rct3], for two        *)
(* reasons: everything already proved about [te_rct3] (including the       *)
(* contrast with [te_obs3]) stays untouched, and the two protocols are     *)
(* genuinely different designs worth comparing.                           *)
(*                                                                        *)
(* Adding [TMeasure x3] is cheap for a specific reason: [apply_op_total]   *)
(* on a [Measure] leaves [cur_fun] alone and only appends to the log, so   *)
(* the SOLVE is unchanged and [rct3_X]/[rct3_Y] are reused verbatim.  Only *)
(* [log_val] changes, and since [get_assigned_value] is first-match the    *)
(* new X entry cannot shadow Y's.                                        *)
(* ===================================================================== *)

Definition te_rct3_full (N : nat) : texperiment dom_3 :=
  mk_texperiment
    (Main.label_of Main.G_3)
    tF_3
    (@TRandomize G3 dom_3 x3 :: @TMeasure G3 dom_3 x3
       :: @TMeasure G3 dom_3 y3 :: nil)
    N.

Example te_rct3_full_elaborates (N : nat) :
  Main.ops (elab_exp enc_3 dec_3 (te_rct3_full N))
  = (Main.Randomize 1 :: Main.Measure 1 :: Main.Measure 2 :: nil)%N.
Proof. reflexivity. Qed.

(* both columns exist now -- this is what [te_rct3] lacks *)
Example te_rct3_full_measures_X (N : nat) :
  is_measured (te_rct3_full N) x3 = true.
Proof. reflexivity. Qed.
Example te_rct3_full_measures_Y (N : nat) :
  is_measured (te_rct3_full N) y3 = true.
Proof. reflexivity. Qed.

(* the X column logs the RANDOMIZED draw: X's own exogenous slot, which by
   the product form of [fdist_context] is independent of every other slot.
   That independence is the whole reason conditioning on this column is
   legitimate, and it is what fails under [te_obs3], where X's logged value
   would be [bias (w z3)] and selecting on it would select on Z. *)
Lemma log_val_rct3_full_X (N : nat) (w : context dom_3) :
  log_val enc_3 dec_3 (elab_exp enc_3 dec_3 (te_rct3_full N)) w x3 = w x3.
Proof.
rewrite /log_val /elab_exp /elab_ops /= /Main.eval (rct3_X w) /=.
by rewrite enc_3K.
Qed.

(* and the Y column is unchanged: measuring X did not perturb the solve *)
Lemma log_val_rct3_full_Y (N : nat) (w : context dom_3) :
  log_val enc_3 dec_3 (elab_exp enc_3 dec_3 (te_rct3_full N)) w y3
  = h3 (w x3) (w z3).
Proof.
rewrite /log_val /elab_exp /elab_ops /= /Main.eval (rct3_Y w) /=.
by rewrite enc_3K.
Qed.

Section Rct3FullLaw.
Import GRing.Theory.
Local Open Scope ring_scope.
Variable R : realType.
Variable P : forall n : Node G3, R.-fdist (dom_3 n).

(* the X column's law is the allocation law itself *)
Lemma rct3_full_X_law (N : nat) :
  fdist_log_val enc_3 dec_3 P (elab_exp enc_3 dec_3 (te_rct3_full N)) x3
  = P x3.
Proof.
rewrite /fdist_log_val -(fdist_context_marginal P x3).
by apply: dmap_eq => w; exact: log_val_rct3_full_X.
Qed.

(* THE JOINT LAW OF THE TWO COLUMNS.  The trial draws the arm from the
   allocation law and then draws the outcome from that arm's INTERVENTIONAL
   law -- which is to say the randomized trial is jointly a mixture of
   do-experiments, not merely a mixture of their marginals.  No positivity
   is needed to say this, and it is strictly stronger than
   [rct3_is_mixture_of_do], which is its second marginal. *)
Theorem rct3_full_joint (N : nat) :
  fdist_log_pair enc_3 dec_3 P (elab_exp enc_3 dec_3 (te_rct3_full N)) x3 y3
  = dbind (P x3)
      (fun x => dmap (fun y => (x, y)) (fdist_do enc_3 dec_3 tF_3 P x3 x y3)).
Proof.
rewrite /fdist_log_pair.
transitivity (dmap (fun w : context dom_3 => (w x3, h3 (w x3) (w z3)))
                   (fdist_context P)).
  apply: dmap_eq => w.
  by rewrite log_val_rct3_full_X log_val_rct3_full_Y.
transitivity (dbind (P x3) (fun x => dmap (fun z => (x, h3 x z)) (P z3))).
  rewrite -(dmap_uncurry_prod (P x3) (P z3) (fun x z => (x, h3 x z))).
  rewrite -(fdist_context_pair P x3_neq_z3) dmap_comp.
  by apply: dmap_eq => w.
apply: dbind_eq => x; rewrite (fdist_do_rct3_Y P x) dmap_comp.
by apply: dmap_eq => z.
Qed.

(* ...and [rct3_is_mixture_of_do] is its Y-marginal, so the joint really
   does subsume the earlier theorem *)
Corollary rct3_full_Y_law (N : nat) :
  fdist_log_val enc_3 dec_3 P (elab_exp enc_3 dec_3 (te_rct3_full N)) y3
  = dbind (P x3) (fun x => fdist_do enc_3 dec_3 tF_3 P x3 x y3).
Proof.
rewrite -(fdist_log_pair_snd enc_3 dec_3 P
            (elab_exp enc_3 dec_3 (te_rct3_full N)) x3 y3).
rewrite rct3_full_joint dmap_dbind.
by apply: dbind_eq => x; exact: dmap_pair_snd.
Qed.

(* ANSWERING THE QUESTION: the law of Y in the arm X = x, as logged by the
   trial, IS the interventional law P(Y | do(X := x)).  Positivity of the
   arm is needed and is exactly the overlap condition -- an arm no unit was
   assigned to has nothing to condition on.  Note the interventional law
   itself needs no such condition (see [fdist_do_rct3_Y]): overlap is about
   ESTIMATING the do-law, not about its existence. *)
Theorem rct3_full_cond (N : nat) (x : dom_3 x3) (y : dom_3 y3) :
  P x3 x != 0 ->
  cPr (fdist_context P)
      (@outcome_set G3 dom_3 enc_3 dec_3
         (elab_exp enc_3 dec_3 (te_rct3_full N)) y3 y)
      (@outcome_set G3 dom_3 enc_3 dec_3
         (elab_exp enc_3 dec_3 (te_rct3_full N)) x3 x)
  = fdist_do enc_3 dec_3 tF_3 P x3 x y3 y.
Proof.
move=> Hpos.
apply: (@cPr_outcome_eq G3 dom_3 enc_3 dec_3 R P
          (elab_exp enc_3 dec_3 (te_rct3_full N)) x3 y3 x y
          (fun a => fdist_do enc_3 dec_3 tF_3 P x3 a y3)).
- by rewrite rct3_full_X_law.
- by rewrite rct3_full_joint rct3_full_X_law.
Qed.

Import Order.TTheory Num.Def Num.Theory.
Local Open Scope proba_scope.

(* --- the experiment level, per arm ------------------------------------- *)
(* The capstone of the per-arm route, and the reason the X column was      *)
(* added.  What a confounded trial REPORTS in the arm X = x -- the         *)
(* fraction of the units assigned x whose outcome was y -- converges to    *)
(* P(Y = y | do(X := x)), one arm at a time, rather than only to the       *)
(* mixture over the allocation ([rct3_emp_converges]).                     *)
(*                                                                        *)
(* [e3] fixes the declared size at 1.  That is not a restriction: by       *)
(* [elab_exp_size] the elaborated experiment is the same term at every     *)
(* declared size, so [e3] IS the elaboration of this protocol whatever     *)
(* size it declares, and naming it at a fixed index is what lets the       *)
(* events -- and so [Pr] of the conditioning arm -- stay fixed while the   *)
(* sample size is quantified.                                             *)
(*                                                                        *)
(* The overlap hypothesis is [0 < P x3 x]: the allocation must actually    *)
(* put units in the arm.  Nothing else about [P] is assumed -- and note    *)
(* this condition is absent from [fdist_do_rct3_Y], because the            *)
(* interventional law exists whether or not the trial estimates it.        *)

Let e3 : Main.experiment := elab_exp enc_3 dec_3 (te_rct3_full 1).

Example e3_is_the_protocol (N : nat) :
  elab_exp enc_3 dec_3 (te_rct3_full N) = e3.
Proof. exact: elab_exp_size. Qed.

Theorem rct3_full_emp_cond_converges (x : dom_3 x3) (y : dom_3 y3)
    (eps delta : R) :
  0 < eps -> 0 < delta -> 0 < P x3 x ->
  exists N0 : nat, forall N : nat, (N0 <= N)%N ->
    `Pr[ (normr `o
          ((@emp_cond G3 dom_3 R P
              (@outcome_set G3 dom_3 enc_3 dec_3 e3 y3 y)
              (@outcome_set G3 dom_3 enc_3 dec_3 e3 x3 x) N)
           `-cst (fdist_do enc_3 dec_3 tF_3 P x3 x y3 y))) >= eps ]
    <= delta.
Proof.
move=> Heps Hdelta Hx.
have HB : Pr (fdist_context P) (@outcome_set G3 dom_3 enc_3 dec_3 e3 x3 x)
          = P x3 x.
  by rewrite Pr_outcome /e3 rct3_full_X_law.
rewrite -(rct3_full_cond 1 y (lt0r_neq0 Hx)).
apply: emp_cond_converges => //.
by rewrite HB.
Qed.


(* --- the whole reported distribution, not one of its values ----------- *)
(* [rct3_full_emp_cond_converges] fixes an outcome value before choosing   *)
(* the sample size, so it does not say the trial's REPORTED TABLE for arm  *)
(* x is close to the interventional law -- only that any one entry of it   *)
(* is.  This closes that: one sample size beyond which, with confidence    *)
(* [1 - delta], EVERY outcome value's reported frequency in arm x is       *)
(* within [eps] of P(Y = y | do(X := x)).                                  *)
(*                                                                        *)
(* The target handed to [emp_cond_converges_fam] is the interventional     *)
(* law, with [rct3_full_cond] discharging the identification hypothesis    *)
(* value by value.  Overlap is still the only assumption on [P].           *)
Theorem rct3_full_emp_cond_converges_all (x : dom_3 x3) (eps delta : R) :
  0 < eps -> 0 < delta -> 0 < P x3 x ->
  exists N0 : nat, forall N : nat, (N0 <= N)%N ->
    Pr (fdist_sample P N.+1)
       (\bigcup_(y : dom_3 y3)
          @cond_off G3 dom_3 R P
            (@outcome_set G3 dom_3 enc_3 dec_3 e3 y3 y)
            (@outcome_set G3 dom_3 enc_3 dec_3 e3 x3 x)
            N (fdist_do enc_3 dec_3 tF_3 P x3 x y3 y) eps)
    <= delta.
Proof.
move=> Heps Hdelta Hx.
have HB : Pr (fdist_context P) (@outcome_set G3 dom_3 enc_3 dec_3 e3 x3 x)
          = P x3 x.
  by rewrite Pr_outcome /e3 rct3_full_X_law.
apply: emp_cond_converges_fam => //.
  by rewrite HB.
move=> y; exact: (esym (rct3_full_cond 1 y (lt0r_neq0 Hx))).
Qed.
(* --- the generalisation, checked against this instance ---------------- *)
(* [rct3_full_joint] above was proved by computing both sides on G_3.
   [TypedExp.rand_full_joint] proves the same shape for EVERY well-formed
   acyclic model, so this file's result is now an instance -- and the
   instance is checked here, which is what makes the general statement
   believable rather than merely plausible. *)
Example rct3_full_joint_is_general (N : nat) :
  fdist_log_pair enc_3 dec_3 P (elab_exp enc_3 dec_3 (te_rct3_full N)) x3 y3
  = dbind (P x3) (fun x => dmap (fun y => (x, y))
                   (fdist_do enc_3 dec_3 tF_3 P x3 x y3)).
Proof.
apply: (@rand_full_joint G3 dom_3 enc_3 dec_3 enc_3K R P
          (te_rct3_full N) x3 y3).
- exact: G3_wf.
- exact: G3_acyc.
- by [].
Qed.

(* the empirical chain generalises too: [rct3_full_emp_cond_converges] is
   [rand_full_emp_cond_converges] at [te_rct3_full 1], whose elaboration
   IS [e3]. *)
Example rct3_full_emp_is_general (x : dom_3 x3) (y : dom_3 y3)
    (eps delta : R) :
  0 < eps -> 0 < delta -> 0 < P x3 x ->
  exists N0 : nat, forall N : nat, (N0 <= N)%N ->
    `Pr[ (normr `o
          ((@emp_cond G3 dom_3 R P
              (@outcome_set G3 dom_3 enc_3 dec_3 e3 y3 y)
              (@outcome_set G3 dom_3 enc_3 dec_3 e3 x3 x) N)
           `-cst (fdist_do enc_3 dec_3 tF_3 P x3 x y3 y))) >= eps ]
    <= delta.
Proof.
move=> Heps Hdelta Hx.
apply: (@rand_full_emp_cond_converges G3 dom_3 enc_3 dec_3 enc_3K R P
          (te_rct3_full 1) x3 y3 x y eps delta) => //.
Qed.

End Rct3FullLaw.


(* ===================================================================== *)
(* A THREE-COLUMN TRIAL: treatment, response, baseline covariate          *)
(* --------------------------------------------------------------------- *)
(* [te_rct3_full] logs two columns.  A real trial also records baseline
   covariates, and in G_3 the baseline covariate IS the confounder z3
   (age): drawn before treatment, a parent of both X and Y, and the whole
   reason the OBSERVATIONAL contrast in [Obs3Law] is wrong.  So this
   protocol logs exactly what a trialist logs, confounder included, and
   the many-column theorem says the table is still a mixture of
   do-experiments -- now jointly over both recorded columns.

   What makes this the right instance to check: nothing about z3 is
   favourable.  It is not a descendant of X, it is a parent of X in the
   pre-surgery graph, and it is the variable whose presence breaks
   observational identification.  Logging it changes nothing, because
   [Randomize] cut X loose from it before any column was read. *)

(* the measured list: response, then baseline covariate *)
Definition cols_rct3 : 2.-tuple (Node G3) :=
  in_tuple (y3 :: z3 :: nil).

Definition te_rct3_cov (N : nat) : texperiment dom_3 :=
  mk_texperiment
    (Main.label_of Main.G_3)
    tF_3
    (@TRandomize G3 dom_3 x3 :: @TMeasure G3 dom_3 x3
       :: map (@TMeasure G3 dom_3) cols_rct3)
    N.

Example te_rct3_cov_elaborates (N : nat) :
  Main.ops (elab_exp enc_3 dec_3 (te_rct3_cov N))
  = (Main.Randomize 1 :: Main.Measure 1 :: Main.Measure 2
       :: Main.Measure 3 :: nil)%N.
Proof. reflexivity. Qed.

Example te_rct3_cov_measures_Z (N : nat) :
  is_measured (te_rct3_cov N) z3 = true.
Proof. reflexivity. Qed.

Section Rct3CovLaw.
Import GRing.Theory.
Local Open Scope ring_scope.
Variable R : realType.
Variable P : forall n : Node G3, R.-fdist (dom_3 n).

(* THE THREE-COLUMN JOINT.  The trial draws the arm from the allocation
   law and then draws the WHOLE TABLE -- response and covariate together
   -- from that arm's interventional joint. *)
Theorem rct3_cov_joint (N : nat) :
  fdist_log_arm_rec enc_3 dec_3 P
    (elab_exp enc_3 dec_3 (te_rct3_cov N)) x3 cols_rct3
  = dbind (P x3) (fun x => dmap (fun y => (x, y))
                   (fdist_do_rec enc_3 dec_3 P tF_3 x cols_rct3)).
Proof.
apply: (@rand_many_joint G3 dom_3 enc_3 dec_3 enc_3K R P
          (te_rct3_cov N) x3 2 cols_rct3).
- exact: G3_wf.
- exact: G3_acyc.
- by [].
Qed.

(* ...and in any arm the allocation law fills, conditioning on the
   recorded treatment gives that interventional joint outright *)
Corollary rct3_cov_cond (N : nat) (x : dom_3 x3)
    (y : logrec dom_3 cols_rct3) :
  P x3 x != 0 ->
  cPr (fdist_context P)
      (@record_set G3 dom_3 enc_3 dec_3
         (elab_exp enc_3 dec_3 (te_rct3_cov N)) 2 cols_rct3 y)
      (@outcome_set G3 dom_3 enc_3 dec_3
         (elab_exp enc_3 dec_3 (te_rct3_cov N)) x3 x)
  = fdist_do_rec enc_3 dec_3 P tF_3 x cols_rct3 y.
Proof.
move=> Hpos.
apply: (@rand_many_cond G3 dom_3 enc_3 dec_3 enc_3K R P
          (te_rct3_cov N) x3 2 cols_rct3 x y) => //.
Qed.

(* the Y column on its own is STILL identified, confounder column and all:
   this is [rct3_full_cond]'s conclusion, recovered from a protocol that
   also logs z3.  Logging a covariate -- even the confounder -- costs the
   treatment-effect claim nothing. *)
Corollary rct3_cov_Y_cond (N : nat) (x : dom_3 x3) (y : dom_3 y3) :
  P x3 x != 0 ->
  cPr (fdist_context P)
      (@outcome_set G3 dom_3 enc_3 dec_3
         (elab_exp enc_3 dec_3 (te_rct3_cov N)) y3 y)
      (@outcome_set G3 dom_3 enc_3 dec_3
         (elab_exp enc_3 dec_3 (te_rct3_cov N)) x3 x)
  = fdist_do enc_3 dec_3 tF_3 P x3 x y3 y.
Proof.
move=> Hpos.
apply: (@rand_many_cond_col G3 dom_3 enc_3 dec_3 enc_3K R P
          (te_rct3_cov N) x3 y3 2 cols_rct3 x y) => //.
Qed.

(* and the whole three-column table converges: with confidence [1 - delta]
   every cell of arm x's joint (response, covariate) table is within [eps]
   of its interventional value, simultaneously *)
Example rct3_cov_emp_converges_all (x : dom_3 x3) (eps delta : R) :
  0 < eps -> 0 < delta -> 0 < P x3 x ->
  exists N0 : nat, forall N : nat, (N0 <= N)%N ->
    Pr (fdist_sample P N.+1)
       (\bigcup_(y : logrec dom_3 cols_rct3)
          cond_off P
            (@record_set G3 dom_3 enc_3 dec_3
               (elab_exp enc_3 dec_3 (te_rct3_cov 1)) 2 cols_rct3 y)
            (@outcome_set G3 dom_3 enc_3 dec_3
               (elab_exp enc_3 dec_3 (te_rct3_cov 1)) x3 x)
            N (fdist_do_rec enc_3 dec_3 P tF_3 x cols_rct3 y) eps)
    <= delta.
Proof.
move=> Heps Hdelta Hx.
apply: (@rand_many_emp_cond_converges_all G3 dom_3 enc_3 dec_3 enc_3K R P
          (te_rct3_cov 1) x3 2 cols_rct3 x eps delta) => //.
Qed.

End Rct3CovLaw.

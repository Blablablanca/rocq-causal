Set Warnings "-notation-overridden,-deprecated-library-file,-ambiguous-paths".
From HB Require Import structures.
From mathcomp Require Import all_ssreflect all_algebra finalg reals matrix.
From infotheo Require Import ssr_ext ssralg_ext fdist proba.
From DAGs Require Import Basics_Constr Descendants CycleDetection.
From CausalDiagrams Require Import Assignments.
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

Example te_rct3_measures_last (N : nat) :
  tmeasures_last (te_ops (te_rct3 N)) = true.
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

End Rct3VsObs3.

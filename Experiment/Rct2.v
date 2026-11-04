(* ===================================================================== *)
(* A TWO-NODE RANDOMIZED TRIAL, end to end                                *)
(* --------------------------------------------------------------------- *)
(* [TypedExp.measure_source_law] measures ONE parentless node.  This file  *)
(* does the smallest experiment that is actually an experiment: a graph    *)
(* T -> R, the protocol "randomize T, then measure R", and the law of what *)
(* gets logged.                                                           *)
(*                                                                        *)
(* Two things are new here, and both matter.                              *)
(*                                                                        *)
(* 1. R HAS A PARENT.  [solve_source] only covers parentless nodes, so     *)
(*    [rct2_R] below is the induction STEP done by hand: T's value         *)
(*    round-trips enc -> dec once as a PARENT value before R's mechanism   *)
(*    reads it.  The whole arithmetic is [encK]; it never needs range      *)
(*    closure [enc (dec m) = m].  That is evidence the general elaboration *)
(*    -correctness induction is viable, since this is its base-plus-one    *)
(*    case.                                                               *)
(*                                                                        *)
(* 2. RANDOMIZATION IS VISIBLE.  T is given a BIASED natural mechanism --  *)
(*    everyone gets placebo -- and it does not appear in the conclusion of *)
(*    [rct2_correct].  Randomization erased it.  And the conclusion is a   *)
(*    MIXTURE over the coin, which is the content of an RCT: T's value is  *)
(*    independent of R's noise, so the outcome law factorises.  Without    *)
(*    that factorisation [rct2_log_law] would be true of any protocol.    *)
(*                                                                        *)
(* The coin needs no new machinery: [rct2_correct] is general in [P], so   *)
(* "the coin at T" is just which [P] you instantiate it at.  A semantic    *)
(* operation on laws becomes necessary only for a compositional runner     *)
(* that walks the operation list.                                         *)
(* ===================================================================== *)

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

(* the two-node RCT graph: T=1 -> R=2 *)
Definition G2 : graph := ([:: 1; 2]%N, [:: (1,2)]%N).

Example G2_wf : G_well_formed G2 = true.
Proof. reflexivity. Qed.
Example G2_acyclic : contains_cycle G2 = false.
Proof. reflexivity. Qed.
Example G2_parents_T : find_parents 1 G2 = nil.
Proof. reflexivity. Qed.
Example G2_parents_R : find_parents 2 G2 = [:: 1]%N.
Proof. reflexivity. Qed.

Definition t2 : Node G2 := @SeqSub _ (nodes_in_graph G2) 1 isT.
Definition r2 : Node G2 := @SeqSub _ (nodes_in_graph G2) 2 isT.

(* T is a treatment (placebo|drug), R an outcome (worse|same|better|cured) *)
Definition dom_2 (n : Node G2) : finType :=
  match ssval n with 1 => treatment | _ => outcome end.

Unset Implicit Arguments.   (* keep the node argument of enc/dec explicit *)
Definition enc_2 (n : Node G2) : dom_2 n -> nat :=
  match ssval n as v
    return (Finite.sort (match v with 1 => treatment | _ => outcome end) -> nat)
  with 1 => t2n | _ => o2n end.

Definition dec_2 (n : Node G2) (m : nat) : dom_2 n :=
  match ssval n as v
    return Finite.sort (match v with 1 => treatment | _ => outcome end)
  with 1 => n2t m | _ => n2o m end.

Set Implicit Arguments.

Example enc_2K : forall n : Node G2, cancel (enc_2 n) (dec_2 n).
Proof. by move=> [[|[|v]] pf] x; case: x. Qed.

(* The model.  T's NATURAL assignment is biased -- everyone gets placebo --
   which is what randomization will overwrite.  R responds to its parent T
   and its own noise through an arbitrary table [h]. *)
Definition tF_2 (h : treatment -> outcome -> outcome) : tgraphfun dom_2 :=
  fun n =>
    match n return tnodefun dom_2 n with
    | SeqSub v pf =>
        (match v return forall pf' : v \in nodes_in_graph G2,
                        tnodefun dom_2 (SeqSub pf')
         with
         | 1 => fun _ => fun (_ : treatment) _ => placebo
         | 2 => fun _ => fun (u : outcome) pa => h (pa t2 isT) u
         | _ => fun _ => fun u _ => u
         end) pf
    end.

(* the protocol: randomize the treatment, then measure the response *)
Definition te_rct2 (h : treatment -> outcome -> outcome) (N : nat)
  : texperiment dom_2 :=
  mk_texperiment
    (fun n => match n with
              | 1 => Main.Treatment | 2 => Main.Response | _ => Main.Unlabeled
              end)
    (tF_2 h)
    (@TRandomize G2 dom_2 t2 :: @TMeasure G2 dom_2 r2 :: nil)
    N.

Example te_rct2_elaborates (h : treatment -> outcome -> outcome) (N : nat) :
  Main.ops (elab_exp enc_2 dec_2 (te_rct2 h N))
  = (Main.Randomize 1 :: Main.Measure 2 :: nil)%N.
Proof. reflexivity. Qed.

(* --- the depth-2 solve ------------------------------------------------- *)
(* [solve_source] handles a parentless node.  R has a parent, so this is the
   induction step done by hand: T's value round-trips through [encK] once as
   a PARENT value before R's mechanism reads it. *)

Section Rct2Solve.
Variable h : treatment -> outcome -> outcome.
Let F' := Main.randomize_graphfun 1 (elab enc_2 dec_2 (tF_2 h)).

(* the two exogenous reads, with node ids already reduced to literals *)
Let HT (w : context dom_2) :
  get_assigned_value (to_assign enc_2 w) 1 = Some (enc_2 t2 (w t2))
  := to_assign_get enc_2 w t2.
Let Ho : @o_node G2 2 = Some r2 := o_node_self r2.
Let HR (w : context dom_2) :
  get_assigned_value (to_assign enc_2 w) 2 = Some (enc_2 r2 (w r2))
  := to_assign_get enc_2 w r2.

(* T, after randomization, simply hands back its own exogenous slot: its
   mechanism is [f_unobs], which returns the raw code untouched -- so no
   decoding happens here at all. *)
Lemma rct2_T (w : context dom_2) :
  find_value G2 F' 1 (to_assign enc_2 w) nil = Some (enc_2 t2 (w t2)).
Proof.
have [Q [_ Hfv]] :=
  find_value_gives_value_of_node G2 F' (to_assign enc_2 w) 1
    (conj G2_wf G2_acyclic)
    (conj (to_assign_complete enc_2 w) (node_in_graph_ssval t2)).
by rewrite Hfv /get_value_of_node /= (HT w).
Qed.

(* R is the induction STEP: its mechanism reads T through the parent view,
   so T's code round-trips [enc -> dec] once as a parent value, and R's own
   noise round-trips once too.  Both are [encK]; neither needs range
   closure. *)
Lemma rct2_R (w : context dom_2) :
  find_value G2 F' 2 (to_assign enc_2 w) nil
  = Some (enc_2 r2 (h (w t2) (w r2))).
Proof.
have [Q [HQ Hfv]] :=
  find_value_gives_value_of_node G2 F' (to_assign enc_2 w) 2
    (conj G2_wf G2_acyclic)
    (conj (to_assign_complete enc_2 w) (node_in_graph_ssval r2)).
move: HQ; rewrite /= (rct2_T w) => /Some_inj HQ2.
rewrite -HQ2 in Hfv.
rewrite Hfv /get_value_of_node /= (HR w) /=.
rewrite /F' /Main.randomize_graphfun /= /elab Ho /=.
by rewrite !enc_2K.
Qed.

End Rct2Solve.

(* --- the logged value, and its law ------------------------------------ *)

Lemma log_val_rct2 (h : treatment -> outcome -> outcome) (N : nat)
    (w : context dom_2) :
  log_val enc_2 dec_2 (elab_exp enc_2 dec_2 (te_rct2 h N)) w r2
  = h (w t2) (w r2).
Proof.
rewrite /log_val /elab_exp /elab_ops /= /Main.eval (rct2_R h w) /=.
by rewrite enc_2K.
Qed.

(* --- the outcome law, and why randomization makes it a mixture -------- *)

Section Rct2Law.
Import GRing.Theory.
Local Open Scope ring_scope.
Variable R : realType.
Variable P : forall n : Node G2, R.-fdist (dom_2 n).

(* the law of the logged value: true of this protocol, but not yet
   informative -- it still mentions the joint context *)
Theorem rct2_log_law (h : treatment -> outcome -> outcome) (N : nat) :
  fdist_log_val enc_2 dec_2 P (elab_exp enc_2 dec_2 (te_rct2 h N)) r2
  = dmap (fun w : context dom_2 => h (w t2) (w r2)) (fdist_context P).
Proof.
rewrite /fdist_log_val; apply: dmap_eq => w; exact: log_val_rct2.
Qed.

Example t2_neq_r2 : t2 != r2.
Proof. by []. Qed.

(* RCT CORRECTNESS.  The outcome law is the coin-MIXTURE of the per-arm
   response laws: draw the treatment from T's law, then push R's noise
   through the response table at that treatment.  This is what
   randomization buys -- T's value is independent of R's noise, so the
   joint factorises -- and it is the two-node instance of Theorem A's
   shape.  Instantiating [P t2] with a 1:1 coin gives the familiar
   balanced trial; nothing in the proof depends on which coin. *)
Theorem rct2_correct (h : treatment -> outcome -> outcome) (N : nat) :
  fdist_log_val enc_2 dec_2 P (elab_exp enc_2 dec_2 (te_rct2 h N)) r2
  = dbind (P t2) (fun t => dmap (h t) (P r2)).
Proof.
rewrite rct2_log_law -(dmap_uncurry_prod (P t2) (P r2) h).
rewrite -(fdist_context_pair P t2_neq_r2) dmap_comp.
by apply: dmap_eq => w.
Qed.

End Rct2Law.

(* ===================================================================== *)
(* THE SAME TRIAL OVER ARBITRARY FINITE DOMAINS                           *)
(* --------------------------------------------------------------------- *)
(* Everything above is stated at [treatment] (2 values) and [outcome] (4  *)
(* values).  Nothing in those proofs ever looked at the tables: [rct2_T]  *)
(* and [rct2_R] run on [enc_2K] alone, and every [reflexivity] in the     *)
(* file is about the GRAPH or the OP LIST, not about values.  So the      *)
(* cardinalities were never load-bearing, and this section says so by     *)
(* replaying the development at two abstract finite domains.             *)
(*                                                                        *)
(* Three things are generalised at once.                                  *)
(*                                                                        *)
(* 1. |D_R| ARBITRARY.  The response domain [B] is any nonempty finType.  *)
(*                                                                        *)
(* 2. |D_T| ARBITRARY.  The treatment domain [A] is any nonempty finType, *)
(*    so this is a k-ARM trial: k = |A| arms, with [P t2] the allocation  *)
(*    law over them.  [P t2 = dunif] is the balanced k-arm trial, a       *)
(*    1:1 coin on a 2-element [A] is the familiar two-arm trial, and      *)
(*    |A| = 1 degenerates to a single-arm study (still true, just empty   *)
(*    of content).  The theorem is uniform in the allocation law, so the  *)
(*    arm count and the randomisation ratio are both free.               *)
(*                                                                        *)
(* 3. THE ERASED MECHANISM IS ARBITRARY.  Above, T's natural assignment   *)
(*    was the constant [placebo].  Here it is an arbitrary [bias : A -> A]*)
(*    of T's own noise, which sharpens the point of [rct2_correct] from   *)
(*    erasing a constant to erasing anything at all: [bias] does not     *)
(*    occur in the conclusion of [rct2_correct_gen].                      *)
(*                                                                        *)
(* The price of abstraction is that the codes come from [enc_default]     *)
(* ([enum_rank]), which does not reduce -- so this section proves laws    *)
(* but, unlike the concrete one, cannot run anything by [reflexivity].    *)
(* That is why both versions are kept: the concrete trial is the one that *)
(* computes, the abstract one is the one that generalises.                *)
(*                                                                        *)
(* NOT claimed here: that the concrete [rct2_correct] is an INSTANCE of   *)
(* [rct2_correct_gen].  It is not, literally -- the concrete development  *)
(* uses hand-written codes [t2n]/[n2t], this one uses [enum_rank], and    *)
(* nothing proved so far says the logged law is independent of which      *)
(* cancelling code pair you pick.  That independence is a corollary of    *)
(* general elaboration correctness (M5e), not of anything available yet.  *)
(* ===================================================================== *)

Section Rct2Gen.

(* the two domains, and a point in each.  The points are what makes [dec]
   TOTAL: [dec : nat -> dom n] must answer on codes that name no value.
   This is not a real restriction -- [P n : R.-fdist (dom n)] already
   forces [dom n] nonempty -- but it has to be assumed separately, since
   [dec] is used by [elab_exp], outside the section where [P] lives. *)
Variable A B : finType.
Variable a0 : A.
Variable b0 : B.

Definition dom_g (n : Node G2) : finType :=
  match ssval n with 1 => A | _ => B end.

Unset Implicit Arguments.   (* keep the node argument of enc/dec explicit *)
Definition enc_g (n : Node G2) : dom_g n -> nat :=
  match ssval n as v
    return (Finite.sort (match v with 1 => A | _ => B end) -> nat)
  with 1 => @enc_default A | _ => @enc_default B end.

Definition dec_g (n : Node G2) (m : nat) : dom_g n :=
  match ssval n as v
    return Finite.sort (match v with 1 => A | _ => B end)
  with 1 => dec_default a0 m | _ => dec_default b0 m end.

Set Implicit Arguments.

Lemma enc_gK : forall n : Node G2, cancel (enc_g n) (dec_g n).
Proof. by move=> [[|[|v]] pf] x; apply: enc_defaultK. Qed.

(* the model: T assigned by an arbitrary rule [bias] on its own noise,
   R responding to its parent T and its own noise through [h] *)
Definition tF_g (bias : A -> A) (h : A -> B -> B) : tgraphfun dom_g :=
  fun n =>
    match n return tnodefun dom_g n with
    | SeqSub v pf =>
        (match v return forall pf' : v \in nodes_in_graph G2,
                        tnodefun dom_g (SeqSub pf')
         with
         | 1 => fun _ => fun (u : A) _ => bias u
         | 2 => fun _ => fun (u : B) pa => h (pa t2 isT) u
         | _ => fun _ => fun u _ => u
         end) pf
    end.

Definition te_rct2_g (bias : A -> A) (h : A -> B -> B) (N : nat)
  : texperiment dom_g :=
  mk_texperiment
    (fun n => match n with
              | 1 => Main.Treatment | 2 => Main.Response | _ => Main.Unlabeled
              end)
    (tF_g bias h)
    (@TRandomize G2 dom_g t2 :: @TMeasure G2 dom_g r2 :: nil)
    N.

(* --- the depth-2 solve, verbatim from the concrete case --------------- *)

Section Rct2GenSolve.
Variable bias : A -> A.
Variable h : A -> B -> B.
Let F' := Main.randomize_graphfun 1 (elab enc_g dec_g (tF_g bias h)).

Let HT (w : context dom_g) :
  get_assigned_value (to_assign enc_g w) 1 = Some (enc_g t2 (w t2))
  := to_assign_get enc_g w t2.
Let Ho : @o_node G2 2 = Some r2 := o_node_self r2.
Let HR (w : context dom_g) :
  get_assigned_value (to_assign enc_g w) 2 = Some (enc_g r2 (w r2))
  := to_assign_get enc_g w r2.

Lemma rct2g_T (w : context dom_g) :
  find_value G2 F' 1 (to_assign enc_g w) nil = Some (enc_g t2 (w t2)).
Proof.
have [Q [_ Hfv]] :=
  find_value_gives_value_of_node G2 F' (to_assign enc_g w) 1
    (conj G2_wf G2_acyclic)
    (conj (to_assign_complete enc_g w) (node_in_graph_ssval t2)).
by rewrite Hfv /get_value_of_node /= (HT w).
Qed.

Lemma rct2g_R (w : context dom_g) :
  find_value G2 F' 2 (to_assign enc_g w) nil
  = Some (enc_g r2 (h (w t2) (w r2))).
Proof.
have [Q [HQ Hfv]] :=
  find_value_gives_value_of_node G2 F' (to_assign enc_g w) 2
    (conj G2_wf G2_acyclic)
    (conj (to_assign_complete enc_g w) (node_in_graph_ssval r2)).
move: HQ; rewrite /= (rct2g_T w) => /Some_inj HQ2.
rewrite -HQ2 in Hfv.
rewrite Hfv /get_value_of_node /= (HR w) /=.
rewrite /F' /Main.randomize_graphfun /= /elab Ho /=.
by rewrite !enc_gK.
Qed.

End Rct2GenSolve.

Lemma log_val_rct2g (bias : A -> A) (h : A -> B -> B) (N : nat)
    (w : context dom_g) :
  log_val enc_g dec_g (elab_exp enc_g dec_g (te_rct2_g bias h N)) w r2
  = h (w t2) (w r2).
Proof.
rewrite /log_val /elab_exp /elab_ops /= /Main.eval (rct2g_R bias h w) /=.
by rewrite enc_gK.
Qed.

Section Rct2GenLaw.
Import GRing.Theory.
Local Open Scope ring_scope.
Variable R : realType.
Variable P : forall n : Node G2, R.-fdist (dom_g n).

Theorem rct2g_log_law (bias : A -> A) (h : A -> B -> B) (N : nat) :
  fdist_log_val enc_g dec_g P (elab_exp enc_g dec_g (te_rct2_g bias h N)) r2
  = dmap (fun w : context dom_g => h (w t2) (w r2)) (fdist_context P).
Proof.
rewrite /fdist_log_val; apply: dmap_eq => w; exact: log_val_rct2g.
Qed.

(* RCT CORRECTNESS, k ARMS AND ARBITRARY RESPONSE DOMAIN.  For any two
   nonempty finite domains, any response table, any pre-randomisation
   assignment rule and any allocation law, the logged outcome law is the
   allocation-MIXTURE of the per-arm response laws.  [bias] is absent from
   the statement: that absence IS the content of randomisation. *)
Theorem rct2_correct_gen (bias : A -> A) (h : A -> B -> B) (N : nat) :
  fdist_log_val enc_g dec_g P (elab_exp enc_g dec_g (te_rct2_g bias h N)) r2
  = dbind (P t2) (fun t => dmap (h t) (P r2)).
Proof.
rewrite rct2g_log_law -(dmap_uncurry_prod (P t2) (P r2) h).
rewrite -(fdist_context_pair P t2_neq_r2) dmap_comp.
by apply: dmap_eq => w.
Qed.

(* --- the experiment level: the concrete run against the abstract law --- *)
(* Everything above compares DISTRIBUTIONS.  This block states the         *)
(* comparison an experimenter actually cares about: the numbers that come  *)
(* out of a concrete run of this protocol approach the abstract output law *)
(* of R, which [rct2_correct_gen] has identified as the allocation         *)
(* mixture.  The two semantics meet here, at the level of an experiment.   *)
(*                                                                        *)
(* THE DECLARED SIZE AND THE SIZE ACTUALLY DRAWN ARE THE SAME.  The        *)
(* protocol is [te_rct2_g bias h N.+1] run on a sample of length [N.+1],   *)
(* and the rate is quoted as [te_size], so a record whose declared size    *)
(* disagreed with its sample is not an instance of this theorem at all.    *)
(* That is the point of pre-registering a size, and it is what             *)
(* [measure_source_emp_lln] enforces with its [Hsz] hypothesis; here the   *)
(* two are identified by construction instead, which needs no hypothesis.  *)
(*                                                                        *)
(* Tying them does cost one lemma.  In the [eps]-[delta] statement the     *)
(* sample size is QUANTIFIED, so the variance constant one picks [N0] from *)
(* must not itself vary with [N] -- and written naively it does, since the *)
(* experiment mentions [N.+1].  [elab_exp_size] discharges this: the       *)
(* elaborated experiment is the same term for every declared size, so the  *)
(* constant can be named once, at a fixed index, and that is what          *)
(* [rct2_var] is.                                                         *)
(* ===================================================================== *)

Import Order.TTheory Num.Def Num.Theory.
Local Open Scope proba_scope.

(* the variance of the indicator of "this unit logged v", named at a fixed
   declared size so that it is a constant of the protocol rather than of
   the sample size *)
Definition rct2_var (bias : A -> A) (h : A -> B -> B) (v : dom_g r2) : R :=
  `V (Ind (@outcome_set G2 dom_g enc_g dec_g
             (elab_exp enc_g dec_g (te_rct2_g bias h 1)) r2 v)
      : {RV (fdist_context P) -> R^o}).

(* ...and it really is independent of the declared size, by [elab_exp_size] *)
Lemma rct2_varE (bias : A -> A) (h : A -> B -> B) (v : dom_g r2) (M : nat) :
  `V (Ind (@outcome_set G2 dom_g enc_g dec_g
             (elab_exp enc_g dec_g (te_rct2_g bias h M)) r2 v)
      : {RV (fdist_context P) -> R^o})
  = rct2_var bias h v.
Proof. rewrite /rct2_var /te_rct2_g; reflexivity. Qed.

(* CHEBYSHEV FORM.  The empirical frequency of the value [v] in the logged
   column at R is within [eps] of the mixture, except on an event of
   probability at most V / (te_size * eps^2) -- the declared size, which is
   also the number of units drawn.  Note what is NOT assumed: no
   constraint on the domains, on [bias], on [h], or on the allocation law
   [P t2].  The structural work was done by [rct2_correct_gen] and the
   probabilistic work by [emp_lln_any]. *)
Theorem rct2_emp_converges (bias : A -> A) (h : A -> B -> B) (N : nat)
    (v : dom_g r2) (eps : R) :
  0 < eps ->
  `Pr[ (normr `o
        ((@emp_freq G2 dom_g enc_g dec_g R P
            (elab_exp enc_g dec_g (te_rct2_g bias h N.+1)) r2 v N)
         `-cst (dbind (P t2) (fun t => dmap (h t) (P r2)) v))) >= eps ]
  <= rct2_var bias h v
     / ((te_size (te_rct2_g bias h N.+1))%:R * eps ^+ 2).
Proof.
move=> Heps.
rewrite -(rct2_correct_gen bias h N.+1) -(rct2_varE bias h v N.+1).
exact: emp_lln_any.
Qed.

(* CONVERGENCE PROPER.  The bound above is a rate, not a limit; this is the
   limit.  For any tolerance [eps] and any confidence [delta] there is a
   pre-registered sample size beyond which the reported frequency is within
   [eps] of the abstract mixture with probability at least [1 - delta].
   That is convergence in probability of the concrete run's log to the
   abstract output law of R, for the two-node trial over arbitrary finite
   domains.  The only analytic input is that R is archimedean; in
   particular no sign information about the variance is needed, since
   [truncnS_gt] holds for every real. *)
Corollary rct2_emp_converges_eps_delta (bias : A -> A) (h : A -> B -> B)
    (v : dom_g r2) (eps delta : R) :
  0 < eps -> 0 < delta ->
  exists N0 : nat, forall N : nat, (N0 <= N)%N ->
    `Pr[ (normr `o
          ((@emp_freq G2 dom_g enc_g dec_g R P
              (elab_exp enc_g dec_g (te_rct2_g bias h N.+1)) r2 v N)
           `-cst (dbind (P t2) (fun t => dmap (h t) (P r2)) v))) >= eps ]
    <= delta.
Proof.
move=> Heps Hdelta.
have Hpos : 0 < delta * eps ^+ 2 by rewrite mulr_gt0 // exprn_gt0.
exists (truncn (rct2_var bias h v / (delta * eps ^+ 2))) => N HN.
apply: (le_trans (@rct2_emp_converges bias h N v eps Heps)).
have Hsz : te_size (te_rct2_g bias h N.+1) = N.+1 by [].
rewrite Hsz.
have Hx : rct2_var bias h v / (delta * eps ^+ 2) < N.+1%:R.
  apply: (lt_le_trans (truncnS_gt _)).
  by rewrite ler_nat ltnS.
move: Hx; rewrite ltr_pdivrMr // => Hlt.
rewrite ler_pdivrMr; last by rewrite mulr_gt0 // exprn_gt0.
by rewrite mulrCA; exact: ltW.
Qed.

End Rct2GenLaw.

End Rct2Gen.

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

Example te_rct2_measures_last (h : treatment -> outcome -> outcome) (N : nat) :
  tmeasures_last (te_ops (te_rct2 h N)) = true.
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

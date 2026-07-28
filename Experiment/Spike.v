(* ===================================================================== *)
(* M1a encoding spike (THROWAWAY / reference only -- NOT part of the       *)
(* dependency graph of Main/Correctness/Prob).                            *)
(*                                                                         *)
(* Question it answers: does infotheo's SSReflect fdist world coexist in   *)
(* one file with dsep-core's vanilla-Rocq nat-valued find_value, and can   *)
(* we push a uniform fdist over worlds through the solve via fdistmap      *)
(* (the D5 boundary encoding)?  Answer: yes, on the first compile.         *)
(* ===================================================================== *)

From mathcomp Require Import all_ssreflect ssralg ssrnum finalg reals.
From infotheo Require Import fdist.

From DAGs Require Import Basics_Constr.
From CausalDiagrams Require Import Assignments.
From Semantics Require Import FunctionRepresentation FindValue.

Set Implicit Arguments.
Unset Strict Implicit.

Local Open Scope fdist_scope.

Section Spike.
Variable R : realType.

(* ---- the finite world: one exogenous bool draw per node of a 2-node graph ---- *)
Definition world := {ffun 'I_2 -> bool}.

Definition n0 : 'I_2 := ord0.
Definition n1 : 'I_2 := @Ordinal 2 1 isT.

(* ---- boundary map into dsep-core's nat-valued assignments (D5) ---- *)
Definition to_assign (w : world) : assignments nat :=
  (0%N, nat_of_bool (w n0)) :: (1%N, nat_of_bool (w n1)) :: nil.

(* the 2-node causal model; mechanism kept nat-valued as in dsep-core (D5) *)
Definition Gspike : graph := (0%N :: 1%N :: nil, (0%N, 1%N) :: nil).
Definition gspike : @graphfun nat :=
  fun u => match u with
           | 1 => fun val => match snd val with p :: _ => p | nil => fst val end
           | _ => fun val => fst val
           end.

(* ---- the solve: dsep-core's find_value, reached through the boundary ---- *)
(* NOTE: the [odflt 0] + [inord] below FAKE a finType codomain to paper over
   find_value's [option nat].  Real code needs M2 (find_value totality, drop
   the option) plus an honest [nat -> V] decode -- this spike deliberately
   cuts that corner to isolate the infotheo/dsep-core integration question. *)
Definition solve (w : world) : nat :=
  odflt 0%N (find_value Gspike gspike 1 (to_assign w) nil).

Definition outcome (w : world) : 'I_2 := inord (solve w).

(* ---- push a uniform fdist over worlds through the solve (fdistmap) ---- *)
Lemma world_card : #|world| = 3.+1.
Proof. by rewrite card_ffun card_bool card_ord. Qed.

Definition unif : R.-fdist world := fdist_uniform world_card.

Definition outcome_dist : R.-fdist 'I_2 := fdistmap outcome unif.

(* the pushforward is a genuine distribution: infotheo's toolkit applies *)
Lemma outcome_dist_sums1 :
  (\sum_(x in 'I_2) outcome_dist x = 1)%R.
Proof. exact: FDist.f1. Qed.

(* ---- ONE round-trip lemma: the boundary faithfully records the world ---- *)
Lemma to_assign_roundtrip (w : world) :
  get_assigned_value (to_assign w) 0%N = Some (nat_of_bool (w n0)).
Proof. reflexivity. Qed.

End Spike.

(* ===================================================================== *)
(* Prob.v -- finite probability layer over infotheo (M1b).                *)
(*                                                                         *)
(* Decisions this file realizes (see RAE_plan.md "Decision log"):          *)
(*   D4  probabilities via infotheo's [fdist] over an abstract realType R  *)
(*   D5  dsep-core's value layer stays nat-valued; finite worlds meet it   *)
(*       only at the [to_assign] boundary                                  *)
(*   D6  nodes share one value finType V; no per-node [dom] yet            *)
(*                                                                         *)
(* Style boundary: SSReflect / infotheo lives HERE, behind the narrow      *)
(* interface below; Main.v / Correctness.v stay vanilla Rocq and must not  *)
(* see fdist / bigop names.                                                *)
(*                                                                         *)
(* STATUS: M1b complete -- all definitions and lemmas proved, no admits.   *)
(* ===================================================================== *)

Set Warnings "-notation-overridden,-deprecated-library-file,-ambiguous-paths".
From mathcomp Require Import all_ssreflect ssralg ssrnum finalg reals.
From infotheo Require Import fdist.
From DAGs Require Import Basics_Constr.
From CausalDiagrams Require Import Assignments.

Set Implicit Arguments.
Unset Strict Implicit.

Local Open Scope fdist_scope.

(* ===================================================================== *)
(* Part 1: narrow finite-distribution interface over infotheo             *)
(* --------------------------------------------------------------------- *)
(* Four wrappers naming the primitives the theorems use, plus the         *)
(* congruence lemmas.  [R] is implicit and inferred from the distribution *)
(* argument (or, for [dret]/[dunif], from the expected return type).      *)
(* ===================================================================== *)

(* note: a distribution "R.-fdist A":finType is a func A->R
    that assigns each elem a prob and sums to 1 *)
Definition dret {R : realType} {A : finType} (a : A) : R.-fdist A :=
  fdist1 a.   (* "dret a" gives a prob 1. used in intervention. *)

Definition dmap {R : realType} {A B : finType} (f : A -> B) (P : R.-fdist A)
  : R.-fdist B := fdistmap f P.   (* "dmap f P" transforms a dist *)

Definition dbind {R : realType} {A B : finType} (P : R.-fdist A)
  (k : A -> R.-fdist B) : R.-fdist B := fdistbind P k.  (* "dbind P k"  *)

Definition dunif {R : realType} {A : finType} {n : nat} (cardA : #|A| = n.+1)
  : R.-fdist A := fdist_uniform cardA.

(* --- the two congruence lemmas the RCT lift (M5) rests on --- *)

(* [dmap] respects pointwise-equal functions: this is how the per-world
   [randomize_semantic_do] equality lifts to the outcome distribution. *)
Lemma dmap_eq {R : realType} {A B : finType} (f g : A -> B) (P : R.-fdist A) :
  f =1 g -> dmap f P = dmap g P.
Proof.
move=> Hfg; rewrite /dmap; apply/fdist_ext => b.
rewrite !fdistmapE; apply: eq_bigl => a.
by rewrite !inE Hfg.
Qed.

(* [dbind] respects a pointwise-equal continuation: used to rewrite the
   per-value do-branch inside the randomizer mixture. *)
Lemma dbind_eq {R : realType} {A B : finType} (P : R.-fdist A)
  (k1 k2 : A -> R.-fdist B) :
  k1 =1 k2 -> dbind P k1 = dbind P k2.
Proof.
move=> Hk; rewrite /dbind; apply/fdist_ext => b.
rewrite !fdistbindE; apply: eq_bigr => a _.
by rewrite Hk.
Qed.

(* [dmap] composition: fuses two solve stages (e.g. do-surgery then measure). *)
Lemma dmap_comp {R : realType} {A B C : finType}
  (g : B -> C) (f : A -> B) (P : R.-fdist A) :
  dmap g (dmap f P) = dmap (g \o f) P.
Proof. by rewrite /dmap fdistmap_comp. Qed.

(* --- helper for the boundary round-trip below --- *)
(* Looking up node [key i] in an association list whose keys [key j] are
   INJECTIVE (so no key collisions) returns exactly [i]'s value [val i].
   dsep-core's [get_assigned_value] takes the first key match; injectivity
   makes that the right one. *)
(* [list I], not [seq I]: dsep-core's imports shadow mathcomp's [seq] type
   with stdlib's [seq : nat -> nat -> list nat] range function.  [list I] is
   the same type and dodges the clash. *)
Lemma get_assigned_value_map (I : eqType) (key val : I -> nat)
  (Hinj : injective key) (l : list I) (i : I) :
  i \in l ->
  get_assigned_value [seq (key j, val j) | j <- l] (key i) = Some (val i).
Proof.
elim: l => [|j l IH]; first by [].
rewrite inE => /orP[/eqP -> | Hin].
- by rewrite /= Nat.eqb_refl.
- rewrite /=; case E: (key j =? key i).
  + apply Nat.eqb_eq in E; apply Hinj in E; by rewrite E.
  + exact: (IH Hin).
Qed.

(* ===================================================================== *)
(* Part 2: the D5 boundary -- finite worlds <-> dsep-core assignments      *)
(* --------------------------------------------------------------------- *)
(* A [world] is a complete assignment of a value in the shared finType V   *)
(* to each node of G.  [to_assign] injects it into dsep-core's nat-valued  *)
(* [assignments], which is what [find_value] will consume at M4.           *)
(* ===================================================================== *)

Section Boundary.
Variable V : finType.        (* shared value finType (D6); e.g. bool *)
Variable decode : V -> nat.  (* the value's dsep-core nat code *)
Variable G : graph.

(* G's nodes as a finType; elements carry distinct nat ids via [ssval].
   The [: finType] ascription keeps canonical-structure resolution working
   (so [enum Node], [{ffun Node -> _}] see the finType instance). *)
Definition Node : finType := seq_sub (nodes_in_graph G).

(* a complete V-assignment over the nodes of G *)
Definition world := {ffun Node -> V}.

(* inject a finite world into dsep-core's nat-valued assignment *)
Definition to_assign (w : world) : assignments nat :=
  [seq (ssval i, decode (w i)) | i <- enum Node].

(* round-trip: the boundary faithfully records each node's value.  The
   nat ids are distinct (ssval is injective), so first-match lookup by
   [get_assigned_value] returns exactly node i's value. *)
Lemma to_assign_get (w : world) (i : Node) :
  get_assigned_value (to_assign w) (ssval i) = Some (decode (w i)).
Proof.
rewrite /to_assign.
apply: get_assigned_value_map; first by move=> a b; exact: val_inj.
by rewrite mem_enum.
Qed.

End Boundary.

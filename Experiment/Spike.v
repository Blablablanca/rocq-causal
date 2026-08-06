(* probability example *)

From mathcomp Require Import all_ssreflect ssralg ssrnum finalg reals.
From infotheo Require Import fdist.

From DAGs Require Import Basics_Constr.
From CausalDiagrams Require Import Assignments.
From Semantics Require Import FunctionRepresentation FindValue EquateValues.

Set Implicit Arguments.
Unset Strict Implicit.

Local Open Scope fdist_scope.

Section Spike.
Variable R : realType.


(* R.-fdist A - a probability distribution over the finite set A.
  fdist_uniform — make uniform distribution over a fintype.
  fdistmap — push a distribution through a function.
  FDist.f1 — the built-in guarantee of summing to 1*)

(* ---- the finite context: one exogenous bool draw per node of a 2-node graph ---- *)
Definition context := {ffun 'I_2 -> bool}. (* nodes {0,1}, value bool *)

Definition n0 : 'I_2 := ord0.     (* node n0 is 0. ord0 is zero of any 'I_(n+1)*)
Definition n1 : 'I_2 := @Ordinal 2 1 isT. (* Ordinal with bound 2, value 1, with proof isT: 1<2 *)

(* ---- boundary map into dsep-core's nat-valued assignments (D5) ---- *)
Definition to_assign (w : context) : assignments nat :=
  (0%N, nat_of_bool (w n0)) :: (1%N, nat_of_bool (w n1)) :: nil.

(* ↑ defined a "scenario": 2 nodes, each as 2 elem in its domain -> 4 contexts in total
  "to_assign" is a translator btw
    mathcomp & infotheo that wants fintype and dsep's assigments that's over nat *)

(* the 2-node causal model 0->1 *)
Definition Gspike : graph := (0%N :: 1%N :: nil, (0%N, 1%N) :: nil).
Definition gspike : @graphfun nat :=
  fun u => match u with
           | 1 => fun val => match snd val with p :: _ => p | nil => fst val end
           | _ => fun val => fst val
           end.

(* run the machine *)
(* NOTE: the [odflt 0] + [inord] below FAKE a finType codomain to paper over
   find_value's [option nat].  Real code needs M2 (find_value totality, drop
   the option) plus an honest [nat -> V] decode -- this spike deliberately
   cuts that corner to isolate the infotheo/dsep-core integration question. *)
Definition solve (w : context) : nat :=
  odflt 0%N (find_value Gspike gspike 1 (to_assign w) nil).

Definition outcome (w : context) : 'I_2 := inord (solve w).
(* the response node's value. type 'I_2 is the node's domain *)

(* ---- push a uniform fdist over contexts through the solve (fdistmap) ---- *)
Lemma context_card : #|context| = 3.+1.
Proof. by rewrite card_ffun card_bool card_ord. Qed.

Definition unif : R.-fdist context := fdist_uniform context_card.

Definition outcome_dist : R.-fdist 'I_2 := fdistmap outcome unif.
(* context distr -> outcome distr, simulates the experiment prog *)


(* the pushforward is a genuine distribution: infotheo's toolkit applies *)
Lemma outcome_dist_sums1 :
  (\sum_(x in 'I_2) outcome_dist x = 1)%R.
Proof. exact: FDist.f1. Qed.

(* ---- ONE read-after-write lemma: the boundary faithfully records the context ---- *)
(* commuting square theorem:
  Read-then-encode: read node 0's value, then encode it to nat.
  Encode-then-read: encode the whole context to nat assignment then read node 0 of that list. *)
Lemma to_assign_get (w : context) :
  get_assigned_value (to_assign w) 0%N = Some (nat_of_bool (w n0)).
Proof. reflexivity. Qed.


(* ===================================================================== *)
(* Second example: G_3 from Main.v (3-node confounded graph)             *)
(* --------------------------------------------------------------------- *)
(* x -> y and x <- z -> y : x=1 (Treatment), y=2 (Response), z=3 an      *)
(* (unlabeled) confounder.  G_3 / g_3 grabbed from Main.v.  Same pipeline *)
(* as above, but the response node is 2, whose value x+z ranges over      *)
(* {0,1,2}, so the outcome codomain is 'I_3 (not 'I_2).                   *)
(* ===================================================================== *)

(* ---- the finite context: one exogenous bool draw per node of G_3 ---- *)
Definition context3 := {ffun 'I_3 -> bool}. (* 3 nodes, value bool *)

Definition m0 : 'I_3 := ord0.              (* -> node id 1 (x) *)
Definition m1 : 'I_3 := @Ordinal 3 1 isT.  (* -> node id 2 (y) *)
Definition m2 : 'I_3 := @Ordinal 3 2 isT.  (* -> node id 3 (z) *)

(* ---- boundary map into dsep-core's nat-valued assignments (D5) ---- *)
(* ordinals 0,1,2 carry G_3's node ids 1,2,3 *)
Definition to_assign3 (w : context3) : assignments nat :=
  (1%N, nat_of_bool (w m0)) ::
  (2%N, nat_of_bool (w m1)) ::
  (3%N, nat_of_bool (w m2)) :: nil.

(* the 3-node causal model, grabbed from Main.v (G_3 / g_3):
     g(z=3) = U_z ;  g(x=1) = if z=1 then 0 else 1 ;  g(y=2) = x + z *)
Definition G3 : graph :=
  (1%N :: 2%N :: 3%N :: nil,
   (1%N, 2%N) :: (3%N, 1%N) :: (3%N, 2%N) :: nil).
Definition g3 : @graphfun nat :=
  fun n =>
    match n with
    | 1 => fun val => if nth_default (fst val) (snd val) 0 =? 1 then 0 else 1
    | 2 => fun val => nth_default (fst val) (snd val) 0
                    + nth_default (fst val) (snd val) 1
    | 3 => f_unobs nat
    | _ => f_unobs nat
    end.

(* run the machine: solve the response node 2 (y).  Same [odflt 0]+[inord]
   corner-cut as above; y ranges over {0,1,2} so the codomain is 'I_3. *)
Definition solve3 (w : context3) : nat :=
  odflt 0%N (find_value G3 g3 2 (to_assign3 w) nil).

Definition outcome3 (w : context3) : 'I_3 := inord (solve3 w).

(* ---- push a uniform fdist over contexts through the solve ---- *)
Lemma context3_card : #|context3| = 7.+1.
Proof. by rewrite card_ffun card_bool card_ord. Qed.

Definition unif3 : R.-fdist context3 := fdist_uniform context3_card.

Definition outcome_dist3 : R.-fdist 'I_3 := fdistmap outcome3 unif3.

(* the pushforward is a genuine distribution *)
Lemma outcome_dist3_sums1 :
  (\sum_(x in 'I_3) outcome_dist3 x = 1)%R.
Proof. exact: FDist.f1. Qed.

(* read-after-write on node id 1 (x): encode then read = read then encode *)
Lemma to_assign3_get (w : context3) :
  get_assigned_value (to_assign3 w) 1%N = Some (nat_of_bool (w m0)).
Proof. reflexivity. Qed.

(* ---- enumerate all 8 contexts of context3 = {ffun 'I_3 -> bool} ---- *)
(* [enum context3] does NOT vm_compute (finType of a function space), and
   applying an [ffun] under [Compute] doesn't reduce either.  So we generate
   the contexts constructively: a readable, computable truth-table list, and
   one [ffun] per (node1, node2, node3) bool triple built from it. *)

(* the 8 truth-tables (computable):
   Compute tables3. =
   [:: (false,false,false); (false,false,true); (false,true,false); (false,true,true);
       (true, false,false); (true, false,true); (true, true,false); (true, true,true)] *)
Definition tables3 : list (bool * bool * bool) :=
  [seq (b0, p.1, p.2) | b0 <- [:: false; true],
                        p  <- [seq (b1, b2) | b1 <- [:: false; true],
                                              b2 <- [:: false; true]]].

(* build a real context3 element from a triple (node id 1<-b0, 2<-b1, 3<-b2) *)
Definition mkctx3 (b0 b1 b2 : bool) : context3 :=
  [ffun i => if i == m0 then b0 else if i == m1 then b1 else b2].

(* the 8 contexts, as genuine context3 elements *)
Definition contexts3 : list context3 := [seq mkctx3 t.1.1 t.1.2 t.2 | t <- tables3].

Lemma contexts3_card : size contexts3 = 8.
Proof. by []. Qed.

End Spike.

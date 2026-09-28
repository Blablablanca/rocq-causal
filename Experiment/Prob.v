Set Warnings "-notation-overridden,-deprecated-library-file,-ambiguous-paths".
From HB Require Import structures.
From mathcomp Require Import all_ssreflect ssralg ssrnum finalg reals.
From infotheo Require Import fdist.
From Stdlib Require Import Lia.
From Stdlib Require Import FunctionalExtensionality.
From DAGs Require Import Basics_Constr Descendants CycleDetection.
(* Require-only: Utils defines its own [index], which would shadow
   mathcomp's [seq.index] used in [elab]. *)
From Utils Require List_Basics.
From CausalDiagrams Require Import Assignments.
From Semantics Require Import FunctionRepresentation FindValue EquateValues.
From Experiment Require Main.

Set Implicit Arguments.
Unset Strict Implicit.

Local Open Scope fdist_scope.

(* narrow finite-distribution interface over infotheo *)

(* note: a distribution "R.-fdist A":finType is a func A->R
    that assigns each elem a prob and sums to 1 *)
Definition dret {R : realType} {A : finType} (a : A) : R.-fdist A :=
  fdist1 a.   (* "dret a" gives a prob 1. used in intervention. *)

Definition dmap {R : realType} {A B : finType} (f : A -> B) (P : R.-fdist A)
  : R.-fdist B := fdistmap f P.   (* "dmap f P" transforms a dist from input set to output set; used in the experiment prog *)
(* same random variables with a deterministic f applied to them *)

Definition dbind {R : realType} {A B : finType} (P : R.-fdist A)
  (k : A -> R.-fdist B) : R.-fdist B := fdistbind P k.
(* while f in dmap f P is a deterministic function,
  k in dbind P k outputs a distribution. *)
(* build a new mixture random variable. draw a~P, then draw W~k(a):=Σ_a P(a)·k(a) *)
(* this is for Randomize *)

Definition dunif {R : realType} {A : finType} {n : nat} (cardA : #|A| = n.+1)
  : R.-fdist A := fdist_uniform cardA. (* for defining a unif distr over sample list *)


Lemma dmap_eq {R : realType} {A B : finType} (f g : A -> B) (P : R.-fdist A) :
  f =1 g -> dmap f P = dmap g P.
Proof.
move=> Hfg; rewrite /dmap; apply/fdist_ext => b.
rewrite !fdistmapE; apply: eq_bigl => a.
by rewrite !inE Hfg.
Qed.

Lemma dbind_eq {R : realType} {A B : finType} (P : R.-fdist A)
  (k1 k2 : A -> R.-fdist B) :
  k1 =1 k2 -> dbind P k1 = dbind P k2.
Proof.
move=> Hk; rewrite /dbind; apply/fdist_ext => b.
rewrite !fdistbindE; apply: eq_bigr => a _.
by rewrite Hk.
Qed.

Lemma dmap_comp {R : realType} {A B C : finType}
  (g : B -> C) (f : A -> B) (P : R.-fdist A) :
  dmap g (dmap f P) = dmap (g \o f) P.
Proof. by rewrite /dmap fdistmap_comp. Qed.

(* --- helper for the read-after-write lemma below --- *)
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

(* --- transparent boolean decision --- *)
(* a reducible (transparent) bool *)
Definition bdec (b : bool) : {b} + {~~ b} :=
  if b as b' return {b'} + {~~ b'}
  then left _ (erefl true)
  else right _ (erefl true).

(* dsep-core states parent-list bounds with Stdlib's [length]; mathcomp's
   seq lemmas ([index_mem] below) speak of [size].  One bridge. *)
Lemma size_length (T : Type) (s : list T) : size s = length s.
Proof. by elim: s => //= x s ->. Qed.

(* dsep-core speaks Stdlib's [In]/[member]; mathcomp speaks [\in].  Two
   more bridges, used to hand [Node]'s membership proof to dsep-core. *)
Lemma mem_In (T : eqType) (x : T) (l : list T) : x \in l -> List.In x l.
Proof.
by elim: l => [|a l IH] //=; rewrite inE => /orP[/eqP->|/IH H]; [left|right].
Qed.

Lemma In_mem (T : eqType) (x : T) (l : list T) : List.In x l -> x \in l.
Proof.
elim: l => [|a l IH] //= [->|H]; first by rewrite inE eqxx.
by rewrite inE IH ?orbT.
Qed.

  (* dom n <-> assignments nat   *)

Section Boundary.
Variable G : graph.

(* seq_sub turns the elements of a list into a finType *)
Definition Node : finType := seq_sub (nodes_in_graph G).
(* G is a section variable. When outside of this section, Node: graph -> finType *)

Unset Implicit Arguments.   (* keep the node argument of enc/dec explicit *)
Variable dom : Node -> finType.                 (* each node's own value space *)
Variable enc : forall n : Node, dom n -> nat.   (* typed value -> nat code *)
Variable dec : forall n : Node, nat -> dom n.   (* code -> typed value (total) *)
Set Implicit Arguments.
Hypothesis encK : forall n : Node, cancel (enc n) (dec n).


(* VOCABULARY (following Main.v): a CONTEXT is one experimental unit --
   a complete instantiation of the UNOBSERVABLES, i.e. the exogenous draw
   that [find_value] consumes in its [U] slot.  A WORLD is the ENDOGENOUS
   outcome, the solved node values a context gives rise to.  Everything in
   this file called "context" is exogenous; the randomness lives here and
   nowhere else, because the mechanisms are deterministic.

   The typed exogenous draw for G: node n's noise slot has type [dom n]
   (see the simplifying assumption in Part 3).  This is the dependent
   finite function type, a genuine finType, so [R.-fdist context] is
   available. *)
Definition context := {dffun forall n : Node, dom n}.

(* the other half of the vocabulary: a WORLD is the endogenous outcome,
   every node's SOLVED value.  Under the Part 3 simplifying assumption
   (noise space = value space) it has the same shape as [context]; the
   two names are kept apart because they mean different things, and they
   would genuinely diverge if noise domains were ever split off. *)
Definition world := {dffun forall n : Node, dom n}.

(* raw nat id -> Node, transparently (None iff the id is not in G) *)
Definition o_node (p : nat) : option Node :=
  match bdec (p \in nodes_in_graph G) with
  | left E => Some (@SeqSub _ _ p E)
  | right _ => None
  end.

Lemma o_node_ssval (p : nat) (nd : Node) :
  o_node p = Some nd -> ssval nd = p.
Proof. by rewrite /o_node; case: (bdec _) => E // [<-]. Qed.

(* inject a typed context (exogenous draw) into dsep-core's nat-valued
   assignment -- this is what [find_value]/[eval] take as [U], and it is
   Main.v's [context] type.  (Lemma-world only: [enum] does not compute,
   see header note.) *)
Definition to_assign (w : context) : assignments nat :=
  [seq (ssval i, enc i (w i)) | i <- enum Node].

(* read-after-write: after [to_assign] writes the context into the
   assignment, reading node i back with [get_assigned_value] returns
   exactly the code of the noise drawn for i.  The nat ids are distinct
   (ssval is injective), so first-match read returns node i's own slot. *)
Lemma to_assign_get (w : context) (i : Node) :
  get_assigned_value (to_assign w) (ssval i) = Some (enc i (w i)).
Proof.
rewrite /to_assign.
apply: get_assigned_value_map; first by move=> a b; exact: val_inj.
by rewrite mem_enum.
Qed.

(* a [Node] is a node of G, in dsep-core's boolean form *)
Lemma node_in_graph_ssval (n : Node) : node_in_graph (ssval n) G = true.
Proof.
case: n => u Hu /=; move: Hu.
rewrite /node_in_graph /nodes_in_graph; case: G => V E /= Hu.
by apply/List_Basics.member_In_equiv; apply: mem_In.
Qed.

(* COMPLETENESS: a typed context assigns every node of G, so it is a
   legitimate exogenous input [U] for [find_value]/[Main.eval].  This is
   what makes the solver total on typed contexts -- see
   [find_value_to_assign] below. *)
Lemma to_assign_complete (w : context) :
  is_assignment_for (to_assign w) (nodes_in_graph G) = true.
Proof.
rewrite /is_assignment_for; apply/forallb_forall => u Hu.
have Hu' : u \in nodes_in_graph G by apply: In_mem.
apply/assigned_is_true.
by exists (enc (@SeqSub _ _ u Hu') (w (@SeqSub _ _ u Hu')));
   exact: (to_assign_get w (@SeqSub _ _ u Hu')).
Qed.

(* ===================================================================== *)
(* Part 3: the wrapper -- typed mechanisms elaborated to nat nodefuns    *)
(* --------------------------------------------------------------------- *)
(* A TYPED mechanism for node n reads (its own exogenous slot : dom n)    *)
(* and (its parents' values, each in ITS OWN domain) and returns a value  *)
(* in dom n.  Parent values are addressed BY NODE, never by position: a   *)
(* mechanism receives a [parent_view], a lookup function that answers     *)
(* for exactly those nodes it can prove are declared parents.  [elab]     *)
(* wraps a whole typed graphfun into dsep-core's nat-valued [graphfun]:   *)
(*     elab tF n = enc . (tF n) . dec                (enc . f . dec)      *)
(* so [find_value] consumes it unchanged.                                  *)
(*                                                                        *)
(* Why by node and not by position: [find_parents] returns parents in     *)
(* EDGE-LIST order, so with a positional interface a mechanism silently   *)
(* changes meaning when the edges are reordered, or when a new parent is  *)
(* inserted rather than appended -- and the typechecker only notices when *)
(* the parents' domains happen to differ.  [elab] resolves every lookup   *)
(* through [index] into that same list, so a mechanism computes the same  *)
(* thing under any spelling of the same dag.                              *)
(*                                                                        *)
(* Addressing by node also makes [elab_compatible] structural: a          *)
(* mechanism cannot MENTION a node that is not a declared parent, because *)
(* it could not supply the [is_parent] ticket the view demands.           *)
(*                                                                        *)
(* SIMPLIFYING ASSUMPTION (noise space = value space).  The exogenous    *)
(* slot of node n shares n's domain [dom n]: one family serves both.      *)
(* This is natural because a source node (no parents) simply TAKES its    *)
(* unobservable as its value -- Z = U_Z in Part 4 -- so for those nodes   *)
(* the two spaces must coincide anyway, and for the rest a law on [dom n] *)
(* is expressive enough for the models here.                              *)
(*                                                                        *)
(* It does forbid |U_n| <> |dom n|, so a latent that selects among more   *)
(* behaviours than the node has values (principal strata: a 4-valued      *)
(* compliance type behind a binary outcome) is out of reach until noise   *)
(* domains are split off into their own family with their own codes.      *)
(* ===================================================================== *)

(* p is a declared parent of n -- a computable test, so on a concrete dag
   the ticket below is discharged by [isT] *)
Definition is_parent (n p : Node) : bool :=
  ssval p \in find_parents (ssval n) G.

(* the typed parent view of node n: read any DECLARED parent, by node,
   and get a value in THAT parent's own domain.  The [is_parent] proof is
   the ticket -- no ticket, no read, so undeclared nodes are unaskable. *)
Definition parent_view (n : Node) : Type :=
  forall p : Node, is_parent n p -> dom p.

(* a typed mechanism / a typed graphfun *)
Definition tnodefun (n : Node) : Type :=
  dom n -> parent_view n -> dom n.
Definition tgraphfun : Type := forall n : Node, tnodefun n.

(* the wrapper: one nat-valued graphfun from a whole typed graphfun.
   dsep-core hands parent values positionally along [find_parents], so a
   read of parent p is resolved by locating p's index in that same list --
   which is what makes the result independent of the edge order.  The
   [nth_default] fallback is unreachable for a declared parent (see
   [index_mem] in the proof below).  Off-graph ids keep dsep-core's
   [f_unobs] (return the unobs term), matching the house style for
   don't-care nodes. *)
Definition elab (tF : tgraphfun) : @graphfun nat :=
  fun w =>
    match o_node w with
    | Some n => fun val =>
        enc n (tF n (dec n (fst val))
                    (fun p _ => dec p
                       (nth_default 0 (snd val)
                          (index (ssval p) (find_parents (ssval n) G)))))
    | None => f_unobs nat
    end.

(* --- the wrapped graphfun reads only declared parents --- *)

(* Theorem: elaboration always produces dag-compatible mechanisms.  Every
   read a mechanism can make is at a declared parent, whose index is in
   range by [index_mem], so dsep-core's positional agreement hypothesis
   covers it.  (The typed analogue of range-closure comes with [encK] in
   the elaboration-correctness lemma, next step.) *)
Lemma elab_compatible (tF : tgraphfun) :
  Main.dag_fun_compatible G (elab tF).
Proof.
rewrite /Main.dag_fun_compatible => n u pa1 pa2 _ Hag.
rewrite /elab.
case E: (o_node n) => [nd|]; last by [].
move: (o_node_ssval E) => Hval /=.
congr (enc nd (tF nd (dec nd u) _)).
apply: functional_extensionality_dep => p.
apply: functional_extensionality_dep => Hp.
congr (dec p _).
apply: Main.nth_default_agree.
apply: Hag; apply/ltP.
rewrite Hval -size_length index_mem.
by move: Hp; rewrite /is_parent Hval.
Qed.

(* --- solving: from one context to one world -------------------------- *)

(* node n's value in the world the context w determines.  [Main.eval] is
   dsep-core's total solver; [dec] brings its nat answer back into n's
   own domain.  Deterministic in w: this is the whole point of the
   vocabulary split -- randomness is in w and nowhere else. *)
Definition solve (tF : tgraphfun) (w : context) (n : Node) : dom n :=
  dec n (Main.eval G (elab tF) (ssval n) (to_assign w)).

(* the whole world a context gives rise to *)
Definition world_of (tF : tgraphfun) (w : context) : world :=
  [ffun n => solve tF w n].

(* [Main.eval]'s [0] default is dead on typed contexts: under
   well-formedness and acyclicity the solver really does return a value
   for every node, because [to_assign_complete] supplies a COMPLETE
   exogenous assignment.  So [solve] names an actual solution rather
   than a fallback. *)
Lemma find_value_to_assign (tF : tgraphfun) (w : context) (n : Node) :
  G_well_formed G = true -> contains_cycle G = false ->
  find_value G (elab tF) (ssval n) (to_assign w) nil
  = Some (Main.eval G (elab tF) (ssval n) (to_assign w)).
Proof.
move=> Hwf Hcyc; apply: Main.eval_find_value => //.
- exact: to_assign_complete.
- exact: node_in_graph_ssval.
Qed.

End Boundary.

(* generic codes for any finType (lemma-world: [enum] does not compute;
   hand-write codes when an example must run by reflexivity) *)
Definition enc_default (T : finType) (v : T) : nat := enum_rank v.
Definition dec_default (T : finType) (x0 : T) (m : nat) : T :=
  seq.nth x0 (enum T) m.
Lemma enc_defaultK (T : finType) (x0 : T) :
  cancel (@enc_default T) (@dec_default T x0).
Proof. move=> v; exact: nth_enum_rank. Qed.

(* ===================================================================== *)
(* Part 4: Main.v's G_3 with categorical domains of varied cardinalities  *)
(* --------------------------------------------------------------------- *)
(* The 3-node confounder example (x=1 Treatment, y=2 Response, z=3        *)
(* confounder; edges x->y, z->x, z->y), read as a small drug trial:       *)
(*     Z : age       = young | middle | old            (3 values)         *)
(*     X : treatment = placebo | drug                  (2 values)         *)
(*     Y : outcome   = worse | same | better | cured   (4 values)         *)
(* Three CATEGORICAL domains, three different cardinalities, one DAG.     *)
(* Mechanisms (typed, total by construction):                             *)
(*     Z = its own noise                       (exogenous demographic)    *)
(*     X = drug if Z is old, else placebo      (confounded assignment:    *)
(*                                              the old get treated)      *)
(*     Y = table of (X, Z):  drug/young->cured, drug/_->better,           *)
(*                           placebo/old->worse, placebo/_->same          *)
(* Note the original nat-level g_3 had y = x + z, which fits NO finite    *)
(* domain; typing forces the total case table -- range closure for free.  *)
(* ===================================================================== *)

Inductive age : Type := young | middle | old.
Inductive treatment : Type := placebo | drug.
Inductive outcome : Type := worse | same | better | cured.

(* finType registration: one cancellation into 'I_k per type *)
Definition a2i (a : age) : 'I_3 :=
  match a with
  | young => @Ordinal 3 0 isT | middle => @Ordinal 3 1 isT
  | old => @Ordinal 3 2 isT
  end.
Definition i2a (i : 'I_3) : age :=
  match val i with 0 => young | 1 => middle | _ => old end.
Lemma a2iK : cancel a2i i2a.
Proof. by case. Qed.
HB.instance Definition _ := Finite.copy age (can_type a2iK).

Definition t2i (t : treatment) : 'I_2 :=
  match t with placebo => @Ordinal 2 0 isT | drug => @Ordinal 2 1 isT end.
Definition i2t (i : 'I_2) : treatment :=
  match val i with 0 => placebo | _ => drug end.
Lemma t2iK : cancel t2i i2t.
Proof. by case. Qed.
HB.instance Definition _ := Finite.copy treatment (can_type t2iK).

Definition o2i (o : outcome) : 'I_4 :=
  match o with
  | worse => @Ordinal 4 0 isT | same => @Ordinal 4 1 isT
  | better => @Ordinal 4 2 isT | cured => @Ordinal 4 3 isT
  end.
Definition i2o (i : 'I_4) : outcome :=
  match val i with 0 => worse | 1 => same | 2 => better | _ => cured end.
Lemma o2iK : cancel o2i i2o.
Proof. by case. Qed.
HB.instance Definition _ := Finite.copy outcome (can_type o2iK).

(* hand-written computable engine codes (enc/dec into nat) *)
Definition a2n (a : age) : nat :=
  match a with young => 0 | middle => 1 | old => 2 end.
Definition n2a (m : nat) : age :=
  match m with 0 => young | 1 => middle | _ => old end.
Definition t2n (t : treatment) : nat :=
  match t with placebo => 0 | drug => 1 end.
Definition n2t (m : nat) : treatment :=
  match m with 0 => placebo | _ => drug end.
Definition o2n (o : outcome) : nat :=
  match o with worse => 0 | same => 1 | better => 2 | cured => 3 end.
Definition n2o (m : nat) : outcome :=
  match m with 0 => worse | 1 => same | 2 => better | _ => cured end.

(* the graph is Main.v's G_3, stripped to its dag *)
Definition G3 : graph := Main.dag Main.G_3.

(* per-node domains: a direct match on the raw node id, which both reduces
   on literals and scales to any number of branches for free. *)
Definition dom_3 (n : Node G3) : finType :=
  match ssval n with 1 => treatment | 2 => outcome | _ => age end.

Definition enc_3 (n : Node G3) : dom_3 n -> nat :=
  match ssval n as v
    return (Finite.sort
              (match v with 1 => treatment | 2 => outcome | _ => age end)
            -> nat)
  with 1 => t2n | 2 => o2n | _ => a2n end.

Definition dec_3 (n : Node G3) (m : nat) : dom_3 n :=
  match ssval n as v
    return Finite.sort
             (match v with 1 => treatment | 2 => outcome | _ => age end)
  with 1 => n2t m | 2 => n2o m | _ => n2a m end.

(* the codes satisfy the boundary contract, all 2+4+3 values round-trip *)
Example enc_3K : forall n : Node G3, cancel (@enc_3 n) (@dec_3 n).
Proof. by move=> [[|[|[|v]]] pf] x; case: x. Qed.

(* G3's nodes, named once: X treatment, Y response, Z confounder *)
Definition x3 : Node G3 := @SeqSub _ (nodes_in_graph G3) 1 isT.
Definition y3 : Node G3 := @SeqSub _ (nodes_in_graph G3) 2 isT.
Definition z3 : Node G3 := @SeqSub _ (nodes_in_graph G3) 3 isT.

(* the typed mechanisms.  Parents are read BY NODE: [pa z3 isT] is Z's
   value no matter where the edge list happens to put Z among the
   parents, so reordering the edges of G3 cannot change what these
   mechanisms mean.  Ids other than 1..3 cannot occur in a run (no
   membership proof); the catch-all echoes the noise. *)
Definition tF_3 : tgraphfun dom_3 :=
  fun n =>
    match n return tnodefun dom_3 n with
    | SeqSub v pf =>
        (match v
           return forall pf' : v \in nodes_in_graph G3,
                  tnodefun dom_3 (SeqSub pf')
         with
         | 1 => fun _ => fun (_ : treatment) pa =>
                  if pa z3 isT is old then drug else placebo
         | 2 => fun _ => fun (_ : outcome) pa =>
                  match pa x3 isT, pa z3 isT with
                  | drug,    young => cured
                  | drug,    _     => better
                  | placebo, old   => worse
                  | placebo, _     => same
                  end
         | 3 => fun _ => fun (u : age) _ => u
         | _ => fun _ => fun u _ => u
         end) pf
    end.

(* the compiled nat-level graphfun: this is the typed replacement of
   Main.v's hand-written [g_3] *)
Definition g3_typed : @graphfun nat := elab enc_3 dec_3 tF_3.

Example g3_compatible : Main.dag_fun_compatible G3 g3_typed.
Proof. exact: elab_compatible. Qed.

(* Runs, through dsep-core's untouched find_value.  Exogenous slots:
   node 3 (Z) carries the age draw; X and Y ignore their noise here. *)

(* a young unit: Z=young, so X=placebo, so Y=same (code 1) *)
Example g3_run_young :
  find_value G3 g3_typed 2 ((1, 0) :: (2, 0) :: (3, 0) :: nil)%N nil
  = Some 1%N.
Proof. reflexivity. Qed.

(* an old unit: Z=old, so X=drug -- the confounding in action ... *)
Example g3_run_old_treated :
  find_value G3 g3_typed 1 ((1, 0) :: (2, 0) :: (3, 2) :: nil)%N nil
  = Some 1%N.
Proof. reflexivity. Qed.

(* ... and Y=better (code 2) *)
Example g3_run_old :
  find_value G3 g3_typed 2 ((1, 0) :: (2, 0) :: (3, 2) :: nil)%N nil
  = Some 2%N.
Proof. reflexivity. Qed.

(* ===================================================================== *)
(* Part 5: the exogenous law -- distributions over contexts              *)
(* --------------------------------------------------------------------- *)
(* THIS IS THE ONLY PLACE RANDOMNESS ENTERS.  A dag carries a law over    *)
(* its UNOBSERVABLES; given a context (one exogenous draw) the mechanisms *)
(* are deterministic, so the world -- the solved node values -- is a      *)
(* function of the context, and the law over worlds is the pushforward    *)
(* of this one.  (That pushforward is the next step; see the note at the  *)
(* end of this part.)                                                     *)
(*                                                                        *)
(* Every node carries its own NOISE law on its own domain,                *)
(*     P : forall n : Node G, R.-fdist (dom n),                           *)
(* and exogenous variables are mutually independent (Universal            *)
(* Assumption 2 in Main.v), so the joint law over [context] is the        *)
(* PRODUCT of the per-node laws:                                          *)
(*     fdist_context P w = \prod_n P n (w n)          [fdist_contextE]    *)
(* [fdist_context_marginal] checks the design claim from the other side:  *)
(* pushing the joint forward along [read node n's noise slot] (dmap)      *)
(* gives back exactly P n -- the joint really is the product of its       *)
(* marginals.                                                             *)
(*                                                                         *)
(* infotheo only ships the HOMOGENEOUS product (fdist_rV: n copies of one *)
(* law, over 'rV[A]_n).  [context] is a heterogeneous dependent product   *)
(* {dffun forall n, dom n}, so the sum-to-one proof needs the dependent   *)
(* distributivity lemma [bigA_distr_big_dffun] below.  It is proved by    *)
(* squeezing the dependent function space into the tagged sum {n & dom n},*)
(* where mathcomp's non-dependent [bigA_distr_big_dep] applies.           *)
(* ===================================================================== *)

Section DepDistributivity.
Import GRing.Theory.
Local Open Scope ring_scope.
Variables (R : comPzRingType) (I : finType) (J : I -> finType).
Local Notation S := {i : I & J i}.

(* a default value in every fibre.  In the application it comes for free
   from the per-node laws: no fdist lives on an empty type. *)
Variable j0 : forall i, J i.

(* sums over dependent finite functions distribute over products: the
   dependent analogue of mathcomp's [bigA_distr_bigA] *)
Lemma bigA_distr_big_dffun (F : forall i, J i -> R) :
  \prod_(i : I) \sum_(j : J i) F i j
  = \sum_(g : {dffun forall i, J i}) \prod_(i : I) F i (g i).
Proof.
pose u0 i : S := Tagged J (j0 i).
pose Fx i (s : S) : R := F i (tagged_as (u0 i) s).
pose Q i := [pred s : S | tag s == i].
(* inner sums: over the fibre J i, or over the tagged sum restricted to
   tag i -- the same thing *)
transitivity (\prod_(i : I) \sum_(s : S | Q i s) Fx i s).
  apply: eq_bigr => i _; symmetry.
  rewrite (reindex_onto (@Tagged I i J) (tagged_as (u0 i))) /=; last first.
    by case=> i' j'; rewrite /Q /= => /eqP <-; rewrite tagged_asE.
  apply: eq_big => [j | j _]; last by rewrite /Fx tagged_asE.
  by rewrite /Q /= tagged_asE !eqxx.
rewrite bigA_distr_big_dep /=.
(* outer sum: functions into the tagged sum with the right tags are
   exactly the dependent functions *)
pose phi (g : {dffun forall i, J i}) : {ffun I -> S} :=
  [ffun i => Tagged J (g i)].
pose psi (f : {ffun I -> S}) : {dffun forall i, J i} :=
  [ffun i => tagged_as (u0 i) (f i)].
rewrite (reindex_onto phi psi) /=; last first.
  move=> f /familyP Hf; apply/ffunP => i; rewrite /phi /psi !ffunE.
  have := Hf i; rewrite -topredE /=.
  by case: (f i) => i' j' /= /eqP <-; rewrite tagged_asE.
apply: eq_big => [g | g _]; last first.
  by apply: eq_bigr => i _; rewrite /Fx /phi ffunE tagged_asE.
apply/andP; split.
  by apply/familyP => i; rewrite -topredE /= /phi ffunE /= eqxx.
by apply/eqP/ffunP => i; rewrite /psi /phi !ffunE tagged_asE.
Qed.

End DepDistributivity.

Section ContextDist.
Import GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Variable G : graph.
Variable dom : Node G -> finType.
Variable R : realType.

(* every node carries its own law, on its own domain *)
Variable P : forall n : Node G, R.-fdist (dom n).

(* a default value per node, from the nonemptiness of each node's law *)
Let j0 (n : Node G) : dom n := sval (fdist_supp_mem (P n)).

Let f : {ffun context dom -> R} :=
  [ffun w : context dom => \prod_(n : Node G) P n (w n)].

Let f0 w : 0 <= f w.
Proof. by rewrite ffunE; apply: prodr_ge0. Qed.

Let f1 : \sum_(w in context dom) f w = 1.
Proof.
under eq_bigr do rewrite ffunE.
rewrite -(bigA_distr_big_dffun j0 (fun n (j : dom n) => P n j)) /=.
by apply: big1 => n _; exact: FDist.f1.
Qed.

(* the joint EXOGENOUS law: one draw of every node's unobservable, the
   product of the per-node noise laws (Universal Assumption 2) *)
Definition fdist_context : R.-fdist (context dom) := locked (FDist.make f0 f1).

Lemma fdist_contextE w : fdist_context w = \prod_(n : Node G) P n (w n).
Proof. by rewrite /fdist_context; unlock; rewrite ffunE. Qed.

(* the design claim, checked: the joint's marginal on node n is n's own
   exogenous law.  (Reading node n's noise slot out of a context is a
   deterministic function, so the marginal is a [dmap] pushforward.) *)
Lemma fdist_context_marginal (n : Node G) :
  dmap (fun w : context dom => w n) fdist_context = P n.
Proof.
apply/fdist_ext => v; rewrite /dmap fdistmapE.
(* the indicator [w n == v] as a factor of the product: the factor at
   node n compares in the tagged sum {m & dom m}, which needs no cast *)
transitivity (\sum_(w : context dom) \prod_(m : Node G)
    ((if m == n then (Tagged dom (w m) == Tagged dom v)%:R else 1) * P m (w m))).
  rewrite big_mkcond /=; apply: eq_bigr => w _; rewrite inE /=.
  rewrite big_split /= -big_mkcond /= big_pred1_eq eq_Tagged /= fdist_contextE.
  by rewrite mulr_natl mulrb.
rewrite -(bigA_distr_big_dffun j0 (fun m (j : dom m) =>
  (if m == n then (Tagged dom j == Tagged dom v)%:R else 1) * P m j)) /=.
(* the factor at node n keeps the indicator, all other factors sum to 1 *)
rewrite (bigD1 n) //= eqxx /= [X in _ * X]big1 ?mulr1; last first.
  by move=> m /negbTE -> /=; under eq_bigr do rewrite mul1r; exact: FDist.f1.
under eq_bigr do rewrite mulr_natl mulrb.
rewrite -big_mkcond /= (big_pred1 v) // => j /=.
by rewrite eq_Tagged.
Qed.

End ContextDist.

(* ===================================================================== *)
(* Part 6: the induced law -- distributions over worlds                  *)
(* --------------------------------------------------------------------- *)
(* Part 5 stops at the exogenous law P(U).  The distribution causal       *)
(* queries actually range over is the law of the SOLVED node values --    *)
(* the world -- and because the mechanisms are deterministic once the     *)
(* context is fixed, that law is a PUSHFORWARD and nothing more:          *)
(*                                                                        *)
(*     fdist_world = dmap world_of (fdist_context P)                      *)
(*                                                                        *)
(* [world_of] is the deterministic solve (Part 3), [fdist_context P] is   *)
(* the product law over unobservables (Part 5).  No new randomness is     *)
(* introduced here, and none can be: this is Main.v's M4 wrapping M2's    *)
(* total solve in [fdistmap], exactly as its header anticipates.          *)
(*                                                                        *)
(* [fdist_world_marginal] is the lemma that makes the object usable: the  *)
(* law of a single node's VALUE is the world law read at that node, which *)
(* is the same as pushing [solve ^~ n] forward directly.  Note how this   *)
(* differs from [fdist_context_marginal] in Part 5: that one recovers a   *)
(* node's NOISE law and is true by construction, whereas this one has to  *)
(* run the mechanisms.  Only at a source node do the two coincide.        *)
(*                                                                        *)
(* CAVEAT (unfinished business).  [fdist_world] is total and always       *)
(* well defined, but it is only MEANINGFUL under well-formedness and      *)
(* acyclicity -- see [find_value_to_assign], which is where those         *)
(* hypotheses discharge [Main.eval]'s default.  And nothing here yet      *)
(* connects [elab tF] running under [find_value] back to what [tF] means  *)
(* on typed values: that is the elaboration-correctness lemma flagged in  *)
(* Part 3, and it needs range-closure of [enc], not just [encK].  Until   *)
(* it exists, [solve] is "whatever dsep-core computes, decoded", not      *)
(* provably "what the typed mechanism says".                              *)
(* ===================================================================== *)

Section WorldDist.
Import GRing.Theory.
Local Open Scope ring_scope.
Variable G : graph.
Variable dom : Node G -> finType.
Variable enc : forall n : Node G, dom n -> nat.
Variable dec : forall n : Node G, nat -> dom n.
Variable tF : tgraphfun dom.
Variable R : realType.

(* the exogenous law: one law per node's unobservable (Part 5) *)
Variable P : forall n : Node G, R.-fdist (dom n).

(* THE INDUCED LAW over endogenous outcomes *)
Definition fdist_world : R.-fdist (world dom) :=
  dmap (world_of enc dec tF) (fdist_context P).

(* a world's probability is the total exogenous mass of the contexts
   that solve to it *)
Lemma fdist_worldE v :
  fdist_world v
  = \sum_(w in context dom | world_of enc dec tF w == v) fdist_context P w.
Proof. by rewrite /fdist_world /dmap fdistmapE. Qed.

(* the per-node outcome law: reading node n out of the world law is the
   same as pushing n's solved value forward directly *)
Lemma fdist_world_marginal (n : Node G) :
  dmap (fun v : world dom => v n) fdist_world
  = dmap (fun w : context dom => solve enc dec tF w n) (fdist_context P).
Proof.
rewrite /fdist_world dmap_comp; apply: dmap_eq => w.
by rewrite /= /world_of ffunE.
Qed.

End WorldDist.

(* --- Part 4 revisited: per-node NOISE laws for the drug trial --------- *)
(* Z is a source node, so it takes its unobservable as its value and the  *)
(* age draw IS Z's noise law -- the simplifying assumption of Part 3 at   *)
(* work.  X's and Y's exogenous slots are ignored by their mechanisms     *)
(* (both are deterministic in their parents), so they carry point masses  *)
(* and the choice of point is immaterial.  Three laws on three different  *)
(* domains, one joint exogenous law over the contexts of G3.              *)

(* #|age| = 3, via the bijection with 'I_3 *)
Lemma i2aK : cancel i2a a2i.
Proof.
case=> [[|[|[|m]]] Hm]; [exact: val_inj | exact: val_inj | exact: val_inj |].
by exfalso; move: Hm; rewrite !ltnS ltn0.
Qed.

Lemma card_age : #|{: age}| = 2.+1.
Proof.
by rewrite -(card_ord 3); exact: (bij_eq_card (Bijective a2iK i2aK)).
Qed.

Section G3_laws.
Variable R : realType.

Definition P_3 (n : Node G3) : R.-fdist (dom_3 n) :=
  match ssval n as v
    return R.-fdist (match v with 1 => treatment | 2 => outcome | _ => age end)
  with
  | 1 => dret placebo          (* X's noise: ignored by X's mechanism *)
  | 2 => dret worse            (* Y's noise: ignored by Y's mechanism *)
  | _ => dunif card_age        (* Z: age drawn uniformly *)
  end.

(* the joint exogenous law over G3's contexts *)
Definition P3_ctx : R.-fdist (context dom_3) := fdist_context P_3.

(* its marginal on Z's noise slot ([z3], defined with the mechanisms
   above) is the uniform age law, by the general lemma.  Because Z is a
   source node this is also Z's law as a VALUE -- the one node where the
   two coincide without pushing anything forward. *)
Example P3_ctx_marginal_z :
  dmap (fun w : context dom_3 => w z3) P3_ctx = dunif card_age.
Proof. exact: (fdist_context_marginal P_3 z3). Qed.

(* --- and the law it induces over worlds (Part 6) --- *)

(* the drug trial's outcome distribution: the age draw pushed through the
   confounded assignment and the response table *)
Definition W3 : R.-fdist (world dom_3) := fdist_world enc_3 dec_3 tF_3 P_3.

(* the law of Y's VALUE -- what the trial is actually about *)
Example W3_marginal_y :
  dmap (fun v : world dom_3 => v y3) W3
  = dmap (fun w : context dom_3 => solve enc_3 dec_3 tF_3 w y3) P3_ctx.
Proof. exact: fdist_world_marginal. Qed.

End G3_laws.

(* G3 really is solvable, so [W3] is not built on [Main.eval]'s default:
   for every context and every node the solver returns an actual value.
   (Well-formedness and acyclicity come from Main.v's [wf_G_3].) *)
Example G3_solved (tF : tgraphfun dom_3) (w : context dom_3) (n : Node G3) :
  find_value G3 (elab enc_3 dec_3 tF) (ssval n) (to_assign enc_3 w) nil
  = Some (Main.eval G3 (elab enc_3 dec_3 tF) (ssval n) (to_assign enc_3 w)).
Proof.
have [Hwf [Hcyc _]] := Main.wf_G_3.
by apply: find_value_to_assign.
Qed.


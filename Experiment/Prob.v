Set Warnings "-notation-overridden,-deprecated-library-file,-ambiguous-paths".
From HB Require Import structures.
From mathcomp Require Import all_ssreflect ssralg ssrnum finalg reals matrix.
From mathcomp Require boolp.
From infotheo Require Import ssr_ext ssralg_ext fdist proba.
From Stdlib Require Import Lia.
From Stdlib Require Import FunctionalExtensionality.
From DAGs Require Import Basics_Constr Descendants CycleDetection.
(* Require-only: Utils defines its own [index], which would shadow
   mathcomp's [seq.index] used in [elab]. *)
From Utils Require List_Basics.
From CausalDiagrams Require Import Assignments.
(* Require-only: [Interventions] imports [Nat] and [Lists], whose names
   would shadow mathcomp's.  Only the qualified [Interventions.do] is used. *)
From CausalDiagrams Require Interventions.
From Semantics Require Import FunctionRepresentation FindValue EquateValues.
From Experiment Require Main.
(* Require-only, like [Interventions]: [Correctness] imports Stdlib's list
   notations.  Only the qualified bridge lemmas are used. *)
From Experiment Require Correctness.

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

(* pushing a map through a mixture is pushing it through each mixand: the
   monad law [fmap] commutes with [bind], needed to marginalise a joint
   that has been written as "draw the first, then the second" *)
Lemma dmap_dbind {R : realType} {A B C : finType} (g : B -> C)
  (P : R.-fdist A) (k : A -> R.-fdist B) :
  dmap g (dbind P k) = dbind P (fun a => dmap g (k a)).
Proof. by rewrite /dmap /dbind /fdistmap fdistbindA. Qed.

(* pairing with a fixed first component and then projecting it away is the
   identity -- the second marginal of a one-armed joint *)
Lemma dmap_pair_snd {R : realType} {A B : finType} (a : A) (P : R.-fdist B) :
  dmap (fun p : A * B => p.2) (dmap (fun b => (a, b)) P) = P.
Proof.
rewrite dmap_comp.
have -> : (fun p : A * B => p.2) \o (fun b => (a, b)) = id
  by apply: functional_extensionality.
by rewrite /dmap fdistmap_id.
Qed.

(* Pushing a two-argument function through a PRODUCT law is the same as
   drawing the first argument and then pushing the second: the product
   really is "draw independently".  This is the monadic shape of
   independence, and it is what turns a pushforward along a function of two
   nodes into a MIXTURE over the first one. *)
Section UncurryProd.
Import GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Context {R : realType}.
Variables (A B C : finType).

Lemma dmap_uncurry_prod (Pa : R.-fdist A) (Pb : R.-fdist B) (F : A -> B -> C) :
  dmap (fun ab : A * B => F ab.1 ab.2) (Pa `x Pb)
  = dbind Pa (fun a => dmap (F a) Pb).
Proof.
apply/fdist_ext => c.
transitivity (\sum_(a : A) \sum_(b : B) (if F a b == c then Pa a * Pb b else 0)).
  rewrite [RHS]pair_bigA /= /dmap fdistmapE big_mkcond /=.
  by apply: eq_bigr => ab _; rewrite inE fdist_prodE.
rewrite /dbind fdistbindE; apply: eq_bigr => a _.
rewrite /dmap fdistmapE big_distrr /= -big_mkcond /=.
by apply: eq_bigl => b; rewrite inE.
Qed.

(* the mass [dmap] puts on a point is the mass of its fibre.  [fdistmapE]
   says this already, but with the index written [a in A | a \in preim ..],
   whose predicate will not unify with a plain [\sum_(a | p a)]; this is
   the form the proofs below need. *)
Lemma dmapE (g : A -> B) (d : R.-fdist A) (b : B) :
  dmap g d b = \sum_(x : A | g x == b) d x.
Proof.
rewrite /dmap fdistmapE big_mkcond [RHS]big_mkcond /=.
by apply: eq_bigr => x _; rewrite !inE.
Qed.

(* the mass a factorised joint puts on one cell: the first component's
   mass times the mass that component's kernel gives the second *)
Lemma dbind_pair_cell_gen (d : R.-fdist A) (k : A -> R.-fdist B)
    (u : A) (v : B) :
  dbind d (fun a => dmap (fun b => (a, b)) (k a)) (u, v) = d u * k u v.
Proof.
rewrite /dbind fdistbindE (bigD1 u) //= big1; last first.
  move=> i Hiu; rewrite /dmap fdistmapE big_pred0; last first.
    by move=> b; rewrite !inE xpair_eqE (negbTE Hiu).
  by rewrite mulr0.
rewrite addr0 /dmap fdistmapE (eq_bigl (fun a => a == v)); last first.
  by move=> a; rewrite !inE xpair_eqE eqxx.
by rewrite big_pred1_eq.
Qed.

End UncurryProd.

(* --- n iid copies of one random variable ------------------------------ *)
(* infotheo ships the n-fold-sum relation [\=sum] and the weak law [wlln],
   but only ever instantiates the sum for one specific random variable
   (aep.v's [sum_mlog_prod]).  This is the generic version -- the sum of n
   iid copies of ANY real-valued random variable -- which is what lets
   [wlln] be applied to an experiment's outcome indicator. *)
Section SumIID.
Import GRing.Theory.
Context {R : realType}.
Variables (A : finType) (P : R.-fdist A).
Local Open Scope vec_ext_scope.
Local Open Scope ring_scope.
Local Open Scope proba_scope.

Definition sum_iid n (f : {RV P -> R^o}) : {RV (P `^ n)%fdist -> R^o} :=
  fun t => \sum_(i < n) f (t ``_ i).

Lemma sum_iidE n (f : {RV P -> R^o}) : @sum_iid n.+1 f \=sum (\row_(i < n.+1) f).
Proof.
elim: n => [|n IH].
- move: (@sum_n_1 _ A P (\row_i f)).
  set g := cast_fun_rV10 _ => Hg.
  suff -> : @sum_iid 1 f = g by [].
  rewrite /g /sum_iid /cast_fun_rV10 /= mxE /=.
  by rewrite boolp.funeqE => ta; rewrite big_ord_recl big_ord0 addr0.
- rewrite [X in _ \=sum X](_ : _ =
      row_mx (\row_(i < 1) f) (\row_(i < n.+1) f)); last first.
    apply/rowP => b; rewrite !mxE; case: splitP.
      by move=> a; rewrite {a}(ord1 a) => _; rewrite mxE.
    by move=> k _; rewrite mxE.
  apply: (sum_n_cons IH _) => /= ta.
  rewrite /sum_iid /= big_ord_recl /=; congr (_ + _).
  by apply: eq_bigr => i _; rewrite mxE.
Qed.

End SumIID.

(* --- the empirical distribution of a length-INDEXED sample ------------ *)
(* infotheo has no "distribution of a sample": [fdist_uniform] is uniform
   over a whole finType, not over a multiset of draws.  This is it --
   [emp_rV s v] is the fraction of [s] equal to [v].

   The sample is a ROW VECTOR, not a list, and that is forced.  A list's
   length is data, and a type whose values have varying length cannot carry
   a LAW: [R.-fdist A] needs [A : finType], and [list A] is not one.  But
   "the empirical distribution converges to the true one" is a claim about
   the probability that a RANDOMLY DRAWN sample lands close, so the
   randomness ranges over samples and samples must have a law.  A row
   vector carries its length in its TYPE, so it does.  There is accordingly
   no single space of all samples, only a family indexed by the length --
   which is exactly why a sample size has to be fixed before the
   probability can even be named.

   Defining [emp_rV] as the pushforward of the uniform law on INDICES
   rather than by counting is what makes [emp_rV_map] -- the one fact that
   makes it useful, that tabulating COMMUTES with applying a function --
   fall out of [dmap_comp] in two lines; by counting it needs a partition
   argument.  [emp_rVE] is the counting form, and the two agree.
   [emp_rV_sum_iid] is the link to [wlln]: the empirical frequency of one
   value IS the normalised sum of indicators that the weak law averages. *)
Section EmpRV.
Import GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope proba_scope.
Local Open Scope vec_ext_scope.
Context {R : realType}.

Definition emp_rV (A : finType) (N : nat) (s : 'rV[A]_N.+1) : R.-fdist A :=
  dmap (fun i : 'I_N.+1 => s ``_ i) (dunif (card_ord N.+1)).

(* tabulating a sample and then pushing it through [f] is the same as
   running [f] on every unit and tabulating -- for free, by [dmap_comp] *)
Lemma emp_rV_map (A B : finType) (N : nat) (f : A -> B) (s : 'rV[A]_N.+1) :
  emp_rV (\row_i f (s ``_ i)) = dmap f (emp_rV s).
Proof.
rewrite /emp_rV dmap_comp; apply: dmap_eq => i /=.
by rewrite mxE.
Qed.

(* the counting form: the fraction of the sample equal to [v] *)
Lemma emp_rVE (A : finType) (N : nat) (s : 'rV[A]_N.+1) (v : A) :
  emp_rV s v = #|[set i : 'I_N.+1 | s ``_ i == v]|%:R / N.+1%:R.
Proof.
rewrite /emp_rV /dmap fdistmapE.
under eq_bigr do rewrite /dunif fdist_uniformE card_ord.
rewrite sumr_const mulr_natl; congr (_ *+ _).
by apply/eq_card => i; rewrite !inE.
Qed.

(* The empirical distribution can only land on the GRID of spacing 1/(N+1):
   it is a count over a fixed denominator, so its range is rational however
   real-valued the true law is.  Stated as "equals [k/(N+1)] for some
   [k <= N+1]" rather than "is rational", which is stronger (it pins the
   denominator) and needs no rationality predicate on a [realType].

   WHY THIS DOES NOT BLOCK CONVERGENCE.  An exact-equality claim is
   impossible against an irrational truth [p]: the error is bounded BELOW by
   [p]'s distance to the grid, which is positive.  So the hypothesis
   [emp_rV _ = fdist_context P] in [measure_source_empirical_rV] is
   satisfiable
   only when P is rational with a denominator dividing N+1 -- a restriction
   hiding in the premise rather than stated.  An [eps]-bound is therefore
   not a weakening adopted for convenience, it is the only shape of theorem
   available: [measure_source_lln] claims only that [|emp_rV - p|] is SMALL,
   never zero, and since the grid spacing 1/(N+1) tends to 0 while [eps] is
   held positive there is always room.  This is the honest reason the
   exact-sample theorems are warm-ups and the weak law is the result. *)
Lemma emp_rV_grid (A : finType) (N : nat) (s : 'rV[A]_N.+1) (v : A) :
  exists k : nat, (k <= N.+1)%N /\ emp_rV s v = k%:R / N.+1%:R.
Proof.
exists #|[set i : 'I_N.+1 | s ``_ i == v]|; split; last exact: emp_rVE.
apply: (@leq_trans #|'I_N.+1|); first exact: max_card.
by rewrite card_ord.
Qed.

(* THE BRIDGE to the weak law: the empirical frequency of [v] in the mapped
   sample is the normalised sum of indicators, which is precisely the
   quantity [wlln] bounds.  So a statement about what a program produced
   needs no new probability theory -- it rewrites into the existing one. *)
Lemma emp_rV_sum_iid (A B : finType) (PA : R.-fdist A) (N : nat)
    (f : A -> B) (v : B) (s : 'rV[A]_N.+1) :
  emp_rV (\row_i f (s ``_ i)) v
  = (@sum_iid R A PA N.+1 (Ind [set a : A | f a == v]) s) / N.+1%:R.
Proof.
rewrite emp_rVE; congr (_ / _).
rewrite /sum_iid -sum1_card natr_sum.
rewrite [RHS](bigID (fun i : 'I_N.+1 => f (s ``_ i) == v)) /=.
rewrite [X in _ + X]big1 ?addr0; last first.
  by move=> i Hi; rewrite /Ind inE (negbTE Hi).
rewrite big_mkcond /= [RHS]big_mkcond /=.
apply: eq_bigr => i _; rewrite inE mxE.
by case: ifPn => Hi; rewrite ?/Ind ?inE ?Hi.
Qed.

End EmpRV.

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

(* ...and the companion: a key no entry carries reads as [None] *)
Lemma get_assigned_value_map_none (I : eqType) (key val : I -> nat)
  (l : list I) (k : nat) :
  (forall j : I, j \in l -> key j <> k) ->
  get_assigned_value [seq (key j, val j) | j <- l] k = None.
Proof.
elim: l => [|j l IH] H; first by [].
rewrite /=; case E: (key j =? k).
- apply Nat.eqb_eq in E.
  by move: (H j (mem_head _ _) E).
- apply: IH => i Hi; apply: H; by rewrite inE Hi orbT.
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

(* ===================================================================== *)
(* A RATIO OF TWO ESTIMATES                                               *)
(* --------------------------------------------------------------------- *)
(* A conditional frequency is a quotient of two counts, and conditioning  *)
(* destroys the i.i.d. structure a weak law needs -- the number of units  *)
(* in an arm is itself random.  The standard way round is to keep both    *)
(* halves of the quotient inside the i.i.d. world and pay for the         *)
(* division separately, with a purely algebraic bound: if the numerator   *)
(* and the denominator are each within [del] of their targets, and [del]  *)
(* is small compared with the target denominator, then the quotient is     *)
(* within [4*del/b] of the target quotient.                               *)
(*                                                                        *)
(* No probability appears here.  The hypothesis [2*del <= b] is what keeps *)
(* the estimated denominator away from zero (it forces [b/2 <= bh]), and   *)
(* [a <= b] holds automatically when the numerator's event is contained in *)
(* the denominator's.                                                     *)
(* ===================================================================== *)

Section RatioClose.
Import GRing.Theory Order.TTheory Num.Def Num.Theory.
Local Open Scope ring_scope.
Variable R : realType.

Lemma ratio_close (a b ah bh del : R) :
  0 <= a -> a <= b -> 0 < b -> 2 * del <= b ->
  `|ah - a| <= del -> `|bh - b| <= del ->
  `|ah / bh - a / b| <= 4 * del / b.
Proof.
move=> Ha Hab Hb Hdb Hah Hbh.
have Hd0 : 0 <= del := le_trans (normr_ge0 _) Hah.
have Hd2 : del <= b / 2 by rewrite ler_pdivlMr // mulrC.
(* the estimated denominator cannot collapse *)
have Hbh2 : b / 2 <= bh.
  have H0 : b - bh <= b / 2.
    apply: le_trans Hd2; apply: le_trans (_ : `|b - bh| <= del).
      exact: ler_norm.
    by rewrite distrC.
  by move: H0; rewrite lerBlDr {1}(splitr b) lerD2l.
have Hbhp : 0 < bh by apply: lt_le_trans Hbh2; rewrite divr_gt0.
have Hb2bh : b <= 2 * bh.
  have H2 : b <= bh * 2 by rewrite -ler_pdivrMr //.
  by rewrite mulrC.
have Hb0 : b != 0 by rewrite gt_eqF.
have Hbh0 : bh != 0 by rewrite gt_eqF.
(* one common denominator *)
have Hnum : (ah - a) * b - a * (bh - b) = ah * b - a * bh.
  by rewrite mulrBl mulrBr opprB addrA subrK.
have Hkey : ah / bh - a / b = ((ah - a) * b - a * (bh - b)) / (bh * b).
  rewrite Hnum.
  have -> : ah / bh - a / b = ah / bh + (- a) / b by rewrite mulNr.
  by rewrite addf_div // mulNr.
rewrite Hkey normrM normfV (ger0_norm (_ : 0 <= bh * b)); last first.
  by rewrite mulr_ge0 ?ltW.
(* the numerator is within del*b of zero, twice over *)
have Hnb : `|(ah - a) * b - a * (bh - b)| <= del * b + del * b.
  apply: le_trans (ler_normB _ _) _.
  rewrite !normrM (ger0_norm (ltW Hb)) (ger0_norm Ha); apply: lerD.
  - exact: (ler_pM (normr_ge0 _) (ltW Hb) Hah (lexx b)).
  - rewrite -[del * b]mulrC; exact: (ler_pM Ha (normr_ge0 _) Hab Hbh).
apply: le_trans (_ : (del * b + del * b) / (bh * b) <= _).
  by rewrite ler_wpM2r // invr_ge0 mulr_ge0 ?ltW.
(* and 2*del*b / (bh*b) = 2*del/bh <= 4*del/b, because b <= 2*bh *)
rewrite ler_pdivrMr ?mulr_gt0 // (_ : 4 * del / b * (bh * b) = 4 * del * bh);
  last by rewrite mulrACA mulVf // mulr1.
rewrite [X in _ <= X]mulrC (_ : bh * (4 * del) = 2 * del * bh + 2 * del * bh);
  last by rewrite mulrC -mulrDl -mulrDl -natrD.
apply: lerD; rewrite -mulrA mulrCA; exact: (ler_wpM2l Hd0 Hb2bh).
Qed.

(* 4 * (u/8) = u/2, the one numeral identity the eps-delta choice needs *)
Lemma quarter_of_eighth (u : R) : 4 * (u / 8) = u / 2.
Proof.
rewrite mulrA; apply/eqP; rewrite eqr_div ?pnatr_eq0 //.
by rewrite mulrAC -natrM mulrC.
Qed.

End RatioClose.

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

(* --- overwriting one coordinate of a context ------------------------- *)

(* [upd a x w] is w with a's slot replaced by x.  The dependent cast is
   unavoidable: the branch taken when [m == a] must deliver a [dom m],
   and what is in hand is an [x : dom a].  [eqP]'s equality is what
   transports it, and the four lemmas below are everything that is ever
   needed of the definition. *)
Definition upd (a : Node) (x : dom a) (w : context) : context :=
  [ffun m => if @eqP _ m a is ReflectT E then ecast k (dom k) (esym E) x
             else w m].

Lemma updE (a : Node) (x : dom a) (w : context) : @upd a x w a = x.
Proof.
rewrite /upd ffunE; case: eqP => [E|H]; last by case: (H erefl).
by rewrite (eq_irrelevance (esym E) (erefl a)).
Qed.

Lemma updO (a : Node) (x : dom a) (w : context) (m : Node) :
  m != a -> @upd a x w m = w m.
Proof.
move=> Hm; rewrite /upd ffunE; case: eqP => // E.
by rewrite E eqxx in Hm.
Qed.

(* a second overwrite at the same slot wins outright *)
Lemma updK (a : Node) (x y : dom a) (w : context) :
  @upd a x (@upd a y w) = @upd a x w.
Proof.
apply/ffunP => m; case: (altP (m =P a)) => [->|Hm].
- by rewrite !updE.
- by rewrite !updO.
Qed.

(* overwriting changes nothing exactly when the slot already held x *)
Lemma upd_fix (a : Node) (x : dom a) (w : context) :
  (@upd a x w == w) = (w a == x).
Proof.
apply/eqP/eqP => [H|H].
- by move: (@updE a x w); rewrite H.
- apply/ffunP => m; case: (altP (m =P a)) => [->|Hm].
  + by rewrite updE H.
  + by rewrite updO.
Qed.

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

(* a nat that names no node of G is unassigned: [to_assign] only ever
   writes keys of the form [ssval i] *)
Lemma to_assign_get_outside (w : context) (k : node) :
  k \notin nodes_in_graph G -> get_assigned_value (to_assign w) k = None.
Proof.
move=> Hk; rewrite /to_assign.
apply: get_assigned_value_map_none => j _.
case: j => u Hu /= E; move: Hk; by rewrite -E Hu.
Qed.

(* contexts agreeing away from [a] give assignments agreeing away from
   [ssval a].  Stated over raw nats, since that is what the engine reads:
   off the graph both sides are [None], on it both are the node's own
   slot. *)
Lemma to_assign_agree_off (a : Node) (w w' : context) :
  (forall m : Node, m != a -> w m = w' m) ->
  forall k : node, k <> ssval a ->
    get_assigned_value (to_assign w) k = get_assigned_value (to_assign w') k.
Proof.
move=> Hoff k Hk; case Hin: (k \in nodes_in_graph G); last first.
  by rewrite !to_assign_get_outside // Hin.
have Hka : (@SeqSub _ (nodes_in_graph G) k Hin) != a.
  by apply/eqP => E; apply: Hk; rewrite -E.
by rewrite -[k]/(ssval (@SeqSub _ _ k Hin)) !to_assign_get (Hoff _ Hka).
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

(* --- source nodes: the first instance of elaboration correctness ------ *)

(* [o_node] is a retraction of [ssval] on genuine nodes *)
Lemma o_node_self (n : Node) : o_node (ssval n) = Some n.
Proof.
case: n => u Hu; rewrite /o_node /=.
case: (bdec _) => E; last by rewrite Hu in E.
by congr Some; apply: val_inj.
Qed.

(* A node with NO PARENTS whose mechanism reads ONLY its own noise -- i.e.
   [tF n u pa = g u] for some [g : dom n -> dom n], with [pa] appearing
   nowhere -- takes the value [g] assigns to the noise drawn for it:
   [solve] applies [g] to the context.  The pure echo is the case [g = id].

   The mechanism is not required to be the identity, only to be independent
   of the parent view; [g] is arbitrary.  (With [find_parents = nil] every
   [tnodefun] at [n] is in fact [pa]-independent, since [parent_view n] is
   then a type with essentially one inhabitant -- but [g] has to be named to
   say what the answer IS.)

   This is the first case where the solver is proved to compute what the
   typed mechanism SAYS, rather than merely something total.  It works here
   because the value round-trips as enc -> dec -> enc -> dec, so every step
   is [encK]; it never needs [enc (dec m) = m], the range-closure property
   that blocks the general elaboration-correctness lemma. *)
Lemma solve_source (tF : tgraphfun) (w : context) (n : Node)
    (g : dom n -> dom n) :
  G_well_formed G = true -> contains_cycle G = false ->
  find_parents (ssval n) G = nil ->
  (forall (u : dom n) (pa : parent_view n), tF n u pa = g u) ->
  solve tF w n = g (w n).
Proof.
move=> Hwf Hcyc Hnp Hmech.
have [P [_ Hfv]] :=
  find_value_gives_value_of_node G (elab tF) (to_assign w) (ssval n)
    (conj Hwf Hcyc) (conj (to_assign_complete w) (node_in_graph_ssval n)).
have Hval : find_value G (elab tF) (ssval n) (to_assign w) nil
            = Some (enc n (g (w n))).
  rewrite Hfv /get_value_of_node /= to_assign_get Hnp /=.
  by rewrite /elab o_node_self /= encK Hmech.
rewrite /solve /Main.eval Hval.
exact: encK.
Qed.

(* --- intervening: the typed do-surgery ------------------------------- *)

(* [solve] above runs the model as given.  [solve_do a v] runs the model
   SURGERED at a: a's mechanism is replaced by the constant v and a's
   incoming edges are cut.  Both pieces are Main.v's [semantic_do], which
   is a DENOTATION -- a second way to read the same model, not an
   operation a protocol performs.  That matters here: the typed layer gets
   an interventional law without any new program construct.

   Note what [solve_do] does NOT read: a's own exogenous slot [w a].  The
   constant mechanism ignores both parents and noise, so a's draw is dead
   -- which is exactly what "setting a" should mean.  The rest of the
   context is untouched, so every OTHER node still runs on its own noise. *)
Definition solve_do (tF : tgraphfun) (a : Node) (v : dom a)
    (w : context) (n : Node) : dom n :=
  dec n (odflt 0 (Main.semantic_do (ssval a) (enc a v) G (elab tF)
                    (ssval n) (to_assign w))).

(* [solve_do] is [solve] on the surgered model: same total-evaluator
   shape, so the [0] default is dead for the same reason (see
   [find_value_to_assign], which transfers because [do] preserves the
   node list).  Stated so proofs can unfold either side. *)
Lemma solve_doE (tF : tgraphfun) (a : Node) (v : dom a)
    (w : context) (n : Node) :
  @solve_do tF a v w n
  = dec n (Main.eval (Interventions.do (ssval a) G)
             (Main.do_graphfun (ssval a) (enc a v) (elab tF))
             (ssval n) (to_assign w)).
Proof.
rewrite /solve_do /Main.semantic_do /Main.eval.
by case: (find_value _ _ _ _ _).
Qed.

(* L2', WHAT [solve_do] DOES NOT READ.  Setting a kills a's draw: the
   constant mechanism discards both the parents and the noise term, so a's
   slot is consulted only for its Some/None status.  Every OTHER node
   still runs on its own noise, which is why this is an agreement-off-[a]
   statement rather than an independence-of-[w] one.  Until now this was
   a comment; [Correctness.find_value_U_ext_ignore] makes it a lemma. *)
Lemma solve_do_off (tF : tgraphfun) (a : Node) (v : dom a)
    (w w' : context) (n : Node) :
  (forall m : Node, m != a -> w m = w' m) ->
  @solve_do tF a v w n = @solve_do tF a v w' n.
Proof.
move=> Hoff.
suff H : find_value (Interventions.do (ssval a) G)
           (Main.do_graphfun (ssval a) (@enc a v) (elab tF))
           (ssval n) (to_assign w) nil
       = find_value (Interventions.do (ssval a) G)
           (Main.do_graphfun (ssval a) (@enc a v) (elab tF))
           (ssval n) (to_assign w') nil.
  by rewrite /solve_do /Main.semantic_do H.
apply: (@Correctness.find_value_U_ext_ignore _ _ _ _ (ssval a)
          (@enc a (w a)) (@enc a (w' a))).
- exact: (to_assign_agree_off Hoff).
- exact: to_assign_get.
- exact: to_assign_get.
- move=> r1 r2 p.
  by rewrite /Main.do_graphfun Nat.eqb_refl.
Qed.

(* setting a node to v makes it v -- the one value [solve_do] computes
   without consulting the mechanisms at all *)
Lemma solve_do_self (tF : tgraphfun) (a : Node) (v : dom a) (w : context) :
  G_well_formed G = true -> contains_cycle G = false ->
  @solve_do tF a v w a = v.
Proof.
move=> Hwf Hcyc; rewrite /solve_do.
rewrite (Correctness.semantic_do_self G (elab tF) (ssval a) (@enc a v)
           (to_assign w) Hwf Hcyc (node_in_graph_ssval a) (to_assign_complete w)).
exact: encK.
Qed.

(* --- randomizing: the same surgery, read as a do --------------------- *)

(* [solve_rand a] runs the model with a's mechanism replaced by "return
   your own exogenous slot" -- the typed reading of a [Randomize a] step.
   Unlike [solve_do] it READS a's noise, and that is the whole difference
   between the two surgeries: the value a takes is the draw the context
   already carries. *)
Definition solve_rand (tF : tgraphfun) (a : Node) (w : context) (n : Node)
  : dom n :=
  dec n (Main.eval G (Main.randomize_graphfun (ssval a) (elab tF))
           (ssval n) (to_assign w)).

(* L1, THE TYPED RANDOMIZE/DO BRIDGE.  Randomizing a and solving is
   intervening on a at the value a's own slot happens to hold.  The
   per-unit content is [Correctness.randomize_semantic_do], already
   general in the graph; the only gap was bookkeeping, since that theorem
   writes the draw at the HEAD of the exogenous list while the typed layer
   hands over [to_assign w], which already maps a to the same value.
   [Correctness.find_value_cons_redundant] closes it, and needs no
   hypothesis: the engine reads the assignment only through
   [get_assigned_value], which takes the first match. *)
Lemma solve_randE (tF : tgraphfun) (a : Node) (w : context) (n : Node) :
  G_well_formed G = true -> contains_cycle G = false ->
  @solve_rand tF a w n = @solve_do tF a (w a) w n.
Proof.
move=> Hwf Hcyc.
have Hred : find_value G (Main.randomize_graphfun (ssval a) (elab tF))
              (ssval n) (to_assign w) nil
            = Main.semantic_do (ssval a) (@enc a (w a)) G (elab tF)
                (ssval n) (to_assign w).
  rewrite -(Correctness.find_value_cons_redundant _ _ _ _ _ _ _
              (to_assign_get w a)).
  apply: Correctness.randomize_semantic_do.
  - exact: Hwf.
  - exact: Hcyc.
  - exact: node_in_graph_ssval.
  - exact: to_assign_complete.
  - exact: node_in_graph_ssval.
rewrite /solve_rand /solve_do /Main.eval Hred.
by case: (Main.semantic_do _ _ _ _ _ _).
Qed.

(* ...so the randomized node logs its own draw *)
Lemma solve_rand_self (tF : tgraphfun) (a : Node) (w : context) :
  G_well_formed G = true -> contains_cycle G = false ->
  @solve_rand tF a w a = w a.
Proof.
move=> Hwf Hcyc; rewrite (solve_randE tF a w a Hwf Hcyc).
exact: (@solve_do_self tF a (w a) w Hwf Hcyc).
Qed.

End Boundary.

(* [a] appears in [x]'s type, so the auto-implicit rule would hide it. *)
Arguments upd {G dom} a x w.
Arguments updE {G dom} a x w.
Arguments updO {G dom} a x w m.
Arguments updK {G dom} a x y w.
Arguments upd_fix {G dom} a x w.

(* [a] appears in [v]'s type, so the auto-implicit rule would hide it;
   both stay explicit, as [solve]'s arguments do. *)
Arguments solve_do {G dom} enc dec tF a v w n.

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

(* The JOINT marginal at two DISTINCT nodes is the product of the two
   marginals -- the two-node version of [fdist_context_marginal], and the
   lemma any two-node query needs.  Same proof shape: insert an indicator
   at each of the two nodes as an extra factor, exchange sum and product by
   the dependent distributivity law, and then every factor except those two
   sums to 1.  Distinctness is what keeps the two isolated factors from
   colliding. *)
Lemma fdist_context_pair (x y : Node G) : x != y ->
  dmap (fun w : context dom => (w x, w y)) fdist_context
  = (P x) `x (P y).
Proof.
move=> Hxy; apply/fdist_ext => v; case: v => v1 v2.
rewrite /dmap fdistmapE fdist_prodE /=.
transitivity (\sum_(w : context dom) \prod_(m : Node G)
    ((if m == x then (Tagged dom (w m) == Tagged dom v1)%:R else 1)
     * (if m == y then (Tagged dom (w m) == Tagged dom v2)%:R else 1)
     * P m (w m))).
  rewrite big_mkcond /=; apply: eq_bigr => w _; rewrite inE /=.
  rewrite !big_split /= -!big_mkcond /= !big_pred1_eq !eq_Tagged /=.
  rewrite fdist_contextE xpair_eqE.
  by rewrite -natrM mulnb mulr_natl mulrb.
rewrite -(bigA_distr_big_dffun j0 (fun m (j : dom m) =>
  (if m == x then (Tagged dom j == Tagged dom v1)%:R else 1)
  * (if m == y then (Tagged dom j == Tagged dom v2)%:R else 1)
  * P m j)) /=.
transitivity (\prod_(i : Node G)
   (if i == x then P x v1 else if i == y then P y v2 else 1)).
  apply: eq_bigr => i _.
  case: (altP (i =P x)) => [->|Hix].
    rewrite (negbTE Hxy) /=.
    under eq_bigr do rewrite mulr1 mulr_natl mulrb.
    rewrite -big_mkcond /= (big_pred1 v1) // => j /=.
    by rewrite eq_Tagged.
  case: (altP (i =P y)) => [->|Hiy].
    under eq_bigr do rewrite mul1r mulr_natl mulrb.
    rewrite -big_mkcond /= (big_pred1 v2) // => j /=.
    by rewrite eq_Tagged.
  under eq_bigr do rewrite !mul1r.
  exact: FDist.f1.
have Hyx : y != x by rewrite eq_sym.
rewrite (bigD1 x) //= eqxx (bigD1 y) //= (negbTE Hyx) eqxx.
by rewrite big1 ?mulr1 // => i /andP[/negbTE -> /negbTE ->].
Qed.

(* ===================================================================== *)
(* L2: SPLITTING ONE COORDINATE OFF THE EXOGENOUS LAW                     *)
(* --------------------------------------------------------------------- *)
(* [fdist_context_marginal] and [fdist_context_pair] factor the law at
   finitely many NAMED slots, and both go through by inserting an
   indicator as an extra factor of the product.  That technique needs the
   summand to be a product of per-node functions, so it cannot reach a
   predicate like "this whole context solves to v" -- which is the shape
   a mechanism produces.

   What works instead is the coordinate overwrite.  A summand that does
   not read slot [a] takes the same value on every context with a given
   off-[a] part, so the sums over the fibres of [w |-> w a] all agree, and
   that is exactly independence of the [a] slot from everything else. *)

(* the fibres of [w |-> w a] carry equal sums, for any summand and any
   side condition that both ignore slot [a] *)
Lemma big_context_off (a : Node G) (q : context dom -> bool)
    (h : context dom -> R) (x y : dom a) :
  (forall w w' : context dom,
     (forall m : Node G, m != a -> w m = w' m) -> q w = q w') ->
  (forall w w' : context dom,
     (forall m : Node G, m != a -> w m = w' m) -> h w = h w') ->
  \sum_(w : context dom | (w a == x) && q w) h w
  = \sum_(w : context dom | (w a == y) && q w) h w.
Proof.
move=> Hq Hf.
rewrite (reindex_onto (upd a x) (upd a y)); last first.
  move=> w /andP[/eqP Hw _]; rewrite updK.
  by apply/eqP; rewrite upd_fix Hw.
apply: eq_big => [w|w _]; last by apply: Hf => m Hm; exact: updO.
rewrite updE eqxx /= updK upd_fix andbC; congr (_ && _).
by apply: Hq => m Hm; exact: updO.
Qed.

(* L2.  The pair (a's slot, anything that does not read it) is drawn by
   first drawing the slot from [P a] and then running the rest on the
   untouched law.  No positivity, no well-formedness: this is a statement
   about the product form of [fdist_context] alone. *)
Theorem dmap_split_off (a : Node G) (B : finType)
    (F : dom a -> context dom -> B) :
  (forall (x : dom a) (w w' : context dom),
     (forall m : Node G, m != a -> w m = w' m) -> F x w = F x w') ->
  dmap (fun w : context dom => (w a, F (w a) w)) fdist_context
  = dbind (P a) (fun x => dmap (fun y => (x, y)) (dmap (F x) fdist_context)).
Proof.
move=> HF; apply/fdist_ext => -[u v].
(* the a-free side condition, and the a-free part of the product *)
set Q := fun w : context dom => F u w == v.
have HQ : forall w w' : context dom,
    (forall m : Node G, m != a -> w m = w' m) -> Q w = Q w'.
  by move=> w w' H; rewrite /Q (HF u w w' H).
set R0 := fun w : context dom => \prod_(m : Node G | m != a) P m (w m).
have HR0 : forall w w' : context dom,
    (forall m : Node G, m != a -> w m = w' m) -> R0 w = R0 w'.
  by move=> w w' H; apply: eq_bigr => m Hm; rewrite H.
have Hsplit : forall w : context dom, fdist_context w = P a (w a) * R0 w.
  by move=> w; rewrite fdist_contextE /R0 (bigD1 a).
(* left side: the cell (u,v) is the a-slot mass times an a-restricted sum *)
have HL : dmap (fun w : context dom => (w a, F (w a) w)) fdist_context (u, v)
        = P a u * \sum_(w : context dom | (w a == u) && Q w) R0 w.
  rewrite dmapE.
  transitivity (\sum_(w : context dom | (w a == u) && Q w) fdist_context w).
    rewrite big_mkcond [RHS]big_mkcond /=.
    apply: eq_bigr => w _; rewrite xpair_eqE /Q.
    case: (altP (w a =P u)) => [Heq|Hne]; last by [].
    by rewrite Heq.
  rewrite big_distrr /=.
  by apply: eq_bigr => w /andP[/eqP Hw _]; rewrite Hsplit Hw.
(* right side: the same mass times the unrestricted sum *)
have HR : dbind (P a)
            (fun x => dmap (fun y => (x, y)) (dmap (F x) fdist_context)) (u, v)
        = P a u * \sum_(w : context dom | Q w) fdist_context w.
  by rewrite dbind_pair_cell_gen dmapE.
rewrite HL HR; congr (_ * _); symmetry.
(* the two sums agree: partition the free one by the a slot, and every
   fibre carries the same sum because neither Q nor R0 reads it *)
transitivity (\sum_(w : context dom | Q w) (P a (w a) * R0 w)).
  by apply: eq_bigr => w _; exact: Hsplit.
transitivity (\sum_(x : dom a)
                \sum_(w : context dom | Q w && (w a == x)) (P a (w a) * R0 w)).
  by rewrite (partition_big (fun w : context dom => w a) xpredT).
transitivity (\sum_(x : dom a)
   (P a x * \sum_(w : context dom | (w a == u) && Q w) R0 w)); last first.
  by rewrite -big_distrl /= FDist.f1 mul1r.
apply: eq_bigr => x _.
transitivity (\sum_(w : context dom | (w a == x) && Q w) (P a x * R0 w)).
  apply: eq_big.
  - by move=> w; rewrite andbC.
  - by move=> w /andP[_ /eqP Hw]; rewrite Hw.
rewrite -big_distrr /=.
by rewrite (@big_context_off a Q R0 x u HQ HR0).
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
(* [fdist_node] is what makes the object usable: the law of a SINGLE       *)
(* node's value, which is what a causal query ranges over.                *)
(* [fdist_world_marginal] proves the two routes to it agree -- read the   *)
(* world law at that node, or push [solve ^~ n] forward directly.         *)
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

(* THE LAW OF ONE NODE'S VALUE -- the abstract program's per-node output,
   and what a causal query actually ranges over.  The exogenous law pushed
   forward along "solve for n": all the randomness is in the context, the
   mechanisms are deterministic, so this is a [dmap] and nothing more. *)
Definition fdist_node (n : Node G) : R.-fdist (dom n) :=
  dmap (fun w : context dom => solve enc dec tF w n) (fdist_context P).

(* the two routes to it agree: read node n out of the world law, or push
   n's solved value forward directly.  Note how this differs from
   [fdist_context_marginal] in Part 5 -- that one recovers a node's NOISE
   law and holds by construction, whereas this one has to run the
   mechanisms.  Only at a source node do the two coincide. *)
Lemma fdist_world_marginal (n : Node G) :
  dmap (fun v : world dom => v n) fdist_world = fdist_node n.
Proof.
rewrite /fdist_world /fdist_node dmap_comp; apply: dmap_eq => w.
by rewrite /= /world_of ffunE.
Qed.

(* THE INTERVENTIONAL LAW.  [fdist_node] above is what the model says a
   node's value looks like when the model is left alone; this is what it
   looks like when a is HELD at v.  Same exogenous law, same mechanisms
   everywhere but a, surgered solve: so P(n | do(a := v)) is again a
   pushforward and nothing more, and in particular it needs no new
   randomness and no new program operation.

   This is the object a causal query asks about.  Nothing here connects it
   to any PROTOCOL yet -- that is what a trial has to earn, and what
   [Rct3.v] earns for the confounded trial. *)
Definition fdist_do (a : Node G) (v : dom a) (n : Node G) : R.-fdist (dom n) :=
  dmap (fun w : context dom => solve_do enc dec tF a v w n) (fdist_context P).

End WorldDist.

Arguments fdist_do {G dom} enc dec tF {R} P a v n.

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


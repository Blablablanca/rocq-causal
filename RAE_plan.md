# Experiments as Programs — Project Plan

Formal framework (in Rocq) for expressing scientific experiments as programs over causal models, so experimental designs can be checked for correctness with program-analysis techniques (e.g., d-separation).

## Motivation

Historically, experiments are error prone: unidentified non-causal influence paths, bad proxies, unexecutable designs. If we treat an experiment as a program transforming a causal model, we can statically verify the design.

A **correct design** means:

1. **Validity** — the experiment successfully measures the effect of the treatment(s) on the response(s).
*Graphically:* the post-experiment graph d-separates T and R from all non-causal influence, and T and R remain reachable via the intended causal path.
*Algebraically:* the outcome law identifies P(R|do(T))
2. **Executability** — all controlled/intervened nodes are not labeled unmeasurable.

## Architecture: two probabilistic programs

the causal model and the experiment are **both
probabilistic programs**.
- The causal model simulates the abstract impact of the experiment steps on a "population"/concept level. Formally, the causal model is a tuple of <G,F>, aug_dag and graphfun, that denotes a probability distribution over the random variables (TBD: over the unoservable values or the leaf nodes or all nodes in the graph)
- The experiment program simulates the concrete impact of each step on each experimental units. Formally, while it also takes <G,F>, it starts with a "sampling" process that randomly draw (TBD: how many? concrete number or variable? a number at all?) samples (TBD: context? or only the intrinsic properties that's sample dependent?) from the population distribution. Each experimental step is applied to the units;the changes propagates in the graph through graphfun; we collect the values of the response nodes (measurement log), which is the output of the program (or the empirical distribution).
- correctness: vaguely (backed up by my "rigorous" stats knowledge), the empirical distribution is a consistent estimator of the "true" distribution - what the causal model outputs.

### 1. The causal model is one object: `⟨G, F⟩`

The DAG is the *syntax* (who may depend on whom — the variable-dependency
structure of the program text); the graphfun is the *semantics* (how — the
assignment bodies). Neither is a separate artifact:

```coq
Record model := {
  structure : aug_graph;        (* dag + labels : the syntax *)
  mech      : @graphfun nat;    (* node bodies  : the semantics *)
}.

Definition wf_model (M : model) : Prop :=
  wf_aug_graph (structure M) /\
  dag_fun_compatible (dag (structure M)) (mech M).
```

`dag_fun_compatible` (already in `Main.v`) is the glue invariant — F reads only
the parents G declares. It is exactly the "syntax and semantics agree"
condition, and it is preserved by every operation (a proof obligation per op).

**Denotation** — the model is a probabilistic program with free exogenous
variables, i.e. a *markov kernel* (a func from an input to a distribution over outputs):

```
⟦M⟧ : fdist U  →  fdist world        (world ≅ assignments over a value finType V)
```

defined as the pushforward (`fdistmap`) of the innate law along the deterministic
solve (Pearl's SCM form: all randomness up front, then solve). The **solve** is
dsep-core's existing `nat`-valued `find_value`, reached through a boundary map
`to_assign : world → assignments nat` (D5) — the causal value layer is never
re-typed. This reuses the evaluator wholesale and needs no enumeration of worlds.
The pushforward form covers straight-line programs, `If`, and bounded loops; only
unbounded recursion would force a fully monadic evaluator, so definitions stay
monadic to keep that door open.

### 2. The experiment is a separate probabilistic program

```
⟦e⟧_M : dist U  →  dist log
```
domain lives here, can be a type.
- **Input** = the population law over innate characteristics (exogenous U).
  The old `sample : list individual` is just the empirical distribution `uniform {u₁ … uₙ}`
  (each u_i is a world, and this is a multiset)
  supplied as input. Sample-dependence disappears from the semantics; finite-
  sample estimation returns later as a statistics layer on top (i.i.d. draws
  from `⟦e⟧(P_U)`).
- **The experiment brings its own coins.** Randomizer draws are the
  experiment's randomness, drawn *fresh at run time* — never pre-baked into the
  innate individual. Per D3 (revised, shadow encoding) the draw is written into
  the randomized node's exogenous slot `U_n`, which `f_n = f_unobs` then reads;
  because it is a fresh independent draw made during the run, the input law
  `P_U` still enters pristine and nothing needs pre-injecting into the
  individual. This resolves the previously flagged open decision ("where do
  per-unit randomizer draws live") and closes the known gap.
- **AST**: start with `operations = list operation` (the straight-line
  fragment), later generalize to `Seq`/`If` (+ bounded loops). `If` on measured
  data is what expresses adaptive designs and dynamic treatment regimes
  (Robins' g-formula) — a static list cannot, because the operation's argument
  depends on runtime data.

### 3. The structural (dag) layer is a *derived projection*, not a parallel definition

`α M = structure M`. The abstract transform is the structural component of the
one model transform, and the soundness statement `α (step op M) = abs_step op
(α M)` is now provable definitionally. (this is a commuting square. Two routes to the same graph:
- do the real full-model step, then project to the graph;
- project to the graph first, then do the cheap graph-only step.)

Static checks (backdoor etc.) read
only `α M`, stay X-free and decidable, and quantify over mechanisms as
`∀ M, structure M = G → …`.

When `If` arrives there is no single post-experiment DAG (the model you end up
with depends on measured data), so the abstract layer becomes a *sound
over-approximation* (join of branch graphs). That is where abstract
interpretation properly re-enters — as an approximation of the distribution
transformer, which stays the well-defined object.

## Decision log

Decisions taken 2026-07-23 (each was a consulted designer's choice):

| # | decision | alternative considered, and why this wins |
|---|---|---|
| D1 | The node set should never change. so `Randomize n` = `remove_incoming n` | Randomization *is* an intervention whose value is drawn — the coin belongs to the experiment, not the model. For non-compliance, IV should be already in the graph. In real world, the random variables will always be there, and we can only interact with their relationships. |
| D2 | P_U is an **input**, not stored inside the model record ⟨G, F⟩ | *Alt:* make P_U a model field (`model = {G; F; exo}`, a closed distribution). Chosen form works because (D1) the node set never changes *during a run*. (Under D3-revised the randomizer coin overwrites `U_n`, so innate and experimental randomness are no longer fully separated *inside* `U` — but `P_U` still enters as an external input, which is what this decision is about.) |
| D3 | **shadow encoding**: the randomized node reads its own exogenous slot (`f_n := f_unobs`), and that slot `U_n` is set to a fresh independent draw from the coin `d_n`, injected at run time; `d_n` is an *abstract* distribution (D6), not hardcoded uniform | *Alt (was chosen):* draw `v` then force a constant intervention (`f_n := const v`), leaving `U` untouched. Shadow chosen because it (a) matches the mechanism the code already uses (`randomize_graphfun` = `f_unobs`), and (b) fits the "all randomness up front, then one deterministic solve" pushforward denotation `⟦M⟧ = fdistmap solve`. Costs: `U_n` is overwritten by the experimenter's coin (no longer purely innate), and "randomize = `do`" is now a *theorem* (`randomize_semantic_do`), not definitional. Structural rule (`remove_incoming`, D1) is unchanged — `f_unobs` ignores parents either way. |
| D4 | **Import infotheo** (`fdist` over `R`), *not* a homemade layer | *Alt:* homemade `dist = list (A*Q)` (computable, but hand-rolls every lemma + setoid tax) or `list (A*R)` (loses computation *and* has no toolkit). RCT theorems are symbolic/parametric, so Q's computation edge is moot; R avoids the setoid tax and brings `bigop`/`lra`/CI machinery. Already installed (infotheo 0.9.7 / mathcomp 2.5.0 / analysis 1.16.0 / Rocq 9.1.0); cost is the finType encoding, contained by D5. |
| D5 | **Keep `nat`-valued mechanisms; encode only at the distribution boundary** | So the probability side wants context as a finType like `{ffun Node -> V}` (with `V` a finite value type, e.g. `bool`), and the causal side wants `assignments nat`. Keeping `nat` reuses the causal core *verbatim*; encoding cost concentrates in one bridge file (`context : finType`, `to_assign : context → assignments nat`, read-after-write + range lemmas). |
| D6 | **No `dom` yet: shared value finType `V` + abstract randomizer `d_n`** | *Alt:* thread `dom : node_card` now and draw `uniform (node_dom dom n)`. Rejected because `dom`'s two jobs split — sample space becomes "pick a finType `V`" (start `bool`), and "coin is uniform" is a needless specialization. Abstract `d_n` proves a **stronger** theorem (RCT correct for any coin independent of U; uniform is a corollary) and defers per-node `dom` to M7. |

Still open (bring to supervisor):
- `Measure` when the solve fails (`find_value = None`): prove totality under `wf`
  and drop the `option` (preferred — avoids stacking `fdist` on `option`), or
  carry option values in the log. **M2.**
- **Identifiability positivity**: Theorem B needs the coin `d_n` to have full
  support on `V` (overlap), and needs independence of confounders. Both hold for
  the RCT by construction; state them as explicit hypotheses on `d_n`.
- Whether to state distribution equality as infotheo's `=` on `fdist` (Leibniz,
  via `fdist_ext`) throughout, or wrap a coarser event-equality relation. Default
  to `fdist` `=`; revisit only if it forces awkward extensionality obligations.
- Timing of `Stratify` / `Timestep` / bounded loops.

## Core Definitions

### Node labels

```coq
Inductive node_label : Type :=
  | Treatment
  | Response
  | Unmeasurable
  | Unlabeled.
```

- `Unmeasurable` nodes cannot be measured and thus cannot be conditioned on.
- Treatment and response should generalize to **sets/vectors of nodes**: the objective is P(R | do(T)) where T and R are vectors. Do not hard-code |T| = |R| = 1.
- Sequential / time-varying treatments: sequential `Intervene`/`Randomize`; adaptive versions need `If` (Robins' g-formula).
- The response may not be directly measurable in reality; the user decides whether to use a proxy as the response node or model response as a function of other nodes.
- Simplifying assumptions: no measurement error, no execution error. Also see "Universal Assumptions" in `Experiment/Main.v`.
- Edge labels (time-step edges, correlation edges) are deferred.

### Operations

```coq
Inductive operation : Type :=
  | Intervene (n : node) (v : nat)   (* do(n=v): set n to a specific value *)
  | Randomize (n : node)             (* n's value is drawn by the experimenter's coin *)
  | Measure   (n : node).            (* record n's current value into the log *)
```

- Minimal set {intervene, randomize, measure}; one abstract `Measure` is deliberate.
- `Randomize` carries **no fresh randomizer node** (D1).
- `Control` still excluded (lacks a clear characterization). Planned: `Control`, `Stratify`, `Timestep`, then `Seq`/`If`.

### Transformation rules (one transform, two projections)

| op | structural (`α`) | mechanism | observation |
|---|---|---|---|
| `Intervene n v` | remove incoming edges to `n` | `f_n := const v` | — |
| `Randomize n` | remove incoming edges to `n` | draw `v ~ d_n` (abstract coin, D6), then `f_n := const v` (D3) | — |
| `Measure n` | — | — | append `n`'s current value to the log |

`Intervene` and `Randomize` are structurally identical; they differ only in
where n's value comes from. `Measure` is the only op that changes nothing on
either projection yet is the only one that produces data.

## Two correctness theorems

**A. Adequacy of the transform** (the rules implement `do`), now typeable
because distributions are not indexed by the graph:

```
⟦step op M⟧ = do_op ⟦M⟧        (as kernels: equal at every P_U)
```

For `Randomize n` (shadow encoding, D3): `⟦Randomize n⟧` injects a fresh draw
`v ~ d_n` into the exogenous slot `U_n` and lets `f_n = f_unobs` read it, then
solves. This *equals* the intervention mixture `fdistbind d_n (fun v => ⟦do(n=v)⟧ M)`
— that equality is exactly `randomize_semantic_do` (**done**), and the
distributional lift is `fdistmap`/`fdistbind` congruence over it.

**B. Soundness of the abstraction** (why static verification is valid):
d-separation on `α M'` implies the target independence / identification in
`⟦M'⟧`. Per-mechanism version done (`backdoor_correspondence`); distributional
version says the log identifies `P(R | do(T))` — needs the coin `d_n` to have
**full support** (overlap) and be **independent of confounders**, both of which
the RCT satisfies by construction (uniformity is *not* required — see D6).

**Design correctness = A + B.**

Proof strategy: finite probability via infotheo `fdist` (D4), `nat` value layer
reused through the boundary encoding (D5); distribution equality is infotheo's
`=` on `fdist`.

## Status: done and surviving

- **`randomize_semantic_do`** (`Correctness.v`) — per-world core of Theorem A
  for Randomize, proved, no admits. Survives the reframe verbatim (it is a
  statement about `find_value`, not about the experiment record). Now read as:
  the bridge between the shadow encoding and the do-surgery encoding, i.e. the
  stratum-v lemma for the mixture in Theorem A.
- **`backdoor_correspondence`** (`Main.v`) — syntactic ⟺ semantic backdoor via
  dsep-core's `semantic_and_d_separation_equivalent`; conditioning set
  deduplicated internally (`dedup`). Untouched by the reframe.
- **`simple_rct_syntactically_correct`** (`Correctness.v`) — restated under D1
  and reproved (2026-07-23): the post-experiment DAG is `do T G`; after the
  backdoor mutilation T is *isolated*, so d-separation with Z = [] is immediate.
  The proof shrank from ~240 lines of fresh-node adjacency analysis to three
  small isolation lemmas.
- **Agreement refactor** (2026-07-23): `Randomize` has no `r`; `abs_apply_op`'s
  Randomize case = Intervene's surgery; all fresh-node lemmas
  (`add_fresh_source`, `G_well_formed_randomize`, `contains_cycle_randomize`,
  `rct_*`) deleted — recoverable from git if the IV work revives them.
- `measured_agree` — the log's node footprint equals the abstract `measured`
  set; simulation infrastructure, unchanged.

## Milestones

Proposed order (dates are suggestions — adjust with supervisor):

- **M0** ✅ 2026-07-23 — agreement refactor (D1): no fresh node, RCT theorem reproved.
- **M1a** ✅ 2026-07-23 — **infotheo encoding spike**: infotheo's SSReflect `fdist` world and dsep-core's vanilla
  `find_value` coexist in one file; a uniform `fdist world` pushed through
  `fdistmap (outcome ∘ to_assign)` yields a genuine `R.-fdist 'I_2` (proved
  `\sum_x od x = 1` via `FDist.f1`); the read-after-write lemma held by `reflexivity`.
  No import-order fighting, no `realType_ext` workaround, no path flags needed
  (infotheo is in `user-contrib`, auto-loaded; `coq-infotheo` already in
  `rocq-causal.opam`). **Reusable incantations for M1b:**
  ```coq
  From mathcomp Require Import all_ssreflect ssralg ssrnum finalg reals.
  From infotheo Require Import fdist.
  (* dsep-core imports as usual; then: *)
  Local Open Scope fdist_scope.   (* for R.-fdist / fdistmap notation *)
  Local Open Scope ring_scope.    (* for \sum over fdist masses *)
  Variable R : realType.          (* keep the real field abstract, as infotheo's own examples do *)
  Definition world := {ffun 'I_2 -> bool}.
  Lemma world_card : #|world| = 3.+1.
  Proof. by rewrite card_ffun card_bool card_ord. Qed.
  Definition unif : R.-fdist world := fdist_uniform world_card.
  ```

- **M1b** ✅ 2026-07-23 — **`Prob.v` rewritten over infotheo**.
  Deleted the old `world`/`enum_worlds`/`prob_measure` layer and both its
  `Admitted`s. Delivered:
  - *Narrow interface* — wrappers `dret`/`dmap`/`dbind`/`dunif` (implicit `R`),
    and the congruence lemmas `dmap_eq` (`f =1 g -> dmap f P = dmap g P`) and
    `dbind_eq` (pointwise continuation).
  - *D5 boundary* — `Node := seq_sub (nodes_in_graph G)` (nodes as a finType),
    `world := {ffun Node -> V}`, `to_assign`, and the read-after-write `to_assign_get`
    (`get_assigned_value (to_assign w) (ssval i) = Some (decode (w i))`), proved
    with a generic key-injective lookup helper + `val_inj` + `mem_enum`.
  - *Gotchas logged for M4+*: (1) `Node` needs a `: finType` ascription or
    canonical-structure resolution fails; (2) write `list I`, never `seq I` —
    dsep-core's imports shadow mathcomp's `seq` type with stdlib's `seq` range
    function; (3) mathcomp `in_nil` is shadowed by stdlib List's `in_nil`, so
    close nil membership with `by []`, not `by rewrite in_nil`.
- **M2** ✅ 2026-07-23 — **total node evaluator** in `Main.v`, no admits.
  dsep-core already proves totality (`find_value_existence`: wf + acyclic +
  complete `U` + `u ∈ G` ⟹ `∃v, find_value … = Some v`), so M2 just packages it:
  `eval G g u U := match find_value G g u U [] with Some v => v | None => 0 end`
  (option-free), with `eval_find_value` proving `find_value … = Some (eval …)`
  under wf — so the `0` default is provably dead code, NOT a clamp (contrast the
  spike's lossy `inord`). This is the total "solve" M4 wraps in `fdistmap`.
  Resolves the open "Measure-on-None" question in favor of totality.
  Remaining M4 prerequisite (deferred): `to_assign_complete`
  (`is_assignment_for (to_assign w) (nodes_in_graph G) = true`) to discharge
  `eval_find_value`'s completeness hypothesis for worlds — needs constructing
  `seq_sub` elements from node membership; lives in `Prob.v`, built at M4.
- **M3** (≈ 1 wk) — **`model` record** + `wf_model` (two clauses; range-closure
  free by typing into `V`, per D6); one transform per op on `model`; projection
  `α`; agreement lemma `α (step op M) = abs_step op (α M)`; ops preserve
  `wf_model` (in particular `dag_fun_compatible`).
- **M4** (≈ 2 wks) — **distribution semantics**: `run : model → operations →
  state → fdist state` (coins `d_n` bound inline via `fdistbind`, per D3/D6);
  `⟦e⟧ : fdist U → fdist log`; `sample` removed from `experiment`, empirical
  distribution as input; denotation `⟦M⟧` as `fdistmap` along the solve.
- **M5** (≈ 2 wks) — **Theorem A**: Randomize (lift `randomize_semantic_do` by
  `fdistmap`/`fdistbind` congruence over the mixture `d_n`), then Intervene
  (near-definitional), then Measure.
- **M6** (≈ 3 wks) — **Theorem B, distributional**: in `⟦simple_rct⟧`, the log
  identifies P(R | do(T)); combines `backdoor_correspondence` with the coin's
  full-support + independence-of-confounders hypotheses (D6).
- **M7** — vector-valued T and R (do not hard-code singletons).
- **M8** — `exp` AST with `Seq`/`If`: adaptive designs, dynamic treatment
  regimes; abstract layer becomes branch-join over-approximation.
- **M9+** — frontdoor, do-calculus rules, ID algorithm, IV/non-compliance
  (reintroduces the explicit randomizer node); `examples/` of historical and
  natural experiments.

**POPL SRC target** (late Oct / early Nov): the story "experiments as
probabilistic programs — a verified RCT" needs M1–M6.

## Static analysis techniques for identifiability

Each criterion = a decidable `syntactic_*` check on `α` of the post-experiment
model + a `semantic_*` counterpart + a `*_correspondence` theorem (instances of
Theorem B).

### Done: backdoor criterion (`Experiment/Main.v`)

`syntactic_backdoor` / `semantic_backdoor` / `backdoor_correspondence`, with
the conditioning set deduplicated internally. RCT is the Z = ∅ special case —
now via **isolation** (D1): randomizing T leaves it with no incident edges in
the mutilated graph.

### TODO: frontdoor criterion
Fully-mediating observed mediator under unobserved T–R confounding; two chained adjustments.

### TODO: do-calculus (three rules)
Each rule a d-separation condition in a mutilated graph; would subsume backdoor and frontdoor.

### TODO: ID algorithm
Tian–Pearl / Shpitser–Pearl; sound and complete; outputs the estimand.

### TODO: instrumental variables (different shape)
Not point-identified; bounds (Balke–Pearl) or LATE under monotonicity. Requires
non-compliance modeling — this is where the explicit randomizer node `r → T`
returns (see D1).

### TODO: testable implications
The d-separations a DAG entails, checked against data to falsify the model; reuses `d_separated_bool` / `semantically_separated` directly.

## Todo outside of this codebase

- Curate historical experiments; check the framework can express them.
- Study natural experiments and simulate them in the framework (avoid the ill-defined "quasi-experiment" framing).

## Deadlines

- POPL Student Research Competition: submission typically end of October / early November.

## Repo Conventions (for Claude Code)

- Language: Rocq 9.1.0. `dsep-core/` is Anna's code — read-only, vanilla Rocq
  (`nat`/`List`/`lia`), value layer stays `nat`-valued (D5).
- Probability: **infotheo 0.9.7** (mathcomp 2.5.0, analysis 1.16.0) — already in
  the `vsrocq` opam switch. Add `coq-infotheo` to `rocq-causal.opam` and its
  logical paths to `_CoqProject`/Makefile at M1a.
- Layout:
  - `Experiment/Main.v` — labels, `aug_graph`, operations, (soon) `model` + one transform per op, backdoor pair.
  - `Experiment/Prob.v` — rewritten over infotheo (M1b): the boundary encoding
    (`world` finType, `to_assign`, read-after-write lemmas) + narrow `fdist` wrappers;
    then the denotation.
  - `Experiment/Correctness.v` — per-world core (`randomize_semantic_do`), RCT syntactic correctness; later Theorems A and B.
  - `examples/` — encodings of historical/natural experiments (future).
- **Style boundary**: SSReflect/infotheo lives *inside* `Prob.v` behind the
  narrow interface; the causal proofs stay vanilla Rocq. Don't let `fdist`/bigop
  names leak into `Main.v`/`Correctness.v`.
- Keep simplifying assumptions documented in module headers.
- Designer's choices are decided with Blanca first, then logged in the Decision log above.

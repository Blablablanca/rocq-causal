# Experiments as Programs — Project Plan

Formal framework (in Rocq) for expressing scientific experiments as programs over causal models, so experimental designs can be checked for correctness with program-analysis techniques (e.g., d-separation).

## Motivation

Historically, experiments are error prone: unidentified non-causal influence paths, bad proxies, unexecutable designs. If we treat an experiment as a program transforming a causal model, we can statically verify the design.

A **correct design** means:

1. **Validity** — the experiment successfully measures the effect of the treatment(s) on the response(s).
*Graphically:* the post-experiment graph d-separates T and R from all non-causal influence, and T and R remain reachable via the intended causal path.
*Algebraically:* the outcome law identifies P(R|do(T))
2. **Executability** — all controlled/intervened nodes are not labeled unmeasurable.

## Architecture: two probabilistic programs (reframe, 2026-07-23)

Supervisor's reframe, adopted: the causal model and the experiment are **both
probabilistic programs**, and the experiment is a **transformer from the
distribution of the experimental units' innate characteristics to the outcome
distribution**. Concretely:

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
variables, i.e. a *kernel*:

```
⟦M⟧ : dist U  →  dist (assignments nat)
```

defined as the pushforward of the innate law along `find_value` (Pearl's SCM
form: all randomness up front, then a deterministic solve). This reuses
dsep-core's evaluator wholesale and needs no enumeration of worlds. The
pushforward form covers straight-line programs, `If`, and bounded loops; only
unbounded recursion would force a fully monadic evaluator, so definitions stay
monadic to keep that door open.

### 2. The experiment is a separate probabilistic program

```
⟦e⟧_M : dist U  →  dist log
```

- **Input** = the population law over innate characteristics (exogenous U).
  The old `sample : list individual` field is *deleted from the record*: a
  concrete cohort is just the empirical distribution `uniform {u₁ … uₙ}`
  supplied as input. Sample-dependence disappears from the semantics; finite-
  sample estimation returns later as a statistics layer on top (i.i.d. draws
  from `⟦e⟧(P_U)`).
- **The experiment brings its own coins.** Randomizer draws are the
  experiment's randomness, bound inline by the run semantics — they are *never*
  written into U. This resolves the previously flagged open decision ("where do
  per-unit randomizer draws live") and closes the known gap (the draw no longer
  needs to be pre-injected into the individual).
- **AST**: start with `operations = list operation` (the straight-line
  fragment), later generalize to `Seq`/`If` (+ bounded loops). `If` on measured
  data is what expresses adaptive designs and dynamic treatment regimes
  (Robins' g-formula) — a static list cannot, because the operation's argument
  depends on runtime data.

### 3. The structural layer is a *derived projection*, not a parallel definition

`α M = structure M`. The abstract transform is the structural component of the
one model transform, and the soundness statement `α (step op M) = abs_step op
(α M)` is now provable — under the agreement refactor (below) it holds
definitionally for the current three ops. Static checks (backdoor etc.) read
only `α M`, stay X-free and decidable, and quantify over mechanisms as
`∀ M, structure M = G → …`.

When `If` arrives there is no single post-experiment DAG (the model you end up
with depends on measured data), so the abstract layer becomes a *sound
over-approximation* (join of branch graphs). That is where abstract
interpretation properly re-enters — as an approximation of the distribution
transformer, which stays the well-defined object.

### Design lesson, revised

The previous plan argued "G and F need not structurally agree" and kept the two
sides as independently-defined transforms related only through a (then-unbuilt)
denotation. That disagreement was an **artifact of the old encoding**, not a
fact about causal models: with no place to put a fresh randomizer's law, the
graph side grew a node `r → n` that the mechanism side never read. Under the
agreement refactor both sides of every op say the same thing, and the DAG-level
reasoning that motivated the split survives intact as the projection `α`.

## Decision log

Decisions taken 2026-07-23 (each was a consulted designer's choice):

| # | decision | rejected alternatives | rationale |
|---|---|---|---|
| D1 | `Randomize n` = `remove_incoming n` structurally; **no fresh randomizer node**; `r` dropped from the AST | (a) graph literally unchanged — breaks the backdoor check and `simple_rct_syntactically_correct`; (b) fresh node on *both* sides — agreement also holds but the node set grows mid-run, complicating the distribution layer | randomization *is* an intervention whose value is drawn; the coin belongs to the experiment, not the model. Reintroduce an explicit `r → T` node only when modeling **non-compliance / IV** (assignment ≠ treatment received) |
| D2 | P_U is an **input** (kernel view), not a model field | `model = {G; F; exo}` denoting a closed distribution | matches the transformer definition verbatim; keeps innate vs. experimental randomness cleanly separated; works because (per D1) the node set never changes |
| D3 | `Randomize` mechanism = **draw v, then intervene** (`bind uniform (fun v => f_n := const v)`) | shadowing encoding (`f_n := f_unobs` + inject `(n,v)` into U) | U stays purely innate; structural rule literally shared with `Intervene`; operationally faithful (coin decides, patient receives). `randomize_semantic_do` survives as the proved bridge between the two encodings |
| D4 | `dist A = list (A * Q)` with observational equality (`d₁ ≈ d₂ := ∀ E, Pr[E] equal`) | weighted list over R (nothing computes); unweighted multiset (uniform-only) | computable — examples check by `vm_compute`; decidable equality; narrow interface keeps migration to R/infotheo open |

Still open (bring to supervisor):
- `Measure` when `find_value` returns `None`: prove totality under `wf` and drop
  the `option` (preferred — avoids stacking `dist` on `option`), or carry
  option values in the log.
- Whether `dist` should be a quotient (canonical normalized form) or a setoid
  under `≈`. Setoid is the default; revisit if rewriting friction grows.
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
| `Randomize n` | remove incoming edges to `n` | draw `v ~ uniform`, then `f_n := const v` (D3) | — |
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

For `Randomize n`: `⟦Randomize n⟧ M = uniform ⊗ (fun v => ⟦do(n=v)⟧ M)` — a
mixture of interventions. The per-world core is **done**
(`randomize_semantic_do`); the distributional lift is pushforward congruence.

**B. Soundness of the abstraction** (why static verification is valid):
d-separation on `α M'` implies the target independence / identification in
`⟦M'⟧`. Per-mechanism version done (`backdoor_correspondence`); distributional
version says the log identifies `P(R | do(T))` — needs the drawn treatments
uniform and independent of confounders, which D3 gives by construction.

**Design correctness = A + B.**

Proof strategy: finite probability, computable `dist` over Q (D4), equality of
distributions is observational.

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
- **M1** (≈ 2 wks) — **Prob.v rewrite**: `dist A = list (A * Q)`; `ret`, `bind`,
  `uniform`, event probability, `≈`, monad laws up to `≈`, pushforward
  congruence (`(∀u, f u = g u) → map f d ≈ map g d`). Deletes
  `world`/`enum_worlds`/`prob_measure` and both `Admitted`s.
- **M2** (small) — `find_value` **totality** under wf (pieces exist:
  `find_value_evaluates_to_g`); drop `option` from `apply_op` *before* adding
  `dist` on top.
- **M3** (≈ 1 wk) — **`model` record** + `wf_model`; one transform per op on
  `model`; projection `α`; agreement lemma `α (step op M) = abs_step op (α M)`;
  ops preserve `wf_model` (in particular `dag_fun_compatible`).
- **M4** (≈ 2 wks) — **distribution semantics**: `run : model → operations →
  state → dist state` (coins bound inline per D3); `⟦e⟧ : dist U → dist log`;
  `sample` removed from `experiment`, empirical distribution as input;
  denotation `⟦M⟧` as pushforward along `find_value`.
- **M5** (≈ 2 wks) — **Theorem A**: Randomize (lift `randomize_semantic_do` by
  congruence over the uniform mixture), then Intervene (near-definitional),
  then Measure.
- **M6** (≈ 3 wks) — **Theorem B, distributional**: in `⟦simple_rct⟧`, the log
  identifies P(R | do(T)); combines `backdoor_correspondence` with uniformity +
  independence of the drawn treatment.
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

- Language: Rocq. `dsep-core/` is Anna's code — read-only.
- Layout:
  - `Experiment/Main.v` — labels, `aug_graph`, operations, (soon) `model` + one transform per op, backdoor pair.
  - `Experiment/Prob.v` — to be rewritten (M1): `dist` over Q behind a narrow interface; then the denotation.
  - `Experiment/Correctness.v` — per-world core (`randomize_semantic_do`), RCT syntactic correctness; later Theorems A and B.
  - `examples/` — encodings of historical/natural experiments (future).
- Keep the probability layer behind a small interface (migration to infotheo must stay feasible).
- Keep simplifying assumptions documented in module headers.
- Designer's choices are decided with Blanca first, then logged in the Decision log above.

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

**Framing (settled 2026-10-20).** The project is *about the two semantics*;
the syntactic checker is an **application** of them. The user runs the
checker, but the checker proper is ~50 lines (`syntactic_backdoor`,
`measures_last`, `twf_operation`) while the semantics and its proofs are a
few thousand, and every hard theorem (Theorem A's adequacy, the pushforward
story, the LLN chain) is semantics. This is the shape of a type system: a
small checker, justified by a soundness proof against a large operational
semantics. Consequence for priorities: build Theorem A (D8's "PL
centerpiece") before adding further criteria to the checker.

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
| D6 | **No `dom` yet: shared value finType `V` + abstract randomizer `d_n`** | *Alt:* thread `dom : node_card` now and draw `uniform (node_dom dom n)`. Rejected because `dom`'s two jobs split — sample space becomes "pick a finType `V`" (start `bool`), and "coin is uniform" is a needless specialization. Abstract `d_n` proves a **stronger** theorem (RCT correct for any coin independent of U; uniform is a corollary) and defers per-node `dom` to M7. **Superseded by D8** — per-node `dom` landed early, in `Prob.v`. |

Decisions taken 2026-09-23:

| # | decision | alternative considered, and why this wins |
|---|---|---|
| D7 | **`sample` is not a field of `experiment`.** Units are an argument to `run_all`/`concrete_logs` | *Alt:* keep `sample : list raw_context` and read it as the empirical distribution. Rejected because an experiment is a *protocol*: a fixed sample conflates it with the population it happens to be run on, and makes the same protocol over a different cohort a different `experiment`. `run_all` already took the units as a parameter, so this cost two lines. (This decision originally also leaned on `Filter` making selection an operation — see D11, now deferred — but it stands without it.) |
| D8 | **Parents are addressed BY NODE, never by position** (`parent_view` in `Prob.v`) | *Alt (was in place):* a positional right-nested tuple `hvals (find_parents n G)`. Rejected because `find_parents` returns parents in **edge-list order**, so re-spelling the same dag silently changed what a mechanism meant, and the typechecker only caught it when the parents' domains happened to differ. Keyed access makes reordering a no-op rather than an error (verified against a reordered `G3`), and makes "reads only declared parents" structural instead of proved. Deleting the positional layer removed `hvals`/`dec_parents`/`dom_of`/`dec_of` and three lemmas. |
| D9 | **`context` = the exogenous draw; `world` = the solved node values**, one meaning each across the development | `Main.v`'s untyped version renamed `raw_context` (nat-coded, what `find_value` takes as `U`); `Prob.v` keeps `context` for the typed one, bridged by `to_assign`. They had not collided only because `Prob.v` does `Require Main` *without* `Import`. A third copy in `Spike.v` was retired to `attic/`. |
| D10 | **Noise space = value space** (`dom n` serves both), documented as a simplifying assumption rather than left implicit | Natural because a *source* node takes its unobservable as its value, so the spaces must coincide there anyway. Known cost: forbids `|U_n| ≠ |dom n|`, so principal strata (a 4-valued compliance type behind a binary outcome) is out of reach until noise domains get their own family and codes. |
| D12 | **A typed operation SURFACE that compiles down** (`toperation` + `elab_op` in `TypedExp.v`), not a retyped `Main.operation` | *Alt 1:* retype `operation` to carry `Node G`/`dom n`. Rejected on three counts: mathcomp would enter `Main.v` against the stated style boundary; the type must be graph-indexed, and after surgery `Node (remove_incoming n G)` is **not convertible** with `Node G` for abstract `G` (`nodes_in_graph (remove_incoming n G)` reduces to `fst G`, `nodes_in_graph G` is stuck), so the abstract layer would thread transports; and every proved theorem over operations needs rework. *Alt 2:* leave operations untyped — keeps `Intervene 1 1` and value-range errors as proof obligations. Compiling down mirrors `tgraphfun`/`elab` exactly, costs one elaboration tax already paid elsewhere, and makes **half of `wf_operation` structural**: a `Node G` cannot name a node outside `G`, so only the label obligations remain. |
| D11 | **DEFERRED 2026-09-28 (supervisor): no `Filter` operation for now.** Design reached, kept for when it returns: `Filter (ns : nodes) (keep : assignments nat -> bool)` — read set separate from rule, because the read set *is* the conditioning set `Z` the d-separation checks consume; a bare `raw_context -> bool` would hide it and make selection bias invisible to them. `keep` takes an `assignments nat` (keyed access, consistent with D8). `abs_state` gained a `conditioned : nodes` field alongside `measured`. Costs that motivated deferring: `operation` loses decidable equality; the distributional semantics acquires a side condition (conditioning on a probability-zero event) that well-formedness cannot discharge; and it breaks the product form of the exogenous law (see below). Code recoverable from commit `0e80c37`. |

| D13 | **2026-10-07: the sample SIZE is a field of the typed experiment (`te_size : nat` on `texperiment`); the sample itself is not.** The sample-level laws take a free `N`, with `te_size te = N.+1` linking it | *Alt 1:* N as a parameter of the denotation only, no field — the semantic functions (`sample`, `fdist_sample`, `log_sample`) take it, the record stays as it was. Cheapest option (zero churn, no consistency hypothesis, and a field nothing in `elab_exp` or the wf-checks *can* read), but rejected: the reason to record N is that a trial's sample size is pre-registered **design**, fixed before any data exists, exactly like the choice of which node to randomize. A protocol that does not state its N is not a protocol. *Alt 2:* `sample : list raw_context` on `Main.experiment` — the field D7 removed. Rejected twice over: it would not even work (`list` has no `fdist`, so it could not be what the LLN quantifies over, and the `'rV`-indexed sample would still be needed beside it), and it reinstates what D7 rejected. **D7 is not reversed by D13:** D7's field held the *units* and served as the input LAW (`uniform {u₁…uₙ}` — an empirical distribution, today's `emp_rV`), so the same protocol over a second cohort was a different experiment. A size names no population: two cohorts of the same size give the *same* `texperiment`, and the population remains `fdist_context P`, which does not mention `te_size`. What `te_size` distinguishes is N = 400 from N = 1000, which is the point. Indeed the passage that removed `sample` promised exactly this layer — "finite-sample estimation returns later as a statistics layer on top (i.i.d. draws)". *Alt 3:* index the sample type by the field (`'rV[context dom]_(te_size te)`), so a size mismatch is caught by **typing**. Rejected for D12's reason: `te_size te` is stuck on an abstract `te`, so every use of a sample would carry a transport. The propositional link costs one hypothesis and no transports — and per the standing preference, robustness beats loudly-caught mistakes. |

| D14 | **2026-10-20: dataset columns are addressed by node with an `is_measured` TICKET** (`dataset te N := forall n, is_measured te n -> 'rV[dom n]_N`), mirroring `parent_view`'s `is_parent` ticket | *Alt:* a total `{dffun forall n : Node G, 'rV[dom n]_N}`. That IS a finType, so it would carry a law (`R.-fdist (dataset N)`), which the ticketed version cannot — a function out of a `Prop` is not enumerable. Rejected anyway, because **the dataset does not need its own law**: a dataset is a deterministic function of the sample, and every probabilistic statement here is already phrased over `fdist_sample`. The concrete side holds DATA, the abstract side holds the law (`fdist_node`), and the two are compared through `emp_rV` — so the law lives where the randomness is and the dataset is free to be faithful instead of enumerable. The total version would hand back a column for a node the protocol never measured, returning `dec n 0` (via `log_val`'s `odflt 0`) — data that looks real and is not. Note this is the one place where a ticket was taken *over* a finType, the opposite of D13's call; the deciding question each time is whether the object needs to carry a distribution. |

| D15 | **2026-10-20: the randomizer coin `d_n` is a PARAMETER of the distributional semantics**, abstract and universally quantified in theorems — not a field of `texperiment`, and not an argument of `TRandomize` | Confirms D6 against a proposal to fix `d_n := unif (dom n)`. Abstract wins three ways: it proves the strictly stronger theorem (correct for *any* coin independent of `U`, with uniform a one-line corollary), it covers unequal allocation (2:1), and it avoids `dunif`'s nonemptiness obligation `#|dom n| = m.+1`. *Alt 1:* a `te_coin` field — but it would have to be total over all nodes, so most entries are junk, and (unlike `te_size`, D13) **no theorem needs to READ it**: a theorem only needs to *substitute* it, which instantiation already does. That is the test D13 applied, with the opposite answer. *Alt 2:* put it on the operation, `TRandomize n d` — the most faithful (each randomization names its own coin) but it parameterises the whole typed-operation layer by `R`, which is currently `R`-free. Available later if protocols must record their allocation. **Consequence found while proving `rct2_correct`:** at the one-experiment level no law-surgery operation is needed at all, because the theorem is general in `P` — so "⟦Randomize n⟧ substitutes `d_n` at `U_n`" is just instantiation. A law-level operation becomes necessary only for a compositional runner over the op list (M4c), and hoisting the surgery before sampling is sound **only because `measures_last` forces all surgery to precede all measurement** — it would break under `If` (M8). |

**Finite sample space is not a finite population.** `R.-fdist A` requires
the *sample space* `A` to be a finType — for us `context dom`, the set of
possible exogenous draws, finite because every node has a finite domain
(UA4). The **population is a distribution, not a list**: each unit is a
fresh draw from `fdist_context P`, so the population is idealised/infinite
and only the *sample* is finite (`us : list (context dom)` with
`size us = N.+1`). `#|context dom| = ∏ₙ |dom n|` counts distinguishable
unit *types*, not people. What finiteness really costs is continuous
outcomes: a real-valued node needs discretising, or a move to
`fsdist`/measure theory. **UA6 ("population is finite") should be reworded
— it is the sample that is finite, not the population.**

**Universal Assumption 2, and why `Filter` is not free** (relevant if D11
returns). "All exogenous variables are mutually independent" holds of the
**initial** law. `Filter` conditions on an
event about *solved* values, which pulls back to a non-product event on
contexts — so after a filter the unobservables are in general **dependent**.
That is not a bug, it *is* selection bias. Consequence for M4c: the running
state of the distributional semantics must be a general `R.-fdist context`,
not a per-node family `forall n, R.-fdist (dom n)`; the product form is the
initial value only.

Still open (bring to supervisor):
- **Elaboration correctness**: nothing yet connects `elab tF` running under
  `find_value` back to what `tF` *means* on typed values at a node WITH
  parents, so `solve` there is still "whatever dsep-core computes, decoded".
  Target: `solve F w n = F n (w n) (fun p _ => solve F w p)`.
  **Diagnosis (2026-10-20): the obstacle is the POSITIONAL ↔ KEYED parent
  correspondence, not the coding.**
  - dsep-core hands a mechanism its parents' values as a **list in
    `find_parents` order**; `elab` reads a parent **by node**, resolving it
    through `index p (find_parents n G)`. Nothing proves the two agree, and
    that is the whole gap — bookkeeping about dsep-core's internals.
  - dsep-core already supplies most of it:
    `find_values_preserves_index` (`FindValue.v:1213`) is the positional
    half by name, `find_values_get_assigned` (`FindValue.v:870`) the keyed
    half. What remains is a ~10-line positional lemma about
    `get_parent_assignments` (its i-th entry is the keyed read of the i-th
    parent), plus dependent funext, already in the axiom set.
  - **Range closure is not involved**, contrary to how this entry read
    before. As a blanket property `enc n (dec n m) = m` is false (`dec` is
    total on `nat` while `enc`'s range is finite: `t2n (n2t 7) = 1 ≠ 7`),
    and restricted to in-range `m` it is free (`m = enc v` ⟹ `dec m = v` by
    `encK` ⟹ `enc (dec m) = m`). Neither version is needed: `elab`'s parent
    view hands the mechanism `dec p ⟨p's positional slot⟩`, and
    `solve F w p` **is** `dec p (eval at p)` by definition, so once the
    slot is known to hold `eval at p` the two sides are *definitionally*
    equal. All the arithmetic is `encK` twice — n's own noise and the outer
    `enc` — which is why `Rct2.v`'s `rct2_R` is nothing but
    `rewrite !enc_2K`.
  - **No induction on the graph is expected.**
    `find_value_gives_value_of_node` already unfolds one step at *every*
    node independently, and the fixpoint equation needs `solve p` only
    *named*, not computed.
- **Zero-probability conditioning** (dormant while D11 is deferred):
  conditioning needs positive mass, and unlike the `Measure`-on-`None`
  partiality that is *not* eliminable by well-formedness — it depends on the
  numbers. Side condition, or a partial distributional semantics?
- Nothing downstream of `to_assign` computes by `reflexivity` (`enum Node` does
  not reduce), so per-node value laws can be *stated* but not *evaluated*.
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
  | Measure   (n : node)             (* record n's current value into the log *)
```
*(`Filter` deferred — see D11.)*

- Set {intervene, randomize, measure, filter} spans *doing*, *seeing* and
  *selecting*; one abstract `Measure` is deliberate.
- `Randomize` carries **no fresh randomizer node** (D1).
- A fourth mode, **selecting** (inclusion criteria, stratification, loss to
  follow-up) is deferred; see D11 for how far the design got.

- `Control` still excluded (lacks a clear characterization). Planned:
  `Control`, `Timestep`, then `Seq`/`If`.

### Transformation rules (one transform, two projections)

| op | structural (`α`) | mechanism | observation |
|---|---|---|---|
| `Intervene n v` | remove incoming edges to `n` | `f_n := const v` | — |
| `Randomize n` | remove incoming edges to `n` | draw `v ~ d_n` (abstract coin, D6), then `f_n := const v` (D3) | — |
| `Measure n` | — | — | append `n`'s current value to the log |


`Intervene` and `Randomize` are structurally identical; they differ only in
where n's value comes from. `Measure` changes nothing on either projection yet
is the only op producing data.

### Ordering discipline: `measures_last`

`wf_operations` has a second clause, `measures_last prog = true`: **no surgery
after a measurement**. The abstract layer has no temporal resolution —
`abs_apply_op` leaves the graph alone on `Measure`, and `abs_run` ends at the
post-surgery dag, so `measured` is read against the *final* graph. A program
measuring a node both before and after surgery would have two concrete values
but only one abstract law.

**Sound but crude.** Measuring a node that no later surgery can affect is
harmless, so a descendant-based condition (`no_descendant_of_b`, already in
`Main.v`, tested against the initial graph — sound because surgery only
removes edges) would be strictly more permissive. Not needed while `Measure`
is the only reader, and `simple_rct` satisfies the crude clause as written.
It *would* be needed if D11 returns, since a filter also reads values and
`screen, then randomize` must stay legal.

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

- **`measure_source_law`** (`TypedExp.v`, 2026-09-30; generalised
  2026-10-03) — the hello-world, at the EXPERIMENT level: run a protocol
  that measures one parentless node whose mechanism reads only its own
  noise (`tF n u pa = g u`, **any** `g`, not just the identity), and the
  law of the logged value is exactly the pushforward `dmap g (P n)`.
  `measure_source_law_echo` is the `g = id` corollary, recovering
  `= P n`. Exercises the whole stack
  (enc/dec → to_assign → find_value → eval → solve → run_unit_total →
  fdist_context). Axioms: boolp's three only.
- **`solve_source`** (`Prob.v`) — the **first proved instance of elaboration
  correctness**: a parentless node whose mechanism is parent-free
  (`tF n u pa = g u`) solves to `g` of the drawn value. It works because
  the value round-trips `enc → dec → enc → dec`, so every step is `encK`;
  it never needs `enc (dec m) = m`, the range-closure property that blocks
  the general lemma. Plus `o_node_self` (`o_node` retracts `ssval`).
  *Why `g` is free:* the proof only ever rewrites with the mechanism
  hypothesis once, so the identity played no role; naming `g` costs
  nothing. (With `find_parents = nil`, `parent_view n` has essentially one
  inhabitant, so every `tnodefun` at `n` is already `pa`-independent — `g`
  just has to be named to say what the answer is.)
- **`measure_source_lln`** (`TypedExp.v`, 2026-09-30) — the weak law for the
  outcome: over N+1 independent units, the empirical frequency of a value
  `v` is within `eps` of `dmap g (P n) v` except with probability at most
  `V / ((N+1) eps^2)`. Finite-N Chebyshev, no limits — which is what makes
  it provable at all, since `fdist` is finite-support and the infinite
  product space almost-sure convergence needs is not expressible. Together
  with `measure_source_law` (population) and
  `measure_source_empirical_rV` (exact sample) this is the full
  "concrete log → abstract law" story.
  Axioms: boolp's three only.
  *Gotcha worth remembering:* `` `E ``/`` `V `` need the codomain seen
  through an **lmodType**. Writing `{RV P -> R}` resolves `R`'s eqType via
  the realType route, which carries no module structure, and nothing in
  scope fixes that (not `all_algebra`, `normedtype`, or proba.v's own
  preamble — even infotheo's `E_Ind` statement fails to re-typecheck).
  **`R^o`** — R as a module over itself — is the ascription that works, and
  `wlln` unifies with it.
- **The sample as a first-class object** (`TypedExp.v`, 2026-10-07, D13) —
  `sample N := 'rV[context dom]_N`, `fdist_sample N := (fdist_context P) `^ N`,
  `log_sample` (run the protocol *once*, over all N units), `emp_freq` (the
  empirical frequency of a value, as a random variable **of the sample**).
  Before this the sample existed only as the anonymous domain of `sum_iid`'s
  random variable — named nowhere, connected to nothing. Two gains beyond
  the naming:
  - **IID sampling became a named assumption.** It lives in `fdist_sample`,
    and now sits visibly beside UA2: `fdist_context` is a product over
    **nodes** (a claim about the model), `` `^ N `` a product over **units**
    (a claim about the design). Both were previously implicit in the single
    step that reached for `sum_iid`.
  - **Why the size has to be a hyperparameter** — recorded because it reads
    like a taste call and is not. `R.-fdist A` needs `A : finType` and
    `list (context dom)` is not one, so a sample that is to be *drawn* must
    be length-indexed. There is therefore no single space of all samples,
    only a family indexed by N, and N is needed to **name the space the
    probability is on** before the statement can exist. This is also the
    reason the exact-sample theorem must assume representativeness rather
    than bound a deviation: with a bare list there is nothing to take a
    probability over.
  - One thing the sample layer does *not* give: `log_sample` is node n's
    **column** of the dataset. The whole dataset (every measured node at
    once) still waits on the finite log type.
- **`measure_source_empirical_rV`** (`TypedExp.v`, 2026-10-07) — the
  exact-sample law on a length-indexed sample: run the protocol on every
  unit, tabulate, and you recover `dmap g (P n)`, given the sample is
  representative (`emp_rV s = fdist_context P`). No size proofs in the
  statement — the length is in the type. Takes **no** `te_size` hypothesis
  either: its conclusion quotes no rate, so a size hypothesis would be one
  the proof never uses.
  **Why this is a warm-up, not the result** (2026-10-14): the
  representativeness premise silently restricts `P` to rationals with
  denominator dividing N+1, since an empirical distribution can only land
  on that grid (`emp_rV_grid`). Against an irrational truth it is vacuous.
  `measure_source_emp_lln` carries no such premise — which is the honest
  reason an `eps`-bound is not a weakening but the only available shape of
  theorem.
- **`measure_source_emp_lln`** (`TypedExp.v`, 2026-10-07) — the weak law
  stated about the **program's own output**: the frequency of `v` among the
  N+1 logged values is within `eps` of `dmap g (P n) v` except with
  probability at most `V / ((te_size te) · eps²)`. This is where `te_size`
  earns its keep — the pre-registered size sets the rate, and dropping
  `Hsz` makes the statement false, so the field is load-bearing rather than
  bookkeeping. Proved from `measure_source_lln` by one rewrite through
  `emp_rV_sum_iid`: no new probability theory. Axioms: boolp's three only.
  **Superseded in generality (2026-10-21)** by `emp_lln_any`, which drops
  all five structural hypotheses by naming the target `fdist_log_val`
  instead of `dmap g (P n)`; `te_size` stays load-bearing only for *this*
  statement, which is the one that quotes the declared size as its rate.
- **New probability machinery** (`Prob.v`), none of which infotheo ships:
  - `emp_rV` / `emp_rVE` — the empirical distribution of a sample
    (`fdist_uniform` is uniform over a whole finType, not over a multiset).
    The sample is a **row vector**, not a list, and that is forced: a
    list's length is data, so `list A` is no finType and cannot carry a
    law. Defined as the pushforward of the uniform law on **indices**
    rather than by counting.
  - `emp_rV_map` — **tabulating then pushing through `f` = running `f` on
    every unit then tabulating.** This is what makes a concrete run
    comparable with an abstract pushforward, and the pushforward definition
    gets it in two lines out of `dmap_comp`.
  - `emp_rV_grid` (2026-10-14) — the empirical distribution can only land
    on the grid of spacing `1/(N+1)`. Stated as "equals `k/(N+1)` for some
    `k ≤ N+1`" rather than "is rational": stronger, and needs no
    rationality predicate on a `realType`. This is what makes exact
    representativeness unachievable against an irrational truth.
  - *Retired 2026-10-14:* a list-based `emp`/`empE`/`emp_map` with
    `count_partition`/`sum_count_size` underneath, together with the
    list-based `measure_source_empirical` that was its only consumer. Two
    parallel implementations of one idea, and the list one could not be
    drawn from. ~90 lines deleted.
  - `fdist_context_pair` (2026-10-20) — the **joint** marginal at two
    DISTINCT nodes is the product of the marginals: the two-node version of
    `fdist_context_marginal`, and the lemma any two-node query needs. Same
    proof shape (one indicator per node, dependent distributivity, the rest
    sums to 1); distinctness is what stops the two isolated factors
    colliding.
  - `dmap_uncurry_prod` (2026-10-20) — pushing a two-argument function
    through a PRODUCT law equals drawing the first argument and then
    pushing the second. The monadic shape of independence, and what turns a
    pushforward along a function of two nodes into a **mixture**.
  - `emp_rV_sum_iid` (2026-10-07) — **the bridge to `wlln`:** the empirical
    frequency of one value *is* the normalised sum of indicators the weak
    law averages. The only real new proof in the sample layer; everything
    else there is restatement.
  - `sum_iidE` — the sum of *n* iid copies of an ARBITRARY random variable
    with its `\=sum` derivation; infotheo only instantiates this for one
    specific RV (`aep.v`'s `sum_mlog_prod`). This is the missing ingredient
    for applying `wlln`.

- **The dataset** (`TypedExp.v`, 2026-10-20, D14) — `tmeasured` /
  `is_measured` (the nodes a protocol measures), `dataset`, `log_dataset`,
  `joint_at`, `is_measured_single`, and `measure_source_dataset` (the
  exact-sample law transferring to a dataset column — one line, since the
  column *is* `log_sample`). This is the **finite log type** the plan had
  been deferring, and what it unlocks is **joint** observation: `joint_at`
  pairs two measured nodes at a real index `i : 'I_N`, so the pairing cannot
  drift. A per-node marginal cannot express a joint, and a joint is what
  `P(R | do(T))` needs.
  *Two gotchas:* `seq (Node G)` does not typecheck (dsep-core shadows
  mathcomp's `seq` with stdlib's range function — use `list`, as M1b already
  recorded); and `Unset Strict Implicit` makes a binder implicit when it
  appears in the **return** type too, not only in a later binder's type, so
  `log_dataset`'s only explicit argument is `s`.
- **The two-node randomized trial** (`Experiment/Rct2.v`, 2026-10-20) — the
  smallest thing that is actually an experiment: `G2 = T -> R`, protocol
  `[TRandomize T; TMeasure R]`, response table `h` arbitrary. Five results:
  `rct2_T`, `rct2_R` (the solve), `log_val_rct2`, `rct2_log_law` (the
  logged law) and **`rct2_correct`**:
  `fdist_log_val … r2 = dbind (P t2) (fun t => dmap (h t) (P r2))`.
  Axioms: boolp's three only. Two things it establishes:
  - **Evidence that the elaboration-correctness induction works.** R has a
    parent, so `rct2_R` is the induction STEP done by hand — and its entire
    arithmetic is `rewrite !enc_2K`. T's code round-trips `enc → dec` once
    as a *parent* value, R's noise once, and **range closure never
    arises**. See the revised "still open" entry below.
  - **The mixture is the RCT content.** `rct2_log_law` (the plain
    pushforward) would be true of *any* protocol; `rct2_correct`
    factorises it into a coin-mixture, which is what randomization buys —
    T's value is independent of R's noise. T is deliberately given a
    *biased* natural mechanism (everyone gets placebo) and it does **not**
    appear in the conclusion: randomization erased it. This is the
    two-node instance of Theorem A's shape.
  *Gotchas:* `enc_2`'s node argument silently becomes implicit (it appears
  in the *return* type), so the definitions are wrapped in
  `Unset Implicit Arguments` as `Prob.v` does for its section variables;
  and `case: (altP (i =P x))` already resolves the cased condition, so the
  `eqxx`/`negbTE` rewrites one expects are absent.
- **Conditional probability, and the trial arm by arm** (`Prob.v` +
  `TypedExp.v` + `Rct3.v`, 2026-11-03) — `rct3_is_mixture_of_do` identifies
  the trial's law with a **mixture** of interventional laws, and a mixture
  cannot be un-averaged: P(Y | do(X := x)) for a *particular* x is not
  recoverable from it. Separating the arms needs an X column, and in the
  typed layer that is enforced rather than merely advisable — `joint_at`
  and `fdist_log_pair` both demand an `is_measured` ticket for **both**
  nodes, so without `TMeasure x3` the conditional cannot be **stated**.
  - **No conditioning machinery was needed.** The decisive find:
    infotheo's `cPr E F = Pr (E :&: F) / Pr F` applies to our events
    *directly*, because `outcome_set` is already a `{set context dom}` and
    the sample space is the single finType `context dom` under the single
    law `fdist_context P`. So a conditional logged probability is a ratio
    of two unconditional ones, and the only new content is that those two
    are the joint and the marginal: `Pr_outcome` and `Pr_outcome_pair`,
    both true by unfolding with no hypothesis on `e`, the nodes or the
    graph (same character as `E_outcome_any`, which is now a two-line
    corollary of `Pr_outcome`). `fdist_log_pair` + `cPr_outcomeE` +
    `dbind_pair_cell` + `cPr_outcome_eq` is the whole layer.
  - **`te_rct3_full`** = `[TRandomize x3, TMeasure x3, TMeasure y3]`, a
    **new** protocol, not an edit to `te_rct3` (so `rct3_correct`,
    `rct3_is_mixture_of_do`, `rct3_emp_converges` and the `te_obs3`
    contrast all stand). Cheap because `apply_op_total` on a `Measure`
    leaves `cur_fun` alone and only appends to the log: the solve is
    unchanged and `rct3_X`/`rct3_Y` are reused **verbatim**, and
    `get_assigned_value`'s first-match discipline keeps the new X entry
    from shadowing Y's.
  - **`rct3_full_joint`** — the headline: the trial's joint (X,Y) law is
    `dbind (P x3) (fun x => dmap (pair x) (fdist_do ... x3 x y3))`. The
    randomized trial is **jointly** a mixture of do-experiments, not
    merely a mixture of their marginals. No positivity needed, and
    `rct3_full_Y_law` recovers `rct3_is_mixture_of_do` as its Y-marginal,
    so the joint subsumes it.
  - **`rct3_full_cond`** — the question answered: for `P x3 x != 0`,
    `cPr (fdist_context P) (outcome_set .. y3 y) (outcome_set .. x3 x)
    = fdist_do .. x3 x y3 y`, i.e. **P(Y=y | X=x) in the trial IS
    P(Y=y | do(X:=x))**. Legitimate because the logged X is `w x3`, X's own
    exogenous slot, independent of every other slot by `fdist_context`'s
    product form; under `te_obs3` the logged X would be `bias (w z3)` and
    selecting on it would select on Z, which is `obs3_is_not_do_mixture`.
  - **The LLN, stripped to an event.** Same move as 2026-10-21, one level
    further: `measure_lln_any`'s node-and-value indexing was about naming
    the *event*, and the proof never used which set it was. `emp_event` +
    **`emp_event_lln`** state it for any `A : {set context dom}`;
    `emp_freqE` recovers the per-column estimator as the instance
    `A := outcome_set e n v`, so `measure_lln_any`/`emp_lln_any` survive as
    corollaries. The gain: **arms** and **cells of a joint** are now in
    range, and they are not of the form "node n logged v".
  - **The estimator.** `emp_cond A B N` is the reported conditional
    frequency, a quotient of two `emp_event`s. Conditioning destroys the
    i.i.d. structure `wlln` needs (the per-arm count is itself random), so
    both halves stay inside the i.i.d. world and the division is paid for
    by **`ratio_close`** (`Prob.v`, pure algebra: `2*del <= b` forces
    `b/2 <= bh`, so the estimated denominator cannot collapse, and the
    quotient is within `4*del/b`). Then `emp_cond_bound` is an event
    *inclusion* plus `le_Pr_setU`, and **`emp_cond_converges`** is the
    eps-delta form with `del := min (Pr B / 2) (eps * Pr B / 8)` — the
    first argument keeps the denominator alive, the second makes the
    quotient bound beat `eps`.
  - **`rct3_full_emp_cond_converges`** — the capstone: what the confounded
    trial *reports* in the arm X = x converges to P(Y | do(X := x)), **arm
    by arm**, strictly stronger than `rct3_emp_converges`, which converges
    only to the mixture. The declared size is fixed at 1 in the events
    (`Let e3`, with `e3_is_the_protocol` proving by `elab_exp_size` that
    this is the elaboration at *every* declared size) — the same trick as
    `rct2_var`, and what lets the conditioning event stay fixed while the
    sample size is quantified.
  Axioms: boolp's three only, throughout.
  *Where positivity lives:* exactly one place, the division. `0 < P x3 x`
  is the **overlap** condition, a statement about the numbers that no
  well-formedness discipline can discharge — hence a hypothesis on the one
  lemma that divides rather than a side condition baked into a
  conditional-distribution type (that was the design choice; the ratio
  formulation is what makes it payable once). Note `fdist_do_rct3_Y` needs
  **no** such condition: the interventional law exists for every arm,
  including arms of probability zero. Overlap is about *estimating* a
  do-law, not about its existence.
  *Still open:* `P_3`'s exogenous slot at X is a point mass on `placebo`,
  so a *numeric* per-arm instance needs a coin with full support; the
  theorems above are all general in `P`. And everything is still
  **per-value** (single `v`), so the union bound over `#|dom n|` remains
  the cheapest open item.
  *Gotchas:* (1) `fdistmapE`'s bigop selector is `a \in preim f (pred1 b)`
  and needs **`!inE`** (single `inE` only adds a `true &&`); `/=` does not
  touch it. (2) infotheo's RV combinators do not reduce under unification:
  `(X `-cst m) u` is *convertible* to `X u - m` but `apply` will not unfold
  the function-space ring, so it needs naming as a lemma proved `by []`
  (`trans_sub_RV_appE`). (3) `le_Pr_setU` takes the fdist **explicitly**
  (`le_Pr_setU _ _ _`). (4) mathcomp's min lemmas here are `ge_min`/
  `le_min`/`lt_min` (not `ge_min_l`), and `ler_wpM2l`/`ler_wpM2r` are
  `{homo}` statements, so `apply:` them rather than `rewrite`.
- **The interventional law, and the trial as a mixture of do-laws**
  (`Prob.v` + `Rct3.v`, 2026-11-03) — the correctness results up to here
  were all *pushforward* statements: `rct3_correct` says the trial's
  outcome law factorises as a mixture over a treatment law, but nothing in
  it mentions `do()`, so it is evidence that randomization worked rather
  than a causal claim. This batch names the mixand.
  - **The typed do-layer** (`Prob.v`, 3 names). `solve_do enc dec tF a v w n`
    is `dec n (odflt 0 (Main.semantic_do (ssval a) (enc a v) G (elab tF)
    (ssval n) (to_assign w)))`, and `fdist_do enc dec tF P a v n` is its
    pushforward along `fdist_context P`, i.e. **P(n | do(a := v))**.
    `solve_doE` restates it on the surgered graph/graphfun, which is the
    form that will chain with `randomize_semantic_do`. The point is that
    this cost **nothing new**: `semantic_do` was already a *denotation*
    (Main.v:220), so the typed layer gets an interventional law with no new
    program construct, no new randomness, and no new axioms — `fdist_do` is
    the exact sibling of `fdist_node`. Note `solve_do` does not read `w a`:
    the constant mechanism ignores parents *and* noise, so `a`'s own draw is
    dead, which is what setting `a` should mean.
  - **The instance** (`Rct3.v`). `Section Do3Solve` solves the surgered
    model node by node (`do3_Z`/`do3_X`/`do3_Y`) on
    `Interventions.do 1 G3`; two `Example`s record the surgery by
    computation (`find_parents 1 Gd = nil`, `find_parents 2 Gd = [1;3]`).
    Then `fdist_do_rct3_Y`: `fdist_do ... x3 t y3 = dmap (h3 t) (P z3)` —
    setting X kills X's draw, so the only randomness left upstream of Y is
    the confounder's **own** noise. Hence the headline
    **`rct3_is_mixture_of_do`**: the law the protocol
    `[Randomize X, Measure Y]` logs at Y **is** the `P x3`-mixture of the
    interventional laws `P(Y | do(X := t))`.
  - **The payoff.** `obs3_is_not_do_mixture`: at `P_3` the *observational*
    protocol's logged law is **≠** that mixture. Seeing is not doing on this
    model, as an inequation between a law the confounded design produces and
    the causal quantity it would be mistaken for. (Proof: two lines —
    `rct3_differs_from_obs3` read through `rct3_is_mixture_of_do`.)
  - **The experiment level.** `rct3_emp_converges` and
    **`rct3_emp_converges_eps_delta`**, mirroring Rct2's pair with
    `rct3_is_mixture_of_do` naming the target: for every `eps`, `delta`
    there is an `N0` beyond which the frequency the trial reports at Y is
    within `eps` of the **interventional mixture** with probability
    `≥ 1 − delta`. `rct3_var`/`rct3_varE` are the `elab_exp_size` trick
    again. This is the first empirical statement about rct3 at all, and it
    closes the full arc — concrete run → empirical frequency → causal
    quantity — on a model where randomization is doing real work.
  Axioms: boolp's three only, throughout.
  *What this does NOT rest on:* the general randomize/do bridge.
  `rct3_is_mixture_of_do` is proved by **computing both sides** on this
  model. `randomize_semantic_do` (Correctness.v:227) is still the per-unit
  statement only; its distributional lift (M5/Theorem A) needs (a) an
  `assignments_equiv` argument reconciling the head-position draw
  `(n,v)::U` with the slot `to_assign enc w` already holds for `n` — sound
  because `get_assigned_value` is first-match — and (b) the `dbind` lift
  through the mixture over the coin. So what is established is that the two
  readings *agree on this model*, not in general.
  *Gotchas:* `a` in `solve_do`/`fdist_do` is auto-implicit because it
  appears in `v`'s type (`v : dom a`); fixed with explicit `Arguments`
  after each section closes rather than `Unset Implicit Arguments`, which
  does nothing useful mid-section since implicits are computed at section
  close. `<>` unfolds to an arrow, so a lemma stated with `<>` makes its
  earlier `nat` arguments implicit too — `@rct3_differs_from_obs3 N`, not
  `rct3_differs_from_obs3 N`. And `Interventions` is **require-only** in
  both files (it imports `Nat` and `Lists`, which shadow mathcomp names);
  only the qualified `Interventions.do` is used.
- **The same trial over arbitrary finite domains** (`Rct2.v`, `Section
  Rct2Gen`, 2026-10-21) — the trial replayed at two abstract nonempty
  finTypes `A`, `B` with points `a0`, `b0`, codes from
  `enc_default`/`dec_default` (`enum_rank`), and `rct2_correct_gen` the
  same mixture conclusion. The headline is that `rct2g_T` and `rct2g_R`
  are the concrete solve proofs **verbatim**, with `enc_2K` swapped for
  `enc_gK`: the cardinalities were never load-bearing, and the only thing
  the proofs ever used about a domain was cancellation. Three
  generalisations at once — `|D_R|` free, `|D_T|` free (so this is a
  **k-arm trial**, `P t2 = dunif` being the balanced one and `|A| = 1` the
  degenerate single-arm case), and T's pre-randomization mechanism an
  arbitrary `bias : A -> A` instead of the constant `placebo`, which
  sharpens the erasure claim from "erased a constant" to "erased
  anything". Axioms: boolp's three only.
  *Why the concrete version is kept too* (her call, 2026-10-21): the
  canonical codes are built from `enum_rank`, which does **not reduce**,
  so this section proves laws but can discharge nothing by
  `reflexivity` — whereas concrete `Rct2.v` evaluates its elaboration and
  its ordering side conditions by computation. Concrete = the one that
  runs, abstract = the one that generalises.
  *Not claimed:* that `rct2_correct` is an **instance** of
  `rct2_correct_gen`. It is not — different code pairs, and nothing yet
  proves the logged law is independent of which cancelling pair is
  chosen. That independence follows from M5e, which gives M5e a second
  motivation: it retroactively makes the concrete trial a corollary of the
  abstract one.
- **Protocol-independent concentration, and the trial at the experiment
  level** (`TypedExp.v` + `Rct2.v`, 2026-10-21) — the correctness results
  up to here all compared *distributions*; this is the comparison an
  experimenter can act on. Two halves.
  - **The hypotheses were about the target, not the probability.**
    `measure_source_emp_lln` carries five structural premises (dag,
    source node, single-measurement protocol, mechanism `= g`), and all
    five are used in exactly one place: `E_outcome`, to rewrite the
    indicator's mean as `dmap g (P n) v`. Naming the target by the
    abstract semantics instead gives `E_outcome_any`:
    `` `E (Ind (outcome_set e n v)) = fdist_log_val e n v ``, true by
    unfolding for **any** experiment, **any** node, no graph assumption.
    Hence `measure_lln_any` and **`emp_lln_any`**: for any protocol, the
    empirical frequency of a logged value concentrates on
    `fdist_log_val`, the population law of that same logged value. All
    protocol-specific work is pushed into *computing* `fdist_log_val`,
    which is exactly what each worked example does.
  - **The instance.** `rct2_emp_converges` (Chebyshev rate) and
    **`rct2_emp_converges_eps_delta`**: for arbitrary finite `A`/`B`,
    arbitrary `bias` and `h`, and any allocation law, for every `eps > 0`
    and `delta > 0` there is an `N0` beyond which the reported frequency
    is within `eps` of the mixture with probability `≥ 1 − delta`. That
    is convergence in probability of the concrete run's log to the
    abstract output law of R. Proof: `rewrite -rct2_correct_gen; exact:
    emp_lln_any`, plus archimedean arithmetic. Axioms: boolp's three only.
  *Declared size = actual size.* First written with the declared size and
  the sample length as two independent parameters; **corrected 2026-10-21
  on her objection**, and she was right. The separation was a workaround,
  not a design: in the `eps`-`delta` statement the sample size is
  *quantified*, so the variance constant that `N0` is chosen from must not
  depend on the `N` being quantified — and written directly it appears to,
  since the experiment mentions `N.+1`. Decoupling the sizes dodged that;
  the honest fix is `elab_exp_size` (`TypedExp.v`, proved `by []`):
  elaboration reads only labels, mechanisms and ops, so two records
  differing *only* in declared size elaborate to the **same term**. Hence
  the indicator — and its variance — is literally size-independent, and
  `rct2_var` names that constant once at a fixed index. The theorems now
  run the protocol `te_rct2_g bias h N.+1` on `N.+1` units and quote
  `te_size` as the rate, so a record whose declaration disagreed with its
  sample is not an instance at all. *Lesson for future statements:* a
  hyperparameter that elaboration drops is size-independent by conversion;
  reach for that rather than for an extra parameter.
  *No variance sign lemma needed:* infotheo proves none for `` `V ``, and
  it turned out not to matter — `truncnS_gt` (`x < (truncn x).+1%:R`) is
  unconditional on a `realType`, so the `eps`-`delta` rearrangement goes
  through without `0 <= V`.
  *Still per-value*, exactly as M5b records: this is convergence at a
  fixed `v`, not of the empirical distribution as a whole. `#|B|` is
  finite, so a union bound (`delta/#|B|` in each instance) upgrades it to
  the supremum distance. Not yet formalised, and now the cheapest open
  item.
  *Gotcha:* `le_trans`/`lt_le_trans` need `Import Order.TTheory`;
  `Num.Theory` alone does not supply them. The import sits **after** the
  earlier proofs in the section, which is safe because `Import` is never
  retroactive.
- **The confounded randomized trial** (`Experiment/Rct3.v`, 2026-10-20) —
  the case randomization exists for. Reuses Main.v's `G_3`
  (`Z -> X`, `Z -> Y`, `X -> Y`) with all of `Prob.v`'s domains, codes and
  `tF_3`, and compares **two protocols on one model**:
  - `rct3_correct` — under `[TRandomize x3; TMeasure y3]` the outcome law
    is `dbind (P x3) (fun t => dmap (h3 t) (P z3))`, a mixture over a
    treatment law that no longer depends on Z.
  - `obs3_log_law` — under `[TMeasure y3]` alone it is
    `dmap (fun a : age => h3 (bias a) a) (P z3)`: **a function of the
    confounder alone.** Z fixes the treatment which fixes the response, so
    there is no treatment law left to mix over — that missing degree of
    freedom *is* the bias.
  - **`rct3_differs_from_obs3`** — the two laws are DIFFERENT at `P_3`,
    witnessed at `worse` (mass `1/3` vs `0`). So randomizing is not a
    no-op and the confounding was real. The mechanism is sharp: `worse`
    arises only from *placebo + old*, and the confounded mechanism treats
    exactly the old, so observationally no unit can be both.
  Axioms: boolp's three only. Three things it adds beyond `Rct2.v`:
  - **The two-parent lookup is finally exercised.**
    `find_parents 2 G3 = [1;3]`, so the keyed reads `pa x3` / `pa z3` must
    resolve to positions 0 and 1. `Rct2.v`'s parent lists had one element,
    where any lookup discipline would have worked.
  - **A three-deep solve** (`obs3_Y`: Z -> X -> Y with X genuinely reading
    Z), and it still went through on `rewrite !enc_3K` alone. See the
    revised elaboration-correctness entry.
  - **The first theorem in the development that computes a number**
    (`rct3_P3_worse = 3^-1`). It works only because it touches `P_3`'s
    components (`dret`, `dunif`) and never routes through
    `to_assign`/`enum`.
  *Caveat on the instance:* at `P_3` the law at X's slot is `dret placebo`
  (a point mass, inherited from the model where X ignored its noise), so
  the trial being separated is **degenerate** — after randomization every
  unit gets placebo. The separation is genuine, and the degeneracy sharpens
  it, but this is not an illustration of a *balanced* trial.
  `rct3_correct` is general in `P`, so a balanced coin is one
  instantiation away.
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
- **Typed mechanism boundary** (`Prob.v`, 2026-09-19..23) — per-node domains
  `dom : Node G -> finType`, typed mechanisms `tnodefun`, and `elab` compiling
  them into dsep-core's `nat` graphfun unchanged. `elab_compatible` is now
  structural (D8). Worked example: the 3-node drug trial with three categorical
  domains of different cardinality.
- **Exogenous law** (`Prob.v` Part 5) — `fdist_context P = \prod_n P n (w n)`,
  the product over unobservables (Universal Assumption 2), with
  `fdist_context_marginal` recovering each node's own noise law. Needed a
  dependent distributivity lemma (`bigA_distr_big_dffun`) since infotheo ships
  only the homogeneous product.
- **Induced law over worlds** (`Prob.v` Part 6) — `fdist_world = dmap world_of
  (fdist_context P)`, and `fdist_node n = dmap (solve ^~ n) (fdist_context P)`
  (2026-10-20) — the abstract program's **per-node output**, which is what a
  causal query ranges over; `fdist_world_marginal` proves the two routes to it
  agree (read the world law at n, or push n's solved value forward directly),
  and `to_assign_complete` / `find_value_to_assign` proving a typed context is
  a *complete* exogenous assignment, so `eval`'s default is dead and `solve`
  names a real solution. Axioms: only boolp's three, already in the base.
- **Total + selecting per-unit runners** (`Main.v`, 2026-09-23) —
  `run_unit_total` with `run_unit_total_correct` (agrees with the partial
  `run_unit` under wf), which frees the `option` for `run_unit_sel`, where
  `None` means *filtered out* rather than *failed*.

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
- **M4a** ✅ 2026-09-23 — **denotation of a model**: `fdist_context` (exogenous
  product law) and `fdist_world = dmap world_of (fdist_context P)` in `Prob.v`,
  with the completeness lemmas that make the solve total on typed contexts.
- **M4b** ✅ 2026-09-23 — **experiment-language groundwork**: `raw_context`
  rename (D9), `sample` dropped (D7), `measures_last` clause on
  `wf_operations`, total per-unit runner. `Spike.v` retired to `attic/`.
  (`Filter` was built here and then deferred per D11; recoverable from
  commit `0e80c37`.)
- **M4b′** ✅ 2026-09-23 — **typed experiment surface** (`TypedExp.v`, D12):
  `toperation` with values in their own domain, `elab_op`/`elab_ops`
  compiling to `Main.operation`; `twf_operation` carrying only the label
  obligations (membership is structural); `measures_last_elab` transferring
  the ordering discipline; `texperiment`/`elab_exp` with `elab_exp_wf`,
  whose `dag_fun_compatible` clause is discharged by `elab_compatible`.
  Worked typed RCT on G3 elaborating to `[Randomize 1; Measure 2]` by
  `reflexivity`, and `TIntervene x3 cured` rejected as a type error.
- **M5a** ✅ 2026-09-30 — **hello-world theorems**: `measure_source_law`
  (exact law equality) and a finite-sample counterpart, plus `solve_source`
  and `sum_iidE`. See Status above. (The finite-sample theorem and its
  list-based `emp` were superseded by the `_rV` versions in M5b and
  retired 2026-10-14.)
  Generalised 2026-10-03 from "mechanism = identity" to "mechanism is
  parent-free", i.e. `tF n u pa = g u` for arbitrary `g`; the laws became
  pushforwards `dmap g (P n)`. Cost: four signatures and one `dmap_comp`
  step. **This is the first fragment of the general pushforward story**
  (M4c): a parent-free node already shows the shape "law of the logged
  value = `dmap` (what the mechanism does) (the exogenous law)".
- **M5b** ✅ 2026-10-07 — **the sample layer** (D13): `te_size` on
  `texperiment`, `sample`/`fdist_sample`/`log_sample`/`emp_freq`, plus
  `emp_rV` and the bridge `emp_rV_sum_iid` in `Prob.v`, and the two laws
  restated about the program's own output
  (`measure_source_empirical_rV`, `measure_source_emp_lln`). The protocol
  still contains **one** `TMeasure n`; the `\row_i` in `log_sample` runs
  that one-op program at each of the N units. See Status above.
  *Still open here:* the LLN remains **per-value** — covering all of
  `dom n` needs a union bound costing `#|dom n|` — and `Var(X_v) = p(1−p)
  ≤ ¼` is still left abstract.
- **M5c** ✅ 2026-10-20 — **the dataset** (D14): every measured node's
  column at once, ticketed by `is_measured`, with `joint_at` making unit i's
  joint observation a real indexed read. Closes the "finite log type"
  item that M5b listed as outstanding. Also `fdist_node`, naming the
  abstract program's per-node law. See Status above.
- **M5d** ✅ 2026-10-20 — **two worked trials** (`Rct2.v`, `Rct3.v`, D15).
  `Rct2.v`: the two-node trial `T -> R` — first experiment with a node that
  has a parent, first *mixture* conclusion. `Rct3.v`: the confounded trial
  on `G_3` — two-parent positional lookup, a three-deep solve, and
  `rct3_differs_from_obs3` showing randomizing changes the law. Supporting
  general lemmas `fdist_context_pair` and `dmap_uncurry_prod` in `Prob.v`.
  See Status above.
- **M5f** ✅ 2026-10-21 — **the trial at arbitrary domains, and the
  experiment level**. `Section Rct2Gen` replays the two-node trial at
  abstract nonempty finTypes (`rct2_correct_gen`, the k-arm trial);
  `E_outcome_any`/`measure_lln_any`/`emp_lln_any` in `TypedExp.v` strip the
  five structural hypotheses off the weak law by naming its target from the
  abstract semantics; and `rct2_emp_converges_eps_delta` is the first
  statement in the development that says the **concrete run's log
  converges to the abstract output law** of a measured node. The concrete
  `Rct2.v` is retained alongside the abstract one (it is the version that
  still computes). See Status above.
  *Still open here:* the union bound over `#|B|` to go from per-value
  convergence to the supremum distance — the cheapest remaining item.
- **M5g** ✅ 2026-11-03 — **the interventional law, and the trial as a
  mixture of do-laws**. `solve_do`/`fdist_do` in `Prob.v` give the typed
  layer `P(n | do(a := v))` out of Main.v's `semantic_do` with no new
  construct; `rct3_is_mixture_of_do` identifies the confounded trial's
  logged law with the `P x3`-mixture of those interventional laws;
  `obs3_is_not_do_mixture` states the confounding bias as an inequation;
  and `rct3_emp_converges_eps_delta` chains `emp_lln_any` onto it, so the
  concrete run's frequencies converge to a **causal** quantity. See Status
  above.
  *Still open here:* the statement is per-model (both sides computed), not
  via the distributional lift of `randomize_semantic_do` — that is M5.
  Also still per-value (union bound over `#|B|`), and `te_rct3` has no X
  column, so no per-arm/conditional version is available.
- **M5h** ✅ 2026-11-03 — **conditional probability, and the trial arm by
  arm**. `te_rct3_full` adds `TMeasure x3`; `rct3_full_joint` shows the
  trial is *jointly* a mixture of do-experiments; `rct3_full_cond` proves
  **P(Y|X=x) in the trial = P(Y|do(X:=x))**; the LLN is restated for an
  arbitrary event (`emp_event_lln`), and `emp_cond_converges` /
  `rct3_full_emp_cond_converges` carry it through the quotient, so the
  reported per-arm frequency converges to the interventional law. Needed no
  conditional-distribution type: infotheo's `cPr` applies to our events as
  they stand. See Status above.
  *Still open here:* a full-support coin for a numeric per-arm instance,
  and the union bound over `#|dom n|` (still per-value).
- **M5e** (next) — **general elaboration correctness**: prove
  `solve F w n = F n (w n) (fun p _ => solve F w p)`, generalising
  `measure_source_law` off parent-free nodes. Per the rediagnosis above the
  work is the positional↔keyed parent lookup, not the coding; `Rct2.v` is
  the depth-2 case where that lookup holds by computation.
- **M4c** — **distribution semantics of a program**: the distributional
  layer attaches to `abs_state`, not to logs (the log is the *concrete*
  output). `Randomize n` is surgery on the exogenous law (substitute the coin
  `d_n` at `U_n`); `Intervene` is surgery on the mechanism. Output: the
  post-experiment world law marginalised to `measured`.
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

**Target story**: "experiments as probabilistic programs — a verified RCT",
which needs M1–M6. (A POPL SRC submission was the original target; dropped
2026-10-12, so there is no external deadline driving the order.)

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

## Repo Conventions (for Claude Code)

- Language: Rocq 9.1.0. `dsep-core/` is Anna's code — read-only, vanilla Rocq
  (`nat`/`List`/`lia`), value layer stays `nat`-valued (D5).
- Probability: **infotheo 0.9.7** (mathcomp 2.5.0, analysis 1.16.0) — already in
  the `vsrocq` opam switch. Add `coq-infotheo` to `rocq-causal.opam` and its
  logical paths to `_CoqProject`/Makefile at M1a.
- Layout:
  - `Experiment/Main.v` — labels, `aug_graph`, operations, concrete +
    abstract semantics, total per-unit runner, backdoor pair;
    (soon) `model` + one transform per op.
  - `Experiment/Prob.v` — the typed boundary (`Node`, `dom`, `context`,
    `world`, `to_assign`, `elab`) + narrow `fdist` wrappers, then the
    denotation: `fdist_context` (Part 5) and `fdist_world` (Part 6).
    `solve_do`/`solve_doE`/`fdist_do` are the surgered siblings of
    `solve`/`fdist_node`, i.e. `P(n | do(a := v))`; `ratio_close` and
    `quarter_of_eighth` are the arithmetic the conditional estimator needs.
  - `Experiment/TypedExp.v` — the typed experiment surface (D12):
    `toperation`/`elab_op`, `texperiment`/`elab_exp`, and the transfer
    lemmas (`elab_op_wf`, `elab_exp_wf`). Then the laws: `fdist_log_val`,
    `fdist_log_pair`, `Pr_outcome`/`Pr_outcome_pair`/`cPr_outcomeE`/
    `cPr_outcome_eq` (conditioning, via infotheo's `cPr`), and the
    concentration layer `emp_event`/`emp_event_lln`/`emp_cond`/
    `emp_cond_bound`/`emp_cond_converges`.
  - `Experiment/Rct2.v` — the two-node randomized trial worked end to end
    (`G2`, `tF_2`, `te_rct2`, `rct2_correct`); the depth-2 case of
    elaboration correctness. Then `Section Rct2Gen`: the same trial at
    arbitrary nonempty finite domains (`rct2_correct_gen`, the k-arm
    trial) and the experiment-level convergence statements
    (`rct2_emp_converges`, `rct2_emp_converges_eps_delta`, with
    `rct2_var`/`rct2_varE` naming the size-independent variance constant).
  - `Experiment/Rct3.v` — the CONFOUNDED trial on `G_3`: `te_rct3` vs
    `te_obs3` on one model, `rct3_correct` / `obs3_log_law`, and
    `rct3_differs_from_obs3`. Depth-3 solve, two-parent lookup, and the
    only numeric computation in the development. Then `Section Do3Solve`
    and `Section Do3Law`: the surgered solve, `fdist_do_rct3_Y`,
    `rct3_is_mixture_of_do`, `obs3_is_not_do_mixture`, and the
    experiment-level `rct3_emp_converges`/`rct3_emp_converges_eps_delta`.
    Then `te_rct3_full` (which also measures X) with `rct3_full_joint`,
    `rct3_full_cond` and `rct3_full_emp_cond_converges`: the per-arm route.
  - `Experiment/Correctness.v` — per-world core (`randomize_semantic_do`), RCT syntactic correctness; later Theorems A and B.
  - `attic/` — retired prototypes, not in `_CoqProject` (`Spike.v`).
  - `examples/` — encodings of historical/natural experiments (future).
- **Vocabulary (D9)**: `context` = exogenous draw (typed, `Prob.v`);
  `raw_context` = its nat-coded form (`Main.v`, what `find_value` takes as
  `U`); `world` = solved node values. One meaning each, everywhere.
- **Style boundary**: SSReflect/infotheo lives *inside* `Prob.v` behind the
  narrow interface; the causal proofs stay vanilla Rocq. Don't let `fdist`/bigop
  names leak into `Main.v`/`Correctness.v`.
- Keep simplifying assumptions documented in module headers.
- Designer's choices are decided with Blanca first, then logged in the Decision log above.

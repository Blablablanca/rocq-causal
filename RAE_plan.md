# Experiments as Programs — Project Plan

Formal framework (in Rocq) for expressing scientific experiments as programs over causal DAGs, so experimental designs can be checked for correctness with program-analysis techniques (e.g., d-separation).

## Motivation

Historically, experiments are error prone: unidentified non-causal influence paths, bad proxies, unexecutable designs. If we treat an experiment as a program transforming a causal DAG, we can statically verify the design.

A **correct design** means:

1. **Validity** — the experiment successfully measures the effect of the treatment(s) on the response(s).
*Graphically:* the post-experiment graph d-separates T and R from all non-causal influence, and T and R remain reachable via the intended causal path.
*Algebraically:* P(R|do(T))
2. **Executability** — all controlled/intervened nodes are not labeled unmeasurable.

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
- Treatment and response should generalize to **sets/vectors of nodes**: the objective is P(R | do(T)) where T and R are vectors, i.e., measure (T₁ ∧ … ∧ Tₙ) → (R₁ ∧ … ∧ Rₖ). Do not hard-code |T| = |R| = 1.
- Sequential / time-varying treatments: handled by sequential `Intervene` operations; relevant theory is Robins' g-formula.
- The response may not be directly measurable in reality; the user decides whether to use a proxy as the response node or model response as a function of other nodes.
- Simplifying assumptions: no measurement error, no execution error.
- Also see "Universal Assumptions" in `Exp_Basics.v`
- Edge labels (time-step edges, correlation edges) are deferred. Time steps can be modeled as causal edges; correlation edges would complicate the construction.

### Experiment

```coq
Record experiment (X : Type) : Type := mk_experiment {
  init_graph : aug_graph;
  init_fun   : @graphfun X;
  sample     : list (individual X);  (* individual = complete instantiation of the unobservables *)
  ops        : program X;
}.
```

- `sample` is finite and concrete for now; the resulting distribution is therefore sample-dependent. To compare experiments, consider asymptotic behavior (**future work**).

### Operations

```coq
Inductive operation (X : Type) : Type :=
  | Intervene (n : node) (v : X)      (* do(n=v): set n to a specific value *)
  | Randomize (n : node) (r : node)   (* RCT: remove incoming edges to n, add fresh r → n *)
  | Measure   (n : node).             (* record n's current value into the log *)
```

- This minimal set {intervene, randomize, measure} is a deliberately simple, well-defined starting point. Even though there are countless ways to "measure" in practice, one abstract `Measure` is useful at this level of abstraction.
- `Control` is intentionally excluded for now — it lacks a clear characterization. Revisit later.
- Planned future operations: `Control`, `Stratify`, `Timestep`.

## Semantics

The DSL has **three layers**, related by an abstraction. The design lesson from
building this out: the DAG is the *abstraction* of the mechanism — it keeps *who
depends on whom* (the arrows), forgets *how* (the functions) and forgets the
data — and static verification lives on that abstraction. Do **not** fuse the two
into one `⟨G,F⟩` object at the level of state/transforms: fusing throws away the
cheap, universal, decidable reasoning that motivates using a DAG at all.

| layer | object | role |
|---|---|---|
| **structural** | DAG `G` + labels + `measured` | abstract interpretation; d-separation for verification |
| **mechanism** | graphfun `F` (+ `dom`) | operational run → log; carries the values |
| **denotation** | `⟦⟨G, F⟩, P_U⟧ = P` | the interventional distribution `P(R \| do(T))` |

- The **structural** layer is **X-free** and touches neither `F` nor data — that
  is what lets it plug into d-separation (graph reachability) and hold for
  *every* parameterization. `abs_state = { dag; labels; measured }`.
- The **mechanism** layer carries `F` and produces the log. `dom` rides here (it
  is value-space metadata) and grows when `Randomize` adds a node. It evaluates
  against the fixed program graph `G0` — graph surgery is *inert for values*
  (each op makes the affected node ignore its parents) — so it carries no DAG:
  `unit_state = { cur_fun; log }`.
- Neither layer alone yields a distribution: the DAG fixes only the Markov
  factorization (the independence structure), the numbers need `F` and the
  exogenous law. The **denotation** reads the whole tuple `⟨G, F⟩` plus
  `P_U`. This is the *only* place the two sides are bundled — bundle the
  *reading*, never the state.

### Transformation rules

Each operation has a rule on the structural side and a rule on the mechanism
side (defined separately; bundled only at the denotation):

| op | structural (`G`) | mechanism (`F`, `dom`) | observation |
|---|---|---|---|
| `Intervene n v` | remove incoming edges to `n` | `f_n := const v` | — |
| `Randomize n r` | add fresh source `r → n`, remove other incoming | `f_n := f_unobs`; draw `(n,v)` shadows `n` | — |
| `Measure n` | — | — | append `n`'s current value to the log |

Concrete encodings: `Intervene n v = do_graphfun n v` on the fixed graph;
`Randomize n r = randomize_graphfun n` (n reads its own exogenous draw), with the
randomizer value injected as `(n, v)` at the head of the individual, *shadowing*
n's natural noise (`get_assigned_value` returns the first match). No fresh node,
no surgery on the mechanism side — `r` is used only structurally.

### G and F need not structurally agree

A tempting but **wrong** goal is "prove the `G`-transform and the `F`-transform
agree with each other." They do not — under the fresh-node-free `Randomize` the
equality is literally *false*: `G'` has the edge `r → n`, but `F'` makes `n` a
noise-root that never reads `r`. Their *syntax* disagrees; what must hold is that
they denote the same **distribution**. So "agreement" is always routed through
the denotation, never asserted between the two representations. (This is the
trivial `graphs_agree` lesson with teeth: even the *content* of a direct G↔F
identity is wrong, not merely shallow.) The extra `r → n` edge only makes `G'` a
*sound over-approximation* of `F'`'s real dependencies — an extra edge can delete
a d-separation but never fabricate one — which is exactly the abstract-
interpretation soundness relation, and is all verification needs.

### Two correctness theorems

**A. Adequacy of the transform** (the rules implement `do`). The transform
commutes with the semantic do-operator on distributions:

```
              transform(op)
        M  ───────────────►  M'
        │                     │
       ⟦·⟧                   ⟦·⟧
        ▼                     ▼
        P  ───────────────►  P'
                do_op
```

`⟦transform(op)(M)⟧ = do_op(⟦M⟧)`. This is where `G` and `F` "meet": both
describe the same `P'`, mediated by the denotation `⟦·⟧`. The probability-free
per-world core for `Randomize` is **done** (see below).

**B. Soundness of the abstraction** (why static verification is valid).
d-separation on `G'` implies the target independence / identification in
`P' = ⟦M'⟧`. This survives the G/F structural disagreement (over-approximation is
sound) and is the dsep-core theorem (d-sep ⟺ semantic separation) lifted to
post-experiment graphs.

**Design correctness = A + B:** A says `P'` is the intended interventional
distribution; B says the `measured`/log footprint structurally identifies it.

Proof strategy:
- Assume a finite probability space; prove **multiset equality** to bypass general probability theory.
- First milestone: prove correctness for RCT (`Randomize`).

### Done: RCT counterfactual consistency (`Experiment/Correctness.v`)

Probability-free **per-world core of Theorem A** for `Randomize`, proved (no
admits). Fresh-node-free formulation — the mechanism side needs no graph surgery:

```coq
Theorem randomize_semantic_do : ...
  find_value G (randomize_graphfun n g) w ((n, v) :: U) []
  = semantic_do n v G g w U.
```

On the stratum where the injected randomizer draw is v, the randomized mechanism
— evaluated against the **fixed** graph G with no surgery — gives every node its
do(n=v) counterfactual value, individual by individual. `v` enters as *data* on
the left (shadowing n's exogenous slot) and as *surgery* on the right
(`semantic_do = do n G + do_graphfun`); the two are indistinguishable. Proved by
strong induction on topological-sort index, dsep-core style. Supporting lemmas:

- `randomize_value_at_n` — node n reads its shadowed draw (`f_unobs`), yielding v.
- `randomize_do_step` — for w ≠ n both sides run the original g on the same
  parents; the shadowing `(n,v)` is invisible to w.
- `do_value_at_n` — the do-side value at n is v.
- `G_well_formed_do/_randomize`, `contains_cycle_do/_randomize` — surgeries
  preserve well-formedness and acyclicity. These serve the **structural** layer's
  invariants (its graph still uses the fresh source `r`), not the value path.
- `randomize_then_measure` — corollary against `apply_op`: the mechanism
  `Randomize` against the fixed program graph `G0` equals do(n=v). Requires the
  individual to carry the injected draw `(n, v)` — concrete `Randomize` does not
  yet inject it (**known gap**).

Lifting this per-world fact over the randomizer's law and the population gives
`P'` — i.e. Theorem A for `Randomize` — which is the multiset/probability layer
(milestones 4–5). What the per-world theorem does *not* yet say: that the log
identifies `P(R | do(T))`; that needs the injected draws uniform and independent
of confounders (Theorem B's job). Also add to `experiment_wf`: every individual
in `sample` assigns all nodes (currently missing).

The surviving cross-layer fact at the value level is a data-free **simulation
invariant** (`measured_agree`): the log's node footprint equals the structural
`measured` set, step for step — infrastructure, not a theorem.

**Open modeling decision** (flagged): where per-unit randomizer draws live — a
separate exogenous family vs. shadowing slot `n` — and how they get injected
during execution (the "known gap" above).

### Probability infrastructure

- Build a self-contained finite probability library rather than importing infotheo, but be aware of the risk: needs tend to grow, and it may become worth switching to an existing library later. Design the probability layer with a narrow interface so migration to infotheo remains feasible if needed.

## Static analysis techniques for identifiability

Each design-correctness criterion is a **graphical (syntactic) check** on the
post-experiment DAG that certifies `P(R | do(T))` is identifiable, paired with a
**value-level (semantic) counterpart** and a soundness/completeness theorem
between them — i.e. an instance of **Theorem B**. Curated here: the backdoor pair
is done; the rest are pinned TODOs. Each new one is a `syntactic_*` bool check, a
`semantic_*` Prop, and a `*_correspondence` theorem.

### Done: backdoor criterion (`Experiment/Main.v`)

```coq
Definition syntactic_backdoor (G : graph) (T R : node) (Z : nodes) : bool :=
  no_descendant_of_b T G (cond_set T R Z)
  && d_separated_bool T R (remove_outgoing T G) (cond_set T R Z).

Definition semantic_backdoor (X : Type) `{EqType X}
    (G : graph) (T R : node) (Z : nodes) : Prop :=
  no_descendant_of_b T G (cond_set T R Z) = true /\
  semantically_separated X (remove_outgoing T G) T R (cond_set T R Z).

Theorem backdoor_correspondence : ...
  syntactic_backdoor G T R Z = true <-> semantic_backdoor X G T R Z.
```

- **Adjustment set** `cond_set T R Z` = `Z` deduplicated and stripped of `T`, `R`
  (never valid covariates) — so `each_node_appears_once` and `T,R ∉ Z` hold by
  construction and are *not* theorem hypotheses.
- **Syntactic side**: `Z` contains no descendant of `T`, and `T` is d-separated
  from `R` given `Z` in `remove_outgoing T G` — the graph with `T`'s *outgoing*
  edges deleted, so only into-`T` (backdoor) paths survive. A decidable check.
- **Semantic side**: same admissibility guard, but blocking is
  `semantically_separated` — perturbing `T` never changes `R` given `Z`, for
  *every* mechanism (∀ graphfun).
- **Proof (brief)**: the shared no-descendant guard splits off via `andb`; the
  remaining `d_separated_bool ⟺ semantically_separated` is dsep-core's
  `semantic_and_d_separation_equivalent` on the outgoing-mutilated graph.
  Remaining hypotheses: `R ∈ G`, `T ≠ R`, `G` well-formed/acyclic (transferred
  through edge removal by `G_well_formed_/contains_cycle_remove_outgoing`).
- **RCT** is the `Z = ∅` special case (randomizing `T` severs all backdoor paths).

### TODO: frontdoor criterion

Unobserved confounding of `T → R`, but a fully-mediating *observed* mediator `M`
(`T → M → R`, no direct `T → R`, confounder doesn't touch `M`). Estimand = two
chained adjustments; conditions on the mediator. `syntactic_frontdoor` /
`semantic_frontdoor` + correspondence.

### TODO: do-calculus (three rules)

The general engine — insertion/deletion of observations, action/observation
exchange, insertion/deletion of actions — each a d-separation condition in a
mutilated graph. Backdoor is essentially rule 2. A verified do-calculus rewrite
system would subsume backdoor and frontdoor.

### TODO: ID algorithm

Tian–Pearl / Shpitser–Pearl: sound **and complete** for nonparametric
identifiability of `P(R | do(T))` from the observed distribution with latents.
The general endpoint (backdoor/frontdoor are special cases), and the natural
place to *output the estimand*, not just a yes/no.

### TODO: instrumental variables (different shape)

Instrument `Z → T`, independent of confounders, affecting `R` only through `T`.
**Not** nonparametrically point-identified (the ID algorithm returns "not
identifiable"): gives bounds (Balke–Pearl) or a LATE under monotonicity. So
"correct" widens to *identifiable-under-extra-assumptions or bounded*. Also the
case that breaks the fixed-`G0` evaluation shortcut (see Semantics).

### TODO: testable implications (model validation, not identifiability)

The conditional independences a DAG *entails* (its d-separations) are exactly the
constraints to check against real data to *falsify* the model. Reuses
`semantically_separated` / `d_separated_bool` directly — the "input your CI
assumptions and see whether the model implies them" use case.

## Todo outside of this codebase

- Curate a list of historical experiments and check whether the framework can express them. Start by collecting candidate experiments this week.
- Study **natural experiments** (sequences of interventions/circumstances that isolate causal effects when an RCT is infeasible) and attempt to simulate them in this framework. (Avoid framing this as "quasi-experiments" — that category is ill-defined.)

## Milestones

1. Generalize node labels / objective to vector-valued T and R.
2. Formalize the d-separation-based correctness criterion (validity + executability) — this is **Theorem B** (abstraction soundness) applied to the design.
3. Define the structural (`G`) and mechanism (`F`) transformation rules for {Intervene, Randomize, Measure}, plus the denotation `⟦⟨G,F,dom⟩,P_U⟧ = P`.
4. Build minimal finite probability layer (multiset-based distribution equality).
5. Prove **Theorem A** (transform commutes with `do`) for RCT. *(per-world core done — see `Correctness.v`; distributional lift over the randomizer's law remains)*

(1)-(5) due 7/15

6. Prove Theorem A (adequacy) and Theorem B (d-sep soundness) for all current operations.
7. Extend operations: Condition, Stratify, Timestep.
8. Future work: asymptotic equivalence of experiments (sample-independence in the limit).

## Deadlines

- POPL Student Research Competition: submission deadline typically end of October / early November.

## Repo Conventions (for Claude Code)

- Language: Rocq (Coq). Keep the probability layer behind a small interface module.
- Suggested layout:
  - `Experiment/Main.v` — node labels, experiment record, operations, programs, structural (`G`) and mechanism (`F`) transformation rules
  - `Experiment/Prob.v` — finite distributions, multiset equality, the denotation `⟦⟨G,F,dom⟩,P_U⟧ = P`.
  - `Experiment/Correctness.v` — validity/executability predicates; Theorem A (adequacy) and Theorem B (d-sep soundness).
  - `examples/` — encodings of historical and natural experiments (future work)
- Keep simplifying assumptions (no measurement error, no execution error, finite sample) documented in module headers so they're not silently violated.

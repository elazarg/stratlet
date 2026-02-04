## Plan for the core calculus formalization

### 1. Objective

A small, typed core calculus is developed for *probabilistic and strategic computation with partial information* such that:

* programs are effect trees (syntax) with no built-in meaning;
* meanings are given by *handlers* (interpretations) that can be exchanged without changing syntax;
* strategic behavior is represented by *profiles* supplied externally to the semantics;
* partial information is represented explicitly by *views* (projections of state).

The basic semantic contract used throughout is:

> For any fixed profile, evaluation yields a stochastic object over outcomes (and/or payoffs).

Solution concepts (Nash, sequential equilibrium, CFR, etc.) are treated as external constructions on top of this contract.

---

### 2. Relation to Fun

The calculus is positioned as a “free/handler-based” reformulation of the design pattern underlying Fun:

* **Fun** supplies a specific semantics via *measure transformers*, with `observe` interpreted as a conditioning/weighting transform (and designed to support continuous distributions).
* The core calculus instead isolates the same idea—*programs denote effectful computations; semantics is an interpretation*—but factors it into:

  1. a free syntax of effect trees, and
  2. handlers implementing particular semantic models.

In the discrete finite-support fragment, Fun-style constructs correspond closely:

* `sample` corresponds to sampling from a kernel;
* `observe` corresponds to a path filter or a likelihood-weighting transform (depending on the chosen observation primitive);
* the semantics can be implemented in a finite-support carrier (`WDist`-style), which aligns with a discrete fragment of Fun but does not replicate the measure-theoretic generality.

The plan therefore treats “Fun compatibility” as a fragment-level correspondence: the calculus can host an interpretation that matches Fun on discrete programs, and can be extended toward Fun’s generality only if a measure-theoretic carrier is adopted.

---

## 3. Design components

### 3.1 Program syntax (effect trees)

A fixed minimal syntax is used:

* `ret e` — return a pure expression
* `letDet e k` — deterministic binding
* `doBind c k` — effectful binding (effects that produce a value)
* `doStmt s k` — effectful statement (effects that return unit)

The intention is that almost all language growth occurs by extending the command signatures `c` and `s`, rather than adding new program constructors.

---

### 3.2 Handler packages (semantics interface)

A *handler package* consists of:

* a carrier type constructor `M : Type → Type`;
* operations `pure`, `bind`, `fail` (monad-with-failure interface);
* an interpretation of bind-commands: `handleBind : c → Env → M value`;
* an interpretation of stmt-commands: `handleStmt : s → Env → M Unit`.

A generic evaluator is defined by structural recursion on programs and delegates all effects to the supplied handlers.

This supports multiple interpretations of the same program: deterministic partiality, finite-support probability, symbolic compilation objects, etc.

---

### 3.3 Observation semantics (scope choice)

Two coherent observation regimes are distinguished early:

* **Filtering observation:** `observe φ` rejects executions when `φ` is false.
* **Scoring/weighting observation:** a primitive `score w` (or equivalent) multiplies the weight/likelihood of the current execution.

Filtering corresponds to discrete “hard evidence”; scoring corresponds more closely to Fun’s “soft evidence” / density-transform view (in the discrete setting). The plan treats this as a controlled scope decision: the initial development uses one regime consistently, with the other remaining an extension.

---

### 3.4 Strategic choice and partial information via views

A strategic layer is added via a bind-command:

* `choose (who, view, actionset)` producing an action.

A **view** is an explicit environment slice:

* a visible context `Δ`;
* a projection `Env Γ → Env Δ`.

Available actions are computed from the visible environment, e.g. `A : Env Δ → List Action`.

A **profile** supplies distributions for choices:

* for each choice point, given the visible environment, a distribution over actions is returned.

This makes information restriction structural: strategies only receive `Env Δ`, never the full environment `Env Γ`.

---

## 4. Milestones

### Milestone 0 — Kernel stabilization

**Deliverables**

* effect-tree syntax and generic evaluator;
* basic rewrite/definitional lemmas for evaluator equations;
* at least one simple handler instance (e.g. `Option`) as a validation of the interface.

**Completion criterion**

* adding new effects requires only adding new command constructors and handlers, with no changes to the evaluator.

**Backtracking indicator**

* repeated pressure to add new program constructors (rather than new command cases) indicates the kernel is mis-scoped.

---

### Milestone 1 — Discrete probabilistic fragment (Fun-aligned fragment)

**Deliverables**

* a finite-support probabilistic carrier with `pure`, `bind`, `zero` (and optionally normalization);
* a bind-command `sample` parameterized by a stochastic kernel `Env → Dist`;
* an observation regime (filtering or scoring) implemented as stmt-commands;
* basic equational and expectation lemmas for simple programs.

**Completion criterion**

* evaluation yields a well-defined finite-support distribution, and the semantics supports compositional reasoning (rewrite-based proofs).

**Backtracking indicator**

* examples requiring continuous conditioning (or zero-probability observations) motivate switching from filtering to scoring, or adopting a measure-theoretic carrier (toward Fun proper).

**Relation to Fun**

* this milestone corresponds to a discrete fragment of Fun where measures can be represented intensionally/extentionally by finite support.

---

### Milestone 2 — Strategic choice with explicit information restriction

**Deliverables**

* `View` and `choose` command;
* profile definition mapping each choice point to a distribution over actions given the view-projected environment;
* evaluation under a fixed profile producing a probabilistic object (distribution over outcomes/payoffs).

**Completion criterion**

* for any fixed profile, evaluation is purely probabilistic (“0-player” semantics) and can be treated as a stochastic process.

**Backtracking indicator**

* if strategies require private memory not represented in the visible environment, profiles are extended to be stateful (strategy state threaded through choice), rather than enlarging the program syntax.

---

### Milestone 3 — Behavioral semantics and adequacy

**Deliverables**

* a behavior-tree interpreter that exposes:

  * choice points with available actions,
  * observation failure points,
  * continuation structure;
* a runner that consumes a profile and produces a probabilistic object;
* an adequacy theorem connecting:

  * direct denotational evaluation under a profile, and
  * running the behavior tree under that profile.

**Completion criterion**

* the calculus supports both intensional (interactive) and extensional (distributional) readings, with a proved equivalence.

**Backtracking indicator**

* if the behavior tree becomes an implicit graph IR, it is restricted back to a tree/trace view; graph objects are handled separately.

---

### Milestone 4 — Graph/DAG semantics as an additional interpretation target

This milestone is pursued when a graph representation is needed for solver interoperation or static analyses.

**Deliverables**

* a typed DAG object language with node kinds (chance/decision/deterministic/utility/observation-factor);
* a compilation from a restricted program fragment to this DAG;
* a semantics of the DAG under a fixed profile;
* a preservation theorem: program evaluation equals DAG evaluation for the fragment.

A practical method is to represent DAG well-formedness via *certificates* (e.g., an explicit topological order) to avoid heavy acyclicity proofs.

**Completion criterion**

* the DAG semantics is equivalent to program semantics for the compiled fragment, enabling external algorithms to be justified by the preservation theorem rather than by informal correspondence.

**Backtracking indicator**

* if compilation becomes fragile, the fragment is reduced (no loops, finite branching, stable decision keys), or the DAG object is strengthened with explicit invariants rather than increasing complexity in the core language.

---

## 5. End state (definition of “core complete”)

The core is considered complete when:

1. a strategic probabilistic program with partial information can be expressed;
2. for a fixed profile, evaluation yields a distributional semantics over outcomes/payoffs;
3. at least one alternate semantics (behavior tree and/or DAG) exists;
4. at least one nontrivial adequacy/preservation theorem relates these semantics.

At that point, extensions—richer observations, continuous distributions, commitment schemes, equilibrium refinements—are treated as modular additions (new commands, new carriers, new compilation targets) rather than redesigns of the kernel.

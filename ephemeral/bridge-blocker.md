# Proving that a compiled Bayesian network fold equals a recursive distribution

## Setup (no codebase knowledge needed)

We have two ways to compute a probability distribution over outcomes:

**Way 1 (recursive).** Given a program AST with constructors `sample` (random
draw), `commit` (agent choice), `letExpr`/`reveal` (deterministic bindings),
and `ret` (return), compute `FDist Outcome` by structural recursion:

```
outcomeDist (.sample x D k) env = FDist.bind (D env) (fun v => outcomeDist k (extend env v))
outcomeDist (.commit x σ k) env = FDist.bind (σ env) (fun v => outcomeDist k (extend env v))
outcomeDist (.letExpr x e k) env = outcomeDist k (extend env (eval e env))
outcomeDist (.ret u) env = FDist.pure (payoff u env)
```

**Way 2 (compiled fold).** A compiler traverses the same AST and emits numbered
nodes into a flat array:

- `sample` emits 1 "chance" node (stores the distribution `D`)
- `commit` emits 1 "decision" node (stores the strategy `σ`)
- `letExpr`/`reveal` emit 0 nodes (only bookkeeping)
- `ret` emits `|Players|` "utility" nodes (store payoff functions)

The flat array is then evaluated by a sequential fold (`evalFoldPrefix.go`)
that processes nodes 0, 1, ..., n-1 in order. At each node it draws a value
from the node's distribution and appends it to a growing "prefix assignment."

The theorem to prove: mapping a deterministic extraction function over the
fold's output equals the recursive `outcomeDist`, converted from `FDist` to
`PMF`.

## What works

The proof proceeds by induction on the AST. Two cases are trivial:

- **letExpr / reveal**: no nodes emitted, so the fold is unchanged and
  the extraction function just updates the environment. The IH applies directly.

## What's stuck (3 cases)

### Case `ret`

The compiler emits `|Players|` utility nodes. The fold processes each by
drawing from `PMF.pure ()` (trivial distribution) and extending the prefix.
The extraction function ignores utility positions entirely. So the fold
should be a no-op. But proving this requires an inner induction on the
player list, showing each utility fold step doesn't change the map result.

### Cases `sample` and `commit`

The compiler emits 1 node, then recurses on the continuation `k`. The fold
processes node `k₀` first, then continues with nodes `k₀+1, ..., n-1`. We
need to:

1. **Unfold the fold one step**: show `go k₀ acc = go (k₀+1) (step acc k₀)`.
2. **Match the step's distribution**: the fold draws from the MAID's
   "node distribution" at `k₀`. The compiler stored `D env` (for sample) or
   `σ env` (for commit) in that node. Show these match.
3. **Apply the IH** for the continuation `k` starting at node `k₀+1`.

## The actual blocker: term size

The compiled state `st = compile(p, st₀)` is a structure containing the
flat node array, variable tracking, and proof obligations. It appears in
the type of every object: the fold's structure type, its semantics, the
policy, the extraction function, the natural-order proof, etc.

When Lean's `simp` unfolds `compile(.sample x D k, st₀)` one level, every
occurrence of `st` expands into:

```
compile(k, (st₀.addNode(.chance ...)).addVar(...))
```

which includes the full chance node (with its distribution closure and
normalization proof), the variable entry, and all proof terms. This
expansion happens in ~10 positions simultaneously. The resulting goal term
is thousands of nodes deep, and basic tactics (`rw`, `congr`, `exact`)
exceed the 200k heartbeat limit trying to unify or traverse it.

**Attempted mitigations:**

- **Local abbreviations** (`set st := ...`): Lean's `set` pattern-matches
  syntactically. After `simp` unfolds `compile`, the expanded and
  abbreviated forms differ, so `set` misses occurrences.

- **Abstract parameter** (take `st` as a parameter with
  `hst : st = compile(p, st₀)`): This would keep `st` opaque, but it
  causes Lean typeclass conflicts. The compiled state carries
  `Fintype Player` via `B.fintypePlayer`, and an abstract `st` doesn't
  expose this instance. Also, `subst hst` re-expands everything.

- **Increasing heartbeats**: `maxHeartbeats 400000` isn't enough; the
  terms are structurally too large for unification.

## What would actually solve it

The cleanest path is probably to prove 3-5 small lemmas about
how the fold interacts with `addNode` / `addUtilityNodes`, stated with
the compiled state already abstracted (e.g., as a `Fin n → NodeDesc` array
rather than the full compiler output). Then the main induction cases become
short applications of these lemmas without ever expanding `compile`.

Alternatively, a different proof architecture: instead of decomposing the
PMF-level prefix fold step by step, work at the `FDist` level (which has
simpler types and avoids the `tsum`/`ENNReal` pain of `PMF`), or prove the
correspondence via the Bayesian network factorization formula (product of
conditionals) rather than the sequential fold.

# Vegas/LetProb -- Probabilistic Layer

This module adds probabilistic computation to the core calculus: weighted distributions, sampling, conditioning, and a bridge to Mathlib's measure theory. Programs in this layer can sample from finite-support distributions and condition on boolean observations, producing unnormalized weighted outcomes.

## Design Overview

The central data structure is `WDist alpha`, a weighted distribution represented as a list of `(value, NNReal)` pairs. This is a purely computational object -- no measure-theory imports are needed to define or compute with it. The key monad operations (`pure`, `bind`, `zero`) are computable, and the `Monad` instance is provided.

Separately, `WDist.toMeasure` lifts a `WDist` into Mathlib's `Measure` type, and a suite of bridge theorems (in `WDistLemmas.lean`) proves that the computational monad operations faithfully implement the corresponding measure-theoretic combinators. This separation lets the evaluator remain computable while still connecting to the rich Mathlib measure theory library for proofs.

Conditioning uses **unnormalized hard rejection**: `observe cond` filters out execution paths where `cond` is false by zeroing their mass. Normalization to a probability measure is performed explicitly and externally via `WDist.toProbabilityMeasure`, which requires a proof that mass is nonzero.

## Key Types

**`WDist alpha`** -- Weighted distribution (finite support). Weights are `NNReal` (non-negative reals). Operations: `pure`, `bind`, `zero` (failure/rejection), `map`, `observe` (filtering), `mass`, `normalize?`, `uniform`, `scale`.

**`Prob.Kernel Gamma tau`** -- A stochastic kernel: `L.Env Gamma -> WDist (L.Val tau)`. Kernels may depend on the full runtime environment.

**`Prob.PProg Gamma tau`** -- Probabilistic programs: `Prog` instantiated with `CmdBindP` (sampling from a kernel) and `CmdStmtP` (observe). Evaluated by `evalP` into `WDist`.

**`Prob.EffWDist`** -- The `Eff` instance for `WDist`: `pure = WDist.pure`, `bind = WDist.bind`, `fail = WDist.zero`.

**`WDist.EV`** -- Expected value of a real-valued function under a weighted distribution. `EV d f = sum over (a, w) in d.weights of w * f(a)`.

**`WDist.EV_cond`** -- Conditional expected value: `EV / mass`, or 0 when mass is 0.

**`Prob.MeasEq`** (notation `~=_m`) -- Measure-level equivalence of two `WDist`s: they denote the same `Measure`.

**`Prob.ProgEq`** (notation `~=`) -- Observational equivalence of two `PProg`s: they produce measure-equivalent distributions in all environments.

**`Prob.MT Gamma tau`** -- Measure transformer type: `L.Env Gamma -> Measure (L.Val tau)`. Used in the alternative denotational semantics.

## Key Results

- **Monad laws** for `WDist`: `bind_pure_left`, `bind_pure_right`, `bind_assoc`, plus zero laws.
- **Mass properties**: `mass_pure = 1`, `mass_zero = 0`, `mass_bind` (closed form), `mass_bind_const` (multiplicativity when continuation has constant mass).
- **Measure bridge**: `toMeasure_bind` (the core bridge theorem showing `bind` denotes discrete integration), `observe_eq_restrict`, `mass_eq_toMeasure_univ`, `toMeasure_scale`.
- **`EV_bind`** (tower property): `EV (bind d g) f = EV d (fun a => EV (g a) f)`.
- **`evalP_eq_denote`**: the compositional evaluator `evalP` agrees with the measure-transformer denotation `denote`.
- **Program equivalence laws**: `ProgEq.refl`, `.symm`, `.trans`, congruence for all constructors, algebraic laws (sample from Dirac = letDet, observe fusion, observe true = id, observe false = zero).
- **Conservation**: `embedDProg` embeds deterministic programs into probabilistic ones, and `evalP_embed_eq_lift` shows the semantics agrees.
- **Posterior**: `posterior` normalizes the output distribution to a `ProbabilityMeasure`, with `posterior_apply` giving the explicit formula.

## What Is Not Modeled

- No continuous distributions; all distributions have finite list support.
- No soft conditioning or likelihood weighting; only hard boolean rejection.
- No explicit model of randomness provenance (public vs. private entropy).
- No sampling from parametric families (Gaussian, Poisson, etc.); kernels are arbitrary Lean functions.
- No small-step or trace semantics at this layer.

## Design Decisions

- **`NNReal` weights** rather than `Real`: ensures non-negativity by construction, avoiding a class of proof obligations.
- **Unnormalized semantics**: `observe` reduces mass rather than renormalizing. This is the standard approach in probabilistic programming (Borgstrom et al., 2013) and avoids division-by-zero issues until the final normalization step.
- **List representation**: `WDist` uses `List (alpha x NNReal)` rather than `Finsupp` or `Multiset`. This is intentionally intensional (list order and duplicates are visible). The `ProgEq` / `MeasEq` layer provides the extensional quotient.

## Further Reading

- Borgstrom, Gordon, Greenberg, Margetson, Van Gael. "Measure Transformer Semantics for Bayesian Machine Learning" (LMCS 9(3:11), 2013) -- the measure transformer framework that this layer implements in the discrete setting.
- Staton. "Commutative Semantics for Probabilistic Programming" (ESOP 2017) -- categorical foundations for probabilistic programming semantics.

## File Listing

| File | Description |
|------|-------------|
| `WDist.lean` | `WDist` definition, monad operations, `toMeasure`, `toProbabilityMeasure`, `observe_eq_restrict` |
| `WDistLemmas.lean` | Monad laws, mass properties, measure bridge theorems (`toMeasure_bind`, scaling, normalization) |
| `Prob.lean` | `PProg` (probabilistic programs), `CmdBindP`, `evalP`, `ProbSem`, design notes |
| `ProbLemmas.lean` | Simp lemmas for `evalP`, observe fusion, conservation (embed deterministic), Kleisli/bind, measure-theoretic interpretation, posterior |
| `EquivLaws.lean` | `MeasEq`, `ProgEq`, equivalence structure (refl/symm/trans), congruence, algebraic laws |
| `MeasureTransformer.lean` | Alternative `MT` denotation, `denote`, `evalP_eq_denote` correctness theorem |
| `ConditionalEU.lean` | `WDist.EV`, `WDist.EV_cond`, `EV_bind` tower property |

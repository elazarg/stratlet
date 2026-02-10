# Vegas/LetProtocol -- Protocol and Strategic Calculi

This module is the strategic heart of the project. It defines several variants of a "protocol-with-yields" calculus: programs where execution can yield to external agents (players) who make strategic choices, and to nature which samples from distributions. Each yield site carries a **View** that restricts what information is available at that point.

## Design Overview

The central type is `ProtoProg` (in `Proto.lean`), which extends the generic `Prog` calculus with two bind-commands: `sample` (chance/nature node) and `choose` (player decision node). Both carry a stable `YieldId`, a `View` (observable projection of the environment), and the relevant payload (kernel for sample, action set for choose).

A `Profile` (total strategy) resolves every `choose` site to a `WDist` over actions. Fixing a profile converts a `ProtoProg` into a purely probabilistic computation evaluated into `WDist`. A `PProfile` (partial profile) resolves only some sites; `applyProfile` is a syntax-to-syntax pass that discharges resolved sites.

The module provides five variant calculi, each emphasizing different aspects:

1. **Proto** (`Proto.lean`) -- The milestone/flagship calculus with yield IDs, Views, Profiles, Nash equilibrium, and game structure (`Game`).
2. **FullInfo** (`FullInfo.lean`) -- A simpler variant without Views: choices depend on the full environment. Includes a behavioral interpreter (`Beh`) and an operational semantics via `Arena`.
3. **PartialInfo** (`PartialInfo.lean`) -- Specialized to `BasicLang` with Views plus commit/reveal protocol commands (placeholder, not cryptographic).
4. **Dag** (`Dag.lean`) -- A DAG-style variant with Views but without yield IDs or game-theoretic structure.
5. **ParentView** (`ParentView.lean`) -- MAID-compatible variant where Views are specified via parent yield IDs rather than arbitrary projection functions.

## Key Types

**`View Gamma`** -- An observable slice of the environment: a visible sub-context `Delta` and a projection `L.Env Gamma -> L.Env Delta`. This is the mechanism for partial information.

**`ProtoProg Gamma tau`** -- Protocol programs. Constructors: `ret`, `letDet`, `observe`, `sample` (chance yield), `choose` (decision yield).

**`Profile`** -- Total strategy: maps `(player, yield_id, view, action_set)` to a kernel `L.Env Delta -> WDist (L.Val tau)`.

**`PProfile`** -- Partial strategy: `choose?` returns `Option`, allowing some decision sites to remain unresolved.

**`Game Gamma`** -- A thin wrapper: protocol program + utility function on terminal values.

**`Deviator who`** -- A replacement strategy for a single player. `Profile.applyDev` patches a profile with a deviator.

**`YieldId`** (= `Nat`) -- Stable identifier for yield sites, assigned by the encoder.

**`ParentProtoProg`** -- Variant syntax where Views are specified via `ParentSite` (a list of parent yield IDs + `VarSpec` for the projection). Embeds into `ProtoProg` via `embed`.

**`VarSpec Gamma Delta`** -- Witnesses that `Delta` is a sub-context of `Gamma` by providing de Bruijn variables for each position.

## Key Results

- **Simp lemmas** for `evalProto`: definitional reductions for `ret`, `letDet`, `observe`, `sample_bind`, `choose_bind`.
- **Profile irrelevance** (`evalProto_profile_indep`): programs with no `choose` nodes evaluate identically under any profile.
- **Observe fusion** inherited from the probabilistic layer.
- **Semantic compatibility** (`evalProto_applyProfile_of_extends`): if a total profile extends a partial one, evaluating after `applyProfile` is the same as evaluating directly.
- **Bridge to Prob** (`evalProto_eq_evalP_toProbNoChoose`): for `NoChoose` programs, the protocol evaluator agrees with the probabilistic evaluator.
- **Compilation correctness** in FullInfo, PartialInfo, and Dag: `evalS_eq_evalP_toProb`, `evalD_eq_evalP_toProb`.
- **Behavioral soundness**: `runBeh_behEval_eq_evalS` (FullInfo, PartialInfo).
- **Operational adequacy**: `evalS_ofArena_eq_evalOp` (FullInfo).
- **EU/Nash**: `EU_dist`, `EU_cond`, `IsNash_WF`, conditional EU equivalence.
- **ParentView embedding**: `embed_isParentDerived`, `noChoose_iff_embed`, round-trip theorem.
- **Local information**: `handleBind_depends_only_on_view` -- yields are view-parametric.
- **Deviator identity**: `Deviator_id` -- deviating with one's own strategy is an identity.

## What Is Not Modeled

- No perfect recall enforcement (responsibility of the encoder via Views).
- No explicit information sets or belief structures; only observable projections.
- No commutativity/commutation quotient on yield sites.
- No cryptographic commitment scheme; commit/reveal in `PartialInfo` is a deterministic placeholder.
- No reachability-from-semantics; `ReachSpec` is threaded parametrically (default: all reachable).
- No subgame perfection or sequential equilibrium; only Nash (no-profitable-deviation).
- No mixed strategy equilibrium existence proofs.
- No measure-theoretic EU at this layer (discrete sums only).

## Design Decisions

- **Yield IDs** are assigned by the encoder (external), not generated internally. This allows stable references across rewrites and compilations.
- **Views are projections, not masks**: a `View` is any function `Env Gamma -> Env Delta`, not necessarily a variable subset. The `ParentView` variant restricts to variable-based projections for MAID compatibility.
- **Profiles are behavioral**: they map `(player, id, view, actions, visible_env)` to distributions. This is history-dependent by construction (the environment encodes history).
- **Separation of syntax and semantics**: `applyProfile` is a syntax-to-syntax transformation; compilation to `Prob` (`toProbNoChoose` / `toProb?`) is separate.

## Further Reading

- Koller, Milch. "Multi-Agent Influence Diagrams for Representing and Solving Games" (GEB 2003) -- MAIDs and the parent-set specification style.
- Kuhn, H.W. "Extensive Games and the Problem of Information" (1953) -- information sets and behavioral strategies.
- Shoham, Leyton-Brown. "Multiagent Systems" (2009) -- textbook treatment of extensive-form games, Nash equilibrium, and game representations.

## File Listing

| File | Description |
|------|-------------|
| `Proto.lean` | Core protocol calculus: `ProtoProg`, `View`, `Profile`, `PProfile`, `applyProfile`, `evalProto`, `Game`, `EU`, `IsNash_WF`, `Deviator` |
| `ProtoLemmas.lean` | Simp lemmas for `evalProto`, profile irrelevance, observe fusion, `applyProfile` structural facts, semantic compatibility, bridge to Prob, WF/legality lemmas |
| `ProtoCondEU.lean` | Conditional EU (`EU_cond`, `EU_Cond`), `IsNash_Cond`, equivalence under WF chance conditions |
| `ProtoGameLemmas.lean` | `EU_dist_pure`, `EU_dist_zero`, `EU_profile_indep_NoChoose`, `Deviator_id` |
| `FullInfo.lean` | Full-information variant: `SProg`, `Profile`, `toProb`, `evalS`, behavioral interpreter (`Beh`, `behEval`, `runBeh`), operational semantics (`Arena`, `evalOp`), bridge theorems |
| `FullInfoLemmas.lean` | Extensional properties: profile independence, observe fusion, choose from singleton/empty, behavioral soundness, operational determinism, player irrelevance |
| `PartialInfo.lean` | Partial-info variant (BasicLang): `View`, `SProg` with choose/commit/reveal, `Profile`, `toProb`, `evalS`, behavioral interpreter, `commitTag` |
| `PartialInfoLemmas.lean` | Commit-reveal coherence, reveal mismatch failure, view projection properties, profile independence, observe fusion |
| `Dag.lean` | DAG-style variant: `View`, `DagProg`, `Profile`, `evalD`, `toProb`, bridge theorem |
| `DagLemmas.lean` | Profile independence, observe fusion for `DagProg` |
| `ParentView.lean` | `ParentSpec`, `VarSpec`, `ParentSite`, `ParentProtoProg`, `embed`, `IsParentDerived`, embedding theorems |
| `ParentViewLemmas.lean` | Local information lemmas (C2), compilation bridge (C3), round-trip translation (C4) |
| `ParentViewExample.lean` | Sequential game example comparing `ParentProtoProg` with raw `ProtoProg` |
| `Step.lean` | `ProtoHandler` callback interface, `stepProto` IO evaluator for interactive execution |
| `Examples/` | Worked examples (see `Examples/README.md`) |

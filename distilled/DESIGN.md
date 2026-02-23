# Vegas: A Game Calculus — Design Document

## Overview

Vegas is a typed let-calculus for specifying multiagent strategic interactions.
A Vegas program is a complete game definition: players, actions, information,
payoffs — one artifact. Analysis (Nash equilibrium, dominance, etc.) is applied
externally to the expected-utility function the program induces.

---

## 1. Base Language

**Base types.**
```
BaseTy ::= int | bool
```

**Values.** `Val : BaseTy → Type` — `int` maps to integers, `bool` to booleans.

**Visibility.** Each binding is tagged with who can see it:
```
Vis ::= pub           -- visible to all players (and to expressions)
       | priv Player   -- visible only to this player
```

Every non-public binding has an owner. Only the owner can reveal it.

**General possibility.** In principle, `Vis` could be any predicate
`Player → Prop` (equivalently, a subset of players). The two constructors
above are the extreme points: `priv p` = singleton {p}, `pub` = universal.
Intermediate cases (e.g., "visible to a coalition") are type-theoretically
valid but require additional program instructions (directed disclosure) and
are not supported in this version of the calculus.

In the two-player case, this recovers classical **polarity**: `priv 0` and
`priv 1` are the two "negative" polarities, `pub` is "positive."

**Note on exogenous randomness.** A third visibility `hidden` (visible to
nobody, no owner) could model truly exogenous protocol-internal randomness
(e.g., a random oracle) that is never owned or revealed by any player.
This sits outside the commit/reveal protocol: a `hidden` value cannot be
`reveal`ed (no owner to authorize it) and would require a separate
`publish` instruction. We omit it from the core calculus.

**Typed bindings.** `Ty = BaseTy × Vis`.

**Variable identifiers.** `VarId` is an abstract type with decidable equality
(e.g., `Nat`). Variables are referenced by name, not by position.

**Contexts.** A context `Γ : VarId →_fin Ty` is a finite map from variable
identifiers to typed bindings. The domain `dom(Γ)` is the set of variables
in scope. We write `Γ, x : τ` for the map extension `Γ[x ↦ τ]`, defined
only when `x ∉ dom(Γ)`. The empty context is `∅`.

**SSA discipline.** Every binder (`letExpr`, `sample`, `commit`, `reveal`)
introduces a fresh `VarId` not already in `dom(Γ)`. Each variable is bound
exactly once. This makes contexts insensitive to binder ordering: the map
`{a : τ₁, b : τ₂}` is the same regardless of which binding was introduced
first. Independent binders commute without changing the continuation's type,
avoiding the transport lemmas that arise with positional (De Bruijn) indices.

**Environments.** `Env Γ` assigns a value `Val b` to each variable `x` in
`dom(Γ)` where `Γ(x) = ⟨b, vis⟩`. At runtime, all bindings hold real
values — the visibility discipline is enforced statically, not by erasure.
We write `env(x)` for lookup and `env[x ↦ v]` for extension.

**Variables.** A variable reference is a name `x` with `x ∈ dom(Γ)` and
`Γ(x) = τ`. We write `x : τ ∈ Γ` for this.

**Public variables.** `PubVar Γ b` = a variable `x` with `Γ(x) = ⟨b, pub⟩`.
Expressions can only reference public variables. Since `⟨b, pub⟩ ≠ ⟨b, priv p⟩`,
the type system prevents expressions from reading non-public bindings.

**Expressions.**
```
Expr Γ b ::=
  | var (x : PubVar Γ b)
  | constInt i | constBool b
  | addInt l r | eqInt l r | eqBool l r
  | andBool l r | notBool e
  | ite cond t f
```
Only public variables are accessible. `evalExpr : Expr Γ b → Env Γ → Val b`.

---

## 2. Views and Projections

**Membership.** A player `p` can see a binding with visibility `vis` iff:
```
canSee : Player → Vis → Bool
canSee _ pub       = true
canSee p (priv q)  = (p == q)
```

**Player view.** The sub-context visible to player `p`:
```
viewCtx : Player → Ctx → Ctx
viewCtx p Γ = { x : τ ∈ Γ | canSee p τ.vis }
```

This is the restriction of `Γ` to bindings whose visibility allows `p` to
see them. It includes all `pub` bindings and all `priv p` bindings — the
player sees public information plus their own private state. It excludes
other players' private bindings.

**Public view.** The sub-context visible to everyone:
```
pubCtx : Ctx → Ctx
pubCtx Γ = { x : τ ∈ Γ | τ.vis = pub }
```

Note: `pubCtx Γ ⊆ viewCtx p Γ` for all players `p`.

**Projections.** Since views are sub-contexts (submaps), projections are
map restrictions:
```
toView (p : Player) : Env Γ → Env (viewCtx p Γ)
toPub              : Env Γ → Env (pubCtx Γ)
```

These drop bindings invisible to the target, preserving the values of
visible bindings unchanged.

**Perfect recall.** A player's view includes their own past private bindings
by construction. If player `p` committed at some earlier program point, that
binding has visibility `priv p` and appears in `viewCtx p Γ`. No special
mechanism is needed — it follows from `canSee p (priv p) = true`.

---

## 3. Weighted Distributions

```
WDist α = { weights : List (α × Rat) }
```

Standard operations: `pure`, `zero`, `bind`, `map`, `scale`, `append`.
This is the semantic domain for probabilistic evaluation.

---

## 4. Kernels, Samplers, and Action Sets

**Sampler.** Who controls the random draw:
```
Sampler ::= Nature | Player Player
```

- `Nature` — exogenous randomness (coin flip, card shuffle, weather).
  Nature's kernel depends only on public state.
- `Player p` — player `p`'s private randomness (e.g., a private dice roll
  whose outcome only `p` sees). The kernel depends on `p`'s view.

This distinction matters for kernel dependencies: Nature cannot peek at
anyone's private state, while a player's private roll may depend on what
that player already knows.

**Sample kernel.** The type depends on the sampler:
```
SampleKernel (s : Sampler) Γ b =
  match s with
  | Nature   => Env (pubCtx Γ)      → WDist (Val b)
  | Player p => Env (viewCtx p Γ)   → WDist (Val b)
```
- For `Nature` samples (pub or priv): depends on `pubCtx Γ` only.
  Nature sees public state, not any player's private state.
- For `Player p` samples: depends on `viewCtx p Γ` (player `p`'s
  view, including own past private state).

**Action set.** What a player may commit to, given their view:
```
ActSet (who : Player) Γ b = Env (viewCtx who Γ) → List (Val b)
```

---

## 5. Assert (Deferred Predicate)

```
Assert (who : Player) Γ = Env (viewCtx who Γ) → Bool
```

An assert is a predicate over the asserting player's **view** — public state
plus their own private state. The type prevents an assert from inspecting
other players' private bindings: if `who` cannot see a binding, it does not
appear in `viewCtx who Γ` and therefore cannot be referenced.

This is the capture mechanism: an assert closes over the player's private
variables (visible via `canSee who (priv who) = true`) and public state.
It can express "my committed value satisfies property P given what I
publicly observe" but not "the other player committed X."

**Freeze-at-assert.** The assert type is indexed by `Γ` at the program point
where the `assert` instruction appears. Since every binder introduces a
*new* variable (SSA), later extensions to the context do not alter the
bindings visible at the assert point. The assert captures the player's view
at that moment — "capture by value." Even if a later `reveal` makes some
value public, the assert's input is fixed to the view at assertion time.
Denotationally, this is a consequence of the type; operationally, the
restricted environment `toView who env` is evaluated and frozen at the
assert point.

Semantically, `assert who P; k` evaluates `P (toView who env)` and
zero-weights if false. Operationally, enforcement may be deferred to reveal
time — the denotation is the same because values don't change between commit
and reveal (SSA).

**Tighter variant (not in core).** For ZK-style "I prove my commit satisfies
a property w.r.t. public state":
```
AssertOn (who : Player) (x : VarId) [Γ(x) = ⟨b, priv who⟩] =
  Env (pubCtx Γ) → Val b → Bool
```
This restricts the predicate to public state plus a single secret. The
owner-indexed `Assert who Γ` subsumes this.

---

## 6. The Program Type

Every binder introduces a fresh variable name; the SSA invariant
(`x ∉ dom Γ`) is left implicit below. Side-conditions on existing
variables are written in brackets.

```
Prog Γ b ::=
  | ret     (e : Expr Γ b)
  | letExpr (x : VarId) (e : Expr Γ b')
            (k : Prog (Γ, x : ⟨b',pub⟩) b)
  | sample  (x : VarId) (id : ChannelId) (vis : Vis) (s : Sampler)
            (K : SampleKernel s Γ b')
            (k : Prog (Γ, x : ⟨b',vis⟩) b)
  | commit  (x : VarId) (id : ChannelId) (who : Player)
            (A : ActSet who Γ b')
            (k : Prog (Γ, x : ⟨b',priv who⟩) b)
  | reveal  (y : VarId) (who : Player) (x : VarId) [Γ(x) = ⟨b',priv who⟩]
            (k : Prog (Γ, y : ⟨b',pub⟩) b)
  | assert  (who : Player) (P : Assert who Γ)
            (k : Prog Γ b)
  | observe (c : Expr Γ bool)
            (k : Prog Γ b)
  | withdraw (payoff : Player → Expr Γ int)
```

Binder variables: `letExpr`, `sample`, and `commit` bind `x`; `reveal`
binds `y` (the fresh public alias) while referencing `x` (the existing
private binding). `assert` and `observe` do not bind.

### Key design points

**Commit and sample are dual binders.** Both introduce a value that is not
(yet) public. The difference is who controls the distribution:

| Binder | Controller | Visibility of binding |
|---|---|---|
| `letExpr x e k` | Determined (expression) | `pub` |
| `sample x id pub Nature K k` | Nature (kernel, pub-dependent) | `pub` |
| `sample x id (priv p) Nature K k` | Nature (kernel, pub-dependent) | `priv p` |
| `sample x id (priv p) (Player p) K k` | Player `p`'s private roll (view-dependent) | `priv p` |
| `commit x id who A k` | Player `who` (strategy) | `priv who` |

Under profile application, a `commit` is rewritten to a `sample` with the
same visibility (`priv who`) — the continuation is unchanged.

**Reveal is owner-restricted.** `reveal y who x` takes a `priv who` variable
`x` and binds a fresh public copy `y` of its value. Only the owner can
reveal: the side-condition `Γ(x) = ⟨b', priv who⟩` requires the variable to
point to a binding owned by `who`. This is enforced by typing — if you can't
name the owner and point to their private binding, you can't form the
`reveal` term.

Operationally, this matches commit/reveal protocols: only the committer can
open their commitment (by publishing the preimage). The protocol designer
places `reveal` instructions, but the type discipline ensures each reveal
names the correct owner.

**Reveal is protocol-forced, not strategic.** The `reveal` instruction is
placed by the protocol designer — it is not a move available to the player.
Once the program reaches a `reveal`, the owner's value is published
unconditionally. Refusal-to-reveal, timeouts, and griefing are not modeled
in this version of the calculus. See §16 (External Assumptions) for the
corresponding liveness assumption.

**Reveal does not distinguish commit from sample.** A `priv p` binding might
come from a `commit` (player `p` chose the value) or a `sample (priv p)`
(nature drew a value visible only to `p`, e.g., a dealt card). In either
case, player `p` is the owner and can reveal it. Before reveal, the value
exists but is not universally readable. After reveal, it is public.

**letExpr binds public.** A `letExpr` evaluates a (necessarily public)
expression and binds the result at public visibility. `sample x id pub K k`
is the probabilistic analogue: a public random draw, immediately visible.

**Expressions access only public variables.** `PubVar Γ b` requires
`Γ(x) = ⟨b, pub⟩`. Expressions appear in `observe`, `letExpr`, and
`withdraw`, which are protocol-level (not player-level) constructs.

**observe vs assert.** `observe` conditions on public data (an expression)
and is checked immediately. `assert who P` conditions on player `who`'s view
(public + own private) and is conceptually deferred to reveal, though
denotationally it checks immediately because the value is already determined.
The key difference: `observe` takes an `Expr` (pub-only), while `assert`
takes a view-indexed predicate (pub + owner's private).

---

## 7. Strategies and Profiles

**Profile** (total):
```
Profile = {
  commit : ∀ Γ b, (who : Player) → ChannelId → ActSet who Γ b →
           Env (viewCtx who Γ) → WDist (Val b)
}
```

A profile resolves every commit site. The strategy function receives the
player's view: public state plus their own past private commitments. It cannot
depend on other players' private state. This is a **definition**, not a theorem.

**PProfile** (partial):
```
PProfile = {
  commit? : ∀ Γ b, (who : Player) → ChannelId → ActSet who Γ b →
            Option (Env (viewCtx who Γ) → WDist (Val b))
}
```

`PProfile.Complete π` asserts all sites are resolved (`isSome` everywhere).

---

## 8. Denotational Semantics

```
eval (σ : Profile) (who : Player) : Prog Γ int → Env Γ → WDist Int
```

| Constructor | Semantics |
|---|---|
| `ret e` | `pure (evalExpr e env)` |
| `letExpr x e k` | `eval σ who k (env[x ↦ evalExpr e env])` |
| `sample x id vis s K k` | `bind (K (projectSampler s env)) (λ v. eval σ who k (env[x ↦ v]))` |
| `commit x id p A k` | `bind (σ.commit p id A (toView p env)) (λ v. eval σ who k (env[x ↦ v]))` |
| `reveal y who' x k` | `eval σ who k (env[y ↦ env(x)])` |
| `assert p P k` | `if P (toView p env) then eval σ who k env else zero` |
| `observe c k` | `if evalExpr c env then eval σ who k env else zero` |
| `withdraw payoff` | `pure (evalExpr (payoff who) env)` |

`projectSampler` selects the right projection:
```
projectSampler : Sampler → Env Γ → ...
projectSampler Nature     env = toPub env
projectSampler (Player p) env = toView p env
```

**No commitment store needed.** Reveal reads the value directly from the
environment (the private binding). The value already exists in the full
store `Env Γ`; reveal monotonically expands what is publicly readable by
adding a `pub` binding `y` holding the same value as the private binding
`x`. Operationally this may be implemented as a state mutation (publishing
on-chain); denotationally it is a monotone knowledge update: public
knowledge only grows, never shrinks.

**The `who` parameter** threads through to `withdraw`, where it selects
the player's payoff expression. All other cases just recurse.

---

## 9. Expected Utility

```
EU (p : Prog Γ int) (σ : Profile) (env : Env Γ) (who : Player) : Rat =
  let d := eval σ who p env
  sum over (v, w) ∈ d.weights of w * v
```

---

## 10. Profile Application

```
applyPProfile (π : PProfile) : Prog Γ b → Prog Γ b

  commit x id who A k =>
    match π.commit? who id A with
    | some Kdec => sample x id (priv who) (Player who) Kdec (applyPProfile π k)
    | none      => commit x id who A (applyPProfile π k)
  sample x id vis s K k => sample x id vis s K (applyPProfile π k)
  reveal y who x k      => reveal y who x (applyPProfile π k)
  (all others recurse structurally)
```

**No visibility shift.** Because `commit x id who` binds `Γ, x : ⟨b', priv who⟩`
and the resolved `sample x id (priv who)` binds the same, the continuation `k`
has identical type before and after resolution. A decision node becomes a chance
node at the same program position, with the same continuation and the same
visibility.

The resolved kernel `Kdec : SampleKernel (Player who) Γ b'` has type
`Env (viewCtx who Γ) → WDist (Val b')` — exactly the profile's strategy
type. No wrapping or coercion needed.

---

## 11. Reductions

| What's fixed | Result | Character |
|---|---|---|
| Full mixed profile | Probabilistic program — all commits become samples | No decisions remain |
| Full pure profile | Deterministic program — all samples are point masses | Just reduce |
| All-but-one mixed | MDP — one player's commits are decisions, rest is stochastic | Single-agent optimization |
| All-but-one pure | Let-calculus with holes — deterministic except one player's commits | Function from choices to payoffs |

After full profile application, the program has no `commit` nodes. Reveals
are still present (promoting `priv who` to `pub`), and semantically valid.
A further optimization pass can inline reveals when the corresponding sample
result is used only once.

---

## 12. Information Structure

Information partitions are derived from visibility tags and program order:

- At any program point, each binding in `Γ` has a visibility `vis ∈ {pub, priv p}`.
- Player `p`'s view is `viewCtx p Γ` = all `pub` bindings + all `priv p` bindings.
- A player's strategy at a commit site depends on their view. By construction,
  this includes their own past private commitments (**perfect recall**) but
  excludes other players' private bindings.
- Sampling kernels depend on the **sampler**, not the visibility:
  `Nature` kernels depend on `pubCtx Γ`; `Player p` kernels depend
  on `viewCtx p Γ`.
- Expressions can only access `pub` bindings.

**Perfect recall** is structural, not an external assumption. When player `p`
commits at channel 0 (binding `a : ⟨b, priv p⟩`) and later commits at
channel 1, their strategy at channel 1 receives `viewCtx p Γ` which includes
the `priv p` binding `a`. The player sees their own past choices because
`canSee p (priv p) = true`.

**Reordering insensitivity.** Because contexts are finite maps (unordered),
permuting two independent binders yields the same context and therefore
the same continuation type. Two binders are independent when neither's
inputs (views) reference the other's output (variable). This holds
automatically for commits by different players, since `canSee q (priv p) = false`
when `p ≠ q`. The calculus does not impose a commutation equivalence — it
simply ensures that independent binders do not produce spurious type
distinctions.

---

## 13. EFG Compilation

```
toEFG : Prog Γ b → Env Γ → GameTree Player

  commit x id who A k  =>
    decision id who (A (toView who env) |>.map (λ a. toEFG k (env[x ↦ a])))
  sample x id vis s K k =>
    chance (K (projectSampler s env) |>.weights.map (λ (v,w). (toEFG k (env[x ↦ v]), w)))
  reveal y who x k     => toEFG k (env[y ↦ env(x)])        -- transparent
  observe c k          => if evalExpr c env then toEFG k env else terminal(0)
  assert p P k         => if P (toView p env) then toEFG k env else terminal(0)
  withdraw payoff      => terminal (λ who. evalExpr (payoff who) env)
  letExpr x e k        => toEFG k (env[x ↦ evalExpr e env])  -- transparent
  ret e                => terminal (λ _. 0)                    -- non-game terminal
```

**Correctness target.** For a well-formed program `p`, profile `σ`, and the
behavioral strategy `β` on `toEFG p env` induced by `σ`:
```
EU p σ env who  =  euBehavioral β who (toEFG p env)
```

---

## 14. Deviation and Nash Equilibrium

**Deviator.** For player `who`, an alternative commit strategy:
```
Deviator who = {
  commit : ∀ Γ b, ChannelId → ActSet who Γ b →
           Env (viewCtx who Γ) → WDist (Val b)
}
```

**Profile deviation.** `σ.deviate δ` patches player `who`'s strategy, leaves
others unchanged.

**Nash equilibrium.** A profile `σ` is Nash for program `p` at environment
`env` if:
```
∀ who, ∀ δ : Deviator who,
  EU p σ env who ≥ EU p (σ.deviate δ) env who
```

---

## 15. Well-Formedness

**Legality.** A profile is legal at a commit site if the strategy's support is
contained in the action set:
```
LegalAt σ who id A obs =
  ∀ v w, (v, w) ∈ (σ.commit who id A obs).weights → w ≠ 0 → v ∈ A obs
```

**Channel consistency.** Each `reveal y who x k` references a variable `x`
that was bound by some `commit` or `sample (priv who)` earlier in the
program. The SSA discipline enforces this: `x` must be in `dom(Γ)` with
`Γ(x) = ⟨b', priv who⟩`.

**Sampler–visibility coherence.** For `sample x id vis s K k`:
- If `s = Nature`, any `vis` is allowed (`pub` or `priv p`).
- If `s = Player p`, then `vis = priv p` (the roller's own private slot).

This prevents nonsensical terms like `sample x id (priv q) (Player p) ...`
with `p ≠ q` (player `p` generating randomness private to `q`) or
`sample x id pub (Player p) ...` (player-controlled "public" randomness,
which is operationally a commit). In the Lean formalization this can be
enforced as a typing side-condition on the `sample` constructor or as a
separate `WFProg` predicate.

---

## 16. External Assumptions and Design Guarantees

**External assumptions** — preconditions on the mapping to real-world
protocols, not properties proved by the semantics:

1. **Binding and hiding.** Commitments cannot be changed after posting, and
   committed values cannot be inferred from the commitment. (Cryptographic.)
2. **No private channels.** Players cannot communicate outside the protocol.
   (Modeling scope.)
3. **Liveness / compliance.** Every player executes their `reveal`
   instructions when the protocol reaches them. Refusal-to-reveal,
   timeouts, and griefing are not modeled. (Enforcement mechanism —
   e.g., slashing, timeout defaults — is external to the calculus.)

**Structural guarantees** — properties that hold by construction, not by
assumption:

4. **Perfect recall.** Each player remembers all their past observations.
   Follows from `canSee p (priv p) = true`: a player's view always
   includes their own past private bindings. See §12.
5. **Assert isolation.** An assert can only inspect the asserting player's
   view. Follows from the type `Assert who Γ = Env (viewCtx who Γ) → Bool`.
6. **Freeze-at-assert.** An assert's input is fixed to the player's view
   at the assertion point. Follows from SSA: later binders extend the
   context but never reassign existing bindings.

---

## 17. Operational Interpretation

| Calculus construct | Blockchain / protocol analogue |
|---|---|
| `commit x id who A k` | Post a commitment (hash of chosen value) |
| `sample x id pub Nature K k` | Public random beacon (VRF, visible immediately) |
| `sample x id (priv p) Nature K k` | Nature deals to `p` (e.g., card from shuffled deck; kernel depends on public state only) |
| `sample x id (priv p) (Player p) K k` | Player `p` rolls private dice (kernel may depend on `p`'s view) |
| `reveal y who x k` | Owner opens commitment / shows card (publish to all) |
| `assert who P k` | Check at reveal time (or via ZK proof at commit); `P` sees only `who`'s view |
| `observe c k` | On-chain conditional (revert if false) |
| `withdraw payoff` | Payout / settlement |

Non-public sampling may be implemented lazily (at reveal rather than at
sample) because non-public bindings cannot influence expressions or other
players' strategies. The denotational equivalence is immediate.

---

## 18. Relationship to Vegas/ Exploration

| Distilled | Vegas/ | Notes |
|---|---|---|
| `commit` | `Proto.choose` | Replaces abstract decision with commit channel |
| `sample vis` | `Proto.sample` | Now parameterized by visibility; needs explicit reveal if non-public |
| `reveal y who x` | (none) | New: owner-restricted phase boundary |
| `assert` | `SupportedOn` / `observe` | Unifies legality and deferred conditioning; view-indexed |
| `withdraw` | `emit` + `ret` | Collapsed to single terminal payoff |
| `viewCtx` / `pubCtx` | `View Γ` | Map restriction, not list filtering |
| `Profile.commit` | `Proto.Profile.choose` | Depends on player's view (Env of restricted ctx) |
| `applyPProfile` | `Proto.applyProfile` | Same, no visibility shift needed |
| SSA named vars | De Bruijn indices | Reordering-insensitive contexts; no transport lemmas |

---

## 19. Example: Matching Pennies

```
matchingPennies : Prog ∅ int :=
  commit a 0 player0 {true,false}             -- P0 commits
    commit b 1 player1 {true,false}           -- P1 commits
      reveal a' 0 a                           -- P0 reveals a as a'
        reveal b' 1 b                         -- P1 reveals b as b'
          withdraw (fun who =>
            ite (eqBool (var a') (var b'))
              (if who = 0 then constInt 1 else constInt (-1))
              (if who = 0 then constInt (-1) else constInt 1))
```

**Contexts at each point.**
```
after commit a:  Γ = {a : ⟨bool, priv 0⟩}
after commit b:  Γ = {a : ⟨bool, priv 0⟩,  b : ⟨bool, priv 1⟩}
  viewCtx 0 = {a}    -- P0 sees own commit only
  viewCtx 1 = {b}    -- P1 sees own commit only
after reveal a': Γ += {a' : ⟨bool, pub⟩}
after reveal b': Γ += {b' : ⟨bool, pub⟩}
  withdraw uses a' and b' (both public)
```

**Profile.** P0 always plays true, P1 always plays false:
```
mpProfile.commit who id A obs :=
  match id with
  | 0 => pure (A obs)[0]     -- first action: true
  | 1 => pure (A obs)[1]     -- second action: false
  | _ => pure (A obs)[0]
```

**Expected utility.** `EU matchingPennies mpProfile ∅ 0 = -1` (P0 loses:
heads vs tails). `EU matchingPennies mpProfile ∅ 1 = 1` (P1 wins).

**After profile application.** Both commits become
`sample x id (priv who) (Player who)`. The visibility is preserved — each
value remains private to its committer until revealed. The `Player who`
sampler means the resolved kernel depends on the committer's view. The
program is purely probabilistic (point-mass distributions in this case).
Evaluation reduces to a deterministic payoff computation.

---

## 20. Example: Sequential Game with Perfect Recall

```
sequentialCommit : Prog ∅ int :=
  commit a 0 player0 {true,false}             -- P0 first commit
    reveal a' 0 a                             -- P0 reveals
      commit b 1 player1 {true,false}         -- P1 commits, seeing a'
        commit c 2 player0 {true,false}       -- P0 commits again
          reveal b' 1 b                       -- P1 reveals
            reveal c' 0 c                     -- P0 reveals second commit
              withdraw (...)
```

**Contexts at each point.**
```
after commit a:   Γ = {a : ⟨bool, priv 0⟩}
after reveal a':  Γ += {a' : ⟨bool, pub⟩}
after commit b:   Γ += {b : ⟨bool, priv 1⟩}
  viewCtx 1 = {a', b}     -- P1 sees P0's reveal + own commit
  viewCtx 0 = {a, a'}     -- P0 sees own original + own reveal
after commit c:   Γ += {c : ⟨bool, priv 0⟩}
  viewCtx 0 = {a, a', c}  -- P0 sees both commits + reveal (perfect recall)
```

At channel 2, player 0's strategy receives `viewCtx 0 Γ` which includes
their original private commitment `a`, their public reveal `a'`, and their
new private commitment `c`. Perfect recall is automatic.

---

## 21. Example: Dealt Card (Private Sample)

```
dealtCard : Prog ∅ int :=
  sample card 0 (priv 0) Nature uniformCard   -- Nature deals card to P0
    commit bet 1 player0 {bet, fold}          -- P0 decides
      reveal bet' 0 bet                       -- P0 reveals action — NOT card
        commit resp 2 player1 {call, fold}    -- P1 decides based on bet'
          reveal resp' 1 resp                 -- P1 reveals
            reveal card' 0 card               -- P0 reveals card (showdown)
              withdraw (...)
```

**Contexts at each point.**
```
after sample card: Γ = {card : ⟨int, priv 0⟩}
  Nature kernel depends on pubCtx only (empty here).
  P0 sees card; P1 does not.
after commit bet:  Γ += {bet : ⟨bool, priv 0⟩}
  viewCtx 0 = {card, bet}   -- P0's strategy depends on their card
after reveal bet': Γ += {bet' : ⟨bool, pub⟩}
after commit resp: Γ += {resp : ⟨bool, priv 1⟩}
  viewCtx 1 = {bet', resp}  -- P1 sees P0's public action + own response
after showdown:    card' : ⟨int, pub⟩ — card is now public
```

The dealt card uses `sample card 0 (priv 0) Nature`: nature draws a value
visible only to player 0. The `Nature` sampler means the kernel
(`uniformCard`) depends only on public state — nature does not peek at
anyone's private information. Player 0 owns the result and reveals it at
showdown. Between deal and showdown, the card is `priv 0` — invisible to P1,
but part of P0's view and available to P0's strategy at their commit sites.

# Vegas: A Typed Calculus for Strategic Protocols

## Overview

Vegas is a typed, SSA-based calculus for specifying multi-agent strategic protocols as a single artifact: actions, information structure, randomness, constraints, and terminal payoffs.

A Vegas program denotes a **game-theoretic object**. Concretely:

* Its denotation is an **extensive-form game (EFG)**.
* Fixing a strategy profile induces a **joint distribution over terminal payoffs**.
* Expected utility is derived from that joint distribution.

Core principles:

1. **Information control by types.** Expressions depend only on public data. Strategies and player-private randomness depend only on the acting player’s view.
2. **Owned commitments.** A commitment produces an owner-tagged secret.
3. **Protocol reveal.** Only the owner may reveal a secret, and reveal mints a fresh public binding definitionally equal to the secret.
4. **Deferred assertions.** Assertions attach to owned secrets and are discharged at reveal.
5. **Coherent sampling.** Ill-formed randomness modes are unrepresentable.
6. **Syntactic terminals.** Programs return payoff maps in syntax.

The calculus is intentionally minimal and closed under SSA monotone context growth.

---

## 1. Players and Base Types

### Players

`Player` is a finite type with decidable equality.

### Base types

```
BaseTy ::= int | bool
```

### Values

```
Val int  = Int
Val bool = Bool
```

---

## 2. Owned Bindings and Publicity

### Binding types

```
BindTy ::= pub BaseTy | hidden Player BaseTy
```

* `pub b` — publicly readable.
* `hidden p b` — secret of base type `b`, owned by player `p`.

Ownership is encoded in the type.

---

## 3. Contexts and SSA Discipline

### Variables

`VarId` is an abstract type with decidable equality.

### Contexts

A context `Γ` is a finite map:

```
Γ : VarId ↦ BindTy
```

Extension:

```
Γ, x : τ     (x ∉ dom(Γ))
```

SSA discipline:

* Every binder introduces a fresh `x`.
* No variable is reassigned.
* Contexts grow monotonically.

---

## 4. Environments

```
Env Γ
```

For each `x ∈ dom(Γ)`:

* If `Γ(x) = pub b`, then `env(x) : Val b`.
* If `Γ(x) = hidden p b`, then `env(x) : Val b`.

All bindings exist at runtime; visibility affects access, not storage.

---

## 5. Views and Projections

### Visibility predicate

```
canSee : Player → BindTy → Bool
canSee _ (pub _)          = true
canSee p (hidden q _)     = (p == q)
```

### Sub-contexts

```
viewCtx p Γ = { x : τ ∈ Γ | canSee p τ }
pubCtx Γ    = { x : τ ∈ Γ | τ is pub _ }
```

### Environment projections

```
toView p : Env Γ → Env (viewCtx p Γ)
toPub    : Env Γ → Env (pubCtx Γ)
```

**Perfect recall (structural).**
Because `viewCtx p Γ` includes all `hidden p _` bindings in scope, strategies can depend on the player’s entire private history.

---

## 6. Public Expressions

Expressions read only public bindings.

### Public variable witness

```
PubVar Γ b := { x : VarId // Γ(x) = pub b }
```

### Syntax

```
Expr Γ b ::=
  | var (x : PubVar Γ b)
  | constInt i | constBool b
  | addInt l r | eqInt l r | eqBool l r
  | andBool l r | notBool e
  | ite cond t f
```

### Semantics

```
evalExpr : Expr Γ b → Env Γ → Val b
```

---

## 7. Weighted Distributions

`WDist α` is a finite-support weighted distribution over `α`.

Operations: `pure`, `zero`, `bind`, `map`.

---

## 8. Action Sets and Commit Kernels

### Action sets

```
ActSet who Γ b :=
  Env (viewCtx who Γ) → List (Val b)
```

### Commit kernels (mixed strategies at a site)

```
CommitKernel who Γ b :=
  Env (viewCtx who Γ) → WDist (Val b)
```

---

## 9. Coherent Sampling

Sampling is indexed by binding type.

### Sampling modes

```
SampleMode (pub b)        = NaturePub
SampleMode (hidden p b)   = NaturePriv | PlayerPriv
```

### Sample kernels

```
SampleKernel τ m Γ :=
  match τ, m with
  | pub b,        NaturePub   => Env (pubCtx Γ)    → WDist (Val b)
  | hidden p b,   NaturePriv  => Env (pubCtx Γ)    → WDist (Val b)
  | hidden p b,   PlayerPriv  => Env (viewCtx p Γ) → WDist (Val b)
```

Consequences:

* Public randomness is exogenous.
* Exogenous private deals depend only on public state.
* Player-private randomness depends only on the owner’s view.
* Ill-formed combinations are unrepresentable.

A `hidden p b` sample behaves like a commitment: it creates an owned secret.

---

## 10. Assertions

An assertion is a predicate over a player's view — public state plus
their own private state.

### Predicate type

```
Assert who Γ :=
  Env (viewCtx who Γ) → Bool
```

The type prevents an assertion from inspecting other players' private
bindings: if `who` cannot see a binding, it does not appear in
`viewCtx who Γ`.

### Current semantics (immediate)

`assert who P k` evaluates `P (toView who env)`. If false, the
execution is zero-weighted. If true, evaluation continues with `k`.

This is equivalent to `observe` but with access to the player's full
view rather than only public expressions.

### Future: deferred assertions

When modeling griefing, regret, or quit/punish handlers, assertions
will be deferred to the first program point where they are publicly
verifiable. That point is statically determinable: it is the latest
`reveal` among the private variables captured in `viewCtx who Γ` at
the assertion point. Until then, the assertion is carried as a thunk
`(toView who env, P)`.

Since SSA freezes captured values, immediate and deferred semantics
produce the same `WDist` when quit/punish is not modeled.

---

## 11. Syntactic Payoff Maps

### Syntax

```
PayoffMap Γ ::=
  | table (entries : List (Player × Expr Γ int))
```

### Well-formedness

* Every player appears exactly once.
* No duplicates.

### Semantics

```
evalPayoffMap u env who : Int
```

---

## 12. Program Syntax

Programs are indexed by context `Γ`.

```
Prog Γ ::=

  | ret     (u : PayoffMap Γ)

  | letExpr (x : VarId) (e : Expr Γ b)
            (k : Prog (Γ, x : pub b))

  | sample  (x : VarId) (τ : BindTy) (m : SampleMode τ)
            (K : SampleKernel τ m Γ)
            (k : Prog (Γ, x : τ))

  | commit  (x : VarId) (who : Player)
            (A : ActSet who Γ b)
            (k : Prog (Γ, x : hidden who b))

  | reveal  (y : VarId) (who : Player) (x : VarId)
            [Γ(x) = hidden who b]
            (k : Prog (Γ, y : pub b))

  | assert  (who : Player)
            (P : Assert who Γ)
            (k : Prog Γ)

  | observe (c : Expr Γ bool)
            (k : Prog Γ)
```

### Reveal semantics (design principle)

* `reveal y who x` is owner-restricted by typing.
* It mints a fresh public binding `y`.
* Runtime invariant: `env(y) = env(x)`.

There is no general extractor `hidden p b → b`. Public access to a secret arises only via `reveal`.

---

## 13. Profiles

Commit sites are identified by their SSA variable `x`.

### Total profile

```
Profile :=
  { commit :
      ∀ Γ b,
      (who : Player) →
      (x   : VarId) →
      ActSet who Γ b →
      CommitKernel who Γ b }
```

### Partial profile

```
PProfile :=
  { commit? :
      ∀ Γ b,
      (who : Player) →
      (x   : VarId) →
      ActSet who Γ b →
      Option (CommitKernel who Γ b) }
```

---

## 14. Game-Theoretic Denotation

A program denotes an extensive-form game.

### EFG interpretation

There exists a compilation:

```
toEFG : Prog Γ → Env Γ → GameTree Player
```

Nodes:

* `commit` → decision node for `who`
* `sample` → chance node
* `reveal`, `letExpr`, `observe` → structural transitions
* `ret` → terminal node with payoff function

Information sets are induced by view equivalence:
two histories are indistinguishable for `p`
iff their projections to `viewCtx p` are equal.

---

## 15. Joint Distribution Under a Profile

Fix:

* program `p`
* initial environment `env`
* strategy profile `σ`

Evaluation yields a joint distribution over terminal payoffs:

```
denote p σ env : WDist (Player → Int)
```

This is the distribution induced by resolving decision nodes via `σ`
and chance nodes via their kernels.

Expected utility is derived:

```
EU p σ env who :=
  Σ (f, w) ∈ denote p σ env,  w * f(who)
```

Expected utility is not the primary denotation; it is computed from the induced joint distribution.

---

## 16. Profile Application

Applying a partial profile rewrites commits into coherent samples:

```
commit x who A k
  ↦ sample x (hidden who b) PlayerPriv Kdec k
```

Type preservation holds because both bind `x : hidden who b`.

---

## 17. Well-Formedness

`WFProg p` requires:

1. SSA freshness.
2. Every committed secret is revealed exactly once by its owner.
3. No deferred obligations exist in the core calculus.
4. Payoff maps are total and duplicate-free.

---

## 18. External Assumptions

When interpreted as a protocol:

* Commitments are binding and hiding.
* No external communication.
* All required reveals occur (no strategic refusal modeled).

---

## 19. Example: Matching Pennies

```
commit a p0 A $
  commit b p1 A $
    reveal a' p0 a $
      reveal b' p1 b $
        ret (table [
          (p0,
            ite (eqBool (var a') (var b'))
                (constInt 1) (constInt (-1))),
          (p1,
            ite (eqBool (var a') (var b'))
                (constInt (-1)) (constInt 1))
        ])
```

The denotation is an extensive-form game with two simultaneous commitments revealed before payoff.

Fixing a strategy profile induces a joint distribution over the payoff function `(Player → Int)`. Expected utilities are derived from that distribution.

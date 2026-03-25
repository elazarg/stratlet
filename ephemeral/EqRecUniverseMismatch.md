# Eq.rec Universe Mismatch in pmfFoldBridge Commit Case

## The problem

In the commit case of `pmfFoldBridgeV` (BridgeV.lean) and `pmfFoldBridge` (Reflection.lean), the proof must equate two `PMF` values that are mathematically identical but elaborated with `Eq.rec` at different universe levels. The kernel rejects this because `Eq.rec.{1,2}` and `Eq.rec.{1,1}` are distinct terms.

## Type architecture

```
MAID library (GameTheory/)        Bridge (Vegas/MAID/)        Vegas (Vegas/)
─────────────────────────         ────────────────────        ──────────────
Struct.Val : Fin n → Type         toStruct.Val nd :=          L.Val b
                                    CompiledNode.valType
                                      (st.descAt nd)

nodeDist S sem pol nd a           extractOutcome              outcomeDistBehavioralPMF
  : PMF (S.Val nd)                rawOfTAssign                nativeOutcomeDistPMFV
                                  reflectPolicyAuxV

Policy S :=                       compiledPolicyV             ProgramBehavioralProfilePMF
  (p : Player) →                  reflectPolicyV
  (I : Infoset S p) →
  PMF (S.Val I.1.val)
```

`S.Val nd = CompiledNode.valType (st.descAt nd)` **definitionally** (from `toStruct`).

`CompiledNode.valType (.decision b ...) = L.Val b` **definitionally** (from `valType`).

But `st.descAt nd0 = .decision b ...` is **propositional** (via `hdesc0`), because `descAt` is a lookup into an array built by `addNode`/`addVar`/`ofProg` — it doesn't reduce.

Therefore `S.Val nd0 = L.Val b` is **propositional**, requiring `Eq.rec` transport on `PMF`.

## Where the mismatch arises

The fold bridge commit case must show:

```
LHS: (nodeDist S sem pol nd0 a₀).bind (fun v : S.Val nd0 => F v)
   =
RHS: (κ view : PMF (L.Val b)).bind (fun v : L.Val b => G v)
```

where:
- LHS comes from unfolding `evalStep` at the decision node `nd0`
- RHS comes from unfolding `nativeOutcomeDistPMFV` at the commit case
- `κ` is the reflected behavioral kernel from `reflectPolicyAuxV`

To equate these, some `Eq.rec` must transport between `PMF (S.Val nd0)` and `PMF (L.Val b)`. The transport proof is `hdesc0 : st.descAt nd0 = nd` (where `nd := .decision b who ...`). But depending on how the transport is introduced — by `nativeOutcomeDistPMFV` unfolding vs. by `pmf_bind_castValType` — Lean elaborates `Eq.rec` at universe `{1,2}` (motive `Type → Type`) vs. `{1,1}` (motive `Type → Sort 1`). These are different kernel terms.

## Why this is a design problem

The issue is not a proof bug. It's that `nativeOutcomeDistPMFV` and `reflectPolicyAuxV` work at the Vegas level (producing/consuming `L.Val b`), while `nodeDist` and `evalStep` work at the MAID level (producing/consuming `S.Val nd`). The bridge proof must cross this boundary, and the crossing requires an `Eq.rec` on `PMF`. The universe of that `Eq.rec` depends on elaboration context, which differs between the two sides.

## Approaches

### Approach 1: Make `nativeOutcomeDistPMFV` work at the MAID level

**Idea**: Redefine `nativeOutcomeDistPMFV` so the commit case binds over `v : S.Val nd` (= `CompiledNode.valType (st.descAt ⟨nextId, _⟩)`) instead of `v : L.Val b`. The raw env extension uses `taggedOfVal (st.descAt nd) v` instead of `⟨b, v⟩`.

**Problem**: `nativeOutcomeDistPMFV` is defined by structural recursion on `VegasCore`, which doesn't know about compile states or `descAt`. It knows `b : L.Ty` from the `VegasCore.commit (b := b)` pattern. To use `st.descAt`, the function would need to thread the compile state, but the compile state is built *by* processing the `VegasCore` — it's not available as an input.

One could thread a `(nextId : Nat) → CompiledNode Player L B` function (a "node oracle") that the fold bridge instantiates with `st.descAt`. But this complicates the definition and the `nativeOutcomeDistPMFV_eq` theorem (which connects to `outcomeDistBehavioralPMF`, a pure Vegas-level function that has no notion of compiled nodes).

**Tradeoff**: Eliminates the cast in the fold bridge, but adds complexity to `nativeOutcomeDistPMFV` and its connection to `outcomeDistBehavioralPMF`.

### Approach 2: Make the fold bridge avoid `nodeDist`

**Idea**: Instead of using `evalStep` → `nodeDist` → `match on kind` → get `PMF (S.Val nd)`, define a compiled version of `evalStep` that directly produces values at the `CompiledNode.valType` level, bypassing `Struct.Val`.

**Problem**: `evalStep` and `evalFold` are MAID library functions. The bridge proof uses `evalAssignDist_eq_evalFold` (from GameTheory/) which is stated in terms of `evalStep`. Avoiding `nodeDist` means rewriting this entire evaluation chain.

**Tradeoff**: Very large change to the proof architecture. Avoids the cast but at the cost of reimplementing MAID evaluation.

### Approach 3: Make `reflectPolicyAuxV` return at the MAID level

**Idea**: Instead of `reflectPolicyAuxV` producing `ProgramBehavioralProfilePMF` (Vegas-level, with `L.Val b`-typed kernels), define a "raw" version that produces something typed at `S.Val nd`:

```lean
rawReflectedKernel : ViewEnv who Γ → PMF (S.Val nd0)
rawReflectedKernel view :=
  if h : ∃ cfg, forwardMap cfg = view then
    pol who ⟨⟨nd0, hkind⟩, Classical.choose h⟩  -- : PMF (S.Val nd0)
  else PMF.pure default
```

This kernel returns `PMF (S.Val nd0)` directly — same type as `nodeDist`. The fold bridge equates `nodeDist S sem pol nd0 a₀` with `rawReflectedKernel view`, both `PMF (S.Val nd0)`. No `Eq.rec` on `PMF`.

The connection from `rawReflectedKernel` to `nativeOutcomeDistPMFV` (which uses `L.Val b`) then requires a value-level cast `castValType hdesc0 : S.Val nd0 → L.Val b` inside the bind continuation:

```
(rawReflectedKernel view).bind (fun v : S.Val nd0 => F (castValType hdesc0 v))
= (κ view : PMF (L.Val b)).bind (fun v : L.Val b => F v)
```

This uses `pmf_bind_castValType` which is `subst hdesc0; rfl` — but `hdesc0` can't be `subst`'d if `nd` (the `.decision b who ...`) is let-bound. So **`nd` must be generalized** for `subst` to work.

**Problem**: Still needs the `generalize`/`subst` trick for `nd`. But now the trick is justified — it's the *only* cast, it's at the value level, and `subst` is the standard way to eliminate propositional equalities.

**Tradeoff**: `rawReflectedKernel` is local to the fold bridge proof (a `have`, not a global definition). `reflectPolicyAuxV` and `nativeOutcomeDistPMFV` stay unchanged. The `generalize`/`subst` is localized to one specific step.

### Approach 4: Restructure `Struct.Val` to avoid the propositional equality

**Idea**: Change `toStruct` so that `S.Val nd` is not `CompiledNode.valType (st.descAt nd)` (which requires `descAt` to reduce) but instead a precomputed value:

```lean
noncomputable def toStruct (st : MAIDCompileState Player L B) :=
  { ...
    Val := fun nd => st.valArray nd  -- looked up from a precomputed array
    ... }
```

where `st.valArray` stores `L.Val b` directly, indexed by node. Then `S.Val nd0 = L.Val b` would be definitional if `valArray` is defined appropriately.

**Problem**: This requires changing the `MAIDCompileState` structure and `toStruct` — core definitions shared between old and new proof paths. And `valArray` would still need to be looked up, facing the same `if` branch reduction issue as `descAt`.

**Tradeoff**: Deep infrastructure change. Likely doesn't solve the problem because the array lookup still doesn't reduce definitionally.

### Approach 5: `generalize nd` in the fold bridge

**Idea**: In the commit case of `pmfFoldBridgeV`, instead of:
```lean
let nd := CompiledNode.decision b who_commit ...
```
use:
```lean
-- Introduce nd as a free variable
suffices ∀ nd, st.descAt nd0 = nd → ... from this _ rfl
intro nd hdesc0
```

With `nd` free, `subst hdesc0` replaces `nd` by `st.descAt nd0` everywhere. After substitution, `S.Val nd0 = CompiledNode.valType (st.descAt nd0)` definitionally, and all casts vanish.

**Problem**: This is a proof trick, not a design fix. The definitions still have the type mismatch between `S.Val nd` and `L.Val b`. The `generalize`/`subst` just hides it by never naming the intermediate value.

**Tradeoff**: Minimal change (a few lines in the proof). Works. But doesn't address the underlying design tension.

## Recommendation

**Approach 3** is the most principled. The key insight:

1. The fold bridge should work entirely at the MAID level (`S.Val nd`). The `rawReflectedKernel` and `nodeDist` both return `PMF (S.Val nd0)` — no PMF-level cast.

2. The boundary crossing from `S.Val nd0` to `L.Val b` happens at the value level, inside a `bind` continuation. Value-level casts don't have the `Eq.rec` universe issue (they're at universe 0, not on `PMF` which is `Type`-valued).

3. The `generalize`/`subst` on `nd` is needed for the value-level cast, but this is the standard Lean pattern for eliminating propositional equalities — it's principled, not a hack, when applied at the right level.

**Implementation**: Define `rawReflectedKernel` as a local `have` in the commit case of `pmfFoldBridgeV`. Show `nodeDist = rawReflectedKernel view` (same type, pure MAID-level). Then use `pmf_bind_castValType` with `generalize`/`subst` to connect to `nativeOutcomeDistPMFV`'s `L.Val b`-typed continuation. No changes to any global definition. The `generalize` is on `nd` (the compiled node value), making it a free variable so `subst hdesc0` works.

Approach 5 achieves the same result with less ceremony (skip the explicit `rawReflectedKernel` factoring). It's Approach 3 without naming the intermediate step. Whether to name it depends on whether the factoring helps readability.

## Impact

This issue exists in both `pmfFoldBridgeV` (BridgeV.lean, new path) and `pmfFoldBridge` (Reflection.lean, old path). The fix applies to both. No theorem statements change. No definitions outside the bridge proofs change.

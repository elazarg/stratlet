# Insights — ChatGPT for Lean Proofs

## Integration approach

We use direct OpenAI API calls via Python's `urllib` from bash. This was chosen over:
- **claude-chatgpt-mcp** (https://github.com/syedazharmbnr1/claude-chatgpt-mcp) — Rejected. It automates the ChatGPT macOS desktop app via AppleScript/UI automation. macOS-only, unreliable (open bugs: "input rarely works"), no model selection, slower than API. Not suitable.
- The direct API approach gives us: cross-platform support, explicit model control, low latency, and full reliability.

## Model selection

Use the newest available model. As of 2026-02-10, available GPT-5.x models:
- `gpt-5.2` — current best (use this). Confirmed working. Note: requires `max_completion_tokens` not `max_tokens` (already handled in `ask_gpt.py`).
- `gpt-5.2-pro` — heavier, slower, possibly better for hard proofs (untested)

Also available: `4o`, `o3`, `o3-pro`, `o4-mini` (reasoning models). Untested for Lean proofs.

**No `gpt-5.3` yet** as of 2026-02-09.

## Prompt construction

- **Include complete context for the goal** - if there's a proof that partially works, attach the context, goal and Lean's warnings for anywhere it does not. 
- **Include all referenced definitions.** ChatGPT has no access to our codebase. Every type, function, and inductive that appears in the goal must be in the prompt. You can use `lean-defs.py` to automate parts of the process of collecting proofs.
- **Hint at proof strategy.** "Proceed by induction on p, case splitting on c" significantly improves output quality vs. just saying "prove this."
- **Low temperature (0.2)** for proof tasks. Creativity hurts here.
- **Learn and apply** - once you understand how one proof or part of a proof works, apply it to others.

## Common failure modes

- **Invented names:** ChatGPT references lemmas or constructors that don't exist. Always verify.
- **Scoping errors:** It uses `let`-bound names from function definitions as if they're in proof scope (e.g. `Kfull` from inside `toProb?`).
- **Missing explicit parameters:** Our codebase uses `(L := L)` throughout. ChatGPT drops these.
- **Over-optimistic `simp`:** It writes `simp [f, g]` expecting it to close goals that actually need manual steps.
- **`Option.map` reasoning:** ChatGPT struggles with goals involving `Option.map f x = some y`. It tries `injection`/`contradiction` where `simp` + case split on the inner option is needed.
- **Smart vs raw constructor mismatch:** ChatGPT doesn't understand that Lean's `simp` matches syntactically, not up to definitional equality. When simp lemmas are stated with smart constructors (e.g. `.sample id v K k`) but the goal has raw constructors (`Prog.doBind (CmdBindProto.sample ...) k`), simp silently fails. ChatGPT will suggest `simp [evalProto_sample_bind, ih]` and not understand why it doesn't work. The fix is `change`/`congr_arg` through definitional equality instead of simp.

## When Claude is better than ChatGPT

- **Semantic analysis of proof obstacles:** When the issue is understanding WHY a proof can't go through (e.g., the observe case mismatch in EU preservation), Claude's ability to trace through definitional reductions and identify the exact semantic mismatch is faster and more reliable than ChatGPT.
- **Definitional equality reasoning:** Claude understands that `ObserveFree (.letDet e k)` unfolds to `ObserveFree k` definitionally, so no explicit `have hofk := ...` is needed. ChatGPT tends to add unnecessary extraction steps.
- **When the proof is simple once the approach is clear:** For the observe case, the actual Lean proof was `exact absurd hof (by simp [ObserveFree])` — a one-liner. Claude can write this directly; ChatGPT wraps it in scaffolding.

## When to use ChatGPT as a "rubber duck"

- When you've identified the approach but want confirmation it's sound before restructuring the theorem. In the ObserveFree case, asking ChatGPT "which of these 3 approaches is best?" confirmed option A quickly.

## Workflow

1. Identify a `sorry`.
2. Read surrounding context — gather all definitions referenced in the goal.
3. Construct prompt: definitions + theorem + strategy hint.
4. Call gpt-5.2 via Python snippet (see CLAUDE.md).
5. Paste into Lean file, attempt build.
6. Fix errors — typically: add `(L := L)`, fix names, strengthen `simp` calls.
7. MANDATORY: Record result in EMPIRICAL.md so the process will improve over time.
8. Optional but important: Record and significant insights in autoproof/INSIGHTS.md

## PMF vs FDist: architectural lesson (2026-02-23)

Replacing list-based `FDist` with Mathlib's `PMF` was a huge win:
- **Equality**: `PMF` uses real equality (`=`), not `FDist.equiv` (up to permutation/duplicates). This eliminates an entire class of proof obligations.
- **Fubini for free**: `PMF.bind_comm` gives the swap theorem for any two independent nodes. Previously required 20+ lines of case-splits for just 2x2; the general n×m was sorry'd.
- **Monad laws**: `PMF.pure_bind`, `PMF.bind_pure`, `PMF.bind_bind` from Mathlib — no need to prove them ourselves.

## Fin-indexed vs List-indexed game trees (2026-02-23)

`Fin n`-indexed branches (`Fin n → GameTree ι`) are strictly better than `List GameTree`:
- **No bridge boilerplate**: `evalDist` is 3 lines with no `go_list` helper. With lists, we needed `go_list`, `go_list_eq_get`, `dep_fun_cast`, `evalDist_decision_ofFn` — dozens of lines of bridge.
- **`PMF (Fin n)` for chance nodes**: Bakes well-formedness (weights sum to 1) into the type. No separate weight list to keep in sync.
- **Pattern matching on `Fin`**: `fun | 0 => ... | 1 => ...` works cleanly in examples.
- **WFTree proofs**: `fin_cases` closes branches automatically.

## ChatGPT for design review (2026-02-23)

ChatGPT is useful for reviewing API design:
- Suggested adding `Outcome` type to `KernelGame` (good — separates outcome space from payoff)
- Suggested renaming `mixedOutcome` → `correlatedOutcome` (good — more precise)
- Suggested universe-polymorphic Type-indexed GameTree (bad — universe bumps, instance params in inductives, loss of computability)
- **Lesson**: Accept suggestions about naming and structure; push back on deep type-level changes without understanding Lean's constraints.

## When Claude doesn't need ChatGPT at all (2026-02-24)

Structural induction proofs on well-designed inductive types are Claude's sweet spot:
- **Trace/CanReach/Reach proofs**: All 5 structural proofs compiled on first try. The pattern is straightforward: `induction t with` or `induction h with`, then apply the matching constructor with `.1`/`.2` to destructure definitionally-reduced conjunctions.
- **Bridge proof (operational↔denotational)**: `induction p with` on the Prog type, then `simp only [outcomeDist, ...]` + constructor matching. More complex but still manageable.
- **Rule of thumb**: If the proof is "follow the structure of the inductive type and apply matching constructors," Claude handles it autonomously. Save ChatGPT for proofs that require non-obvious algebraic manipulation or creative lemma discovery.

## ℚ≥0 (NNRat) gotchas in Lean 4 (2026-02-24)

Working with `ℚ≥0` (NNRat) as the base type for FDist has several Mathlib pitfalls:
- **`Mathlib.Data.NNRat.Defs` is not enough**: It doesn't provide `CanonicallyOrderedAdd ℚ≥0`. You need `import Mathlib.Data.NNRat.Order` for `le_self_add`, ordered addition, etc.
- **`mul_pos` doesn't work**: `PosMulStrictMono ℚ≥0` doesn't exist. Use the contrapositive approach: `mul_ne_zero` (from `NoZeroDivisors`) instead of `mul_pos`.
- **`zero_le'` has a type class diamond**: The `Zero` instance from `LinearOrderedCommMonoidWithZero` conflicts with the one from `NNRat.instSemifield`. Workaround: derive `0 ≤ x` from `zero_add x ▸ le_self_add` instead.
- **Finsupp names are camelCase**: `Finsupp.not_mem_support_iff` → `Finsupp.notMem_support_iff`. Always check exact Mathlib names.
- **`Finset.single_le_sum` needs explicit import**: `Mathlib.Algebra.Order.BigOperators.Group.Finset`. Consider if you can avoid it entirely (the `add_sum_erase` + `le_self_add` pattern is self-contained).

## Finsupp.sum algebra: distributing totalWeight over bind (2026-02-24)

The key lemma `totalWeight (d.bind f) = ∑ a ∈ d.support, d a * totalWeight (f a)`:
1. `Finsupp.sum_sum_index (fun _ => rfl) (fun _ _ _ => rfl)` distributes `Finsupp.sum` over another `Finsupp.sum` (since `bind` is `d.sum (fun a w => mapRange ...)`).
2. `Finsupp.sum_mapRange_index (fun _ => rfl)` rewrites `(mapRange (w * ·) ... (f a)).sum (fun _ x => x)` to `(f a).sum (fun _ b => w * b)`.
3. `Finset.mul_sum` factors out the constant `w`.

**Important**: `simp_rw [Finsupp.sum_mapRange_index (fun _ => rfl)]` doesn't work directly — the `rfl` proof for `h0` fails to unify when `simp_rw` tries to match. Workaround: use a `have` wrapper:
```lean
have hmr : ∀ (a : α) (w : ℚ≥0),
    (Finsupp.mapRange (w * ·) (mul_zero w) (f a)).sum (fun _ x => x) =
    (f a).sum (fun _ b => w * b) :=
  fun _ _ => Finsupp.sum_mapRange_index (fun _ => rfl)
simp_rw [hmr]
```

## FDist.mem_support_bind proof pattern (2026-02-24)

The key infrastructure lemma `b ∈ (d.bind f).support ↔ ∃ a ∈ d.support, b ∈ (f a).support`:
- **→ direction**: `by_contra` + `push_neg` to get `∀ a ∈ d.support, b ∉ (f a).support`. Then `Finset.sum_eq_zero` with each term being `d a * 0 = 0` (since `(f a) b = 0` from the negated support membership).
- **← direction**: `Finset.add_sum_erase` splits `∑ = term + rest`. Since the total sum = 0 (by contradiction hypothesis) but `term > 0` (both factors nonzero from support membership), we get contradiction via `le_self_add` + `le_antisymm`.
- This pattern avoids needing `Finset.sum_eq_zero_iff` (which requires `OrderedAddCommMonoid` or similar, not always available) and `mul_pos` (which needs `PosMulStrictMono`).

## Lean 4 higher-order unification with `match` (2026-02-24)

Lean 4's unifier **cannot** assign a metavariable to a `match` expression. This means:
- `constructor` / `apply` fails when the goal contains a `fun x ↦ match x with ...` that needs to unify with a metavariable.
- Example: `WFTree (GameTree.decision 0 (fun x ↦ match x with | 0 => t₁ | 1 => t₂))` — `constructor` tries `WFTree.decision` which needs `?next := fun x ↦ match x with ...`, and fails.

**Workarounds:**
1. **`induction` first**: After `induction t`, the `match` is eliminated and `next` becomes a plain variable. `constructor` then works.
2. **Inversion lemmas with variable signatures**: Define `ReachBy_decision_inv` with `{f : Fin (S.arity I₀) → GameTree ι S}` (all variables). `cases hr` works because no `match` expressions appear. Apply the lemma to specific trees via `rcases`.
3. **Avoid the problem entirely**: For `WFTree`, since every `GameTree` is well-formed (conditions baked into types via `arity_pos` and `Fin (n+1)`), prove `allWFTree` generically by structural induction.

**Key insight**: The issue is NOT about `@[reducible]`/`abbrev` transparency. Even with maximal transparency, the unifier won't match `?next` against `fun x ↦ match x with ...`. The fix is always to restructure the proof so metavariables align with plain variables, not match expressions.

## Perfect recall proof pattern for small trees (2026-02-24)

For small game trees where each info set appears at most once per path:
1. Prove `playerHistory S (S.player I) h = []` for all valid `ReachBy h tree (.decision I next)`.
2. Use cascading `rcases ReachBy_decision_inv` / `ReachBy_chance_inv'` to enumerate all paths.
3. Close terminal-to-decision cases with `nomatch`.
4. Close playerHistory cases with `simp [playerHistory]` (chance steps filtered, wrong-player actions filtered).
5. Final theorem: `rw [helper h₁, helper h₂]`.

This is cleaner than trying to directly relate `h₁` and `h₂` because each path is analyzed independently.

## ENNReal gotchas (2026-02-23)

- `norm_num` does NOT handle ENNReal division/inverse. `2 * 2⁻¹ = 1` in ENNReal needs `ENNReal.mul_inv_cancel (by norm_num) (by norm_num)`.
- `PMF.map` on a PMF resolves to `Subtype.map` (since PMF is a Subtype). Use `.bind (fun x => PMF.pure (f x))` instead.
- `PMF.ofFintype` is in `Mathlib.Probability.ProbabilityMassFunction.Constructions` — not transitively imported through `Monad`.

## Commutativity proof hierarchy (2026-02-25)

The DAG property (independent events commute) has a natural hierarchy of proof difficulty:

1. **reveal/reveal** (trivial): Reveals are deterministic — no `FDist.bind`, no profile interaction. After `simp only [outcomeDist]`, the proof is a single `exact hk_eq ...`. Key structural trick: use `.there` on `HasVar` proofs directly in the statement (`hx₂.there`, `hx₁.there`) to shift through the other reveal's public binding. This makes `(Env.cons v env).get (.there h) = env.get h` fire definitionally via `@[simp] Env.cons_get_there`.

2. **commit/commit** (moderate): Two `FDist.bind`s need swapping via `FDist.bind_comm`. Requires strategy equivalence hypotheses (`hσ₁`, `hσ₂`) showing each player's distribution is independent of the other's hidden binding. Proof: `simp_rw` + `rw [FDist.bind_comm]` + `congr 1; funext` + `exact hk_eq`.

3. **commit/reveal, sample/commit** (not commutative): These are genuinely order-dependent — the committer or sampler may see the newly-revealed/sampled variable. Stated as non-goals (refutation comments in `Operational.lean`).

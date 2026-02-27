# Empirical Results — ChatGPT for Lean Proofs

## Attempt Log

### Attempt 1 — `toProb?_some_iff_NoChoose`

- **Date:** 2026-02-09
- **Model:** gpt-4o (gpt-4o-2024-08-06)
- **Temperature:** 0.2
- **Max tokens:** 1500
- **Token usage:** prompt=13 (for connectivity test); proof attempt not metered separately
- **File:** `Vegas/ProtoLetLemmas.lean:304-308`
- **Theorem:**
  ```lean
  theorem toProb?_some_iff_NoChoose {Γ τ} (p : ProtoProg (L := L) Γ τ) :
      (∃ q, toProb? (L := L) p = some q) ↔ NoChoose (L := L) p
  ```
- **Context given:** Definitions of `NoChoose`, `toProb?`, `toProbNoChoose`. Hint: induction on `p`, case split on `c`.
- **Result:** Structurally correct proof skeleton. Correct use of `induction p with` and `cases c with`.
- **Issues found (not yet verified in Lean):**
  - References `Kfull` which is a `let` binding inside `toProb?`, not in scope in the proof
  - Missing `(L := L)` explicit annotations throughout
  - `injection h; assumption` pattern may not work with Lean 4's `Option.map`
  - `contradiction` used without `simp` to reduce `Option.map ... = some ...` — likely needs `simp [toProb?]` first
- **Verdict:** Good first draft. Estimated 60-70% of the proof usable as-is, rest needs manual fixing.
- **Compiled successfully?** Not tested yet.

### Attempt 2 — `evalProto_applyProfile_of_extends` (doBind cases)

- **Date:** 2026-02-10
- **Model:** gpt-5.2
- **Temperature:** 0.2
- **Max tokens:** 4000
- **File:** `Vegas/ProtoLetLemmas.lean:262-298`
- **Theorem:**
  ```lean
  theorem evalProto_applyProfile_of_extends
      (σ : Profile (L := L)) (π : PProfile (L := L))
      (hExt : Extends (L := L) σ π) :
      ∀ {Γ τ} (p : ProtoProg (L := L) Γ τ) (env : L.Env Γ),
        evalProto σ (applyProfile π p) env = evalProto σ p env
  ```
- **Context given:** Full definitions of `applyProfile`, `Extends`, `evalProto` simp lemmas, `ProgCore.evalWith` simp lemmas, `ProtoSem` simp lemmas, `EffWDist`. Partial proof with ret/letDet/doStmt cases done, two sorry cases for doBind (sample and choose). Explained the difficulty: simp lemmas use smart constructors but applyProfile produces raw constructors.
- **Result:** gpt-5.2 suggested:
  - sample: `simp [applyProfile, evalProto_sample_bind, ih]`
  - choose: `by_cases h : π.choose? = none` then `simp [applyProfile, h, ...]` for both branches, with `rcases Option.ne_none_iff_exists'.1 h` and `subst` for the some case.
- **Issues found:**
  - `simp [applyProfile, evalProto_sample_bind, ih]` failed — simp lemmas use smart constructors (`.sample id v K k`) but after applyProfile reduction the goal has raw constructors (`Prog.doBind (CmdBindProto.sample id v K) (applyProfile π k)`). Simp can't match these despite definitional equality.
  - Same issue for all three `simp` calls — the evalProto simp lemmas are unused.
- **Fix applied (manual):**
  - sample: `change WDist.bind (K (v.proj env)) ... = ...; congr 1; funext x; exact ih (x, env)` — use `change` to restate goal at the WDist.bind level (definitional equality), then close with IH.
  - choose/none: `simp only [applyProfile, hπ]` to propositionally reduce the match, then `congr_arg (WDist.bind ...) (funext ...)` through definitional equality.
  - choose/some: same simp reduction, `subst hσ` to unify kernels, then `congr_arg`.
- **Verdict:** gpt-5.2 identified the right high-level strategy (by_cases, rcases, subst) but couldn't navigate the smart-vs-raw constructor mismatch. Manual fix required understanding of definitional equality vs simp matching. ~40% of the final proof came from gpt-5.2's structure, ~60% was manual.
- **Compiled successfully?** Yes, after manual fixes.
- **Iterations:** 3 (initial gpt-5.2 suggestion → fix simp failures with show → fix show failures with simp+congr_arg)

### Attempt 3 — `eu_preservation_directEU` (observe case)

- **Date:** 2026-02-10
- **Model:** gpt-5.2
- **Temperature:** 0.2
- **File:** `Vegas/LetProtocol/EUBridge.lean:113-152`
- **Theorem:**
  ```lean
  theorem eu_preservation_directEU
      (σ : Profile (L := BasicLang))
      (u : Proto.Utility (L := BasicLang) τ) (who : Player) :
      (p : ParentProtoProg (L := BasicLang) Γ τ) → (env : BasicLang.Env Γ) →
      ObserveFree p →
      EU_dist (p.eval σ env) u who = p.directEU σ u who env
  ```
- **Context given:** Full definitions of WDist, EU_dist, ParentProtoProg.eval, directEU, observe semantics. Analysis of observe case showing semantic mismatch (Proto filters mass via bind+zero, directEU passes through). Three proposed approaches (ObserveFree predicate, fix directEU, add all-observe-pass hypothesis).
- **Result:** gpt-5.2 confirmed ObserveFree approach, gave correct skeleton:
  - `ObserveFree (.observe _ _) = False`, so `exact absurd hof ...` or `exfalso; exact hof.elim`
  - Other cases: extract `hof : ObserveFree k` via `simpa [ObserveFree] using hof` then pass to IH
- **Issues found:**
  - gpt-5.2 used `{G t : Type*}` instead of `{Γ : BasicLang.Ctx} {τ : BasicLang.Ty}` (type parameter mismatch)
  - Used `simpa [ObserveFree] using hof` to extract continuation hypothesis; in practice `hof` is already definitionally `ObserveFree k` so no extraction needed
  - All cases wrapped in unnecessary `simpa using (by admit)` scaffolding
- **Fix applied (manual):**
  - Observe case: `exact absurd hof (by simp [ObserveFree])` (clean one-liner)
  - Other cases: just pass `hof` directly to `ih` since `ObserveFree (.letDet e k)` unfolds to `ObserveFree k` definitionally
- **Verdict:** gpt-5.2 correctly identified the approach (ObserveFree predicate with False elimination). The actual proof was simpler than what ChatGPT suggested — definitional unfolding meant no explicit `have hofk` extraction was needed. ~70% of the insight came from Claude's analysis of the semantic mismatch, ~30% from ChatGPT's confirmation.
- **Compiled successfully?** Yes, after simplification.
- **Iterations:** 1

### Attempt 4 — FDist→PMF migration + Fin-indexed GameTree rewrite

- **Date:** 2026-02-23
- **Model:** Claude (primary), ChatGPT review (advisory)
- **Files:** `GameTheory/OutcomeKernel.lean`, `GameTheory/EFG.lean`, `GameTheory/EFGExamples.lean`, `GameTheory/NFG.lean`, `GameTheory/MAID.lean`, `distilled/GameSemantics.lean`, `distilled/OutcomeKernelBridge.lean`
- **Task:** Replace list-based `FDist` with Mathlib's `PMF` throughout; rewrite `GameTree` from `List`-based branches to `Fin n`-indexed branches
- **ChatGPT role:** Code review of OutcomeKernel design. Suggested adding `Outcome` type to `KernelGame`, renaming `mixedOutcome` → `correlatedOutcome`, generic `expect`. Also proposed universe-polymorphic Type-indexed GameTree (rejected — universe bump issues).
- **Key results:**
  - **Swap theorems**: Previously 20+ lines of case-splits for 2x2; now one-liners via `PMF.bind_comm`. General n×m swap for free. Also got chance-decision and chance-chance swaps.
  - **evalDist**: Was complex with `go_list` helper + bridge lemmas (`go_list_eq_get`, `dep_fun_cast`, `evalDist_decision_ofFn`). Now 3 lines, no helpers needed.
  - **WFTree proofs**: `fin_cases` works cleanly for Fin-indexed branches.
  - **coinFlip PMF**: Built via `PMF.ofFintype` with `ENNReal.mul_inv_cancel` (not `norm_num` — ENNReal division).
  - **`mkSimultaneousTree_evalDist`**: Upgraded from placeholder `True` to actual theorem, proved by `simp`.
- **Issues encountered:**
  - `noncomputable` needed for all Kernel defs (PMF.pure/bind are noncomputable)
  - `PMF.map` resolves to `Subtype.map` (PMF is a Subtype) — use `.bind` + `PMF.pure` instead
  - Doc comment `/-- ... -/` before commented-out code makes Lean expect declaration — convert to `--`
  - `PMF.ofFintype` requires explicit `Constructions` import
  - Structural recursion fails for `(branches.get i).1.toEFG` — use `where` clause helpers
- **Remaining sorry:** `RGameTree.toEFG` chance node PMF construction (bridge TODO)
- **Compiled successfully?** Yes, all 7 files compile (0 errors, only sorry warnings on bridge).
- **Verdict:** This was primarily architecture/refactoring work, not proof-finding. Claude handled the rewrite autonomously. ChatGPT's review was useful for design (Outcome type suggestion), but its GameTree proposal (universe-polymorphic) was rejected. The Fin-indexed design (user's counter-proposal) was the right call.

### Attempt 5 — Operational semantics proofs (6 theorems)

- **Date:** 2026-02-24
- **Model:** Claude Opus 4.6 (solo, no ChatGPT)
- **Files:** `distilled/Operational.lean`, `distilled/Vegas.lean`
- **Task:** Complete 6 sorry'd proofs in the operational semantics module + add 3 FDist infrastructure lemmas
- **Theorems proved:**
  1. `legal_trace_canReach` — induction on `Trace`, ~8 lines
  2. `pos_weight_trace_reach` — induction on `Trace`, uses `left_ne_zero_of_mul`/`right_ne_zero_of_mul` + `Finsupp.mem_support_iff`, ~12 lines
  3. `canReach_has_trace` — induction on `CanReach`, constructs witness `Trace`, ~14 lines
  4. `admissible_pos_weight_legal` — induction on `Trace`, combines weight decomposition with `AdmissibleProfile`, ~14 lines
  5. `admissible_reach_canReach` — induction on `Reach`, uses `hadm.1`/`hadm.2`, ~10 lines
  6. `reach_iff_outcomeDist_support` — bridge proof, induction on `Prog`, ~35 lines
- **Infrastructure added (Vegas.lean):**
  - `FDist.bind_apply` — pointwise evaluation of bind via `Finsupp.sum`
  - `FDist.mem_support_bind` — support characterization: `b ∈ (d.bind f).support ↔ ∃ a ∈ d.support, b ∈ (f a).support`
  - `FDist.mem_support_pure` — `b ∈ (FDist.pure a).support ↔ b = a`
  - Added `import Mathlib.Data.NNRat.Order` for `CanonicallyOrderedAdd ℚ≥0`
- **ChatGPT used?** No. All proofs written by Claude directly.
- **Key results:**
  - Phase 1 (3 structural proofs) + Phase 3 (2 FDist-dependent proofs): **all compiled on first try**, zero iterations
  - Phase 4 (FDist infrastructure): 3 iterations for `mem_support_bind` (Mathlib name errors, missing type class instances for ℚ≥0)
  - Phase 4 (bridge proof): 4 iterations (cross-file LSP limitations, IH application pattern, variable count in `commit` case)
- **Issues encountered:**
  - `Finsupp.not_mem_support_iff` → correct camelCase: `Finsupp.notMem_support_iff`
  - `mul_pos` fails for ℚ≥0: `PosMulStrictMono ℚ≥0` doesn't exist. Workaround: use `mul_ne_zero` (contrapositive approach)
  - `le_self_add` and `zero_le` need `Mathlib.Data.NNRat.Order` (not just `Defs`)
  - `zero_le'` has type class diamond on ℚ≥0 — workaround: `zero_add _ ▸ le_self_add`
  - `Finsupp.mem_support_single_ne_zero` doesn't exist — use `rw [support_pure, Finset.mem_singleton]`
  - LSP can't see cross-file changes from Vegas.lean in Operational.lean — used `lake build distilled.Vegas` fallback
  - `induction p` auto-generalizes `env` but not `oc`; IH is `∀ env, Iff`, accessed via `(ih _).mp`
- **Compiled successfully?** Yes, all 6 proofs + 3 infrastructure lemmas. 0 errors.
- **Stretch goal also completed:**
  - `FDist.totalWeight_bind` — general identity: `totalWeight (d.bind f) = ∑ a, d a * totalWeight (f a)`. Uses `Finsupp.sum_sum_index`, `sum_mapRange_index`, `Finset.mul_sum`. 3 iterations (needed `have` wrapper for `sum_mapRange_index` due to `simp_rw` unification issue).
  - `FDist.totalWeight_bind_of_normalized` — specialization to normalized dists: 1 iteration (direct from `totalWeight_bind`).
  - `outcomeDist_totalWeight_eq_one` — structural induction on `Prog`, 2 iterations (needed `hd.1 _` not `hd.1` to unfold `DistExpr.Normalized`).
- **Verdict:** Structural induction proofs on well-designed inductive types are Claude's sweet spot — no ChatGPT needed. The FDist infrastructure was harder due to Mathlib API discovery (name mismatches, missing instances for ℚ≥0), but still manageable via iterative fixing. The bridge proof required understanding how `induction p` auto-generalizes variables. The stretch goal (Finsupp algebra) was the hardest part — required understanding how `Finsupp.sum_sum_index` and `sum_mapRange_index` compose.

### Attempt 6 — EFG2 InfoStructure redesign (WFTree, evalTotal, perfect recall)

- **Date:** 2026-02-24
- **Model:** Claude Opus 4.6 (solo, no ChatGPT)
- **Files:** `GameTheory/EFG2.lean`, `GameTheory/EFG2Examples.lean`
- **Task:** Complete EFG2Examples.lean — fix WFTree proofs, evalTotal proofs, perfect recall proofs. Also add structural lemmas to EFG2.lean.
- **Theorems proved:**
  1. `allWFTree` — every GameTree is well-formed (WFTree is trivially true), ~4 lines
  2. `seqTree_wf`, `matchingPenniesTree_wf`, `hiddenDecTree_wf` — one-liner applications of `allWFTree`
  3. `ReachBy_terminal_absurd` — no path from terminal to decision, `nomatch`
  4. `ReachBy_decision_inv` — inversion for ReachBy from a decision node, `cases hr`
  5. `ReachBy_chance_inv'` — inversion for ReachBy from a chance node, `cases hr`
  6. `seqTree_playerHistory_nil` / `mpTree_playerHistory_nil` / `hdTree_playerHistory_nil` — helper: all playerHistories to reachable decision nodes are `[]`
  7. `seqTree_perfectRecall` / `matchingPenniesTree_perfectRecall` / `hiddenDecTree_perfectRecall` — perfect recall via `rw [helper, helper]`
- **ChatGPT used?** No.
- **Key challenges:**
  - **Higher-order unification failure**: `constructor`/`apply WFTree.decision` fails when `next` is a pattern-matching lambda (`fun x ↦ match x with ...`). Lean 4's unifier can't match a metavariable against a `match` expression. This blocked both term-mode and tactic-mode WFTree proofs.
  - **Dependent elimination failure**: `cases` on `ReachBy hr₁` fails when the root argument is a defined constant (e.g., `seqTree`) rather than a constructor application with variable arguments.
- **Solutions found:**
  - **WFTree**: `allWFTree` via `induction t with | terminal => constructor | ...` — avoids the unification issue entirely because after `induction`, `next` is a variable, and `constructor` on `WFTree (GameTree.decision I next)` trivially matches.
  - **ReachBy inversion**: Separate lemmas (`ReachBy_decision_inv`, `ReachBy_chance_inv'`) where the root is in explicit constructor form with variable arguments (`{f : Fin (S.arity I₀) → GameTree ι S}`). `cases hr` works on these because all indices are variables. Applied to specific trees via `rcases ReachBy_decision_inv hr with ⟨rfl, rfl, _⟩ | ⟨a, rest, rfl, hr'⟩`.
  - **Perfect recall pattern**: `suffices playerHistory = []` for each path, then `rw [helper, helper]`. Proved via cascading `rcases ReachBy_decision_inv` + `fin_cases` + `nomatch` for terminal cases.
- **Iterations:** 4 (constructor attempt → direct term-mode → generalize → induction/inversion lemma approach)
- **Compiled successfully?** Yes. EFG2.lean: 0 errors, 1 sorry warning (Kuhn). EFG2Examples.lean: 0 errors, 0 warnings.
- **Verdict:** The fundamental Lean 4 limitation here is that higher-order unification doesn't match metavariables against `match` expressions. Two workarounds: (1) use `induction` so the match is already eliminated and arguments are plain variables, (2) define inversion lemmas with all-variable signatures so `cases` can handle dependent elimination. These patterns are reusable for any tree-based proof.

### Attempt 7 — `outcomeDist_comm_reveal`

- **Date:** 2026-02-25
- **Model:** Claude Opus 4.6 (solo)
- **File:** `distilled/Operational.lean:635-656`
- **Theorem:**
  ```lean
  theorem outcomeDist_comm_reveal
      {Γ : Ctx} {σ : Profile} {env : Env Γ}
      {y₁ : VarId} {who₁ : Player} {x₁ : VarId} {b₁ : BaseTy}
      {hx₁ : HasVar Γ x₁ (.hidden who₁ b₁)}
      {y₂ : VarId} {who₂ : Player} {x₂ : VarId} {b₂ : BaseTy}
      {hx₂ : HasVar Γ x₂ (.hidden who₂ b₂)}
      {k : Prog ((y₂, .pub b₂) :: (y₁, .pub b₁) :: Γ)}
      {k' : Prog ((y₁, .pub b₁) :: (y₂, .pub b₂) :: Γ)}
      (hk_eq : ∀ (v₁ : Val b₁) (v₂ : Val b₂) (e : Env Γ),
        outcomeDist σ k (Env.cons v₂ (Env.cons v₁ e)) =
        outcomeDist σ k' (Env.cons v₁ (Env.cons v₂ e))) :
      outcomeDist σ
        (.reveal y₁ who₁ x₁ hx₁ (.reveal y₂ who₂ x₂ hx₂.there k)) env =
      outcomeDist σ
        (.reveal y₂ who₂ x₂ hx₂ (.reveal y₁ who₁ x₁ hx₁.there k')) env
  ```
- **Context given:** N/A (solo Claude — designed from understanding of `outcomeDist` semantics and existing `outcomeDist_comm_commit` pattern)
- **Result:** 2-line proof, compiled first try, 0 errors 0 warnings.
- **Proof:**
  ```lean
  simp only [outcomeDist]
  exact hk_eq (env.get hx₁) (env.get hx₂) env
  ```
- **Key insight:** Reveal/reveal is much simpler than commit/commit because reveals are purely deterministic (no `FDist.bind`). The `@[simp]` lemma `Env.cons_get_there` makes `(Env.cons v env).get (.there h) = env.get h` definitional, so after `simp only [outcomeDist]` inlines both reveals, `exact` handles the rest via definitional equality. No need for `hσ₁`/`hσ₂` strategy equivalence hypotheses — just `hk_eq`.
- **Design choice:** Inner `HasVar` proofs use `.there` directly in the statement (e.g., `hx₂.there`) rather than separate hypotheses relating inner/outer proofs. This eliminates two hypotheses vs. the commit/commit approach.
- **ChatGPT used?** No.
- **Iterations:** 1.
- **Compiled successfully?** Yes. 0 errors, 0 warnings.
- **Verdict:** Reveals are deterministic substitutions — no algebraic commutativity (`FDist.bind_comm`) needed. The `.there` pattern for `HasVar` shifting is the key structural insight.

## Summary Statistics

| Metric | Value |
|--------|-------|
| Total attempts | 7 |
| Compiled as-is | 6/7 (attempt 5 proofs, phase 1+3) |
| Usable skeleton | 3/3 (ChatGPT attempts 1-3) |
| Claude solo success | 18/18 (attempts 5+6+7) |
| Avg response time | ~5s (ChatGPT) |
| Models used | gpt-4o, gpt-5.2, claude opus 4.6 |

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

## Summary Statistics

| Metric | Value |
|--------|-------|
| Total attempts | 3 |
| Compiled as-is | 0/3 |
| Usable skeleton | 3/3 |
| Avg response time | ~5s |
| Models used | gpt-4o, gpt-5.2 |

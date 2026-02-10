import Vegas.LetProtocol.FullInfo
import Vegas.LetProb.Prob
import Vegas.LetProb.ProbLemmas

/-!
# Extensional Properties for FullInfoLet / SProg

These lemmas state "sanity" properties that FullInfoLet strategic programs should satisfy.

Important modeling note:
`FullInfo.Profile` does **not** enforce legality (support ⊆ offered action set).
So any statement that assumes "if A env = [] then the program fails regardless of σ"
needs an extra hypothesis about the profile (or a separate `WFProfile` predicate).
-/

namespace FullInfo

open Prog Defs

/-! ## Profile Independence for Deterministic Subprograms -/

/-- A program with no strategic choices is profile-independent.

In `FullInfo`, the only bind-command is `choose`, so we can characterize
"no strategic choices" as "no `.doBind` nodes at all".
-/
def noChoices {Γ τ} : SProg (L := L) Γ τ → Prop
  | .ret _        => True
  | .letDet _ k   => noChoices k
  | .doStmt _ k   => noChoices k
  | .doBind _ _   => False

@[simp] lemma StratSem_E_bind (σ : Profile (L := L)) {α β} (xs : WDist α) (f : α → WDist β) :
    (StratSem σ).E.bind xs f = WDist.bind xs f := rfl

/-- Profile-independence: programs without choices evaluate the same under any profile. -/
theorem evalS_profile_indep {Γ τ} (p : SProg Γ τ) (hp : noChoices p)
    (σ₁ σ₂ : Profile (L := L)) (env : L.Env Γ) :
    evalS σ₁ p env = evalS σ₂ p env := by
  induction p with
  | ret e =>
      simp [evalS]
      rfl
  | letDet e k ih =>
      -- hp : noChoices (letDet e k) = noChoices k
      have hk : noChoices k := hp
      simp only [evalS, evalWith_letDet]
      simp_all only [forall_const]
      apply ih
  | doStmt s k ih =>
      have hk : noChoices k := hp
      cases s with
      | observe cond =>
          by_cases h : L.toBool (L.eval cond env)
          · -- observe succeeds: bind (pure ()) (fun _ => ...) so just IH
            simp only [evalS, evalWith_doStmt, StratSem_handleStmt_observe, h, ↓reduceIte,
              StratSem_E_bind, WDist.bind_pure]
            simp_all only [forall_const]
            apply ih
          · -- observe fails: bind zero ... = zero on both sides
            simp [evalS, Prog.evalWith_doStmt, StratSem_handleStmt_observe, h]
  | doBind c k =>
      cases hp


variable (σ : Profile (L := L))

/-! ## Observe-Fusion in Strategic Programs -/

/-- Observe-fusion: consecutive observations fuse into conjunction. -/
theorem observe_fuse {EL : ExprLaws (L := L)} {Γ τ} (c₁ c₂ : L.Expr Γ L.bool) (k : SProg Γ τ) :
    (fun env => evalS σ (SProg.observe c₁ (SProg.observe c₂ k)) env)
    =
    (fun env => evalS σ (SProg.observe (EL.andBool c₁ c₂) k) env) := by
  funext env
  simp [evalS_eq_evalP_toProb, SProg.observe, toProb]
  simpa using congrArg (fun f => f env) (Prob.observe_fuse EL)

/-! ## Choose from Singleton -/

/-- Choose from singleton is deterministic if the profile’s kernel is Dirac at that value. -/
theorem choose_singleton {Γ τ τ'} (p : Player) (a : L.Val τ')
    (A : Act Γ τ')
    (k : SProg (τ' :: Γ) τ) (env : L.Env Γ)
    (hσ : σ.choose p A env = WDist.pure a) :
    evalS σ (SProg.letChoose p A k) env = evalS σ k (a, env) := by
  -- unfold one step of the evaluator
  simp [SProg.letChoose, evalS, Prog.evalWith_doBind,
        StratSem_handleBind_choose, hσ, StratSem_E_bind, WDist.bind_pure]


/-! ## Choose from Empty -/

/-- Choose from empty action set yields empty distribution
 (requires the profile to yield `zero`). -/
theorem choose_empty {Γ τ τ'} (p : Player)
    (A : Act Γ τ')
    (k : SProg (τ' :: Γ) τ)
    (hσ : ∀ env, σ.choose p A env = WDist.zero) :
    (fun env => evalS σ (SProg.letChoose p A k) env) = (fun _ => WDist.zero) := by
  funext env
  simp [SProg.letChoose, evalS, Prog.evalWith_doBind,
        StratSem_handleBind_choose, hσ env, StratSem_E_bind, WDist.bind_zero]

/-! ## Behavioral Interpretation Properties -/

/-- Behavioral evaluation preserves the meaning under all profiles. -/
theorem behEval_sound {Γ τ} (p : SProg Γ τ) (env : L.Env Γ) :
    runBeh σ (behEval p env) = evalS σ p env := by
  exact runBeh_behEval_eq_evalS σ p env

/-- Two programs with the same behavior tree are semantically equivalent. -/
theorem beh_eq_implies_evalS_eq {Γ τ} (p₁ p₂ : SProg Γ τ) (env : L.Env Γ)
    (h : behEval p₁ env = behEval p₂ env) :
    evalS σ p₁ env = evalS σ p₂ env := by
  -- rewrite both sides using `runBeh ∘ behEval`
  have h1 : evalS σ p₁ env = runBeh σ (behEval p₁ env) := by
    simpa using (behEval_sound (p := p₁) (env := env) (σ := σ)).symm
  have h2 : evalS σ p₂ env = runBeh σ (behEval p₂ env) := by
    simpa using (behEval_sound (p := p₂) (env := env) (σ := σ)).symm
  -- finish
  calc
    evalS σ p₁ env
        = runBeh σ (behEval p₁ env) := h1
    _   = runBeh σ (behEval p₂ env) := by simp [h]
    _   = evalS σ p₂ env := h2.symm

/-! ## Operational Semantics Properties -/

/-- Operational evaluation is deterministic given an arena. -/
theorem evalOp_deterministic {Γ τ} (arena : Arena) (p : SProg Γ τ) (env : L.Env Γ) :
    ∃! result, evalOp arena p env = result := by
  refine ⟨evalOp arena p env, rfl, ?_⟩
  intro r hr
  simp [hr]

/-! ## Translation Preserves Structure -/

/-- `toProb` preserves `ret`. -/
theorem toProb_ret {Γ τ} (e : L.Expr Γ τ) :
    toProb σ (SProg.ret e) = Prog.Prog.ret e := by
  rfl

/-- `toProb` preserves `letDet`. -/
theorem toProb_letDet {Γ τ τ'} (e : L.Expr Γ τ') (k : SProg (τ' :: Γ) τ) :
    toProb σ (SProg.letDet e k) = Prog.Prog.letDet e (toProb σ k) := by
  rfl

/-- `toProb` preserves `observe`. -/
theorem toProb_observe {Γ τ} (c : L.Expr Γ L.bool) (k : SProg Γ τ) :
    toProb σ (SProg.observe c k) = Prog.Prog.doStmt (.observe c) (toProb σ k) := by
  rfl

/-! ## Player Irrelevance for Same Strategy -/

/-- Player identity is irrelevant at a choice point if the induced kernels agree. -/
theorem player_irrelevant {Γ τ τ'} (p₁ p₂ : Player)
    (A : Act Γ τ') (k : SProg (τ' :: Γ) τ)
    (h : ∀ env, σ.choose p₁ A env = σ.choose p₂ A env) :
    (fun env => evalS σ (SProg.letChoose p₁ A k) env)
    =
    (fun env => evalS σ (SProg.letChoose p₂ A k) env) := by
  funext env
  -- one-step unfold at the `choose`
  simp [SProg.letChoose, evalS, Prog.evalWith_doBind, StratSem_handleBind_choose, h env]

end FullInfo

/-!
## What we might want to add next

This file intentionally proves only "unconditional" extensional laws—statements that do not
require additional modeling commitments beyond the current definitions.

For a more complete characterization of FullInfoLet, we will likely want:

1. **Legality / well-formed profiles (`WFProfile`)**
   A predicate ensuring that strategic kernels respect the offered action sets, e.g.
   `support (σ.choose p A env) ⊆ A env`.
   Many game-theoretic "obvious" lemmas (like "choose from [] always fails") require this.

2. **Normalization + probability-level reasoning**
   Today `WDist` is unnormalized and allows subprobabilities (observe rejects mass).
   If we introduce a normalization layer (partial `ProbabilityMeasure`), we can state laws about
   posteriors / conditional distributions and connect to MeasureTheory cleanly.

3. **Equivalence notions beyond definitional equality**
   `WDist` equality is intensional (`List`-equality). For reasoning "up to permutation/merging,"
   we may introduce an extensional quotient (finite measures / multisets) or a canonicalization,
   and then restate the laws with respect to that equivalence.

4. **Strategy composition assumptions (correlation model)**
   If the intent is to interpret "mixed strategies," we may need explicit assumptions about:
   - independence across distinct choice points (or explicit correlation devices),
   - what information each choice may condition on (full info vs view-based).
   These should become hypotheses of theorems (not silently baked into evaluation).

5. **Dynamic/game-theoretic solution concepts**
   Once "profiles" are first-class objects, we can define and study:
   - best response, Nash equilibrium,
   - subgame perfection / sequential rationality
    (which will likely require an explicit history view),
   - refinements relevant to the commit–reveal / blockchain target (credible punishment, quitting).

6. **Operational semantics + compilation adequacy**
   If there is a blockchain target, add adequacy theorems relating:
   - operational traces (including quits/timeouts),
   - compiled protocol behavior (commit/reveal/oracle),
   - denotational `evalS` / `evalP` results.

All of the above are *additive*: they should refine or constrain the model rather than forcing
changes to the core `Prog` evaluator.
-/

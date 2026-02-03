import Vegas.FullInfoLet
import Vegas.ProbLet

/-!
# Extensional Properties for FullInfoLet / SProg

These lemmas state properties that strategic programs with full information should satisfy.
They serve as sanity checks for the game-theoretic semantics.
-/

namespace FullInfoLet

/-! ## Profile Independence for Deterministic Subprograms

If a program has no `choose` commands, the profile shouldn't matter.
This is fundamental: strategies only affect strategic choices.
-/

/-- A program with no strategic choices is profile-independent -/
def noChoices : SProg Γ τ → Prop
  | .ret _ => True
  | .letDet _ k => noChoices k
  | .doStmt _ k => noChoices k
  | .doBind (.choose _ _) _ => False

/-- Profile-independence: programs without choices evaluate the same under any profile -/
theorem evalS_profile_indep {Γ τ} (p : SProg Γ τ) (hp : noChoices p)
    (σ₁ σ₂ : Profile) (env : Env Γ) :
    evalS σ₁ p env = evalS σ₂ p env := by
  sorry

/-! ## Observe-Fusion in Strategic Programs -/

/-- Observe-fusion: consecutive observations fuse into conjunction -/
theorem observe_fuse {Γ τ} (σ : Profile) (c₁ c₂ : Expr Γ .bool) (k : SProg Γ τ) :
    (fun env => evalS σ (SProg.observe c₁ (SProg.observe c₂ k)) env)
    =
    (fun env => evalS σ (SProg.observe (Expr.andBool c₁ c₂) k) env) := by
  sorry

/-! ## Choose from Singleton

If the action set has exactly one element, the choice is forced.
-/

/-- Choose from singleton is deterministic regardless of profile -/
theorem choose_singleton {Γ τ τ'} (σ : Profile) (p : Player) (a : Val τ')
    (A : Act Γ τ') (hA : ∀ env, A env = [a])
    (k : SProg (τ' :: Γ) τ) (env : Env Γ)
    (hσ : σ.choose p A env = WDist.pure a) :
    evalS σ (SProg.letChoose p A k) env = evalS σ k (a, env) := by
  sorry

/-! ## Choose from Empty

If the action set is empty, the program fails regardless of strategy.
-/

/-- Choose from empty action set yields empty distribution -/
theorem choose_empty {Γ τ τ'} (σ : Profile) (p : Player)
    (A : Act Γ τ') (hA : ∀ env, A env = [])
    (k : SProg (τ' :: Γ) τ) :
    (fun env => evalS σ (SProg.letChoose p A k) env) = (fun _ => []) := by
  sorry

/-! ## Behavioral Interpretation Properties

Properties relating `behEval` and `runBeh` to `evalS`.
The main theorem `runBeh_behEval_eq_evalS` is already proven;
these are additional structural properties.
-/

/-- Behavioral evaluation preserves the meaning under all profiles -/
theorem behEval_sound {Γ τ} (p : SProg Γ τ) (env : Env Γ) (σ : Profile) :
    runBeh σ (behEval p env) = evalS σ p env := by
  exact runBeh_behEval_eq_evalS σ p env

/-- Two programs with the same behavior tree are semantically equivalent -/
theorem beh_eq_implies_evalS_eq {Γ τ} (p₁ p₂ : SProg Γ τ) (env : Env Γ)
    (h : behEval p₁ env = behEval p₂ env) (σ : Profile) :
    evalS σ p₁ env = evalS σ p₂ env := by
  sorry

/-! ## Operational Semantics Properties -/

/-- Operational evaluation is deterministic given an arena -/
theorem evalOp_deterministic {Γ τ} (arena : Arena) (p : SProg Γ τ) (env : Env Γ) :
    ∃! result, evalOp arena p env = result := by
  sorry  -- trivially true, but good to state

/-! ## Translation Preserves Structure -/

/-- toProb preserves ret -/
theorem toProb_ret {Γ τ} (σ : Profile) (e : Expr Γ τ) :
    toProb σ (SProg.ret e) = ProgCore.Prog.ret e := by
  sorry

/-- toProb preserves letDet -/
theorem toProb_letDet {Γ τ τ'} (σ : Profile) (e : Expr Γ τ') (k : SProg (τ' :: Γ) τ) :
    toProb σ (SProg.letDet e k) = ProgCore.Prog.letDet e (toProb σ k) := by
  sorry

/-- toProb preserves observe -/
theorem toProb_observe {Γ τ} (σ : Profile) (c : Expr Γ .bool) (k : SProg Γ τ) :
    toProb σ (SProg.observe c k) = ProgCore.Prog.doStmt (.observe c) (toProb σ k) := by
  sorry

/-! ## Player Irrelevance for Same Strategy

If two players use the same strategy at a choice point, the result is the same.
-/

/-- Player identity is irrelevant if strategies agree on the action set -/
theorem player_irrelevant {Γ τ τ'} (σ : Profile) (p₁ p₂ : Player)
    (A : Act Γ τ') (k : SProg (τ' :: Γ) τ)
    (h : ∀ env, σ.choose p₁ A env = σ.choose p₂ A env) :
    (fun env => evalS σ (SProg.letChoose p₁ A k) env)
    =
    (fun env => evalS σ (SProg.letChoose p₂ A k) env) := by
  sorry

end FullInfoLet

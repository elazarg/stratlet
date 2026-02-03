import Vegas.PartialInfoLet
import Vegas.ProbLet

/-!
# Extensional Properties for PartialInfoLet / SProg

These lemmas state properties that partial-information strategic programs should satisfy.
They serve as sanity checks, especially for the commit-reveal protocol semantics.
-/

namespace PartialInfoLet

/-! ## Commit-Reveal Coherence

The fundamental property: if you commit to a value and then reveal with the
correct token, you get the original value back.
-/

/-- Extend view to see a newly bound variable -/
def extendView {Γ τ'} (v : View Γ) : View (τ' :: Γ) := {
  Δ := τ' :: v.Δ
  proj := fun (a, env) => (a, v.proj env)
}

/-- Commit followed by reveal with matching token succeeds and returns the value -/
theorem commit_reveal_coherent {Γ τ τ'} (σ : Profile)
    (who : Player) (v : View Γ) (x : Var v.Δ τ')
    -- after commit, token is at vz and x is shifted
    (k : SProg (τ' :: Ty.int :: Γ) τ) (env : Env Γ) :
    let obs := v.proj env
    let xv := Env.get obs x
    let tok := commitTag who xv
    -- Program: commit x; reveal using fresh token and original x
    -- (simplified: assumes we can refer to tok and xv after commit)
    evalS σ (.doBind (.commit who v x)
      (.doBind (.reveal who (extendView v) Var.vz (Var.vs x)) k)) env
    =
    WDist.bind (WDist.pure tok) (fun t =>
      WDist.bind (WDist.pure xv) (fun r =>
        evalS σ k (r, t, env))) := by
  sorry

/-! ## Reveal with Wrong Token Fails

If the token doesn't match, reveal rejects.
-/

/-- Reveal with mismatched token yields empty distribution -/
theorem reveal_mismatch_fails {Γ τ τ'} (σ : Profile)
    (who : Player) (v : View Γ) (c : Var v.Δ .int) (x : Var v.Δ τ')
    (k : SProg (τ' :: Γ) τ) (env : Env Γ)
    (h : (v.proj env).get c ≠ commitTag who ((v.proj env).get x)) :
    evalS σ (.doBind (.reveal who v c x) k) env = [] := by
  sorry

/-! ## View Projection Properties -/

/-- Identity view sees everything: projection is identity -/
def idView (Γ : Ctx) : View Γ := { Δ := Γ, proj := id }

/-- Evaluation with identity view uses full environment -/
theorem choose_idView {Γ τ τ'} (σ : Profile) (who : Player)
    (A : Act (v := idView Γ) τ') (k : SProg (τ' :: Γ) τ) (env : Env Γ) :
    evalS σ (.doBind (.choose who (idView Γ) A) k) env
    =
    WDist.bind (σ.choose who (idView Γ) A env) (fun a => evalS σ k (a, env)) := by
  sorry

/-- Empty view sees nothing -/
def emptyView (Γ : Ctx) : View Γ := { Δ := [], proj := fun _ => () }

/-- With empty view, strategy cannot depend on environment -/
theorem choose_emptyView_const {Γ τ τ'} (σ : Profile) (who : Player)
    (A : Act (v := emptyView Γ) τ') (k : SProg (τ' :: Γ) τ)
    (env₁ env₂ : Env Γ) :
    σ.choose who (emptyView Γ) A ((emptyView Γ).proj env₁)
    =
    σ.choose who (emptyView Γ) A ((emptyView Γ).proj env₂) := by
  sorry

/-! ## Profile Independence for Non-Choose Programs

Same as FullInfoLet: programs without `choose` are profile-independent.
-/

/-- A program with no strategic choices -/
def noChoices : SProg Γ τ → Prop
  | .ret _ => True
  | .letDet _ k => noChoices k
  | .doStmt _ k => noChoices k
  | .doBind (.choose _ _ _) _ => False
  | .doBind (.commit _ _ _) k => noChoices k
  | .doBind (.reveal _ _ _ _) k => noChoices k

/-- Profile-independence for programs without choose -/
theorem evalS_profile_indep {Γ τ} (p : SProg Γ τ) (hp : noChoices p)
    (σ₁ σ₂ : Profile) (env : Env Γ) :
    evalS σ₁ p env = evalS σ₂ p env := by
  sorry

/-! ## Observe-Fusion -/

/-- Observe-fusion: consecutive observations fuse into conjunction -/
theorem observe_fuse {Γ τ} (σ : Profile) (c₁ c₂ : Expr Γ .bool) (k : SProg Γ τ) :
    (fun env => evalS σ (SProg.observe c₁ (SProg.observe c₂ k)) env)
    =
    (fun env => evalS σ (SProg.observe (Expr.andBool c₁ c₂) k) env) := by
  sorry

/-! ## Commit is Deterministic

Commit always succeeds and produces exactly one token.
-/

/-- Commit produces a Dirac distribution -/
theorem commit_dirac {Γ τ τ'} (σ : Profile)
    (who : Player) (v : View Γ) (x : Var v.Δ τ')
    (k : SProg (Ty.int :: Γ) τ) (env : Env Γ) :
    evalS σ (.doBind (.commit who v x) k) env
    =
    let tok := commitTag who ((v.proj env).get x)
    evalS σ k (tok, env) := by
  sorry

/-! ## Behavioral Interpretation Properties -/

/-- Behavioral evaluation is sound -/
theorem behEval_sound {Γ τ} (p : SProg Γ τ) (env : Env Γ) (σ : Profile) :
    runBeh σ (behEval p env) = evalS σ p env := by
  exact runBeh_behEval_eq_evalS σ p env

/-! ## Translation to ProbLet Preserves Semantics -/

-- Already proven as evalS_eq_evalP_toProb, but state explicitly:

/-- Translation is semantics-preserving -/
theorem toProb_correct {Γ τ} (σ : Profile) (p : SProg Γ τ) (env : Env Γ) :
    ProbLet.evalP (toProb σ p) env = evalS σ p env := by
  exact (evalS_eq_evalP_toProb σ p env).symm

/-! ## CommitTag Properties

Properties of the placeholder commitment scheme.
-/

-- /-- Different values for same player give different tags (for Int) -/
-- theorem commitTag_injective_int (who : Player) (x y : Int) (h : x ≠ y) :
--     commitTag who x ≠ commitTag who y := by
--   sorry

-- /-- Same value, different players give different tags -/
-- theorem commitTag_player_distinct (who₁ who₂ : Player) (x : Int)
--     (h : who₁ ≠ who₂) :
--     commitTag who₁ x ≠ commitTag who₂ x := by
--   sorry

end PartialInfoLet

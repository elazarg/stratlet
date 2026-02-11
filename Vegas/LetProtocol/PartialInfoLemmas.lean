import Vegas.LetProtocol.PartialInfo
import Vegas.LetProb.Prob

/-!
# Extensional Properties for PartialInfoLet / SProg

These lemmas state properties that partial-information strategic programs should satisfy.
They serve as sanity checks, especially for the commit-reveal protocol semantics.

Important modeling note:
`PartialInfo.Profile` controls only `.choose`. The `.commit` / `.reveal` binds are
deterministic protocol steps in the current placeholder scheme.
-/

namespace PartialInfo

open Prog Defs

variable {W : Type} [WeightModel W]

/-! ## Commit-Reveal Coherence -/

/-- Extend a view after a `.commit` bind:

In context `Ty.int :: Γ` the freshly bound token is available as the head of the env.
We extend the visible context to `Ty.int :: v.Δ` by pairing that token with the old projection.
-/
def extendViewTok {Γ} (v : View Γ) : View (Ty.int :: Γ) := {
  Δ := Ty.int :: v.Δ
  proj := fun (tok, env) => (tok, v.proj env)
}

/-- Commit then reveal with the freshly produced token succeeds and returns the original value. -/
theorem commit_reveal_coherent {Γ τ τ'} (σ : Profile (W := W))
    (who : Player) (v : View Γ) (x : Env.Var v.Δ τ')
    (k : SProg (τ' :: Ty.int :: Γ) τ) (env : L.Env Γ) :
    let obs := v.proj env
    let xv  := obs.get x
    let tok := commitTag who xv
    evalS σ
      (.doBind (.commit who v x)
        (.doBind (.reveal who (extendViewTok v) Env.Var.vz (Env.Var.vs x)) k)) env
    =
    evalS σ k (xv, tok, env) := by
  -- unfold the let-binders in the statement so we can rewrite with `tok`/`xv`
  simp (config := {zeta := true}) only
  -- now unfold the two `.doBind`s under the big-step evaluator
  simp only [evalS, SProg.doBind, extendViewTok, evalWith_doBind, StratSem_handleBind_commit,
    StratSem_handleBind_reveal, Env.Env.get_vz, beq_iff_eq, StratSem_E_bind, WDist.bind_pure]
  split
  next h =>
    simp
    rfl
  next h =>
    contrapose h
    rfl

/-! ## Reveal with Wrong Token Fails -/

/-- Reveal with mismatched token yields empty distribution. -/
theorem reveal_mismatch_fails {Γ τ τ'} (σ : Profile (W := W))
    (who : Player) (v : View Γ) (c : Env.Var v.Δ .int) (x : Env.Var v.Δ τ')
    (k : SProg (τ' :: Γ) τ) (env : L.Env Γ)
    (h : (v.proj env).get c ≠ commitTag who ((v.proj env).get x)) :
    evalS σ (.doBind (.reveal who v c x) k) env = WDist.zero := by
  simp only [evalS, SProg.doBind, Prog.evalWith_doBind,
             StratSem_handleBind_reveal, StratSem_E_bind, beq_iff_eq]
  simp [h]

/-! ## View Projection Properties -/

/-- Evaluation with identity view uses the full environment (definitionally). -/
theorem choose_idView {Γ τ τ'} (σ : Profile (W := W)) (who : Player)
    (A : Act (v := idView Γ) τ') (k : SProg (τ' :: Γ) τ) (env : L.Env Γ) :
    evalS σ (.doBind (.choose who (idView Γ) A) k) env
    =
    WDist.bind (σ.choose who (idView Γ) A env) (fun a => evalS σ k (a, env)) := by
  simp only [evalS, SProg.doBind, Prog.evalWith_doBind,
             StratSem_handleBind_choose, StratSem_E_bind]
  rfl

/-- Empty view sees nothing. -/
def emptyView (Γ : Ctx) : View Γ := { Δ := [], proj := fun _ => () }

omit [WeightModel W] in
/-- With empty view, the projected observation is always `()`,
hence strategies cannot vary with `env`. -/
theorem choose_emptyView_const {Γ τ} (σ : Profile (W := W)) (who : Player)
    (A : Act (v := emptyView Γ) τ)
    (env₁ env₂ : L.Env Γ) :
    σ.choose who (emptyView Γ) A ((emptyView Γ).proj env₁)
    =
    σ.choose who (emptyView Γ) A ((emptyView Γ).proj env₂) := by
  rfl

/-! ## Profile Independence for Non-Choose Programs -/

/-- A program with no strategic choices (`choose`).

`commit` / `reveal` do not consult the profile in the current semantics, so they are allowed.
-/
def noChoices {Γ τ} : SProg Γ τ → Prop
  | .ret _ => True
  | .letDet _ k => noChoices k
  | .doStmt _ k => noChoices k
  | .doBind (.choose _ _ _) _ => False
  | .doBind (.commit _ _ _) k => noChoices k
  | .doBind (.reveal _ _ _ _) k => noChoices k

/-- Profile-independence for programs without `choose`. -/
theorem evalS_profile_indep {Γ τ} (p : SProg Γ τ) (hp : noChoices p)
    (σ₁ σ₂ : Profile (W := W)) (env : L.Env Γ) :
    evalS σ₁ p env = evalS σ₂ p env := by
  induction p with
  | ret e => rfl
  | letDet e k ih =>
      exact ih (hp := hp) (env := (L.eval e env, env))
  | doStmt s k ih =>
      cases s with
      | observe cond =>
          simp only [evalS, Prog.evalWith_doStmt,
                     StratSem_handleStmt_observe, StratSem_E_bind]
          by_cases h : L.toBool (L.eval cond env)
          · simp only [h, ite_true, WDist.bind_pure]
            exact Function.const Ctx (ih hp env) Γ
          · simp [h]
  | doBind c k ih =>
      cases c with
      | choose who v A =>
          cases hp
      | commit who v x =>
          simp only [evalS, Prog.evalWith_doBind,
                     StratSem_handleBind_commit, StratSem_E_bind, WDist.bind_pure]
          exact ih (hp := hp) (env := (commitTag who ((v.proj env).get x), env))
      | reveal who v c x =>
          simp only [evalS, Prog.evalWith_doBind,
                     StratSem_handleBind_reveal, StratSem_E_bind]
          split
          · -- token matches: both continue with pure xv
            simp only [WDist.bind_pure]
            exact ih (hp := hp) (env := ((v.proj env).get x, env))
          · -- token mismatch: both sides are bind zero = zero
            simp [WDist.bind_zero]

/-! ## Observe-Fusion -/

/-- Observe-fusion: consecutive observations fuse into conjunction. -/
theorem observe_fuse {Γ τ} (σ : Profile (W := W)) (c₁ c₂ : Expr Γ .bool) (k : SProg Γ τ) :
    (fun env => evalS σ (SProg.observe c₁ (SProg.observe c₂ k)) env)
    =
    (fun env => evalS σ (SProg.observe (Expr.andBool c₁ c₂) k) env) := by
  funext env
  simp only [SProg.observe, SProg.doStmt, evalS, Prog.evalWith_doStmt,
             StratSem_handleStmt_observe, StratSem_E_bind]
  cases h1 : L.toBool (L.eval c₁ env) <;> cases h2 : L.toBool (L.eval c₂ env) <;>
    simp_all [WDist.bind_pure, WDist.bind_zero, BasicLang, evalExpr]

/-! ## Commit is Deterministic -/

/-- Commit produces a Dirac distribution (operationally: it just extends the env and continues). -/
theorem commit_dirac {Γ τ τ'} (σ : Profile (W := W))
    (who : Player) (v : View Γ) (x : Env.Var v.Δ τ')
    (k : SProg (Ty.int :: Γ) τ) (env : L.Env Γ) :
    evalS σ (.doBind (.commit who v x) k) env
    =
    let tok := commitTag who ((v.proj env).get x)
    evalS σ k (tok, env) := by
  simp only [evalS, SProg.doBind, Prog.evalWith_doBind,
             StratSem_handleBind_commit, StratSem_E_bind, WDist.bind_pure]

/-! ## Behavioral Interpretation Properties -/

/-- Behavioral evaluation is sound. -/
theorem behEval_sound {Γ τ} (p : SProg Γ τ) (env : L.Env Γ) (σ : Profile (W := W)) :
    runBeh σ (behEval (W := W) p env) = evalS σ p env := by
  exact runBeh_behEval_eq_evalS σ p env

/-! ## Translation to ProbLet Preserves Semantics -/

/-- Translation is semantics-preserving. -/
theorem toProb_correct {Γ τ} (σ : Profile (W := W)) (p : SProg Γ τ) (env : L.Env Γ) :
    Prob.evalP (W := W) (toProb σ p) env = evalS σ p env := by
  exact (evalS_eq_evalP_toProb σ p env).symm

end PartialInfo

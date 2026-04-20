import Vegas.WF
import Vegas.Scope
import Vegas.WFProgram

namespace Vegas

namespace Examples

def va : VarId := 0
def vb : VarId := 1
def va' : VarId := 2
def vb' : VarId := 3

def Γ0 : VCtxSimple := []
def Γ1 : VCtxSimple := [(va, .hidden 0 .bool)]
def Γ2 : VCtxSimple := [(vb, .hidden 1 .bool), (va, .hidden 0 .bool)]
def Γ3 : VCtxSimple :=
  [(va', .pub .bool), (vb, .hidden 1 .bool), (va, .hidden 0 .bool)]
def Γ4 : VCtxSimple :=
  [(vb', .pub .bool), (va', .pub .bool),
   (vb, .hidden 1 .bool), (va, .hidden 0 .bool)]

def hva_in_Γ2 : VHasVarSimple Γ2 va (.hidden 0 .bool) := .there .here
def hvb_in_Γ3 : VHasVarSimple Γ3 vb (.hidden 1 .bool) := .there .here
def hva'_in_p1_view : VHasVarSimple (viewVCtx 1 ((va', .pub .bool) :: Γ1)) va' (.pub .bool) := by
  change VHasVarSimple [(va', .pub .bool)] va' (.pub .bool)
  exact .here

-- HasVar proofs in erasePubVCtx Γ4 = [(vb', .bool), (va', .bool)]
def hva'_in_eΓ4 : HasVar (erasePubVCtx Γ4) va' .bool := .there .here
def hvb'_in_eΓ4 : HasVar (erasePubVCtx Γ4) vb' .bool := .here

def mpPayoff : PayoffMap Γ4 :=
  ⟨[ (0, .ite
        (.eqBool (.var va' hva'_in_eΓ4) (.var vb' hvb'_in_eΓ4))
        (.constInt 1) (.constInt (-1))),
     (1, .ite
        (.eqBool (.var va' hva'_in_eΓ4) (.var vb' hvb'_in_eΓ4))
        (.constInt (-1)) (.constInt 1))
   ], by decide⟩

noncomputable def matchingPennies : VegasSimple Γ0 :=
  .commit va 0 (b := .bool) (.constBool true)
    (.commit vb 1 (b := .bool) (.constBool true)
      (.reveal va' 0 va hva_in_Γ2
        (.reveal vb' 1 vb hvb_in_Γ3
          (.ret mpPayoff.entries))))

noncomputable def mpProfile : OmniscientOperationalProfileSimple where
  commit := fun {_Γ} {b} _who x _R _env =>
    match x with
    | 0 =>
      match b with
      | .bool => FDist.pure true
      | .int => FDist.zero
    | 1 =>
      match b with
      | .bool => FDist.pure false
      | .int => FDist.zero
    | _ => FDist.zero

-- conditionedGame: commit guard references revealed value
-- Guard for player 1: the expression sees (vb, .bool) :: eraseVCtx Γ1'
-- where Γ1' = [(va', .pub .bool), (vb, .hidden 1 .bool), (va, .hidden 0 .bool)]
-- eraseVCtx Γ1' = [(va', .bool), (vb, .bool), (va, .bool)]
-- so guard context is (vb, .bool) :: [(va', .bool), (vb, .bool), (va, .bool)]
-- and the guard var va' is at .there .here
noncomputable def conditionedGame : VegasSimple Γ0 :=
  .commit va 0 (b := .bool) (.constBool true)
    (.reveal va' 0 va .here
      (.commit vb 1 (b := .bool)
        (.var va' (.there .here))
        (.reveal vb' 1 vb .here
          (.ret [(0, .constInt 1), (1, .constInt 0)]))))

example : RevealComplete [] matchingPennies := by
  decide

example : FreshBindings matchingPennies := by
  decide

example : ViewScoped matchingPennies := by
  constructor
  · intro x hx
    exact Finset.mem_insert_of_mem hx
  · constructor
    · intro x hx
      exfalso
      change x ∈ (∅ : Finset VarId) at hx
      simp at hx
    · trivial

example : WF matchingPennies := by
  exact ⟨by decide, by decide, by
    constructor
    · intro x hx
      exact Finset.mem_insert_of_mem hx
    · constructor
      · intro x hx
        exfalso
        change x ∈ (∅ : Finset VarId) at hx
        simp at hx
      · trivial⟩

example : Legal matchingPennies := by
  constructor
  · intro _env
    exact ⟨true, by rfl⟩
  · constructor
    · intro _env
      exact ⟨true, by rfl⟩
    · trivial

example : NormalizedDists matchingPennies := by
  simp [matchingPennies, NormalizedDists]

example : mpProfile.NormalizedOn matchingPennies := by
  constructor
  · intro _env
    simp [mpProfile, va, FDist.totalWeight_pure]
  · constructor
    · intro _env
      simp [mpProfile, vb, FDist.totalWeight_pure]
    · trivial

example : RevealComplete [] conditionedGame := by
  decide

example : FreshBindings conditionedGame := by
  decide

example : ViewScoped conditionedGame := by
  constructor
  · intro x hx
    exact Finset.mem_insert_of_mem hx
  · constructor
    · intro x hx
      exact Finset.mem_insert_of_mem hx
    · trivial

example : WF conditionedGame := by
  exact ⟨by decide, by decide, by
    constructor
    · intro x hx
      exact Finset.mem_insert_of_mem hx
    · constructor
      · intro x hx
        exact Finset.mem_insert_of_mem hx
      · trivial⟩

example : ¬ Legal conditionedGame := by
  intro hlegal
  -- The guard for player 1's commit is (.var va' (.there .here)) which reads va'.
  -- With va' = false, guard evaluates to false for all choices,
  -- contradicting Legal (which requires ∃ choice satisfying the guard).
  -- Full erased env with va' = false, va = true
  let envFalse :
      Env simpleExpr.Val (eraseVCtx ((va', .pub .bool) :: (va, .hidden 0 .bool) :: Γ0)) :=
    Env.cons false (Env.cons true (Env.empty _))
  obtain ⟨a, hg⟩ := hlegal.2.1 envFalse
  cases a <;>
    simp [envFalse, Γ0, va, va', Vegas.evalGuard, Vegas.evalExpr,
      Vegas.simpleExpr, Env.cons, Env.get, BindTy.base] at hg

example : NormalizedDists conditionedGame := by
  simp [conditionedGame, NormalizedDists]

example : mpProfile.NormalizedOn conditionedGame := by
  constructor
  · intro _env
    simp [mpProfile, va, FDist.totalWeight_pure]
  · constructor
    · intro _env
      simp [mpProfile, vb, FDist.totalWeight_pure]
    · trivial

-- sequentialReveal: same as matching pennies but Player 0 reveals before
-- Player 1 commits, giving Player 1 information about Player 0's choice.
noncomputable def sequentialReveal : VegasSimple Γ0 :=
  .commit va 0 (b := .bool) (.constBool true)
    (.reveal va' 0 va .here
      (.commit vb 1 (b := .bool) (.constBool true)
        (.reveal vb' 1 vb .here
          (.ret mpPayoff.entries))))

example : FreshBindings sequentialReveal := by
  decide

example : RevealComplete [] sequentialReveal := by
  decide

example : ViewScoped sequentialReveal := by
  constructor
  · intro x hx
    exact Finset.mem_insert_of_mem hx
  · constructor
    · intro x hx
      exfalso
      change x ∈ (∅ : Finset VarId) at hx
      simp at hx
    · trivial

example : WF sequentialReveal := by
  exact ⟨by decide, by decide, by
    constructor
    · intro x hx
      exact Finset.mem_insert_of_mem hx
    · constructor
      · intro x hx
        exfalso
        change x ∈ (∅ : Finset VarId) at hx
        simp at hx
      · trivial⟩

example : Legal sequentialReveal := by
  constructor
  · intro _env
    exact ⟨true, by rfl⟩
  · constructor
    · intro _env
      exact ⟨true, by rfl⟩
    · trivial

example : NormalizedDists sequentialReveal := by
  simp [sequentialReveal, NormalizedDists]

example : mpProfile.NormalizedOn sequentialReveal := by
  constructor
  · intro _env
    simp [mpProfile, va, FDist.totalWeight_pure]
  · constructor
    · intro _env
      simp [mpProfile, vb, FDist.totalWeight_pure]
    · trivial

/-! ### Paper claims: visibility contexts -/

-- Matching Pennies: after both commits, Player 0's view contains only their own variable.
-- Paper: "Player 0's view Γ↓₀ = [(a, hid(0, bool))]"
example : viewVCtx 0 Γ2 = [(va, .hidden 0 .bool)] := by
  simp [viewVCtx, canSee, Γ2, va, vb]

-- Matching Pennies: Player 1's view contains only their own variable.
example : viewVCtx 1 Γ2 = [(vb, .hidden 1 .bool)] := by
  simp [viewVCtx, canSee, Γ2, va, vb]

-- Sequential Reveal: at Player 1's commit point, a' is in Player 1's view.
-- Paper: "Player 1's view includes a' (public)"
-- Context at Player 1's commit: (va', .pub .bool) :: Γ1
def Γ_seqRevealAtP1Commit : VCtxSimple := (va', .pub .bool) :: Γ1

example : va' ∈ visibleVars (L := simpleExpr) 1 Γ_seqRevealAtP1Commit := by
  simp [Γ_seqRevealAtP1Commit, Γ1, visibleVars, va, va']

/-! ### Paper claims: conditioned game guard behavior -/

-- The guard for Player 1's commit in conditionedGame.
-- Guard context: (vb, .bool) :: eraseVCtx [(va', .pub .bool), (va, .hidden 0 .bool)]
--              = [(vb, .bool), (va', .bool), (va, .bool)]
-- Guard expression: .var va' (.there .here)  — reads va' from the environment.

private def cgGuard : simpleExpr.Expr ((vb, .bool) :: eraseVCtx Γ_seqRevealAtP1Commit) .bool :=
  .var va' (.there .here)

-- When va' = true in the environment, the guard evaluates to true for ANY proposed action.
-- Paper: "When a' = true, Player 1's choices are unrestricted"
example : ∀ (a : Bool) (va_val : Bool),
    let env : Env simpleExpr.Val (eraseVCtx Γ_seqRevealAtP1Commit) :=
      Env.cons true (Env.cons va_val (Env.empty _))
    evalGuard cgGuard a env = true := by
  intro a va_val
  cases a <;> cases va_val <;>
    (simp [cgGuard, evalGuard, evalExpr, simpleExpr, BindTy.base]; rfl)

-- When va' = false, the guard evaluates to false for ANY proposed action — deadlock.
-- Paper: "When a' = false, no Boolean value satisfies the guard"
example : ∀ (a : Bool) (va_val : Bool),
    let env : Env simpleExpr.Val (eraseVCtx Γ_seqRevealAtP1Commit) :=
      Env.cons false (Env.cons va_val (Env.empty _))
    evalGuard cgGuard a env = false := by
  intro a va_val
  cases a <;> cases va_val <;>
    (simp [cgGuard, evalGuard, evalExpr, simpleExpr, BindTy.base]; rfl)

/-! ### The well-formed-program bundle

Having proven `WF`, `NormalizedDists`, and `Legal` individually above, we can
assemble them into a `WFProgram` bundle. This is the object that downstream
game-theory APIs (`toKernelGame`, `IsNash`, `IsεNash`, etc.) consume. -/

/-- Matching Pennies as a `WFProgram`: program + empty initial environment +
the three well-formedness witnesses. -/
noncomputable def matchingPenniesWF :
    WFProgram Player simpleExpr where
  Γ := Γ0
  prog := matchingPennies
  env := VEnv.empty simpleExpr
  wf := ⟨by decide, by decide, by
    constructor
    · intro x hx
      exact Finset.mem_insert_of_mem hx
    · constructor
      · intro x hx
        exfalso
        change x ∈ (∅ : Finset VarId) at hx
        simp at hx
      · trivial⟩
  normalized := by simp [matchingPennies, NormalizedDists]
  legal := by
    constructor
    · intro _env
      exact ⟨true, by rfl⟩
    · constructor
      · intro _env
        exact ⟨true, by rfl⟩
      · trivial

end Examples

end Vegas

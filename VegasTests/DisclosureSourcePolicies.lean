/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import VegasTests.OptionalDisclosure

/-! # Written-order policies for the optional-disclosure source -/

noncomputable section

namespace VegasTests.OptionalDisclosure.SourcePolicies

open Vegas GameTheory.Math.Probability

private def beforeCommit {Γ : VCtx TestPlayer simpleExpr} {x : VarId} {actor : TestPlayer}
    {b : BaseTy} {guard : Expr ((x, b) :: eraseVCtx (viewVCtx actor Γ)) .bool}
    {tail : VegasCore TestPlayer simpleExpr ((x, .sealed actor b) :: Γ)}
    (choose : (visible : Env Val (eraseVCtx (viewVCtx actor Γ))) →
      FinDist {value : Val b // evalGuard (L := simpleExpr) guard value visible = true})
    (profile : SourceBehavioralProfile tail) :
    SourceBehavioralProfile (.commit x actor guard tail) := by
  intro who Δ y ty guard' site
  cases site with
  | here => exact choose
  | commit site => exact profile who site

private def beforeReveal {Γ : VCtx TestPlayer simpleExpr} {x y : VarId}
    {actor : TestPlayer} {b : BaseTy} {source : VHasVar Γ x (.sealed actor b)}
    {tail : VegasCore TestPlayer simpleExpr ((y, .pub b) :: Γ)}
    (profile : SourceBehavioralProfile tail) :
    SourceBehavioralProfile (.reveal y actor x source tail) := by
  intro who Δ z ty guard site
  cases site with
  | reveal site => exact profile who site

private def beforeSample {Γ : VCtx TestPlayer simpleExpr} {x : VarId} {b : BaseTy}
    {dist : DistExpr (erasePubVCtx Γ) b}
    {tail : VegasCore TestPlayer simpleExpr ((x, .pub b) :: Γ)}
    (profile : SourceBehavioralProfile tail) :
    SourceBehavioralProfile (.sample x dist tail) := by
  intro who Δ z ty guard site
  cases site with
  | sample site => exact profile who site

private def atReturn {Γ : VCtx TestPlayer simpleExpr}
    (payouts : List (TestPlayer × Expr (erasePubVCtx Γ) .int)) :
    SourceBehavioralProfile (L := simpleExpr) (.ret payouts) := by
  intro who Δ z ty guard site
  cases site

private theorem beforeCommit_here {Γ : VCtx TestPlayer simpleExpr} {x : VarId}
    {actor : TestPlayer} {b : BaseTy}
    {guard : Expr ((x, b) :: eraseVCtx (viewVCtx actor Γ)) .bool}
    {tail : VegasCore TestPlayer simpleExpr ((x, .sealed actor b) :: Γ)}
    (choose : (visible : Env Val (eraseVCtx (viewVCtx actor Γ))) →
      FinDist {value : Val b // evalGuard (L := simpleExpr) guard value visible = true})
    (profile : SourceBehavioralProfile tail) :
    beforeCommit choose profile actor (.here guard tail) = choose := by
  rfl

private theorem afterCommit_beforeCommit {Γ : VCtx TestPlayer simpleExpr} {x : VarId}
    {actor : TestPlayer} {b : BaseTy}
    {guard : Expr ((x, b) :: eraseVCtx (viewVCtx actor Γ)) .bool}
    {tail : VegasCore TestPlayer simpleExpr ((x, .sealed actor b) :: Γ)}
    (choose : (visible : Env Val (eraseVCtx (viewVCtx actor Γ))) →
      FinDist {value : Val b // evalGuard (L := simpleExpr) guard value visible = true})
    (profile : SourceBehavioralProfile tail) :
    (beforeCommit choose profile).afterCommit = profile := by
  rfl

private theorem afterReveal_beforeReveal {Γ : VCtx TestPlayer simpleExpr} {x y : VarId}
    {actor : TestPlayer} {b : BaseTy} {source : VHasVar Γ x (.sealed actor b)}
    {tail : VegasCore TestPlayer simpleExpr ((y, .pub b) :: Γ)}
    (profile : SourceBehavioralProfile tail) :
    (beforeReveal (source := source) profile).afterReveal = profile := by
  rfl

private theorem afterSample_beforeSample {Γ : VCtx TestPlayer simpleExpr} {x : VarId}
    {b : BaseTy} {dist : DistExpr (erasePubVCtx Γ) b}
    {tail : VegasCore TestPlayer simpleExpr ((x, .pub b) :: Γ)}
    (profile : SourceBehavioralProfile tail) :
    (beforeSample (dist := dist) profile).afterSample = profile := by
  rfl

def pureProfile (payouts : List (TestPlayer × Expr PayoffContext .int))
    (secret : Bool) (complete : Bool → Bool → Bool)
    (response : Bool → Option Bool → Bool) :
    SourceBehavioralProfile (coreWithPayoffs payouts) := by
  unfold coreWithPayoffs
  apply beforeCommit (fun _ => FinDist.pure ⟨secret, rfl⟩)
  apply beforeCommit (fun _ => FinDist.pure ⟨false, rfl⟩)
  apply beforeReveal
  apply beforeSample
  refine beforeCommit ?_ ?_
  · intro visible
    let bound : Bool := visible.get (.there (.there (.there .here)))
    let signal : Bool := visible.get .here
    let opening := if complete bound signal then some bound else none
    refine FinDist.pure ⟨opening, ?_⟩
    change (if opening.isNone then true else decide (opening = some bound)) = true
    cases h : complete bound signal <;> simp [opening, h]
  apply beforeReveal
  refine beforeCommit ?_ ?_
  · exact fun visible => FinDist.pure
      ⟨response (visible.get (.there .here)) (visible.get .here), rfl⟩
  apply beforeReveal
  exact atReturn (Γ := TerminalContext) payouts

theorem pure_law (payouts : List (TestPlayer × Expr PayoffContext .int))
    (secret : Bool) (complete : Bool → Bool → Bool)
    (response : Bool → Option Bool → Bool) :
    denoteSource (coreWithPayoffs payouts) (pureProfile payouts secret complete response)
        (VEnv.empty simpleExpr) =
      fairCoin.denote.map fun signal =>
        let opening := if complete secret signal then some secret else none
        terminalEnv secret signal opening (response signal opening) := by
  simp only [pureProfile, coreWithPayoffs, denoteSource, id_eq,
    beforeCommit_here, afterCommit_beforeCommit, afterReveal_beforeReveal,
    afterSample_beforeSample, FinDist.pure_bind]
  change (if false then fairCoin.denote else fairCoin.denote).bind
    (fun signal => FinDist.pure
      (terminalEnv secret signal (if complete secret signal then some secret else none)
        (response signal (if complete secret signal then some secret else none)))) = _
  simp only [Bool.false_eq_true, ↓reduceIte, FinDist.map_eq_bind]

end VegasTests.OptionalDisclosure.SourcePolicies

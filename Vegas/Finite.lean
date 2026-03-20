import Vegas.Strategies

/-!
# Finite Infrastructure

Finite-enumeration instances for Vegas environments under `FiniteValuation`.

This file intentionally stops at environments. The current global strategy
types in `Vegas.Strategies` quantify over all commit sites in all contexts, so
their finiteness does not follow from `FiniteValuation` alone.
-/

namespace Vegas

namespace Env

noncomputable instance instFintype
    {L : IExpr} (LF : FiniteValuation L) :
    {Γ : Ctx L.Ty} → Fintype (Env L.Val Γ)
  | [] =>
      let e : Env L.Val [] ≃ Unit :=
        { toFun := fun _ => ()
          invFun := fun _ => Env.empty L.Val
          left_inv := by
            intro env
            funext x τ h
            nomatch h
          right_inv := by
            intro u
            cases u
            rfl }
      Fintype.ofEquiv Unit e.symm
  | (x, τ) :: Γ =>
      let _ : Fintype (L.Val τ) := LF.fintypeVal τ
      let _ : Fintype (Env L.Val Γ) := instFintype LF
      let e : Env L.Val ((x, τ) :: Γ) ≃ (L.Val τ × Env L.Val Γ) :=
        { toFun := fun env => (env x τ .here, fun y σ h => env y σ (.there h))
          invFun := fun ve => Env.cons ve.1 ve.2
          left_inv := by
            intro env
            funext y σ h
            cases h with
            | here => rfl
            | there h' => rfl
          right_inv := by
            intro ve
            cases ve
            rfl }
      Fintype.ofEquiv (L.Val τ × Env L.Val Γ) e.symm

end Env

end Vegas

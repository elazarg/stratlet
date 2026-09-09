/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import Vegas.Foundation.Env

/-!
# Extending a visible environment

A full environment supplies values for bindings hidden from a player.  Any
environment on that player's visible subcontext can therefore replace the
visible part of the full environment while the latter supplies the hidden
part.  This is a proof-facing extension result; it does not evaluate a program
or introduce an operational store.
-/

namespace Vegas

namespace VEnv

/-- A prescribed player view extends to the full context when a baseline full
environment supplies values for the hidden bindings. Distinct variable names
make environment values independent of the intrinsic membership witness. -/
theorem exists_toView_eq {Player : Type} [DecidableEq Player] {L : IExpr}
    {Γ : VCtx Player L} (who : Player) (baseline : VEnv L Γ)
    (viewNodup : ((viewVCtx who Γ).map Prod.fst).Nodup)
    (visible : VEnv L (viewVCtx who Γ)) :
    ∃ full : VEnv L Γ, full.toView who = visible := by
  classical
  let full : VEnv L Γ := fun x τ binding =>
    if h : ∃ visibleBinding : VHasVar (viewVCtx who Γ) x τ,
        visibleBinding.ofViewVCtx = binding then
      visible x τ h.choose
    else
      baseline x τ binding
  refine ⟨full, ?_⟩
  funext x τ binding
  have hexists : ∃ visibleBinding : VHasVar (viewVCtx who Γ) x τ,
      visibleBinding.ofViewVCtx = binding.ofViewVCtx :=
    ⟨binding, rfl⟩
  simp only [VEnv.toView, full]
  rw [dif_pos hexists]
  congr 1
  exact HasVar.eq_of_nodup viewNodup _ _

end VEnv

end Vegas

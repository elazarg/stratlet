/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import Vegas.Core.ExprSimple
import Vegas.Core.Finite

/-!
# Finite environment regressions

The generic finite-context infrastructure enumerates both plain and
visibility-aware environments, including the empty context.
-/

namespace VegasTests.CoreFinite

open Vegas
abbrev BoolCtx : Ctx simpleExpr.Ty := [(0, .bool)]

abbrev VisibleBoolCtx : VCtx (Fin 2) simpleExpr :=
  [(0, .sealed 1 .bool)]

noncomputable local instance emptyEnvFintype :
    Fintype (Env simpleExpr.Val ([] : Ctx simpleExpr.Ty)) :=
  Env.instFintypeOfProof (L := simpleExpr) .nil

noncomputable local instance boolEnvFintype :
    Fintype (Env simpleExpr.Val BoolCtx) :=
  Env.instFintypeOfProof (L := simpleExpr)
    (.cons finiteType_bool .nil)

noncomputable local instance emptyVEnvFintype :
    Fintype (VEnv (Player := Fin 2) simpleExpr ([] : VCtx (Fin 2) simpleExpr)) :=
  VEnv.instFintypeOfProof (Player := Fin 2) (L := simpleExpr) .nil

noncomputable local instance visibleBoolEnvFintype :
    Fintype (VEnv simpleExpr VisibleBoolCtx) :=
  VEnv.instFintypeOfProof (Player := Fin 2) (L := simpleExpr)
    (.cons finiteType_bool .nil)

noncomputable example : Fintype (Env simpleExpr.Val ([] : Ctx simpleExpr.Ty)) :=
  inferInstance

noncomputable example : Fintype (Env simpleExpr.Val BoolCtx) :=
  inferInstance

example : Fintype.card (Env simpleExpr.Val ([] : Ctx simpleExpr.Ty)) = 1 := by
  rw [Fintype.card_congr (Env.emptyEquivUnit (L := simpleExpr))]
  simp

example : Fintype.card (Env simpleExpr.Val BoolCtx) = 2 := by
  calc
    _ = Fintype.card (Bool × Env simpleExpr.Val []) :=
      Fintype.card_congr
        (Env.consEquiv (L := simpleExpr) (Γ := []) (x := 0) (τ := .bool))
    _ = Fintype.card (Bool × Unit) :=
      Fintype.card_congr
        (Equiv.prodCongr (Equiv.refl Bool)
          (Env.emptyEquivUnit (L := simpleExpr)))
    _ = 2 := by simp

noncomputable example :
    Fintype (VEnv (Player := Fin 2) simpleExpr ([] : VCtx (Fin 2) simpleExpr)) :=
  inferInstance

noncomputable example : Fintype (VEnv simpleExpr VisibleBoolCtx) :=
  inferInstance

example :
    Fintype.card
        (VEnv (Player := Fin 2) simpleExpr ([] : VCtx (Fin 2) simpleExpr)) = 1 := by
  rw [Fintype.card_congr
    (VEnv.emptyEquivUnit (Player := Fin 2) (L := simpleExpr))]
  simp

example : Fintype.card (VEnv simpleExpr VisibleBoolCtx) = 2 := by
  calc
    _ = Fintype.card (Bool × VEnv (Player := Fin 2) simpleExpr []) :=
      Fintype.card_congr
        (VEnv.consEquiv (Player := Fin 2) (L := simpleExpr) (Γ := [])
          (x := 0) (τ := .sealed 1 .bool))
    _ = Fintype.card (Bool × Unit) :=
      Fintype.card_congr
        (Equiv.prodCongr (Equiv.refl Bool)
          (VEnv.emptyEquivUnit (Player := Fin 2) (L := simpleExpr)))
    _ = 2 := by simp

end VegasTests.CoreFinite

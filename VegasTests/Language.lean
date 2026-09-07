/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import Vegas.Language

/-! Focused regression tests for the typed surface-to-core translation. -/

namespace VegasTests.Language

open Vegas

def letProgram : VegasLang (Fin 1) [] :=
  .letExpr 0 (.constInt 7) (.ret [(0, .var 0 .here)])

/-- Administrative lets are substituted and do not create core events. -/
theorem lower_letProgram :
    VegasLang.lower letProgram =
      (VegasCore.ret [(0, .constInt 7)] : VegasCore (Fin 1) simpleExpr []) := by
  rfl

def yieldProgram : VegasLang (Fin 1) [] :=
  .yield 0 1 0
    (Expr.constBool true : Expr [(0, .bool)] .bool)
    (.ret [])

/-- A yield is concretely a nullable commitment followed by its public reveal. -/
theorem lower_yieldProgram :
    VegasLang.lower yieldProgram =
      (VegasCore.commit 0 0
        (Expr.nullableCommitGuard
          (Expr.constBool true : Expr [(0, .bool)] .bool))
        (.reveal 1 0 0 .here (.ret [])) :
          VegasCore (Fin 1) simpleExpr []) := by
  rfl

/-- The synthesized decline remains legal even when the source guard rejects
every ordinary value. -/
theorem rejecting_yield_still_allows_none :
    evalGuard (Player := Fin 1) (L := simpleExpr)
      (Γ := ([] : VCtx (Fin 1) simpleExpr)) (b := .option .bool) (x := 0)
      (Expr.nullableCommitGuard
        (Γ := []) (x := 0) (b := .bool)
        (Expr.constBool false : Expr [(0, .bool)] .bool) :
          Expr ((0, .option .bool) ::
            eraseVCtx ([] : VCtx (Fin 1) simpleExpr)) .bool)
      (Option.none : Val (.option .bool))
      (Env.empty Val : Env Val (eraseVCtx ([] : VCtx (Fin 1) simpleExpr))) = true := by
  exact VegasLang.nullableGuard_none_legal
    (Γ := ([] : VCtx (Fin 1) simpleExpr)) (secret := 0) (b := .bool)
    (Expr.constBool false : Expr [(0, .bool)] .bool) (Env.empty Val)

end VegasTests.Language

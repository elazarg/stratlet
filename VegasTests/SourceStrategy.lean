/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import Vegas.Core.ExprSimple
import Vegas.Core.Strategy

/-! # Written-order source strategy regressions

A player commits to a bit before a fresh public fair coin is sampled. Every
source behavioral commitment law therefore guesses the later coin with
probability exactly one half.
-/

noncomputable section

namespace VegasTests.SourceStrategy

open Vegas GameTheory.Math.Probability

abbrev Player := Fin 1

def fairCoin : RationalLaw Bool where
  entries := [(false, 1 / 2), (true, 1 / 2)]
  normalized := by norm_num

abbrev guessingProgram : VegasCore Player simpleExpr [] :=
  .commit (b := .bool) 0 0 (Expr.constBool true)
    (.sample 1 (DistExpr.weighted (b := .bool) fairCoin)
      (.reveal (b := .bool) 2 0 0 (.there .here) (.ret [])))

def guessedCoin :
    VEnv simpleExpr (sourceTerminalCtx guessingProgram) → Bool :=
  fun env =>
    env 2 (.pub .bool) (by
      change VHasVar
        ([(2, .pub .bool), (1, .pub .bool), (0, .sealed 0 .bool)] :
          VCtx Player simpleExpr) 2 (.pub .bool)
      exact .here) =
    env 1 (.pub .bool) (by
      change VHasVar
        ([(2, .pub .bool), (1, .pub .bool), (0, .sealed 0 .bool)] :
          VCtx Player simpleExpr) 1 (.pub .bool)
      exact .there .here)

@[simp] theorem guessedCoin_terminal (guess coin : Bool) :
    guessedCoin
        (VEnv.cons guess
          (VEnv.cons coin
            (VEnv.cons guess (VEnv.empty simpleExpr)))) = decide (guess = coin) := by
  rfl

/-- The arbitrary commitment distribution is chosen before the independent
coin sample, so it cannot improve on one-half guessing probability. -/
theorem guessing_success_probability
    (profile : SourceBehavioralProfile guessingProgram) :
    ((denoteSource guessingProgram profile (VEnv.empty simpleExpr)).map
        guessedCoin).prob true = 1 / 2 := by
  rw [FinDist.prob_map]
  simp only [guessingProgram, denoteSource]
  rw [FinDist.expect_bind]
  calc
    _ = (profile 0 (.here _ _) ((VEnv.empty simpleExpr).toView 0).eraseEnv).expect
        (fun _ => 1 / 2) := by
          apply FinDist.expect_congr
          rintro ⟨guess, _⟩ _
          cases guess
          · simp only [IExpr.evalDist, simpleExpr, evalLawDistExpr,
              FinDist.expect_bind, FinDist.expect_pure, guessedCoin,
              VEnv.get, VEnv.cons]
            rw [FinDist.expect_eq_sum]
            simp [fairCoin, RationalLaw.prob_denote, Fin.sum_univ_two]
          · simp only [IExpr.evalDist, simpleExpr, evalLawDistExpr,
              FinDist.expect_bind, FinDist.expect_pure, guessedCoin,
              VEnv.get, VEnv.cons]
            rw [FinDist.expect_eq_sum]
            simp [fairCoin, RationalLaw.prob_denote, Fin.sum_univ_two]
    _ = 1 / 2 := FinDist.expect_const _ _

end VegasTests.SourceStrategy

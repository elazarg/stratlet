import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure

import Vegas.LetProb.WDist
import Vegas.LetProb.WDistLemmas
import Vegas.LetProb.Prob
import Vegas.LetProb.ProbLemmas

namespace Prob

open MeasureTheory ENNReal NNReal
open Prog

variable {L : Language}

/-! ## 0. Instances for Runtime Values

We define the discrete measurable space for `L.Val τ` globally.
This is necessary so that `MeasurableSpace` resolution works for intermediate
types (hidden inside `doBind`) during induction.
-/

/-!
# Measure-Transformer Semantics (Finite-Support / Discrete)

Denotation of `PProg` as measure transformers, proved correct w.r.t. `evalP`
via the existing WDist ↔ Measure bridge lemmas.
-/

/-- A measure transformer for pure-output programs: environment ↦ measure on results. -/
abbrev MT (Γ : L.Ctx) (τ : L.Ty) [MeasurableSpace (L.Val τ)] : Type :=
  L.Env Γ → Measure (L.Val τ)

namespace MT

variable {Γ : L.Ctx} {τ : L.Ty} [MeasurableSpace (L.Val τ)]

/-- Discrete integration / extension along a finite-support weighted distribution. -/
noncomputable def extendW {α : Type*}
    (d : WDist α) (k : α → MT Γ τ) : MT Γ τ :=
  fun env =>
    d.weights.foldr
      (fun (x : α × ℝ≥0) (μ : Measure (L.Val τ)) =>
        μ + (x.2 : ℝ≥0∞) • (k x.1 env))
      0

/-- `ret` transformer: Dirac at the returned value. -/
noncomputable def ret (e : L.Expr Γ τ) : MT Γ τ :=
  fun env => Measure.dirac (L.eval e env)

/-- `observe` transformer: keep or kill the measure. -/
def observe (c : L.Expr Γ L.bool) (m : MT Γ τ) : MT Γ τ :=
  fun env => if L.toBool (L.eval c env) then m env else 0

end MT

/-!
## Denotation

Important: `denote` is parameterized by *fixed* `{Γ τ}` so induction on `p`
does not generalize away the `MeasurableSpace (L.Val τ)` instance.
-/

/-- Denotational semantics into measure transformers (finite-support / discrete). -/
noncomputable def denote
    {Γ : L.Ctx} {τ : L.Ty} [MeasurableSpace (L.Val τ)] :
    PProg Γ τ → MT Γ τ
  | .ret e =>
      MT.ret e
  | .letDet e k =>
      fun env => denote k (L.eval e env, env)
  | .doStmt (.observe c) k =>
      MT.observe c (denote k)
  | .doBind (.sample K) k =>
      fun env =>
        MT.extendW (d := K env)
          (fun v env' => denote k (v, env')) env

section Correctness

local instance instMeasurableSpaceVal (τ : L.Ty) : MeasurableSpace (L.Val τ) := ⊤

theorem evalP_eq_denote :
  ∀ {Γ : L.Ctx} {τ : L.Ty}
    (p : PProg Γ τ) (env : L.Env Γ),
    (evalP p env).toMeasure = denote p env := by
  intro Γ τ p env
  induction p with
  | ret e =>
      -- now both sides use the *same* MeasurableSpace instance (the global ⊤ one)
      simpa [denote, MT.ret] using (toMeasure_evalP_ret (e := e) (env := env))
  | letDet e k ih =>
      simpa [denote, evalP, Prog.evalWith_letDet] using
        ih (env := (L.eval e env, env))
  | doStmt s k ih =>
      cases s with
      | observe c =>
          by_cases h : L.toBool (L.eval c env)
          · -- true
            simp [denote, MT.observe, h, ih]
          · -- false
            simp [denote, MT.observe, h, WDist.zero, WDist.toMeasure]
  | doBind c k ih =>
      cases c with
      | sample K =>
          -- convert LHS to foldr form
          have h_eval :
              (evalP (.doBind (.sample K) k) env).toMeasure =
                (K env).weights.foldr
                  (fun (vw : (L.Val _ × ℝ≥0)) μ =>
                    μ + (vw.2 : ℝ≥0∞) • (evalP k (vw.1, env)).toMeasure)
                  0 := by
            simpa using (toMeasure_evalP_sample (K := K) (k := k) (env := env))
          -- put goal in the same "foldr" shape as RHS
          rw [h_eval]
          -- unfold RHS denote/doBind/extendW
          simp only [denote, MT.extendW]
          -- now rewrite the integrand pointwise using ih, by induction over the list
          induction (K env).weights with
          | nil =>
              simp
          | cons head tail ihTail =>
              rcases head with ⟨v, w⟩
              have hk :
                  (evalP k (v, env)).toMeasure = denote k (v, env) := by
                simpa using (ih (env := (v, env)))
              simp [hk, ihTail, add_comm]

end Correctness

end Prob

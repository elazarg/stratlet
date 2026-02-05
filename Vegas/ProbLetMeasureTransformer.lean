import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure

import Vegas.WDist
import Vegas.WDistLemmas
import Vegas.ProbLet
import Vegas.ProbLetLemmas

namespace ProbLet

open MeasureTheory ENNReal NNReal
/-! ## 0. Instances for Runtime Values
We define the discrete measurable space for `Val τ` globally.
This is necessary so that `MeasurableSpace` resolution works for
intermediate types (hidden inside `doBind`) during induction.
-/

instance instMeasurableSpaceVal (τ : Ty) : MeasurableSpace (Val τ) := ⊤

instance instMeasurableSingletonClassVal (τ : Ty) : MeasurableSingletonClass (Val τ) :=
  ⟨fun _ => trivial⟩

/-!
# Measure-Transformer Semantics (Finite-Support / Discrete)

Denotation of `PProg` as measure transformers, proved correct w.r.t. `evalP`
via the existing WDist ↔ Measure bridge lemmas.
-/

/-- A measure transformer for pure-output programs: environment ↦ measure on results. -/
abbrev MT (Γ : Ctx) (τ : Ty) (ms : MeasurableSpace (Val τ)) : Type :=
  Env Γ → @MeasureTheory.Measure (Val τ) ms

namespace MT
variable {Γ : Ctx} {τ : Ty}
variable {ms : MeasurableSpace (Val τ)}

noncomputable def extendW {α : Type*} (d : WDist α) (k : α → MT Γ τ ms) : MT Γ τ ms :=
  fun env =>
    d.weights.foldr
      (fun (x : α × ℝ≥0) (μ : Measure (Val τ)) =>
        μ + (x.2 : ENNReal) • (k x.1 env))
      0

/-- `ret` transformer: Dirac at the returned value. -/
noncomputable def ret (e : Expr Γ τ) : MT Γ τ ms :=
  fun env => Measure.dirac (evalExpr e env)

/-- `observe` transformer: keep or kill the measure. -/
def observe (c : Expr Γ .bool) (m : MT Γ τ ms) : MT Γ τ ms :=
  fun env => if evalExpr c env then m env else 0

end MT

/-!
## Denotation
Important: `denote` is parameterized by *fixed* `{Γ τ}` so induction on `p`
does not generalize away the `MeasurableSpace (Val τ)` instance.
-/

/-- Denotational semantics into measure transformers (finite-support / discrete). -/
noncomputable def denote {Γ : Ctx} {τ : Ty} {ms : MeasurableSpace (Val τ)} : PProg Γ τ → MT Γ τ ms
  | .ret e =>
      MT.ret  e
  | .letDet e k =>
      fun env => denote k (evalExpr e env, env)
  | .doStmt (.observe c) k =>
      MT.observe c (denote k)
  | .doBind (.sample K) k =>
      fun env =>
        MT.extendW (d := K env)
          (fun v => fun env' => denote k (v, env') ) env

section Correctness

theorem evalP_eq_denote :
    ∀ {Γ : Ctx} {τ : Ty}
      {p : PProg Γ τ} {env : Env Γ},
      (evalP p env).toMeasure = denote p env := by
  intro Γ τ p env
  induction p with
  | ret e =>
      -- now `inst` is `MeasurableSpace (Val τ)` for THIS branch's τ
      -- and simp/bridge lemmas typecheck.
      simpa [denote, MT.ret] using (toMeasure_evalP_ret e env)
  | letDet e k ih =>
      simpa [denote, evalP, ProgCore.evalWith_letDet] using
        ih (env := (evalExpr e env, env))
  | doStmt s k ih =>
    cases s with
    | observe c =>
      -- goal: (evalP (doStmt (observe c) k) env).toMeasure = denote (doStmt (observe c) k) env
      -- after unfolding denote it is MT.observe c (denote k) env,
      -- i.e. if evalExpr c env then denote k env else 0
      simp [denote, MT.observe]  -- makes RHS: if evalExpr c env then denote k env else 0
      -- now use your observe bridge on the LHS
      -- but it produces "if ... then (evalP k env).toMeasure else 0"
      -- so split on the condition and use ih in the true branch
      by_cases h : evalExpr c env
      · -- true branch
        -- LHS becomes (evalP k env).toMeasure, RHS becomes denote k env
        simpa [evalP_observe, h] using ih
      · -- false branch
        -- both sides become 0
        simp_all only [Bool.not_eq_true, Bool.false_eq_true, ↓reduceIte]
        rfl
  | doBind c k ih =>
    cases c with
      | sample K =>
          -- now τ' is a real identifier you can refer to
          have h_eval :
              (evalP (.doBind (.sample K) k) env).toMeasure =
                (K env).weights.foldr
                  (fun vw μ =>
                    μ + (vw.2 : ENNReal) • (evalP k (vw.1, env)).toMeasure)
                  0 := by
            -- if your lemma expects τ' explicitly, pass it:
            simpa using (toMeasure_evalP_sample (K := K) (k := k) (env := env))
          rw [h_eval]
          simp only [denote, MT.extendW]
          induction (K env).weights with
          | nil =>
              simp
          | cons head tail ihTail =>
              rcases head with ⟨v, w⟩
              have hk : (evalP k (v, env)).toMeasure = denote k (v, env) :=
                ih (env := (v, env))
              simp [hk, ihTail, add_comm]

end Correctness

end ProbLet

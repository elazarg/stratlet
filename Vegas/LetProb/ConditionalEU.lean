import Mathlib.Data.Real.Basic
import Mathlib.Data.NNReal.Basic
import Vegas.LetProb.WDist
import Vegas.LetProb.WDistLemmas

/-!
# Expected Value under Weighted Distributions

Generic expected value (`EV`) and conditional expected value (`EV_cond`)
for `WDist`, factoring out the EU computation from `Proto.lean` into a
reusable, type-generic form.
-/

namespace WDist

open NNReal

variable {α β : Type*}

/-- Expected value of a real-valued function under a weighted distribution.
    Computes `Σ (a,w) ∈ d.weights, w * f a`. -/
noncomputable def EV (d : WDist α) (f : α → ℝ) : ℝ :=
  d.weights.foldr (fun (aw : α × ℝ≥0) acc => acc + ((aw.2 : ℝ) * f aw.1)) 0

/-- Conditional expected value: normalize by mass. Returns 0 when mass = 0. -/
noncomputable def EV_cond (d : WDist α) (f : α → ℝ) : ℝ :=
  if d.mass = 0 then 0 else d.EV f / (d.mass : ℝ)

/-! ## Basic EV lemmas -/

@[simp]
theorem EV_pure (x : α) (f : α → ℝ) : (WDist.pure x).EV f = f x := by
  simp [EV, WDist.pure, one_mul]

@[simp]
theorem EV_zero (f : α → ℝ) : (WDist.zero : WDist α).EV f = 0 := by
  simp [EV, WDist.zero]

theorem EV_cond_eq_EV_div_mass {d : WDist α} {f : α → ℝ} (h : d.mass ≠ 0) :
    d.EV_cond f = d.EV f / (d.mass : ℝ) := by
  simp [EV_cond, h]

theorem EV_cond_of_mass_one {d : WDist α} {f : α → ℝ} (h : d.mass = 1) :
    d.EV_cond f = d.EV f := by
  simp [EV_cond, h]

/-! ## The tower property: EV distributes over bind -/

/-- Helper: EV over concatenated weight lists. -/
private theorem EV_mk_append (ws₁ ws₂ : List (α × ℝ≥0)) (f : α → ℝ) :
    (WDist.mk (ws₁ ++ ws₂)).EV f =
      (WDist.mk ws₁).EV f + (WDist.mk ws₂).EV f := by
  simp only [EV]
  induction ws₁ with
  | nil => simp
  | cons h t ih =>
    simp only [List.cons_append, List.foldr_cons, ih]
    ring

/-- Helper: EV over scaled weight list. -/
private theorem EV_mk_map_scale (c : ℝ≥0) (ws : List (α × ℝ≥0)) (f : α → ℝ) :
    (WDist.mk (ws.map (fun (a, w') => (a, c * w')))).EV f =
      (c : ℝ) * (WDist.mk ws).EV f := by
  simp only [EV]
  induction ws with
  | nil => simp
  | cons h t ih =>
    rcases h with ⟨a, w⟩
    simp only [List.map_cons, List.foldr_cons, ih]
    push_cast
    ring

/-- The tower property: `EV (bind d g) f = EV d (fun a => EV (g a) f)`.
    This is the key compositional property for expected values. -/
theorem EV_bind (d : WDist α) (g : α → WDist β) (f : β → ℝ) :
    (d.bind g).EV f = d.EV (fun a => (g a).EV f) := by
  cases d with
  | mk ws =>
    induction ws with
    | nil => simp [EV, WDist.bind]
    | cons head tail ih =>
      rcases head with ⟨a, w⟩
      -- Use the append and scale helpers
      have h1 : (WDist.bind (WDist.mk ((a, w) :: tail)) g).EV f
          = (WDist.mk (((g a).weights.map (fun bw => (bw.1, w * bw.2)))
              ++ (WDist.bind (WDist.mk tail) g).weights)).EV f := by
            unfold EV; congr 1
      have h2 := EV_mk_append ((g a).weights.map (fun bw => (bw.1, w * bw.2)))
                   (WDist.bind (WDist.mk tail) g).weights f
      have h3 := EV_mk_map_scale w (g a).weights f
      rw [h1, h2, h3, ih]
      simp [EV, add_comm]

end WDist

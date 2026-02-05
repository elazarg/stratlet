import Vegas.WDist
import Mathlib.Data.List.Basic
import Mathlib.Data.NNReal.Basic

namespace WDist

open MeasureTheory ENNReal NNReal

variable {α β γ : Type*}

@[simp] lemma mk_weights {ws : List (α × ℝ≥0)} :
  (WDist.mk ws).weights = ws := rfl

theorem ext_weights {d₁ d₂ : WDist α} (h : d₁.weights = d₂.weights) :
    d₁ = d₂ := by
  cases d₁
  cases d₂
  cases h
  rfl

/-! ## Monad laws -/

/-- Right identity: `bind m pure = m` (definitionally, for this list representation). -/
theorem bind_pure_right (m : WDist α) :
    bind m pure = m := by
  cases m with
  | mk ws =>
    cases ws with
    | nil =>
        simp [WDist.bind, WDist.pure]
    | cons head tail =>
        rcases head with ⟨a, w⟩
        simp [WDist.bind, WDist.pure, mul_one]

/-- Left identity: `bind (pure a) f = f a` (you already have `[simp]` as `bind_pure`). -/
theorem bind_pure_left (a : α) (f : α → WDist β) :
    bind (pure a) f = f a := by
  simp

/-- Associativity of bind. -/
theorem bind_assoc (m : WDist α) (f : α → WDist β) (g : β → WDist γ) :
    bind (bind m f) g = bind m (fun x => bind (f x) g) := by
  cases m with
  | mk ws =>
    apply ext_weights
    simp only [bind]
    induction ws with
    | nil => simp
    | cons head tail ih =>
        rcases head with ⟨a, w⟩
        simp only [List.flatMap_cons, List.flatMap_append]
        congr 1
        · -- head: scale-flatMap commutativity, by inner induction on (f a).weights
          induction (f a).weights with
          | nil => simp
          | cons bhead btail bih =>
              rcases bhead with ⟨b, w'⟩
              simp only [List.map_cons, List.flatMap_cons, List.map_append, List.map_map, mul_assoc]
              congr 1

/-! ## Zero / failure laws -/

/-- Left zero: `bind zero f = zero` (you already have `[simp]` as `bind_zero`). -/
theorem bind_zero_left (f : α → WDist β) :
    bind (zero : WDist α) f = (zero : WDist β) := by
  simp

/-- Right zero: `bind m (fun _ => zero) = zero`. -/
theorem bind_zero_right (m : WDist α) :
    bind m (fun _ => (zero : WDist β)) = (zero : WDist β) := by
  cases m with
  | mk ws =>
    apply ext_weights
    induction ws with
    | nil =>
        simp [WDist.bind, WDist.zero]
    | cons head tail ih =>
        rcases head with ⟨a, w⟩
        simp [WDist.bind, WDist.zero]

/-! ## Mass properties -/

/-- Mass of `pure` is 1. -/
theorem mass_pure (a : α) : mass (pure a) = 1 := by
  simp [WDist.mass, WDist.pure]

/-- Mass of `zero` is 0. -/
theorem mass_zero : mass (zero : WDist α) = 0 := by
  simp [WDist.mass, WDist.zero]

/-- A convenient closed form for `mass` of `bind`:
`mass (bind d f) = Σ (a,w)∈d.weights, w * mass (f a)`. -/
theorem mass_bind (d : WDist α) (f : α → WDist β) :
    mass (bind d f) =
      (d.weights.map (fun aw => aw.2 * mass (f aw.1))).sum := by
  cases d with
  | mk ws =>
    induction ws with
    | nil =>
        simp [WDist.bind, WDist.mass]
    | cons head tail ih =>
        rcases head with ⟨a, w⟩
        -- key lemma: sum of snd after scaling weights by w
        have hscale :
            (((f a).weights.map (fun bw => (bw.1, w * bw.2))).map Prod.snd).sum
              = w * ((f a).weights.map Prod.snd).sum := by
          induction (f a).weights with
          | nil => simp
          | cons h t iht =>
              rcases h with ⟨b, w'⟩
              simp [mul_add]
              simp_all only [List.map_map]
        -- now unfold mass/bind at the head and use `ih` on the tail
        simp only [mass, bind, List.flatMap_cons, List.map_append, List.map_map, List.sum_append,
          List.map_cons, List.sum_cons]
        simp_all only [List.map_map, _root_.add_right_inj]
        exact ih

/-- Mass is multiplicative under bind when the continuation has constant mass. -/
theorem mass_bind_const (m : WDist α) (f : α → WDist β) (w : ℝ≥0)
    (hf : ∀ a, mass (f a) = w) :
    mass (bind m f) = mass m * w := by
  -- start from mass_bind
  rw [mass_bind (d := m) (f := f)]
  cases m with
  | mk ws =>
    -- rewrite each term using hf
    have : (ws.map (fun aw => aw.2 * mass (f aw.1))).sum
          = (ws.map (fun aw => aw.2 * w)).sum := by
      apply congrArg List.sum
      apply List.map_congr_left
      intro aw
      rcases aw with ⟨a, wa⟩
      simp [hf]
    -- now factor w out: Σ (wa*w) = (Σ wa) * w
    have hfactor :
        (ws.map (fun aw => aw.2 * w)).sum = (ws.map Prod.snd).sum * w := by
      induction ws with
      | nil =>
          simp
      | cons h t iht =>
          rcases h with ⟨a, wa⟩
          simp [add_mul]
          simp_all only [forall_const, List.map_cons, List.sum_cons]
    simp only [mass]
    calc
      (ws.map (fun aw => aw.2 * mass (f aw.1))).sum
          = (ws.map (fun aw => aw.2 * w)).sum := this
      _   = (ws.map Prod.snd).sum * w := hfactor

/-! ## Observe / conditioning laws -/

/-- A “guard” distribution: succeed with `()` if `b`, else fail. -/
def guard (b : Bool) : WDist Unit :=
  if b then pure () else zero

theorem guard_true : guard true = pure () := by
  simp [guard]

theorem guard_false : guard false = (zero : WDist Unit) := by
  simp [guard]

theorem bind_guard (b : Bool) (k : Unit → WDist α) :
    bind (guard b) k = if b then k () else zero := by
  simp [guard]
  by_cases hb : b <;> simp [hb]

/-- `observe` never increases computational mass. -/
theorem mass_observe_le (p : α → Bool) (d : WDist α) :
    mass (observe p d) ≤ mass d := by
  cases d with
  | mk ws =>
    induction ws with
    | nil =>
        simp [WDist.mass, WDist.observe]
    | cons head tail ih =>
        rcases head with ⟨a, w⟩
        by_cases hp : p a = true
        · -- kept
          simp only [mass, observe, hp, List.filter_cons_of_pos, List.map_cons,
                     List.sum_cons, add_le_add_iff_left]
          exact ih
        · -- dropped
          -- LHS = mass(observe tail) ≤ mass(tail) ≤ w + mass(tail) = RHS
          simp only [mass, observe, hp, Bool.false_eq_true, not_false_eq_true,
            List.filter_cons_of_neg, List.map_cons, List.sum_cons]
          exact le_add_of_le_right ih


/-! ## Scale laws (if you still want them) -/

/-- Scale all weights by a constant factor. -/
def scale (c : ℝ≥0) (d : WDist α) : WDist α :=
  { weights := d.weights.map (fun aw => (aw.1, c * aw.2)) }

theorem scale_one (xs : WDist α) : scale 1 xs = xs := by
  cases xs with
  | mk ws =>
    apply ext_weights
    simp [scale]

theorem mass_scale (c : ℝ≥0) (xs : WDist α) :
    mass (scale c xs) = c * mass xs := by
  cases xs with
  | mk ws =>
    -- unfold mass/scale before induction so ih matches the goal form
    simp only [mass, scale]
    induction ws with
    | nil => simp
    | cons head tail ih =>
        rcases head with ⟨a, w⟩
        simp only [List.map_cons, List.sum_cons, mul_add]
        congr 1

theorem mass_scale_zero (xs : WDist α) : mass (scale 0 xs) = 0 := by
  simp [mass_scale]

/-- Scaling commutes with bind (left scaling). -/
theorem scale_bind (c : ℝ≥0) (m : WDist α) (f : α → WDist β) :
    scale c (bind m f) = bind (scale c m) f := by
  cases m with
  | mk ws =>
    apply ext_weights
    induction ws with
    | nil =>
        simp [WDist.bind, scale]
    | cons head tail ih =>
        rcases head with ⟨a, w⟩
        -- unfold bind/scale; head part aligns by `mul_assoc`, tail by `ih`
        simp only [scale, bind, List.flatMap_cons, List.map_append, List.map_map, List.map_cons,
          mul_assoc]
        exact
          (List.append_right_inj
                (List.map ((fun aw ↦ (aw.1, c * aw.2)) ∘ fun x ↦ (x.1, w * x.2)) (f a).weights)).mpr
            ih

end WDist

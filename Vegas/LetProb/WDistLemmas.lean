import Mathlib.Data.List.Basic

import Vegas.LetProb.WDist

namespace WDist

open MeasureTheory ENNReal NNReal

/-! ## Algebraic lemmas -/

section Algebraic

variable {W : Type*} [WeightModel W] {α β γ : Type*}

omit [WeightModel W] in
@[simp] lemma mk_weights {ws : List (α × W)} :
  (WDist.mk ws).weights = ws := rfl

omit [WeightModel W] in
theorem ext_weights {d₁ d₂ : WDist W α} (h : d₁.weights = d₂.weights) :
    d₁ = d₂ := by
  cases d₁
  cases d₂
  cases h
  rfl

/-! ## Monad laws -/

/-- Right identity: `bind m pure = m` (definitionally, for this list representation). -/
theorem bind_pure_right (m : WDist W α) : bind m pure = m := by
  cases m with
  | mk ws =>
    apply ext_weights
    simp [WDist.bind, WDist.pure, mul_one]

/-- Left identity: `bind (pure a) f = f a`. -/
theorem bind_pure_left (a : α) (f : α → WDist W β) :
    bind (pure a) f = f a := by
  simp

/-- Associativity of bind. -/
theorem bind_assoc (m : WDist W α) (f : α → WDist W β) (g : β → WDist W γ) :
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

/-- Left zero: `bind zero f = zero`. -/
theorem bind_zero_left (f : α → WDist W β) :
    bind (zero : WDist W α) f = (zero : WDist W β) := by
  simp

/-- Right zero: `bind m (fun _ => zero) = zero`. -/
theorem bind_zero_right (m : WDist W α) :
    bind m (fun _ => (zero : WDist W β)) = (zero : WDist W β) := by
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
theorem mass_pure (a : α) : mass (pure a : WDist W α) = 1 := by
  simp [WDist.mass, WDist.pure]

/-- Mass of `zero` is 0. -/
theorem mass_zero : mass (zero : WDist W α) = 0 := by
  simp [WDist.mass, WDist.zero]

/-- A convenient closed form for `mass` of `bind`:
`mass (bind d f) = Σ (a,w)∈d.weights, w * mass (f a)`. -/
theorem mass_bind (d : WDist W α) (f : α → WDist W β) :
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
        simp only [mass, bind, List.flatMap_cons, List.map_append, List.sum_append,
          List.map_cons, List.sum_cons]
        -- normalize the composed map to match hscale
        simp only [List.map_map] at hscale ⊢
        rw [hscale]; congr 1

/-- Mass is multiplicative under bind when the continuation has constant mass. -/
theorem mass_bind_const (m : WDist W α) (f : α → WDist W β) (c : W)
    (hf : ∀ a, mass (f a) = c) :
    mass (bind m f) = mass m * c := by
  -- start from mass_bind
  rw [mass_bind (d := m) (f := f)]
  cases m with
  | mk ws =>
    -- rewrite each term using hf
    have : (ws.map (fun aw => aw.2 * mass (f aw.1))).sum
          = (ws.map (fun aw => aw.2 * c)).sum := by
      apply congrArg List.sum
      apply List.map_congr_left
      intro aw
      rcases aw with ⟨a, wa⟩
      simp [hf]
    -- now factor c out: Σ (wa*c) = (Σ wa) * c
    have hfactor :
        (ws.map (fun aw => aw.2 * c)).sum = (ws.map Prod.snd).sum * c := by
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
          = (ws.map (fun aw => aw.2 * c)).sum := this
      _   = (ws.map Prod.snd).sum * c := hfactor

/-! ## Observe / conditioning laws -/

/-- A "guard" distribution: succeed with `()` if `b`, else fail. -/
def guard (b : Bool) : WDist W Unit :=
  if b then pure () else zero

theorem guard_true : guard (W := W) true = pure () := by
  simp [guard]

theorem guard_false : guard (W := W) false = (zero : WDist W Unit) := by
  simp [guard]

theorem bind_guard (b : Bool) (k : Unit → WDist W α) :
    bind (guard b) k = if b then k () else zero := by
  simp [guard]
  by_cases hb : b <;> simp [hb]

/-! ## Scale laws -/

/-- Scale all weights by a constant factor. -/
def scale (c : W) (d : WDist W α) : WDist W α :=
  { weights := d.weights.map (fun aw => (aw.1, c * aw.2)) }

theorem scale_one (xs : WDist W α) : scale 1 xs = xs := by
  cases xs with
  | mk ws =>
    apply ext_weights
    simp [scale]

theorem mass_scale (c : W) (xs : WDist W α) :
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

theorem mass_scale_zero (xs : WDist W α) : mass (scale (0 : W) xs) = 0 := by
  simp [mass_scale]

/-- Scaling commutes with bind (left scaling). -/
theorem scale_bind (c : W) (m : WDist W α) (f : α → WDist W β) :
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

end Algebraic

/-! ## Ordering through toReal -/

section Ordering

variable {W : Type*} [WeightModel W] {α : Type*}

/-- `observe` never increases computational mass (via `toReal`). -/
theorem mass_observe_le_toReal (p : α → Bool) (d : WDist W α) :
    WeightModel.toReal (mass (observe p d)) ≤ WeightModel.toReal (mass d) := by
  cases d with
  | mk ws =>
    simp only [mass, observe]
    induction ws with
    | nil =>
        simp
    | cons head tail ih =>
        rcases head with ⟨a, w⟩
        by_cases hp : p a = true
        · -- kept: both sides have w + ...
          simp only [hp, List.filter_cons_of_pos, List.map_cons, List.sum_cons]
          have ih' : WeightModel.toReal (List.map Prod.snd (List.filter (fun x => p x.1) tail)).sum
              ≤ WeightModel.toReal (List.map Prod.snd tail).sum := ih
          rw [WeightModel.toReal_add, WeightModel.toReal_add]
          linarith
        · -- dropped: LHS missing w, RHS has w + ...
          simp only [hp, Bool.false_eq_true, not_false_eq_true,
            List.filter_cons_of_neg, List.map_cons, List.sum_cons]
          have ih' : WeightModel.toReal (List.map Prod.snd (List.filter (fun x => p x.1) tail)).sum
              ≤ WeightModel.toReal (List.map Prod.snd tail).sum := ih
          rw [WeightModel.toReal_add]
          linarith [WeightModel.toReal_nonneg w]

end Ordering

/-! ## Measure-theoretic bridge: WDist operations as measure combinators

The following lemmas connect the computational `WDist` monad operations
to their measure-theoretic counterparts, establishing that:

- `WDist.pure` denotes a Dirac measure,
- `WDist.zero` denotes the zero measure,
- `WDist.bind` denotes discrete integration (the `extend` combinator).

This mirrors the measure transformer framework of
Borgström, Gordon, Greenberg, Margetson, and Van Gael,
"Measure Transformer Semantics for Bayesian Machine Learning"
(LMCS 9(3:11), 2013).

In their notation, `WDist.bind d f` is the discrete specialization of

    extend m µ AB = ∫ m(x)({y | (x,y) ∈ AB}) dµ(x)

where the base measure µ = d.toMeasure has finite discrete support.
Together with `observe_eq_restrict` (WDist.lean) and `mass_eq_toMeasure_univ`,
these lemmas show that the `WDist` monad faithfully implements the
discrete measure transformer combinators `pure`, `extend`, and `observe`.
-/

open MeasureTheory ENNReal NNReal

section MeasureBridge

variable {W : Type*} [WeightModel W]
variable {α β : Type*} [MeasurableSpace β]

/-- Weight-list concatenation corresponds to measure addition. -/
theorem toMeasure_mk_append [MeasurableSpace α] (ws₁ ws₂ : List (α × W)) :
    (WDist.mk (ws₁ ++ ws₂)).toMeasure
    = (WDist.mk ws₁).toMeasure + (WDist.mk ws₂).toMeasure := by
  classical
  simp only [toMeasure]
  induction ws₁ with
  | nil => simp
  | cons head tail ih =>
      rcases head with ⟨a, w⟩
      simp only [List.cons_append, List.foldr_cons]
      rw [ih, add_right_comm]

/-- Key helper: foldr over toMeasure step is "right-additive" in the accumulator. -/
private lemma foldr_toMeasure_add_right [MeasurableSpace α]
    (ws : List (α × W)) (μ ν : Measure α) :
    List.foldr
      (fun (x : α × W) acc => acc + (WeightModel.toENNReal x.2) • Measure.dirac x.1)
      (μ + ν) ws
    = List.foldr
      (fun (x : α × W) acc => acc + (WeightModel.toENNReal x.2) • Measure.dirac x.1)
      μ ws + ν := by
  classical
  induction ws with
  | nil => simp
  | cons head tail ih =>
      simp only [List.foldr_cons]
      rw [ih, add_right_comm]

/-- Scaling all weights by `c` corresponds to scaling the measure by `c`. -/
theorem toMeasure_mk_map_scale [MeasurableSpace α] (c : W) (ws : List (α × W)) :
    (WDist.mk (ws.map (fun (b, w') => (b, c * w')))).toMeasure
    = (WeightModel.toENNReal c) • (WDist.mk ws).toMeasure := by
  classical
  simp only [toMeasure]
  induction ws with
  | nil =>
      simp
  | cons head tail ih =>
      rcases head with ⟨b, w'⟩
      simp only [List.map_cons, List.foldr_cons]
      rw [ih, WeightModel.toENNReal_mul]
      simp [smul_add, smul_smul, add_comm]

/-- **The core bridge theorem.** `WDist.bind` denotes discrete measure integration.

This is the discrete specialization of the `extend` combinator from
Borgström et al. (2013), §3.3:

    extend m µ AB = ∫ m(x)({y | (x,y) ∈ AB}) dµ(x)

For a discrete base measure µ = Σᵢ wᵢ · δ_{aᵢ} (encoded as `d : WDist W α`),
the integral reduces to a weighted sum:

    (bind d f).toMeasure = Σᵢ wᵢ • (f aᵢ).toMeasure

The right-hand side is expressed as a `List.foldr` to match the structure
of `toMeasure`.  An equivalent pointwise formulation: for any measurable B,

    (bind d f).toMeasure B = Σ_{(a,w) ∈ d.weights} w * (f a).toMeasure B

which is the discrete integration formula. -/
theorem toMeasure_bind
    (d : WDist W α) (f : α → WDist W β) :
    (WDist.bind d f).toMeasure =
      d.weights.foldr (fun (a, w) μ =>
        μ + (WeightModel.toENNReal w) • (f a).toMeasure) 0 := by
  classical
  cases d with
  | mk ws =>
      induction ws with
      | nil =>
          simp [WDist.bind, WDist.toMeasure]
      | cons head tail ih =>
          rcases head with ⟨a, w⟩
          -- Head scaling lemma
          have h_scale :
              (WDist.mk ((f a).weights.map (fun x_1 => (x_1.1, w * x_1.2)))).toMeasure
                =
              (WeightModel.toENNReal w) • (f a).toMeasure := by
            simpa [mul_comm] using toMeasure_mk_map_scale (α := β) (c := w) (ws := (f a).weights)
          calc
            (WDist.bind (WDist.mk ((a, w) :: tail)) f).toMeasure
                =
              (WDist.mk
                (((f a).weights.map (fun x_1 => (x_1.1, w * x_1.2)))
                  ++ (WDist.bind (WDist.mk tail) f).weights)).toMeasure := by
                simp [WDist.toMeasure, WDist.bind]
            _   =
              (WDist.mk ((f a).weights.map (fun x_1 => (x_1.1, w * x_1.2)))).toMeasure
                + (WDist.bind (WDist.mk tail) f).toMeasure := by
                simpa using
                  (toMeasure_mk_append (α := β)
                    ((f a).weights.map (fun x_1 => (x_1.1, w * x_1.2)))
                    ((WDist.bind (WDist.mk tail) f).weights))
            _   =
              (WeightModel.toENNReal w) • (f a).toMeasure
                + (WDist.bind (WDist.mk tail) f).toMeasure := by
                simp [h_scale]
            _   =
              (WeightModel.toENNReal w) • (f a).toMeasure +
                (tail.foldr (fun (a, w) μ =>
                  μ + (WeightModel.toENNReal w) • (f a).toMeasure) 0) := by
                simp_all only
            _   =
              ((a, w) :: tail).foldr (fun (a, w) μ =>
                μ + (WeightModel.toENNReal w) • (f a).toMeasure) 0 := by
                simp [List.foldr, add_comm]

/-- Scaling a `WDist` corresponds to scaling its denoted measure. -/
theorem toMeasure_scale [MeasurableSpace α] (c : W) (d : WDist W α) :
    (WDist.scale c d).toMeasure = (WeightModel.toENNReal c) • d.toMeasure := by
  cases d with
  | mk ws =>
    simpa [WDist.scale] using (toMeasure_mk_map_scale (c := c) (ws := ws))

end MeasureBridge

/-! ## Normalization lemmas -/

section Normalization

variable {W : Type*} [WeightModel W] {α : Type*}

/-- mass (bind d pure) = mass d (right identity for mass). -/
theorem mass_bind_pure (d : WDist W α) : mass (bind d pure) = mass d := by
  rw [bind_pure_right]

/-- normalize? returns some iff mass ≠ 0. -/
theorem normalize?_isSome_iff [Inv W] [DecidableEq W]
    (d : WDist W α) :
    (∃ d', d.normalize? = some d') ↔ d.mass ≠ 0 := by
  constructor
  · intro ⟨d', h⟩
    by_contra hm
    simp [normalize?, hm] at h
  · intro h
    exact ⟨_, if_neg h⟩

/-- normalize? returns none iff mass = 0. -/
theorem normalize?_isNone_iff [Inv W] [DecidableEq W]
    (d : WDist W α) :
    d.normalize? = none ↔ d.mass = 0 := by
  simp [normalize?]

/-- Helper: factoring a constant out of a sum. -/
private theorem sum_map_mul_right' (ws : List (α × W)) (c : W) :
    (ws.map (fun x : α × W => x.2 * c)).sum = (ws.map Prod.snd).sum * c := by
  induction ws with
  | nil => simp
  | cons hd tl ih =>
    simp only [List.map_cons, List.sum_cons, add_mul]
    congr 1

/-- Mass of normalize? (when it succeeds) is 1. -/
theorem mass_normalize?_eq_one [Inv W] [DecidableEq W]
    (d : WDist W α) (d' : WDist W α)
    (h : d.normalize? = some d')
    (h_inv : ∀ (w : W), w ≠ 0 → w * w⁻¹ = 1) :
    d'.mass = 1 := by
  have hm : d.mass ≠ 0 := by
    by_contra habs
    simp [normalize?, habs] at h
  have h' : d' = { weights := d.weights.map (fun x => (x.1, x.2 * d.mass⁻¹)) } := by
    simp only [normalize?, hm, ↓reduceIte, Option.some.injEq] at h
    exact h.symm ▸ rfl
  rw [h']
  simp only [mass, List.map_map, Function.comp_def]
  rw [sum_map_mul_right']
  exact h_inv _ hm

end Normalization

end WDist

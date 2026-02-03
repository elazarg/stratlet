import Vegas.WDist

/-!
# Extensional Properties for Weighted Distributions

These lemmas state properties that `WDist` should satisfy as a probability monad.
If any of these fail, something is likely wrong with the `WDist` definitions.
-/

namespace WDist

/-! ## Monad Laws

These are the fundamental laws any probability monad must satisfy.
-/

/-- Right identity: `bind m pure = m` (up to list structure) -/
theorem bind_pure_right (m : WDist α) :
    bind m pure = m := by
  sorry

/-- Associativity: bind is associative -/
theorem bind_assoc (m : WDist α) (f : α → WDist β) (g : β → WDist γ) :
    bind (bind m f) g = bind m (fun x => bind (f x) g) := by
  sorry

/-! ## Zero/Failure Laws

Properties about how `zero` (failure/rejection) interacts with bind.
-/

/-- Left zero: `bind zero f = zero` -/
theorem bind_zero_left (f : α → WDist β) :
    bind zero f = zero := by
  sorry

/-- Right zero: `bind m (fun _ => zero) = zero` -/
theorem bind_zero_right {β : Type} (m : WDist α) :
    bind m (fun _ => (zero : WDist β)) = zero := by
  sorry

/-! ## Mass Properties

Properties about how mass behaves under operations.
-/

/-- Mass of pure is 1 -/
theorem mass_pure (a : α) : mass (pure a) = 1 := by
  sorry

/-- Mass of zero is 0 -/
theorem mass_zero : mass (zero : WDist α) = 0 := by
  sorry

/-- Mass is multiplicative under bind (when f always produces same mass) -/
theorem mass_bind_const (m : WDist α) (f : α → WDist β) (w : W)
    (hf : ∀ a, mass (f a) = w) :
    mass (bind m f) = mass m * w := by
  sorry

/-- Conditioning preserves or reduces mass -/
theorem mass_cond_le (p : α → Bool) (xs : WDist α) :
    mass (cond p xs) ≤ mass xs := by
  sorry

/-! ## Guard/Conditioning Laws

Properties about guard and its interaction with bind.
-/

/-- Guard true is pure unit -/
theorem guard_true : guard true = pure () := by
  sorry

/-- Guard false is zero -/
theorem guard_false : guard false = zero := by
  sorry

/-- bind guard with continuation: factors through the boolean -/
theorem bind_guard (b : Bool) (k : Unit → WDist α) :
    bind (guard b) k = if b then k () else zero := by
  sorry

/-! ## Scale Properties -/

/-- Scaling by 1 is identity -/
theorem scale_one (xs : WDist α) : scale 1 xs = xs := by
  sorry

/-- Scaling by 0 gives zero mass -/
theorem mass_scale_zero (xs : WDist α) : mass (scale 0 xs) = 0 := by
  sorry

/-- Scale distributes through bind -/
theorem scale_bind (c : W) (m : WDist α) (f : α → WDist β) :
    scale c (bind m f) = bind (scale c m) f := by
  sorry

end WDist

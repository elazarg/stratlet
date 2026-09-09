/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import Vegas.Compile.ApplicationImage

/-! # Binding origins for conditional application instructions

The current conditional-publication kernel is commitment-backed: readiness
requires an accepted canonical handle. From initialization without provisioned
handles, its source-ordered realization needs an earlier compatible binding.
This certificate is only static metadata.  It does not assert that the binding
was submitted, included, or backed by a private registration in an execution.
In particular, an earlier public value does not synthesize an ideal handle.
-/

namespace Vegas

variable {P : Type} {L : IExpr}

/-- A binding instruction allocates exactly the commitment reference expected
by a later conditional instruction. -/
def BindingCode.OriginFor (binding : BindingCode P)
    (conditional : ConditionalCode P L) : Prop :=
  binding.sourceField = conditional.sourceField ∧
    binding.owner = conditional.endpoint.owner ∧
    binding.sourceSlot = conditional.endpoint.sourceSlot ∧
    binding.node < conditional.endpoint.choiceNode

instance [DecidableEq P] (binding : BindingCode P)
    (conditional : ConditionalCode P L) : Decidable (binding.OriginFor conditional) := by
  unfold BindingCode.OriginFor
  infer_instance

namespace ApplicationImage

/-- Scan emitted instructions while retaining exactly the earlier binding
instructions. -/
def HasBindingOriginsFrom (earlier : List (BindingCode P)) :
    List (ApplicationInstruction P L) → Prop
  | [] => True
  | .bind binding :: rest => HasBindingOriginsFrom (binding :: earlier) rest
  | .conditional conditional :: rest =>
      (∃ binding ∈ earlier, binding.OriginFor conditional) ∧
        HasBindingOriginsFrom earlier rest
  | _ :: rest => HasBindingOriginsFrom earlier rest

instance [DecidableEq P] (earlier : List (BindingCode P))
    (instructions : List (ApplicationInstruction P L)) :
    Decidable (HasBindingOriginsFrom earlier instructions) := by
  induction instructions generalizing earlier with
  | nil => simp only [HasBindingOriginsFrom]; infer_instance
  | cons instruction rest ih =>
      cases instruction <;> simp only [HasBindingOriginsFrom] <;> infer_instance

/-- Every conditional instruction has a compatible binding instruction that
occurs strictly earlier in the emitted instruction list. -/
def HasBindingOrigins (image : ApplicationImage P L) : Prop :=
  HasBindingOriginsFrom [] image.instructions

instance [DecidableEq P] (image : ApplicationImage P L) :
    Decidable image.HasBindingOrigins := by
  unfold HasBindingOrigins
  infer_instance

private theorem origin_of_split
    (earlier : List (BindingCode P))
    (before after : List (ApplicationInstruction P L))
    (conditional : ConditionalCode P L)
    (horigins : HasBindingOriginsFrom earlier
      (before ++ .conditional conditional :: after)) :
    ∃ binding,
      (binding ∈ earlier ∨ .bind binding ∈ before) ∧
        binding.OriginFor conditional := by
  induction before generalizing earlier with
  | nil =>
      obtain ⟨binding, hmem, hcompatible⟩ := horigins.1
      exact ⟨binding, Or.inl hmem, hcompatible⟩
  | cons instruction rest ih =>
      have liftRest
          (found : ∃ binding,
            (binding ∈ earlier ∨ .bind binding ∈ rest) ∧
              binding.OriginFor conditional) :
          ∃ binding,
            (binding ∈ earlier ∨ .bind binding ∈ instruction :: rest) ∧
              binding.OriginFor conditional := by
        obtain ⟨binding, horigin, hcompatible⟩ := found
        refine ⟨binding, ?_, hcompatible⟩
        exact horigin.elim Or.inl fun hmem => Or.inr (by
          simp only [List.mem_cons]
          exact Or.inr hmem)
      cases instruction with
      | bind binding =>
          have found := ih (binding :: earlier) horigins
          obtain ⟨origin, horigin, hcompatible⟩ := found
          refine ⟨origin, ?_, hcompatible⟩
          rcases horigin with horigin | horigin
          · simp only [List.mem_cons] at horigin
            rcases horigin with rfl | horigin
            · exact Or.inr (by simp)
            · exact Or.inl horigin
          · exact Or.inr (by simp only [List.mem_cons]; exact Or.inr horigin)
      | sample code =>
          exact liftRest (ih earlier horigins)
      | publicChoice code =>
          exact liftRest (ih earlier horigins)
      | conditional code =>
          exact liftRest (ih earlier horigins.2)

/-- Eliminate the image certificate at a particular conditional occurrence.
The witness is an actual earlier instruction, with all compatibility facts
retained in `OriginFor`. -/
theorem HasBindingOrigins.origin
    {image : ApplicationImage P L}
    (horigins : image.HasBindingOrigins)
    (before after : List (ApplicationInstruction P L))
    (conditional : ConditionalCode P L)
    (himage : image.instructions = before ++ .conditional conditional :: after) :
    ∃ binding, .bind binding ∈ before ∧ binding.OriginFor conditional := by
  rw [HasBindingOrigins, himage] at horigins
  obtain ⟨binding, horigin, hcompatible⟩ :=
    origin_of_split [] before after conditional horigins
  exact ⟨binding, horigin.resolve_left (by simp), hcompatible⟩

/-- Membership-oriented elimination when the caller does not need to retain a
particular list decomposition. -/
theorem HasBindingOrigins.origin_of_mem
    {image : ApplicationImage P L}
    (horigins : image.HasBindingOrigins) (conditional : ConditionalCode P L)
    (hmem : .conditional conditional ∈ image.instructions) :
    ∃ before binding after,
      image.instructions = before ++ .bind binding :: after ∧
        .conditional conditional ∈ after ∧ binding.OriginFor conditional := by
  obtain ⟨before, after, heq⟩ := List.mem_iff_append.mp hmem
  obtain ⟨binding, hbinding, hcompatible⟩ :=
    horigins.origin before after conditional heq
  obtain ⟨bindingBefore, bindingAfter, hbefore⟩ := List.mem_iff_append.mp hbinding
  refine ⟨bindingBefore, binding, bindingAfter ++ .conditional conditional :: after, ?_, ?_,
    hcompatible⟩
  · rw [heq, hbefore]
    simp only [List.append_assoc, List.cons_append]
  · simp

end Vegas.ApplicationImage

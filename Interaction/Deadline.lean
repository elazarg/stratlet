/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

/-! # Explicit one-obligation deadline races

Time passage does not resolve an obligation. Completion may win while the
obligation is pending, even after its deadline; expiration is an explicit
competing action enabled strictly after the deadline. At the boundary only
completion can resolve it. Strictly afterward, the first resolving action wins.

The enclosing runtime supplies its current clock. Payloads and committed values
belong to the application service, not this resolution component.
-/

namespace Interaction

inductive DeadlineResolution where
  | pending
  | completed
  | expired
  deriving DecidableEq, Repr

structure Deadline where
  «at» : Nat
  resolution : DeadlineResolution
  deriving DecidableEq, Repr

namespace Deadline

def complete (state : Deadline) : Option Deadline :=
  if state.resolution = .pending then
    some { state with resolution := .completed }
  else none

def expire (now : Nat) (state : Deadline) : Option Deadline :=
  if state.resolution = .pending ∧ state.at < now then
    some { state with resolution := .expired }
  else none

def resolved (state : Deadline) : Bool :=
  state.resolution != .pending

theorem complete_pending (state : Deadline)
    (hpending : state.resolution = .pending) :
    complete state = some { state with resolution := .completed } := by
  simp [complete, hpending]

theorem complete_resolved (state : Deadline)
    (hresolved : state.resolution ≠ .pending) : complete state = none := by
  simp [complete, hresolved]

theorem complete_at (state next : Deadline)
    (hcomplete : complete state = some next) : next.at = state.at := by
  simp only [complete] at hcomplete
  split at hcomplete
  · cases hcomplete
    rfl
  · contradiction

theorem expire_success_iff (now : Nat) (state : Deadline) :
    (∃ next, expire now state = some next) ↔
      state.resolution = .pending ∧ state.at < now := by
  simp [expire]

theorem expire_at_boundary (state : Deadline) : expire state.at state = none := by
  simp [expire]

theorem expire_before_boundary (now : Nat) (state : Deadline)
    (hle : now ≤ state.at) : expire now state = none := by
  simp [expire, Nat.not_lt_of_ge hle]

theorem expire_pending_after (now : Nat) (state : Deadline)
    (hpending : state.resolution = .pending) (hpast : state.at < now) :
    expire now state = some { state with resolution := .expired } := by
  simp [expire, hpending, hpast]

theorem expire_at (now : Nat) (state next : Deadline)
    (hexpire : expire now state = some next) : next.at = state.at := by
  simp only [expire] at hexpire
  split at hexpire
  · cases hexpire
    rfl
  · contradiction

theorem expire_after_complete (now : Nat) (state completed : Deadline)
    (hcomplete : complete state = some completed) : expire now completed = none := by
  simp only [complete] at hcomplete
  split at hcomplete
  · cases hcomplete
    simp [expire]
  · contradiction

theorem complete_after_expire (now : Nat) (state expired : Deadline)
    (hexpire : expire now state = some expired) : complete expired = none := by
  simp only [expire] at hexpire
  split at hexpire
  · cases hexpire
    simp [complete]
  · contradiction

/-- Strictly after the deadline, explicit expiration can win and permanently
exclude completion. -/
theorem late_expire_wins (now : Nat) (state : Deadline)
    (hpending : state.resolution = .pending) (hpast : state.at < now) :
    ∃ expired, expire now state = some expired ∧ complete expired = none := by
  refine ⟨{ state with resolution := .expired }, ?_, ?_⟩
  · exact expire_pending_after now state hpending hpast
  · simp [complete]

end Deadline

end Interaction

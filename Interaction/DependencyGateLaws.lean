/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import Interaction.DependencyGate

/-! # Laws for transactional timeout dependency gates -/

namespace Interaction.DependencyGate

universe uPrincipal uIndex

variable {Principal : Type uPrincipal} {Index : Type uIndex}
variable [DecidableEq Principal] [DecidableEq Index]

/-- Resetting the shared activity origin after resolving the first missing
dependency prevents a second, active owner from being resolved in the same
sliding-expiry pass. Since `checkAll` returns `none`, the caller has no staged
state to commit. -/
theorem checkAll_slidingExpiry_two_missing
    (now window : Nat) (first second : Principal × Index)
    (state : DependencyGate Principal Index)
    (hfirstMissing : first ∉ state.completed)
    (hsecondMissing : second ∉ state.completed)
    (hsecondActive : second.1 ∉ state.excluded)
    (howners : second.1 ≠ first.1)
    (hfirstExpired : state.lastActivity + window < now) :
    checkAll now (slidingExpiry now window) [first, second] state = none := by
  have hresetNotExpired : ¬now + window < now := by omega
  simp [checkAll, check, slidingExpiry, hfirstMissing, hsecondMissing,
    hsecondActive, howners, hfirstExpired, hresetNotExpired]

/-- Two missing dependencies of distinct active owners cannot pass one
sliding-expiry batch, regardless of how long the caller waits. -/
theorem checkAll_slidingExpiry_two_active_missing
    (now window : Nat) (first second : Principal × Index)
    (state : DependencyGate Principal Index)
    (hfirstMissing : first ∉ state.completed)
    (hsecondMissing : second ∉ state.completed)
    (hfirstActive : first.1 ∉ state.excluded)
    (hsecondActive : second.1 ∉ state.excluded)
    (howners : second.1 ≠ first.1) :
    checkAll now (slidingExpiry now window) [first, second] state = none := by
  by_cases hfirstExpired : state.lastActivity + window < now
  · exact checkAll_slidingExpiry_two_missing now window first second state
      hfirstMissing hsecondMissing hsecondActive howners hfirstExpired
  · simp [checkAll, check, slidingExpiry, hfirstMissing, hfirstActive, hfirstExpired]

/-- The canonical state obtained by resolving every dependency missing from
the initial completed set. -/
def fixedResolvedState (now : Nat) (initialCompleted : Finset (Principal × Index)) :
    List (Principal × Index) → DependencyGate Principal Index →
      DependencyGate Principal Index
  | [], state => state
  | dependency :: rest, state =>
      let next := if dependency ∈ initialCompleted then state else
        { state with excluded := insert dependency.1 state.excluded, lastActivity := now }
      fixedResolvedState now initialCompleted rest next

/-- Owners of dependencies missing from a fixed initial completed set. -/
def missingOwners (initialCompleted : Finset (Principal × Index)) :
    List (Principal × Index) → Finset Principal
  | [] => ∅
  | dependency :: rest =>
      if dependency ∈ initialCompleted then missingOwners initialCompleted rest
      else insert dependency.1 (missingOwners initialCompleted rest)

private theorem fixedResolvedState_completed
    (now : Nat) (initialCompleted : Finset (Principal × Index))
    (dependencies : List (Principal × Index)) (state : DependencyGate Principal Index) :
    (fixedResolvedState now initialCompleted dependencies state).completed = state.completed := by
  induction dependencies generalizing state with
  | nil => rfl
  | cons dependency rest ih =>
      simp only [fixedResolvedState]
      split <;> apply ih

/-- When every initially missing dependency is overdue, fixed expiry has an
exact, constructive result rather than merely succeeding. -/
theorem checkAll_fixedExpiry_exact
    (now : Nat) (deadline : Principal × Index → Nat)
    (dependencies : List (Principal × Index))
    (state : DependencyGate Principal Index)
    (hready : ∀ dependency ∈ dependencies,
      dependency ∈ state.completed ∨ deadline dependency < now) :
    checkAll now (fixedExpiry now deadline) dependencies state =
      some (fixedResolvedState now state.completed dependencies state) := by
  induction dependencies generalizing state with
  | nil => rfl
  | cons dependency rest ih =>
      have hdependency := hready dependency (by simp)
      by_cases hdone : dependency ∈ state.completed
      · rw [checkAll, check_completed _ _ _ _ hdone]
        simp only [fixedResolvedState, if_pos hdone]
        apply ih
        intro dep hdep
        exact hready dep (by simp [hdep])
      · have hexpired : deadline dependency < now := hdependency.resolve_left hdone
        rw [checkAll, check_expired]
        · simp only [fixedResolvedState, if_neg hdone]
          apply ih
          intro dep hdep
          simpa using hready dep (by simp [hdep])
        · exact hdone
        · simp [fixedExpiry, hexpired]

/-- Fixed resolution never changes the completed-obligation set. -/
theorem fixedResolvedState_completed_eq
    (now : Nat) (dependencies : List (Principal × Index))
    (state : DependencyGate Principal Index) :
    (fixedResolvedState now state.completed dependencies state).completed = state.completed :=
  fixedResolvedState_completed now state.completed dependencies state

/-- Fixed resolution excludes exactly the initially excluded principals plus
the owners of initially missing requested dependencies. -/
theorem fixedResolvedState_excluded_eq
    (now : Nat) (dependencies : List (Principal × Index))
    (state : DependencyGate Principal Index) :
    (fixedResolvedState now state.completed dependencies state).excluded =
      state.excluded ∪ missingOwners state.completed dependencies := by
  induction dependencies generalizing state with
  | nil => simp [fixedResolvedState, missingOwners]
  | cons dependency rest ih =>
      simp only [fixedResolvedState, missingOwners]
      by_cases hdone : dependency ∈ state.completed
      · simp [hdone, ih]
      · simp only [hdone, if_false]
        let next : DependencyGate Principal Index :=
          { state with excluded := insert dependency.1 state.excluded, lastActivity := now }
        have hrest := ih next
        rw [hrest]
        ext owner
        simp [next, or_assoc, or_left_comm]

/-- The activity timestamp is `now` when a requested dependency is initially
missing, and is the initial timestamp otherwise. -/
theorem fixedResolvedState_lastActivity_eq
    (now : Nat) (dependencies : List (Principal × Index))
    (state : DependencyGate Principal Index) :
    (fixedResolvedState now state.completed dependencies state).lastActivity =
      if dependencies.any (fun dependency => decide (dependency ∉ state.completed))
      then now else state.lastActivity := by
  induction dependencies generalizing state with
  | nil => rfl
  | cons dependency rest ih =>
      by_cases hdone : dependency ∈ state.completed
      · simp only [fixedResolvedState, if_pos hdone]
        rw [ih]
        have hfalse : decide (dependency ∉ state.completed) = false := by
          apply Bool.eq_false_iff.mpr
          intro htrue
          exact (of_decide_eq_true htrue) hdone
        change (if rest.any (fun dependency => decide (dependency ∉ state.completed)) = true
          then now else state.lastActivity) =
          if (decide (dependency ∉ state.completed) ||
            rest.any (fun dependency => decide (dependency ∉ state.completed))) = true
          then now else state.lastActivity
        simp only [hfalse, Bool.false_or]
      · let next : DependencyGate Principal Index :=
          { state with excluded := insert dependency.1 state.excluded, lastActivity := now }
        have hrest := ih next
        simp only [fixedResolvedState, if_neg hdone]
        rw [hrest]
        have htrue : decide (dependency ∉ state.completed) = true := by
          exact decide_eq_true hdone
        simp only [next, List.any_cons, htrue, Bool.true_or, if_true]
        split <;> rfl

/-- With immutable deadlines, every dependency that is not already completed
or discharged can be checked once its own deadline has passed. -/
theorem checkAll_fixedExpiry_exists
    (now : Nat) (deadline : Principal × Index → Nat)
    (dependencies : List (Principal × Index))
    (state : DependencyGate Principal Index)
    (hready : ∀ dependency ∈ dependencies,
      dependency ∈ state.completed ∨ dependency.1 ∈ state.excluded ∨
        deadline dependency < now) :
    ∃ next, checkAll now (fixedExpiry now deadline) dependencies state = some next := by
  induction dependencies generalizing state with
  | nil => exact ⟨state, rfl⟩
  | cons dependency rest ih =>
      have hdependency := hready dependency (by simp)
      by_cases hdone : dependency ∈ state.completed
      · rw [checkAll, check_completed _ _ _ _ hdone]
        apply ih
        intro dep hdep
        exact hready dep (by simp [hdep])
      · by_cases hexpired : deadline dependency < now
        · let staged : DependencyGate Principal Index :=
            { state with excluded := insert dependency.1 state.excluded, lastActivity := now }
          have hcheck : check now (fixedExpiry now deadline) dependency state = some staged := by
            exact check_expired now (fixedExpiry now deadline) dependency state hdone (by
              simp [fixedExpiry, hexpired])
          rw [checkAll, hcheck]
          apply ih
          intro dep hdep
          rcases hready dep (by simp [hdep]) with h | h | h
          · exact Or.inl (by simpa [staged] using h)
          · exact Or.inr (Or.inl (by
              change dep.1 ∈ insert dependency.1 state.excluded
              exact Finset.mem_insert_of_mem h))
          · exact Or.inr (Or.inr h)
        · have hexcluded : dependency.1 ∈ state.excluded := by
            rcases hdependency with h | h | h
            · exact (hdone h).elim
            · exact h
            · exact (hexpired h).elim
          have hcheck : check now (fixedExpiry now deadline) dependency state = some state := by
            simp [check, fixedExpiry, hdone, hexcluded, hexpired]
          rw [checkAll, hcheck]
          apply ih
          intro dep hdep
          exact hready dep (by simp [hdep])

/-- A body rejection makes the entire staged call uncommittable. -/
theorem call_body_rejects
    (now : Nat)
    (expired : DependencyGate Principal Index → Principal × Index → Bool)
    (actor : Principal) (action : Principal × Index)
    (dependencies : List (Principal × Index))
    (state : DependencyGate Principal Index) :
    call now expired actor action dependencies (fun _ => false) state = none := by
  simp [call]

end Interaction.DependencyGate

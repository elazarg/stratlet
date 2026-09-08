/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import Mathlib.Data.Finset.Basic

/-! # Transactional timeout dependency gates

This component stages completion and principal-exclusion effects while checking
a call's ordered dependencies. A failed check or rejected body returns `none`;
the enclosing application transaction decides whether to commit the result.

Clock readings are natural-number units supplied by the enclosing runtime.
The component does not advance a clock, schedule a call, resolve a source quit
continuation, or implement a complete contract. Caller authorization and the
call's dependency list are supplied by its compiled entry point.
-/

namespace Interaction

universe uPrincipal uIndex

structure DependencyGate (Principal : Type uPrincipal) (Index : Type uIndex) where
  completed : Finset (Principal × Index)
  excluded : Finset Principal
  lastActivity : Nat
  deriving DecidableEq

namespace DependencyGate

variable {Principal : Type uPrincipal} {Index : Type uIndex}
variable [DecidableEq Principal] [DecidableEq Index]

/-- Clock-expiry policy that re-reads the current staged activity origin on
every dependency check. -/
def slidingExpiry (now window : Nat) :
    DependencyGate Principal Index → Principal × Index → Bool :=
  fun state _ => decide (state.lastActivity + window < now)

/-- Clock-expiry policy using an immutable deadline for each obligation.
It also represents a call-entry snapshot by supplying a constant deadline. -/
def fixedExpiry (now : Nat) (deadline : Principal × Index → Nat) :
    DependencyGate Principal Index → Principal × Index → Bool :=
  fun _ dependency => decide (deadline dependency < now)

/-- An overdue missing dependency excludes its owner and records activity.
An excluded owner discharges all of its dependencies; this is a principal-wide
policy, distinct from resolving just one obligation. -/
def check (now : Nat)
    (expired : DependencyGate Principal Index → Principal × Index → Bool)
    (dependency : Principal × Index) (state : DependencyGate Principal Index) :
    Option (DependencyGate Principal Index) :=
  let next := if dependency ∉ state.completed ∧ expired state dependency then
      { state with excluded := insert dependency.1 state.excluded, lastActivity := now }
    else state
  if dependency.1 ∈ next.excluded ∨ dependency ∈ next.completed then some next else none

/-- Dependency effects are staged in list order. Failure discards the staged
result rather than returning a partially updated application state. -/
def checkAll (now : Nat)
    (expired : DependencyGate Principal Index → Principal × Index → Bool) :
    List (Principal × Index) → DependencyGate Principal Index →
      Option (DependencyGate Principal Index)
  | [], state => some state
  | dependency :: rest, state =>
      (check now expired dependency state).bind (checkAll now expired rest)

/-- Gate-state computation for an action call. Authentication and binding of
these raw arguments to an entry point are obligations of the enclosing
runtime. Its actor may differ from the recorded action owner (for example,
a registration entry point).
The body can observe staged exclusions and reject. Reentrancy or other writes
to gate-owned fields require an additional operational model. -/
def call (now : Nat)
    (expired : DependencyGate Principal Index → Principal × Index → Bool)
    (actor : Principal) (action : Principal × Index) (dependencies : List (Principal × Index))
    (bodyAccepts : DependencyGate Principal Index → Bool)
    (state : DependencyGate Principal Index) : Option (DependencyGate Principal Index) := do
  if actor ∈ state.excluded ∨ action ∈ state.completed then none else do
    let staged := { state with completed := insert action state.completed }
    let checked ← checkAll now expired dependencies staged
    if bodyAccepts checked then some { checked with lastActivity := now } else none

theorem check_completed (now : Nat)
    (expired : DependencyGate Principal Index → Principal × Index → Bool)
    (dependency : Principal × Index) (state : DependencyGate Principal Index)
    (hdone : dependency ∈ state.completed) :
    check now expired dependency state = some state := by
  simp [check, hdone]

theorem check_not_expired (now : Nat)
    (expired : DependencyGate Principal Index → Principal × Index → Bool)
    (dependency : Principal × Index) (state : DependencyGate Principal Index)
    (hdone : dependency ∉ state.completed) (hactive : dependency.1 ∉ state.excluded)
    (hdeadline : expired state dependency = false) :
    check now expired dependency state = none := by
  simp [check, hdone, hactive, hdeadline]

theorem check_expired (now : Nat)
    (expired : DependencyGate Principal Index → Principal × Index → Bool)
    (dependency : Principal × Index) (state : DependencyGate Principal Index)
    (hdone : dependency ∉ state.completed) (hdeadline : expired state dependency = true) :
    check now expired dependency state =
      some { state with excluded := insert dependency.1 state.excluded, lastActivity := now } := by
  simp [check, hdone, hdeadline]

theorem call_excluded (now : Nat)
    (expired : DependencyGate Principal Index → Principal × Index → Bool)
    (actor : Principal) (action : Principal × Index) (dependencies : List (Principal × Index))
    (bodyAccepts : DependencyGate Principal Index → Bool)
    (state : DependencyGate Principal Index) (hexcluded : actor ∈ state.excluded) :
    call now expired actor action dependencies bodyAccepts state = none := by
  simp [call, hexcluded]

end DependencyGate

end Interaction

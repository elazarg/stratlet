/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import Vegas.Compile.BindingSourceCoupling
import Vegas.Compile.ConditionalSourceCoupling
import Vegas.Compile.SourceExecutionOutcome
import VegasTests.ConditionalApplicationImage

/-! # Source continuations through generated binding and disclosure

The actual generated application includes a prepared binding and then an
opening or decline. Both inclusions share one final graph and preserve the
chosen source values. Advancing the clock alone does not close the endpoint.
-/

noncomputable section

namespace VegasTests.ConditionalSourceCoupling

open Vegas Vegas.EventGraph Vegas.ToEventGraph Interaction
open VegasTests.ConditionalApplicationImage

def checkpoint : CoupledAt ConditionalApplicationImage.compiled.graph compilerInitial :=
  compiledInitialCoupled source

def boundBuild : BuildState (Fin 2) simpleExpr OpeningContext :=
  (compilerInitial.addCommitEvent 0 0
    (Expr.constBool (Γ := [(0, .bool)]) true) source.fresh.1).1

def finalBuild :=
  (((boundBuild.addCommitEvent 1 0 openingGuard source.fresh.2.1).1).addRevealEvent
    2 0 .here source.fresh.2.2.1).1

def bindingSubmitted (secret : Bool) : (image 10).application.State :=
  { initialExecution 10 with
    application := initialNative.register 0 0 ⟨.bool, secret⟩
    pool := ((initialExecution 10).pool.submit 0 bindingPayload).2 }

def bound (secret : Bool) : (image 10).application.State :=
  (image 10).application.includePending (bindingSubmitted secret) (0, 0)

def conditionalSubmitted (secret : Bool) (chosen : Option Bool) (clock : Nat) :
    (image 10).application.State :=
  { bound secret with
    application := (bound secret).application.advance clock
    pool := ((bound secret).pool.submit 0
      (.conditional 2 ((conditionalCode 10).requestPayload chosen))).2 }

def published (secret : Bool) (chosen : Option Bool) (clock : Nat) :
    (image 10).application.State :=
  (image 10).application.includePending (conditionalSubmitted secret chosen clock) (0, 1)

private theorem bound_source_successor (secret : Bool) :
    ∃ next : CoupledAt ConditionalApplicationImage.compiled.graph boundBuild,
      next.current.source = source.env.cons secret ∧
      (bound secret).application.Refines next.current.graph.1 ∧
      ApplicationImage.AcceptedSnapshot (L := simpleExpr) 0 (0, 0)
        (some ⟨.bool, secret⟩) (bound secret).application := by
  exact SourceDecisionSite.include_binding_source_coupling
    (P := Fin 2) (L := simpleExpr) (Γ := []) (name := 0) (who := 0) (ty := .bool)
    (.constBool true) _ source.fresh compilerInitial checkpoint (image 10)
    (bindingSubmitted secret)
    ((ApplicationImage.State.initial_refines ConditionalApplicationImage.compiled.graph).register
      0 0 ⟨.bool, secret⟩)
    0 0 (image_lookup_binding 10) secret (by rfl) (by rfl) (by rfl)

/-- Both voluntary outcomes reach the exact source continuation after actual
binding and conditional inclusion. The clock is unrestricted because no
competing expiry transaction has resolved the endpoint. -/
theorem published_source_successor (secret : Bool) (chosen : Option Bool) (clock : Nat)
    (hchoice : chosen = none ∨ chosen = some secret) :
    ∃ next : CoupledAt ConditionalApplicationImage.compiled.graph finalBuild,
      next.current.source = ((source.env.cons secret).cons chosen).cons chosen ∧
      (published secret chosen clock).application.Refines next.current.graph.1 := by
  obtain ⟨current, hsource, hrefines, hsnapshot⟩ := bound_source_successor secret
  have hlegal : evalGuard openingGuard chosen
      ((current.current.source.toView (0 : Fin 2)).eraseEnv) = true := by
    rw [hsource]
    rcases hchoice with rfl | rfl
    · rfl
    · change decide (some secret = some secret) = true
      simp
  have hfrozen : ∀ value, specification.encoding chosen = some value →
      ((conditionalSubmitted secret chosen clock).application.frozen 0).bind
        (fun typed => typed.as? (L := simpleExpr) .bool) = some value := by
    intro value hvalue
    have heq : value = secret := by
      change chosen = some value at hvalue
      rcases hchoice with rfl | rfl
      · contradiction
      · exact (Option.some.inj hvalue).symm
    subst value
    change ((bound secret).application.frozen 0).bind _ = some secret
    rw [hsnapshot.2]
    rfl
  obtain ⟨next, hnextSource, hnextRefines⟩ :=
    ConditionalPublicationSite.include_source_coupling
      (P := Fin 2) (L := simpleExpr) (Γ := OpeningContext)
      (name := 1) (publicName := 2) (who := 0) (ty := .option .bool)
      openingGuard tail specification source.fresh.2 boundBuild 0 10 current
      (image 10) (conditionalSubmitted secret chosen clock) (hrefines.advance clock)
      opening_publicly_validatable hsnapshot.1 2 1 (image_lookup_conditional 10)
      chosen (by rfl) hlegal hfrozen
  exact ⟨next, hnextSource.trans (by rw [hsource]), hnextRefines⟩

def unpreparedBound : (image 10).application.State :=
  (image 10).application.includePending
    { initialExecution 10 with
      pool := ((initialExecution 10).pool.submit 0 bindingPayload).2 } (0, 0)

def unopenableDeclineSubmitted : (image 10).application.State :=
  { unpreparedBound with
    pool := (unpreparedBound.pool.submit 0 declinePayload).2 }

/-- An actual binding accepted without registration can still decline. The
source witness supplies a legal hidden value; it does not fabricate a native
opening or require a frozen snapshot to resolve the source quitting outcome. -/
theorem unopenable_decline_source_successor :
    unpreparedBound.application.frozen 0 = none ∧
      ∃ next : CoupledAt ConditionalApplicationImage.compiled.graph finalBuild,
        next.current.source = ((source.env.cons false).cons none).cons none ∧
        ((image 10).application.includePending unopenableDeclineSubmitted
          (0, 1)).application.Refines next.current.graph.1 := by
  refine ⟨rfl, ?_⟩
  obtain ⟨current, hsource, hrefines, _⟩ := bound_source_successor false
  have hunprepared : unpreparedBound.application.Refines current.current.graph.1 := by
    refine ⟨hrefines.memory, hrefines.reachable, ?_⟩
    intro field handle haccepted
    obtain ⟨spec, value, hfield, howner, hstored, _⟩ :=
      hrefines.bindings field handle haccepted
    refine ⟨spec, value, hfield, howner, hstored, ?_⟩
    intro recovered hrecovered
    have hnone : unpreparedBound.application.frozen field = none := by
      change (if field = 0 then none else none) = none
      simp
    rw [hnone] at hrecovered
    contradiction
  obtain ⟨next, hnextSource, hnextRefines⟩ :=
    ConditionalPublicationSite.include_source_coupling
      (P := Fin 2) (L := simpleExpr) (Γ := OpeningContext)
      (name := 1) (publicName := 2) (who := 0) (ty := .option .bool)
      openingGuard tail specification source.fresh.2 boundBuild 0 10 current
      (image 10) unopenableDeclineSubmitted hunprepared
      opening_publicly_validatable (by rfl) 2 1 (image_lookup_conditional 10)
      none (by rfl) (by rfl) (by intro value hvalue; cases hvalue)
  exact ⟨next, hnextSource.trans (by rw [hsource]), hnextRefines⟩

end VegasTests.ConditionalSourceCoupling

/-- info: 'VegasTests.ConditionalSourceCoupling.published_source_successor' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms VegasTests.ConditionalSourceCoupling.published_source_successor

/-- info: 'VegasTests.ConditionalSourceCoupling.unopenable_decline_source_successor' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms VegasTests.ConditionalSourceCoupling.unopenable_decline_source_successor

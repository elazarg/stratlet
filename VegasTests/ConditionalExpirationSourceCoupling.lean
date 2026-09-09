/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import Vegas.Compile.ConditionalExpirationSourceCoupling
import VegasTests.ConditionalSourceCoupling
import Interaction.MessagePoolFreshness

/-! # Permissionless generated conditional expiration

The non-owner submits an expiry packet after the public deadline. The shared
policy runner records its real submission and environment inclusion, while the
generated endpoint realizes the source-certified decline continuation.
-/

noncomputable section

namespace VegasTests.ConditionalExpirationSourceCoupling

open Vegas Vegas.EventGraph Vegas.ToEventGraph Interaction
  Interaction.MessageApplication GameTheory.Math.Probability
open VegasTests.ConditionalApplicationImage
open VegasTests.ConditionalSourceCoupling

/-- Player 1 starts from the genuinely bound native checkpoint after the public
clock has advanced beyond the generated deadline. -/
def expirationStart (secret : Bool) : (image 10).application.PolicyExecution :=
  PolicyExecution.initial (image 10).application
    { bound secret with application := (bound secret).application.advance 11 }

/-- The expiry author is player 1, whereas the generated endpoint owner is
player 0. Expiration itself is intentionally permissionless. -/
def expirationPlayers : Fin 2 → (image 10).application.PlayerPolicy :=
  fun player _ _ =>
    if player = 1 then FinDist.pure (.submit expiryPayload) else FinDist.pure .wait

def includeExpiration : (image 10).application.EnvironmentPolicy :=
  fun _ _ => FinDist.pure (.include (1, 0))

/-- The fixture really invokes player 1 and then the environment through the
shared policy runner; no hand-written execution function is substituted. -/
private theorem expiration_run (secret : Bool) :
    (image 10).application.runPolicies expirationPlayers includeExpiration
        [.player 1, .environment] (expirationStart secret) =
      ((image 10).application.playerStep 1 (expirationStart secret)
        (.submit expiryPayload)).bind fun submitted =>
          (image 10).application.environmentPolicyStep submitted (.include (1, 0)) := by
  simp [MessageApplication.runPolicies, MessageApplication.invoke,
    expirationPlayers, includeExpiration]

/-- Every supported result of the concrete non-owner expiry run reaches the
decline source successor through the actual recorded inclusion. -/
theorem other_sender_expiry_source_successor (secret : Bool)
    (included : (image 10).application.PolicyExecution)
    (hincluded : included ∈ ((image 10).application.runPolicies
      expirationPlayers includeExpiration [.player 1, .environment]
      (expirationStart secret)).support) :
    ∃ next : CoupledAt ConditionalApplicationImage.compiled.graph finalBuild,
      next.current.source =
        ((source.env.cons secret).cons (none : Option Bool)).cons none ∧
        included.native.application.Refines next.current.graph.1 := by
  rw [expiration_run] at hincluded
  simp only [FinDist.support_bind, Set.mem_iUnion] at hincluded
  obtain ⟨submitted, hsubmitted, hincluded⟩ := hincluded
  obtain ⟨current, hsource, hrefines, hsnapshot⟩ := bound_source_successor secret
  have hrefinesStart : (expirationStart secret).native.application.Refines
      current.current.graph.1 := hrefines.advance 11
  have hsubmittedNative : submitted.native ∈
      (((image 10).application.playerStep 1 (expirationStart secret)
        (.submit expiryPayload)).map PolicyExecution.native).support := by
    rw [FinDist.support_map]
    exact ⟨submitted, hsubmitted, rfl⟩
  rw [(image 10).application.playerStep_native] at hsubmittedNative
  simp only [PlayerCommand.toAction, MessageApplication.step,
    FinDist.mem_support_pure] at hsubmittedNative
  have happlication : submitted.native.application =
      (expirationStart secret).native.application := by
    simpa using congrArg MessageApplication.State.application hsubmittedNative
  have hlookup : submitted.native.pool.lookup (1, 0) =
      some ⟨(1, 0), .conditional
        (conditionalCode 10).endpoint.publicationNode .expire⟩ := by
    rw [hsubmittedNative]
    exact (expirationStart secret).native.pool.lookup_submit_fresh 1 expiryPayload (by rfl)
  have haccepted : submitted.native.application.memory.accepted
      (boundBuild.fieldOf specification.binding) = some (0, 0) := by
    rw [happlication]
    exact hsnapshot.1
  have hoverdue : 10 < submitted.native.application.memory.clock := by
    rw [happlication]
    change 10 < max (bound secret).application.memory.clock 11
    exact Nat.lt_of_lt_of_le (by decide) (Nat.le_max_right _ _)
  have hresult := ConditionalPublicationSite.expiry_include_source_coupling
    (P := Fin 2) (L := simpleExpr) (Γ := OpeningContext)
    (name := 1) (publicName := 2) (who := 0) (ty := .option .bool)
    openingGuard tail specification source.fresh.2 boundBuild 0 10 current
    (image 10) submitted included (happlication.symm ▸ hrefinesStart) haccepted hoverdue
    (conditionalCode 10).endpoint.publicationNode (image_lookup_conditional 10)
    (1, 0) hlookup hincluded
  rcases hresult with ⟨_, _, _, next, hnextSource, hnextRefines⟩
  refine ⟨next, ?_, hnextRefines⟩
  rw [hnextSource, hsource]
  rfl

end VegasTests.ConditionalExpirationSourceCoupling

/-- info: 'VegasTests.ConditionalExpirationSourceCoupling.other_sender_expiry_source_successor'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  VegasTests.ConditionalExpirationSourceCoupling.other_sender_expiry_source_successor

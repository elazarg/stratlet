/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import Vegas.Compile.ApplicationForwardLaw
import VegasTests.ApplicationBindingOrigins
import VegasTests.GeneratedPersistentDisclosure

/-! # Whole generated application source law

The existing persistent-disclosure plan exercises every implemented image
constructor: opaque binding, ordinary public choice, fixed chance, accounted
conditional publication, and a later conditional copy.  For an arbitrary
source behavioral profile, its actual generated invocation script and serial
service have exactly the independent source law, including completion.
-/

noncomputable section

namespace VegasTests.GeneratedApplicationSourceLaw

open Vegas Vegas.EventGraph Vegas.ToEventGraph Interaction
  Interaction.MessageApplication GameTheory.Math.Probability
open VegasTests.PersistentDisclosure
open VegasTests.GeneratedPersistentDisclosure

def deadlineOf : Nat → Nat := fun _ => 10

theorem initial_reads_public : applicationPlan.InitialControllerReadsPublic := by
  apply applicationPlan.initialControllerReadsPublic_of_allInitialFieldsPublic
  apply (compileCore source.prog source.fresh compilerInitial).allInitialFieldsPublic_of_owners
  intro initial hinitial
  change initial ∈ [] at hinitial
  cases hinitial

/-- The exact joint completion and public-terminal law of the full generated
reference execution, for every original source behavioral profile. -/
theorem generated_source_public_law
    (profile : SourceBehavioralProfile source.prog) :
    ((((applicationPlan.image deadlineOf).application.runPolicies
      (applicationPlan.liftProfile deadlineOf profile)
      (applicationPlan.image deadlineOf).serialService
      (applicationPlan.image deadlineOf).serviceInvocations
      (applicationPlan.initialExecution deadlineOf)).map fun out =>
        (out.native.application.memory.finished (compile source).graph.nodeCount,
          (compile source).readPublicTerminal? out.native.application.memory))) =
      (denoteSource source.prog profile source.env).map fun terminal =>
        (true, some (cast (congrArg (VEnv simpleExpr)
          (compileCore_terminalCtx_eq_sourceTerminalCtx source.prog source.fresh
            compilerInitial).symm) terminal).erasePubEnv) := by
  exact applicationPlan.service_source_public_law
    DisclosureAccounting.persistentChecked deadlineOf profile initial_reads_public
    ApplicationBindingOrigins.persistent_image_has_binding_origins

end VegasTests.GeneratedApplicationSourceLaw

/--
info: 'VegasTests.GeneratedApplicationSourceLaw.generated_source_public_law' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms VegasTests.GeneratedApplicationSourceLaw.generated_source_public_law

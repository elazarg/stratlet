/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import Vegas.Compile.ApplicationPlanOrigin
import Vegas.Compile.BindingResolution
import Vegas.Compile.PublicationStateRefinement
import Vegas.Compile.ApplicationImageSamples
import Vegas.Compile.SampleImageRefinement
import Interaction.MessageApplicationPolicyLaws

/-! # Generated application refinement under arbitrary traffic

The native interpreter receives arbitrary messages, not source-certified
requests. Successful dispatch recovers the originating source instruction and
its backend certificate. The proof-only graph witness tracks accepted sealed
bindings without placing their values in public runtime memory.

These support invariants constrain possible executions. They neither equate
profile outcome laws nor assert that a source strategy can generate a runtime
player's observations or decisions.
-/

noncomputable section

namespace Vegas.ApplicationPlan

open EventGraph ToEventGraph Interaction GameTheory.Math.Probability

variable {P : Type} [DecidableEq P] {L : IExpr}
variable {Γ : VCtx P L} {pending : Finset VarId} {prog : VegasCore P L Γ}
variable {accounted : CommitmentAccounting pending prog} {fresh : FreshBindings prog}
variable {build : BuildState P L Γ}

private theorem private_preserves_refinement (image : ApplicationImage P L)
    (graph : Graph P L) (native : ApplicationImage.State P L) (who : P)
    (command : image.application.PrivateCommand)
    (hstate : ∃ cfg : Config graph, native.Refines cfg) :
    ∃ cfg : Config graph, (image.application.privateStep native who command).Refines cfg := by
  obtain ⟨cfg, hrefines⟩ := hstate
  cases command with
  | register slot value => exact ⟨cfg, hrefines.register who slot value⟩

private theorem environment_preserves_refinement (plan : ApplicationPlan accounted fresh build)
    (deadlineOf : Nat → Nat) (native : ApplicationImage.State P L)
    (command : (plan.image deadlineOf).application.EnvironmentCommand)
    (next : ApplicationImage.State P L)
    (hstate : ∃ cfg : Config (compileCore prog fresh build).graph, native.Refines cfg)
    (hnext : next ∈ ((plan.image deadlineOf).application.environmentStep native command).support) :
    ∃ cfg : Config (compileCore prog fresh build).graph, next.Refines cfg := by
  obtain ⟨cfg, hrefines⟩ := hstate
  cases command with
  | advance clock =>
      simp only [ApplicationImage.application, FinDist.mem_support_pure] at hnext
      subst next
      exact ⟨cfg, hrefines.advance clock⟩
  | sample address =>
      change next ∈ ((plan.image deadlineOf).sample native address).support at hnext
      rcases (plan.image deadlineOf).sample_support native address next hnext with rfl |
        ⟨code, reads, value, hlookup, hnotDone, hrequires, hreads, hvalue, rfl⟩
      · exact ⟨cfg, hrefines⟩
      · cases plan.origin_of_lookup deadlineOf address (.sample code) hlookup with
        | sample node dist hsem hcode =>
            subst code
            obtain ⟨graphReads, _, hnativeReads, _, hdraw⟩ :=
              ApplicationImage.sample_law_refines (plan.image deadlineOf) native cfg
                hrefines (compileCore prog fresh build).graphWF address _ hlookup
                node rfl rfl rfl _
                ((compileCore prog fresh build).graph.nodes_get?_nodeRow node)
                hsem hnotDone hrequires
            have heq : reads = graphReads := Option.some.inj (hreads.symm.trans hnativeReads)
            subst reads
            exact ⟨_, hdraw value hvalue⟩

/-- Every accepted raw packet preserves a reachable graph witness for the
generated application's storage, completion flags, and accepted bindings. -/
theorem handle_refines (plan : ApplicationPlan accounted fresh build)
    (deadlineOf : Nat → Nat) (initial : VEnv L Γ) (legal : Legal prog)
    (native : ApplicationImage.State P L)
    (cfg : Config (compileCore prog fresh build).graph)
    (hrefines : native.Refines cfg)
    (message : Message P (ApplicationImage.Payload P L))
    (next : ApplicationImage.State P L)
    (hnext : (plan.image deadlineOf).handle native message = some next) :
    ∃ cfg' : Config (compileCore prog fresh build).graph, next.Refines cfg' := by
  let image := plan.image deadlineOf
  change image.handle native message = some next at hnext
  cases message with
  | mk id payload =>
      cases payload with
      | malformed data => simp [ApplicationImage.handle] at hnext
      | choice address typed =>
          cases hlookup : image.lookup address with
          | none => simp [ApplicationImage.handle, hlookup] at hnext
          | some instruction =>
              cases instruction with
              | sample code => simp [ApplicationImage.handle, hlookup] at hnext
              | bind code => simp [ApplicationImage.handle, hlookup] at hnext
              | conditional code => simp [ApplicationImage.handle, hlookup] at hnext
              | publicChoice code =>
                  cases plan.origin_of_lookup deadlineOf address (.publicChoice code) hlookup with
                  | publicChoice site publicGuard =>
                      simp only [ApplicationImage.handle, hlookup, Option.bind_eq_bind,
                        Option.bind_some] at hnext
                      cases htyped : typed.as? (site.code fresh build).guard.ty with
                      | none => simp [htyped] at hnext
                      | some value =>
                          simp only [htyped, Option.bind_some] at hnext
                          cases hresolved : (site.code fresh build).endpoint.resolve?
                              native.memory.done
                              ((site.code fresh build).guard.validate native.memory.store)
                              ⟨id, value⟩ with
                          | none => simp [hresolved] at hnext
                          | some accepted =>
                              simp only [hresolved, Option.bind_some] at hnext
                              cases hnext
                              exact ⟨_, site.resolution_refines fresh build native cfg
                                hrefines publicGuard ⟨id, value⟩ accepted hresolved⟩
      | binding address handle =>
          cases hlookup : image.lookup address with
          | none => simp [ApplicationImage.handle, hlookup] at hnext
          | some instruction =>
              cases instruction with
              | sample code => simp [ApplicationImage.handle, hlookup] at hnext
              | publicChoice code => simp [ApplicationImage.handle, hlookup] at hnext
              | conditional code => simp [ApplicationImage.handle, hlookup] at hnext
              | bind code =>
                  cases plan.origin_of_lookup deadlineOf address (.bind code) hlookup with
                  | binding site unrestricted =>
                      simp only [ApplicationImage.handle, hlookup, Option.bind_eq_bind,
                        Option.bind_some] at hnext
                      split at hnext
                      · rename_i hadmitted
                        cases hnext
                        obtain ⟨value, ⟨step⟩, hsnapshot⟩ := site.binding_resolution_step
                          fresh build initial legal unrestricted native cfg hrefines.memory
                          hrefines.reachable (decisionSiteState site fresh build).nextField
                          handle hadmitted.2.1 hadmitted.2.2.2.1 hadmitted.2.2.2.2
                        exact ⟨_, hrefines.bind (compileCore prog fresh build).graphWF
                          _ (site.compiledNode fresh build) rfl rfl handle
                          (congrArg Prod.fst hadmitted.2.1) _ step hsnapshot⟩
                      · contradiction
      | conditional address payload =>
          cases hlookup : image.lookup address with
          | none => simp [ApplicationImage.handle, hlookup] at hnext
          | some instruction =>
              cases instruction with
              | sample code => simp [ApplicationImage.handle, hlookup] at hnext
              | publicChoice code => simp [ApplicationImage.handle, hlookup] at hnext
              | bind code => simp [ApplicationImage.handle, hlookup] at hnext
              | conditional code =>
                  cases plan.origin_of_lookup deadlineOf address (.conditional code) hlookup with
                  | conditional site publicGuard =>
                      let code := site.code fresh build (site.sourceField fresh build)
                        (deadlineOf (site.choice.publicationNode fresh build))
                      simp only [ApplicationImage.handle, hlookup, Option.bind_eq_bind,
                        Option.bind_some] at hnext
                      change ((code.decode payload).bind fun decoded =>
                        (code.endpoint.resolve? native.memory.clock (native.verify code)
                          (native.memory.accepted code.sourceField) native.memory.done
                          (code.canOpen native.memory.store) ⟨id, decoded⟩).bind
                            fun result => some (native.publishConditional code result)) =
                        some next at hnext
                      cases hdecoded : code.decode payload with
                      | none => simp only [hdecoded, Option.bind_none, reduceCtorEq] at hnext
                      | some decoded =>
                          simp only [hdecoded, Option.bind_some] at hnext
                          cases hresolved : code.endpoint.resolve? native.memory.clock
                              (native.verify code) (native.memory.accepted code.sourceField)
                              native.memory.done (code.canOpen native.memory.store)
                              ⟨id, decoded⟩ with
                          | none => simp [hresolved] at hnext
                          | some result =>
                              simp only [hresolved, Option.bind_some] at hnext
                              cases hnext
                              exact ⟨_, site.resolution_refines fresh build
                                (site.sourceField fresh build)
                                (deadlineOf (site.choice.publicationNode fresh build)) initial legal
                                native cfg hrefines publicGuard ⟨id, decoded⟩ result hresolved⟩

/-- Arbitrary native action lists retain a reachable source-graph witness.
Delivery, replay, rejection, and time advancement require no fairness premise
for this safety statement. -/
theorem run_refines (plan : ApplicationPlan accounted fresh build)
    (deadlineOf : Nat → Nat) (initial : VEnv L Γ) (legal : Legal prog)
    (state next : (plan.image deadlineOf).application.State)
    (actions : List (plan.image deadlineOf).application.Action)
    (hstate : ∃ cfg : Config (compileCore prog fresh build).graph,
      state.application.Refines cfg)
    (hnext : next ∈ ((plan.image deadlineOf).application.run actions state).support) :
    ∃ cfg : Config (compileCore prog fresh build).graph, next.application.Refines cfg := by
  apply (plan.image deadlineOf).application.run_application_invariant
    (fun native => ∃ cfg : Config (compileCore prog fresh build).graph, native.Refines cfg)
    (private_preserves_refinement _ _) _ (environment_preserves_refinement plan deadlineOf)
    state next actions hstate hnext
  rintro native message updated ⟨cfg, hrefines⟩ hupdated
  exact plan.handle_refines deadlineOf initial legal native cfg hrefines message updated hupdated

/-- The same safety result holds for arbitrary randomized players and
environments using the shared authenticated policy interface. -/
theorem runPolicies_refines (plan : ApplicationPlan accounted fresh build)
    (deadlineOf : Nat → Nat) (initial : VEnv L Γ) (legal : Legal prog)
    (players : P → (plan.image deadlineOf).application.PlayerPolicy)
    (environment : (plan.image deadlineOf).application.EnvironmentPolicy)
    (schedule : List (@MessageApplication.Invocation P))
    (execution next : (plan.image deadlineOf).application.PolicyExecution)
    (hstate : ∃ cfg : Config (compileCore prog fresh build).graph,
      execution.native.application.Refines cfg)
    (hnext : next ∈ ((plan.image deadlineOf).application.runPolicies
      players environment schedule execution).support) :
    ∃ cfg : Config (compileCore prog fresh build).graph, next.native.application.Refines cfg := by
  apply (plan.image deadlineOf).application.runPolicies_application_invariant
    (fun native => ∃ cfg : Config (compileCore prog fresh build).graph, native.Refines cfg)
    (private_preserves_refinement _ _) _ (environment_preserves_refinement plan deadlineOf)
    players environment schedule execution next hstate hnext
  rintro native message updated ⟨cfg, hrefines⟩ hupdated
  exact plan.handle_refines deadlineOf initial legal native cfg hrefines message updated hupdated

end Vegas.ApplicationPlan

/-- info: 'Vegas.ApplicationPlan.run_refines' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.ApplicationPlan.run_refines

/-- info: 'Vegas.ApplicationPlan.runPolicies_refines' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.ApplicationPlan.runPolicies_refines

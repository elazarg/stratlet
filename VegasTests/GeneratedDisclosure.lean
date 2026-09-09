/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import Vegas.Compile.ApplicationPlanOutcome
import VegasTests.DisclosureAccounting

/-! # Generated public application for optional disclosure

The complete accounting tree emits one opaque binding, two ordinary public
choice pairs, one source chance instruction, and one conditional publication.
The concrete run below uses the shared message application runner.
-/

noncomputable section

namespace VegasTests.GeneratedDisclosure

open Vegas Vegas.EventGraph Vegas.ToEventGraph Interaction
  GameTheory.Math.Probability
open VegasTests.OptionalDisclosure

def compilerInitial : BuildState TestPlayer simpleExpr source.Γ :=
  BuildState.fromInitial (initialState source.Γ source.env source.wctx)

def applicationPlan : ApplicationPlan DisclosureAccounting.optionalPlan
    source.fresh compilerInitial := by
  unfold DisclosureAccounting.optionalPlan DisclosureAccounting.optionalPlanWithPayoffs
  unfold core coreWithPayoffs
  apply ApplicationPlan.binding
  · intro _ _
    rfl
  apply ApplicationPlan.publicChoice
  · intro ref href
    change ref ∈ (∅ : Finset (FieldRef simpleExpr)) at href
    exact False.elim (Finset.notMem_empty ref href)
  apply ApplicationPlan.sample
  apply ApplicationPlan.conditional
  · intro ref href
    left
    change ref ∈ ({({ field := 0, ty := .bool } : FieldRef simpleExpr)} :
      Finset (FieldRef simpleExpr)) at href
    change _ = ({ field := 0, ty := .bool } : FieldRef simpleExpr)
    simpa using href
  apply ApplicationPlan.publicChoice
  · intro ref href
    change ref ∈ (∅ : Finset (FieldRef simpleExpr)) at href
    exact False.elim (Finset.notMem_empty ref href)
  apply ApplicationPlan.ret

def image : ApplicationImage TestPlayer simpleExpr :=
  applicationPlan.image (fun _ => 10)

def afterBinding : BuildState TestPlayer simpleExpr [(0, .sealed 0 .bool)] :=
  (compilerInitial.addCommitEvent (actionName := 0) (actionTy := BaseTy.bool)
    0 0 (.constBool true) source.fresh.1).1

def afterMarkerChoice : BuildState TestPlayer simpleExpr
    [(1, .sealed 0 .bool), (0, .sealed 0 .bool)] :=
  (afterBinding.addCommitEvent (actionName := 1) (actionTy := BaseTy.bool)
    1 0 (.notBool (.var 1 .here)) source.fresh.2.1).1

def beforeSignal : BuildState TestPlayer simpleExpr
    [(2, .pub .bool), (1, .sealed 0 .bool), (0, .sealed 0 .bool)] :=
  (afterMarkerChoice.addRevealEvent 2 0 .here source.fresh.2.2.1).1

def signalCode : SampleCode simpleExpr :=
  ApplicationPlan.headSampleCode source.fresh.2.2.2 beforeSignal

@[simp] theorem signalCode_node : signalCode.node = 3 := by
  change beforeSignal.nodes.length = 3
  simp [beforeSignal, afterMarkerChoice, afterBinding, compilerInitial]

theorem signalCode_requires : signalCode.requires = [0, 1, 2] := by
  unfold signalCode
  rw [ApplicationPlan.headSampleCode_requires source.fresh.2.2.2 beforeSignal
    ⟨3, by decide⟩ (by rfl)]
  decide

theorem image_lookup_signal : image.lookup 3 = some (.sample signalCode) := by
  have hmem : (ApplicationInstruction.sample (P := TestPlayer) signalCode) ∈
      applicationPlan.instructions (fun _ => 10) := by
    change _ ∈ [_, _, ApplicationInstruction.sample signalCode, _, _]
    simp
  simpa only [image, ApplicationInstruction.address, signalCode_node] using
    applicationPlan.image_lookup_of_mem (fun _ => 10) _ hmem

abbrev compiled := compile source

def initialExecution : image.application.State :=
  MessageApplication.State.initial image.application
    (ApplicationImage.State.initial (ApplicationImage.Memory.initial compiled.graph))

def prefixActions : List image.application.Action :=
  [.privateCommand 0 (.register 0 ⟨.bool, false⟩),
    .submit 0 (.binding 0 (0, 0)), .include (0, 0),
    .submit 0 (.choice 2 ⟨.bool, false⟩), .include (0, 1)]

def suffix : List image.application.Action :=
  [.submit 0 (.conditional 5 .decline), .include (0, 2),
    .submit 1 (.choice 7 ⟨.bool, false⟩), .include (1, 0)]

def actions : List image.application.Action :=
  prefixActions ++ .environment (.sample 3) :: suffix

def repeatedSampleActions : List image.application.Action :=
  prefixActions ++ .environment (.sample 3) :: .environment (.sample 3) :: suffix

def checkpoint : image.application.State :=
  let registered : image.application.State := { initialExecution with
    application := initialExecution.application.register 0 0 ⟨.bool, false⟩ }
  let submitted : image.application.State := { registered with
    pool := (registered.pool.submit 0 (.binding 0 (0, 0))).2 }
  let bound := image.application.includePending submitted (0, 0)
  let markerSubmitted : image.application.State := { bound with
    pool := (bound.pool.submit 0 (.choice 2 ⟨.bool, false⟩)).2 }
  image.application.includePending markerSubmitted (0, 1)

private theorem prefix_law :
    image.application.run prefixActions initialExecution = FinDist.pure checkpoint := by
  simp only [prefixActions, MessageApplication.run_cons, MessageApplication.run_nil,
    MessageApplication.step, FinDist.pure_bind]
  rfl

private theorem signal_distribution (reads : ReadEnv simpleExpr signalCode.dist.reads) :
    signalCode.dist.eval reads = fairCoin.denote := by
  unfold EventDist.eval EventDist.evalLaw
  change (if _ then fairCoin else fairCoin).denote = fairCoin.denote
  rw [ite_self]

private theorem checkpoint_sample_law :
    image.sample checkpoint.application 3 =
      fairCoin.denote.map (checkpoint.application.sample signalCode) := by
  have hreadable : (ReadEnv.ofStoreExec? checkpoint.application.memory.store
      signalCode.dist.reads).isSome = true := by decide
  obtain ⟨reads, hreads⟩ := Option.isSome_iff_exists.mp hreadable
  rw [image.sample_law checkpoint.application 3 signalCode image_lookup_signal
    (by decide) (by decide) reads hreads, signal_distribution]

def publicResult (execution : image.application.State) :
    Option Bool × Option Bool × Option (Option Bool) × Option Bool × Bool :=
  (Store.getAs execution.application.memory.store 2 .bool,
    Store.getAs execution.application.memory.store 3 .bool,
    Store.getAs execution.application.memory.store 5 (.option .bool),
    Store.getAs execution.application.memory.store 7 .bool,
    execution.application.memory.finished compiled.graph.nodeCount)

private theorem suffix_result (signal : Bool) :
    ((image.application.run suffix
      { checkpoint with application := checkpoint.application.sample signalCode signal }).map
        publicResult) =
      FinDist.pure (some false, some signal, some none, some false, true) := by
  cases signal <;>
    simp only [suffix, MessageApplication.run_cons, MessageApplication.run_nil,
      MessageApplication.step, FinDist.pure_bind, FinDist.map_pure] <;> rfl

/-- The generated chance instruction has the source coin law inside the
actual message-application execution. The environment supplies no outcome. -/
theorem public_result_law :
    ((image.application.run actions initialExecution).map publicResult) =
      fairCoin.denote.map fun signal =>
        (some false, some signal, some none, some false, true) := by
  rw [actions, MessageApplication.run_append, prefix_law, FinDist.pure_bind]
  change (((image.sample checkpoint.application 3).map
    (fun native => { checkpoint with application := native })).bind
      (image.application.run suffix)).map publicResult = _
  rw [checkpoint_sample_law]
  simp only [FinDist.bind_map, FinDist.map_bind, suffix_result]
  rfl

/-- Invoking the completed chance instruction again cannot redraw its value. -/
theorem repeated_sample_public_result_law :
    ((image.application.run repeatedSampleActions initialExecution).map publicResult) =
      fairCoin.denote.map fun signal =>
        (some false, some signal, some none, some false, true) := by
  rw [repeatedSampleActions, MessageApplication.run_append, prefix_law, FinDist.pure_bind]
  change (((image.sample checkpoint.application 3).map
    (fun native => { checkpoint with application := native })).bind
      (image.application.run (.environment (.sample 3) :: suffix))).map publicResult = _
  rw [checkpoint_sample_law]
  simp only [FinDist.bind_map, FinDist.map_bind]
  conv_rhs => rw [FinDist.map_eq_bind]
  apply FinDist.bind_congr
  intro signal _hsignal
  change (((image.sample (checkpoint.application.sample signalCode signal) 3).map
    (fun native => { checkpoint with application := native })).bind
      (image.application.run suffix)).map publicResult = _
  rw [ApplicationImage.sample_after_completion image _ 3 signalCode
    image_lookup_signal signal]
  simpa only [FinDist.map_pure, FinDist.pure_bind] using suffix_result signal

private theorem run_finished_of_support (next : image.application.State)
    (hnext : next ∈ (image.application.run actions initialExecution).support) :
    next.application.memory.finished compiled.graph.nodeCount = true := by
  have hresult : publicResult next ∈
      ((image.application.run actions initialExecution).map publicResult).support := by
    rw [FinDist.support_map]
    exact ⟨next, hnext, rfl⟩
  rw [public_result_law, FinDist.support_map] at hresult
  obtain ⟨signal, _hsignal, heq⟩ := hresult
  exact congrArg (fun result => result.2.2.2.2) heq.symm

/-- At least one completed execution of the generated image has an actual
written-order source execution and the same executable public terminal
bindings. This is an inhabited safety witness, not a strategy-law theorem. -/
theorem completed_source_public_outcome_exists :
    ∃ (next : image.application.State)
      (terminalEnv : VEnv simpleExpr compiled.terminalCtx),
      next ∈ (image.application.run actions initialExecution).support ∧
      SmallStep.Star
        { ctx := source.Γ, env := source.env, cont := source.prog }
        { ctx := compiled.terminalCtx, env := terminalEnv,
          cont := .ret compiled.sourcePayoffs } ∧
      compiled.readPublicTerminal? next.application.memory =
        some terminalEnv.erasePubEnv := by
  let law := image.application.run actions initialExecution
  obtain ⟨next, hnext⟩ := law.support_nonempty
  obtain ⟨terminalEnv, hstar, hreadout⟩ :=
    applicationPlan.run_source_public_outcome DisclosureAccounting.optionalChecked
      (fun _ => 10) actions next hnext (run_finished_of_support next hnext)
  exact ⟨next, terminalEnv, hnext, hstar, hreadout⟩

end VegasTests.GeneratedDisclosure

/-- info: 'VegasTests.GeneratedDisclosure.public_result_law' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms VegasTests.GeneratedDisclosure.public_result_law

/-- info: 'VegasTests.GeneratedDisclosure.repeated_sample_public_result_law' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms VegasTests.GeneratedDisclosure.repeated_sample_public_result_law

/-- info: 'VegasTests.GeneratedDisclosure.completed_source_public_outcome_exists' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms VegasTests.GeneratedDisclosure.completed_source_public_outcome_exists

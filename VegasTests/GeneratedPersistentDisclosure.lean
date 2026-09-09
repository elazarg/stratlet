/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import Vegas.Compile.ApplicationPlanOutcome
import VegasTests.DisclosureAccounting

/-! # Generated application for persistent disclosure

The persistent source has two conditional-publication sites for the same
original sealed binding.  The first site accounts for that binding; the later
ordinary commit/reveal is generated with `ApplicationPlan.conditionalCopy`.
The concrete executions below use the shared message-application runner.
-/

noncomputable section

namespace VegasTests.GeneratedPersistentDisclosure

open Vegas Vegas.EventGraph Vegas.ToEventGraph Interaction
  GameTheory.Math.Probability
open VegasTests.PersistentDisclosure

def secondSpecification : ConditionalOpening
    (P := TestPlayer) (L := simpleExpr) (Γ := SecondContext)
    (copyName := 8) (who := 0) (copyTy := .option .bool) secondGuard where
  secretTy := .bool
  source := 0
  binding := .there (.there (.there (.there (.there (.there (.there .here))))))
  encoding := Equiv.refl (Option Bool)
  sound := second_guard_sound
  decline_legal := second_decline_legal

def compilerInitial : BuildState TestPlayer simpleExpr source.Γ :=
  BuildState.fromInitial (initialState source.Γ source.env source.wctx)

def applicationPlan : ApplicationPlan DisclosureAccounting.persistentPlan
    source.fresh compilerInitial := by
  unfold DisclosureAccounting.persistentPlan core
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
  apply ApplicationPlan.conditionalCopy secondSpecification
  · intro ref href
    have hmem : ref ∈ ({({ field := 0, ty := .bool } : FieldRef simpleExpr),
        ({ field := 5, ty := .option .bool } : FieldRef simpleExpr)} :
          Finset (FieldRef simpleExpr)) := by
      revert ref
      decide
    simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
    rcases hmem with rfl | rfl
    · left
      rfl
    · right
      exact ⟨⟨.option .bool, none, .event 5⟩, rfl, rfl, rfl⟩
  apply ApplicationPlan.ret

def image : ApplicationImage PersistentDisclosure.Player simpleExpr :=
  applicationPlan.image (fun _ => 10)

abbrev compiled := compile source

def initialExecution : image.application.State :=
  MessageApplication.State.initial image.application
    (ApplicationImage.State.initial (ApplicationImage.Memory.initial compiled.graph))

def prefixActions (secret : Bool) : List image.application.Action :=
  [.privateCommand 0 (.register 0 ⟨.bool, secret⟩),
    .submit 0 (.binding 0 (0, 0)), .include (0, 0),
    .submit 0 (.choice 2 ⟨.bool, false⟩), .include (0, 1)]

def checkpoint (secret : Bool) : image.application.State :=
  let registered : image.application.State := { initialExecution with
    application := initialExecution.application.register 0 0 ⟨.bool, secret⟩ }
  let submitted : image.application.State := { registered with
    pool := (registered.pool.submit 0 (.binding 0 (0, 0))).2 }
  let bound := image.application.includePending submitted (0, 0)
  let markerSubmitted : image.application.State := { bound with
    pool := (bound.pool.submit 0 (.choice 2 ⟨.bool, false⟩)).2 }
  image.application.includePending markerSubmitted (0, 1)

private theorem prefix_law (secret : Bool) :
    image.application.run (prefixActions secret) initialExecution =
      FinDist.pure (checkpoint secret) := by
  simp only [prefixActions, MessageApplication.run_cons, MessageApplication.run_nil,
    MessageApplication.step, FinDist.pure_bind]
  rfl

def beforeSignal : BuildState TestPlayer simpleExpr
    [(2, .pub .bool), (1, .sealed 0 .bool), (0, .sealed 0 .bool)] :=
  let afterBinding :=
    (compilerInitial.addCommitEvent (actionName := 0) (actionTy := BaseTy.bool)
      0 0 (.constBool true) source.fresh.1).1
  let afterMarker :=
    (afterBinding.addCommitEvent (actionName := 1) (actionTy := BaseTy.bool)
      1 0 (.notBool (.var 1 .here)) source.fresh.2.1).1
  (afterMarker.addRevealEvent 2 0 .here source.fresh.2.2.1).1

def afterSignal : BuildState TestPlayer simpleExpr FirstContext :=
  (beforeSignal.addSampleEvent 3 (.weighted (b := .bool) fairCoin)
    source.fresh.2.2.2.1).1

abbrev ResponseContext : VCtx TestPlayer simpleExpr :=
  [(5, .pub (.option .bool)), (4, .sealed 0 (.option .bool))] ++ FirstContext

def beforeResponse : BuildState TestPlayer simpleExpr
    ResponseContext :=
  let chosen : BuildState TestPlayer simpleExpr
      ((4, .sealed 0 (.option .bool)) :: FirstContext) :=
    (afterSignal.addCommitEvent (actionName := 4)
      (actionTy := BaseTy.option BaseTy.bool)
      4 0 firstGuard source.fresh.2.2.2.2.1).1
  (BuildState.addRevealEvent (P := TestPlayer) (L := simpleExpr)
    (Γ := (4, .sealed 0 (.option .bool)) :: FirstContext)
    (sourceName := 4) (ty := BaseTy.option BaseTy.bool)
    chosen 5 0 .here source.fresh.2.2.2.2.2.1).1

def beforeSecond : BuildState TestPlayer simpleExpr SecondContext :=
  let responded : BuildState TestPlayer simpleExpr
      ((6, .sealed 1 .bool) :: ResponseContext) :=
    (beforeResponse.addCommitEvent (actionName := 6) (actionTy := BaseTy.bool)
      6 1 (.constBool true)
      source.fresh.2.2.2.2.2.2.1).1
  (BuildState.addRevealEvent (P := TestPlayer) (L := simpleExpr)
    (Γ := (6, .sealed 1 .bool) ::
      ResponseContext)
    (sourceName := 6) (ty := BaseTy.bool)
    responded 7 1 .here source.fresh.2.2.2.2.2.2.2.1).1

def terminalCore : VegasCore TestPlayer simpleExpr
    ((9, .pub (.option .bool)) :: (8, .sealed 0 (.option .bool)) :: SecondContext) :=
  .ret [(0, payoff)]

def secondCore : VegasCore TestPlayer simpleExpr SecondContext :=
  .commit 8 0 secondGuard (.reveal 9 0 8 .here terminalCore)

def secondSite : ConditionalPublicationSite secondCore :=
  ConditionalPublicationSite.atHead (P := TestPlayer) (L := simpleExpr)
    (Γ := SecondContext) (ty := BaseTy.option BaseTy.bool)
    8 9 0 secondGuard terminalCore secondSpecification

def secondCode : ConditionalCode TestPlayer simpleExpr :=
  secondSite.code source.fresh.2.2.2.2.2.2.2.2 beforeSecond
    (secondSite.sourceField source.fresh.2.2.2.2.2.2.2.2 beforeSecond) 10

@[simp] theorem secondCode_publicationNode : secondCode.endpoint.publicationNode = 9 := rfl

@[simp] theorem secondCode_sourceField : secondCode.sourceField = 0 := rfl

theorem image_lookup_second : image.lookup 9 = some (.conditional secondCode) := by
  have hmem : (ApplicationInstruction.conditional secondCode) ∈
      applicationPlan.instructions (fun _ => 10) := by
    change _ ∈ [_, _, _, _, _, ApplicationInstruction.conditional secondCode]
    simp
  simpa only [image, ApplicationInstruction.address, secondCode_publicationNode] using
    applicationPlan.image_lookup_of_mem (fun _ => 10) _ hmem

def signalCode : SampleCode simpleExpr :=
  ApplicationPlan.headSampleCode source.fresh.2.2.2 beforeSignal

@[simp] theorem signalCode_node : signalCode.node = 3 := by
  change beforeSignal.nodes.length = 3
  simp [beforeSignal, compilerInitial]

theorem image_lookup_signal : image.lookup 3 = some (.sample signalCode) := by
  have hmem : (ApplicationInstruction.sample (P := TestPlayer) signalCode) ∈
      applicationPlan.instructions (fun _ => 10) := by
    change _ ∈ [_, _, ApplicationInstruction.sample signalCode, _, _, _]
    simp
  simpa only [image, ApplicationInstruction.address, signalCode_node] using
    applicationPlan.image_lookup_of_mem (fun _ => 10) _ hmem

/-- The later generated conditional instruction reuses source field zero at
nodes 8--9, distinct from the first conditional pair at nodes 4--5. -/
theorem second_site_metadata :
    secondCode.sourceField = 0 ∧ secondCode.endpoint.choiceNode = 8 ∧
      secondCode.endpoint.publicationNode = 9 ∧
      secondCode.endpoint.choiceNode ≠ 4 ∧ secondCode.endpoint.publicationNode ≠ 5 := by
  decide

private theorem signal_distribution (reads : ReadEnv simpleExpr signalCode.dist.reads) :
    signalCode.dist.eval reads = fairCoin.denote := by
  rfl

private theorem checkpoint_sample_law (secret : Bool) :
    image.sample (checkpoint secret).application 3 =
      fairCoin.denote.map ((checkpoint secret).application.sample signalCode) := by
  have hreadable : (ReadEnv.ofStoreExec? (checkpoint secret).application.memory.store
      signalCode.dist.reads).isSome = true := by
    cases secret <;> decide
  obtain ⟨reads, hreads⟩ := Option.isSome_iff_exists.mp hreadable
  rw [image.sample_law (checkpoint secret).application 3 signalCode image_lookup_signal
    (by cases secret <;> decide) (by cases secret <;> decide) reads hreads,
    signal_distribution]

def firstOpeningSuffix (secret : Bool) : List image.application.Action :=
  [.submit 0 (.conditional 5 (.opening (0, 0) ⟨.bool, secret⟩)), .include (0, 2),
    .submit 1 (.choice 7 ⟨.bool, false⟩), .include (1, 0)]

def reregisterSuffix (secret : Bool) : List image.application.Action :=
  [.privateCommand 0 (.register 0 ⟨.bool, !secret⟩)]

def secondOpeningSuffix (secret : Bool) : List image.application.Action :=
  [.submit 0 (.conditional 9 (.opening (0, 0) ⟨.bool, secret⟩)), .include (0, 3)]

def openingSuffix (secret : Bool) : List image.application.Action :=
  firstOpeningSuffix secret ++ reregisterSuffix secret ++ secondOpeningSuffix secret

def openingActions (secret : Bool) : List image.application.Action :=
  prefixActions secret ++ .environment (.sample 3) :: openingSuffix secret

def publicResult (execution : image.application.State) :
    Option Bool × Option Bool × Option (Option Bool) × Option Bool ×
      Option (Option Bool) × Bool :=
  (Store.getAs execution.application.memory.store 2 .bool,
    Store.getAs execution.application.memory.store 3 .bool,
    Store.getAs execution.application.memory.store 5 (.option .bool),
    Store.getAs execution.application.memory.store 7 .bool,
    Store.getAs execution.application.memory.store 9 (.option .bool),
    execution.application.memory.finished compiled.graph.nodeCount)

def afterResponse (secret signal : Bool) : image.application.State :=
  let sampled : image.application.State := { checkpoint secret with
    application := (checkpoint secret).application.sample signalCode signal }
  let openingSubmitted : image.application.State := { sampled with
    pool := (sampled.pool.submit 0
      (.conditional 5 (.opening (0, 0) ⟨.bool, secret⟩))).2 }
  let opened := image.application.includePending openingSubmitted (0, 2)
  let responseSubmitted : image.application.State := { opened with
    pool := (opened.pool.submit 1 (.choice 7 ⟨.bool, false⟩)).2 }
  image.application.includePending responseSubmitted (1, 0)

def afterFirstOpening (secret signal : Bool) : image.application.State :=
  let responded := afterResponse secret signal
  { responded with application := responded.application.register 0 0 ⟨.bool, !secret⟩ }

def secondSubmitted (secret signal : Bool) : image.application.State :=
  let before := afterFirstOpening secret signal
  { before with pool := (before.pool.submit 0
      (.conditional 9 (.opening (0, 0) ⟨.bool, secret⟩))).2 }

private theorem afterFirstOpening_pool_shape (secret signal : Bool) :
    (afterFirstOpening secret signal).pool.pending = [] ∧
      (afterFirstOpening secret signal).pool.nextSerial 0 = 3 := by
  cases secret <;> cases signal <;>
    simp [afterFirstOpening, afterResponse, checkpoint, initialExecution,
      MessageApplication.State.initial, MessageApplication.includePending_pool,
      MessagePool.includePending, MessagePool.lookup, MessagePool.submit,
      MessagePool.empty, MessagePool.removeFirst]

private theorem first_opening_suffix_law (secret signal : Bool) :
    image.application.run (firstOpeningSuffix secret)
      { checkpoint secret with
        application := (checkpoint secret).application.sample signalCode signal } =
      FinDist.pure (afterResponse secret signal) := by
  cases secret <;> cases signal <;>
    simp only [firstOpeningSuffix, MessageApplication.run_cons,
      MessageApplication.run_nil, MessageApplication.step, FinDist.pure_bind] <;> rfl

private theorem reregister_suffix_law (secret signal : Bool) :
    image.application.run (reregisterSuffix secret) (afterResponse secret signal) =
      FinDist.pure (afterFirstOpening secret signal) := by
  simp only [reregisterSuffix, MessageApplication.run_cons, MessageApplication.run_nil,
    MessageApplication.step, FinDist.pure_bind]
  rfl

private theorem second_opening_ready (secret signal : Bool) :
    secondCode.endpoint.ready
      ((secondSubmitted secret signal).application.memory.accepted secondCode.sourceField)
      (secondSubmitted secret signal).application.memory.done = true := by
  cases secret <;> cases signal <;> decide +kernel

private theorem second_opening_verified (secret signal : Bool) :
    (secondSubmitted secret signal).application.verify secondCode ⟨(0, 0), secret⟩ = true := by
  cases secret <;> cases signal <;> decide +kernel

private theorem second_opening_valid (secret signal : Bool) :
    secondCode.canOpen (secondSubmitted secret signal).application.memory.store secret = true := by
  cases secret <;> cases signal <;> decide +kernel

private theorem second_published_result (secret signal : Bool) :
    publicResult { secondSubmitted secret signal with
      application := (secondSubmitted secret signal).application.publishConditional
        secondCode (some secret) } =
      (some false, some signal, some (some secret), some false,
        some (some secret), true) := by
  cases secret <;> cases signal <;> decide +kernel

private theorem second_opening_suffix_result (secret signal : Bool) :
    ((image.application.run (secondOpeningSuffix secret) (afterFirstOpening secret signal)).map
      publicResult) =
      FinDist.pure
        (some false, some signal, some (some secret), some false,
          some (some secret), true) := by
  have hlookup : (secondSubmitted secret signal).pool.lookup (0, 3) =
      some ⟨(0, 3), .conditional 9 (.opening (0, 0) ⟨.bool, secret⟩)⟩ := by
    obtain ⟨hpending, hserial⟩ := afterFirstOpening_pool_shape secret signal
    simp [secondSubmitted, MessagePool.lookup, MessagePool.submit, hpending, hserial]
  have hresolve : secondCode.endpoint.resolve?
      (secondSubmitted secret signal).application.memory.clock
      ((secondSubmitted secret signal).application.verify secondCode)
      ((secondSubmitted secret signal).application.memory.accepted secondCode.sourceField)
      (secondSubmitted secret signal).application.memory.done
      (secondCode.canOpen (secondSubmitted secret signal).application.memory.store)
      ⟨(0, 3), .opening (0, 0) secret⟩ = some (some secret) := by
    apply (secondCode.endpoint.resolve_opening _ _ _ _ _ _ (0, 0) secret rfl).2
    exact ⟨second_opening_ready secret signal, rfl, rfl,
      second_opening_verified secret signal, second_opening_valid secret signal⟩
  have happ := (image.include_conditional (secondSubmitted secret signal) 9 secondCode
    image_lookup_second (0, 3) (.opening (0, 0) ⟨.bool, secret⟩)
    (.opening (0, 0) secret) rfl (some secret) hlookup hresolve).1
  simp only [secondOpeningSuffix, MessageApplication.run_cons, MessageApplication.run_nil,
    MessageApplication.step, FinDist.pure_bind, FinDist.map_pure]
  apply congrArg FinDist.pure
  change publicResult (image.application.includePending (secondSubmitted secret signal) (0, 3)) = _
  unfold publicResult
  rw [show (image.application.includePending (secondSubmitted secret signal) (0, 3)).application =
      (secondSubmitted secret signal).application.publishConditional secondCode (some secret)
      from happ]
  exact second_published_result secret signal

private theorem opening_suffix_result (secret signal : Bool) :
    ((image.application.run (openingSuffix secret)
      { checkpoint secret with
        application := (checkpoint secret).application.sample signalCode signal }).map
      publicResult) =
      FinDist.pure
        (some false, some signal, some (some secret), some false,
          some (some secret), true) := by
  rw [openingSuffix, List.append_assoc, MessageApplication.run_append,
    first_opening_suffix_law,
    FinDist.pure_bind, MessageApplication.run_append, reregister_suffix_law,
    FinDist.pure_bind, second_opening_suffix_result]

/-- Both generated conditional sites accept the same opening of the original
frozen binding. The two sites have distinct output nodes but share source slot
zero, and the final state is operationally complete. -/
theorem opening_public_result_law (secret : Bool) :
    ((image.application.run (openingActions secret) initialExecution).map publicResult) =
      fairCoin.denote.map fun signal =>
        (some false, some signal, some (some secret), some false,
          some (some secret), true) := by
  rw [openingActions, MessageApplication.run_append, prefix_law, FinDist.pure_bind]
  simp only [MessageApplication.run_cons, MessageApplication.step,
    ApplicationImage.application, checkpoint_sample_law,
    FinDist.bind_map, FinDist.map_bind]
  rw [FinDist.map_eq_bind]
  apply FinDist.bind_congr
  intro signal _
  exact opening_suffix_result secret signal

private theorem opening_run_finished_of_support (secret : Bool)
    (next : image.application.State)
    (hnext : next ∈ (image.application.run (openingActions secret) initialExecution).support) :
    next.application.memory.finished compiled.graph.nodeCount = true := by
  have hresult : publicResult next ∈
      ((image.application.run (openingActions secret) initialExecution).map
        publicResult).support := by
    rw [FinDist.support_map]
    exact ⟨next, hnext, rfl⟩
  rw [opening_public_result_law, FinDist.support_map] at hresult
  obtain ⟨signal, _hsignal, heq⟩ := hresult
  exact congrArg (fun result => result.2.2.2.2.2) heq.symm

/-- Every supported completed execution in the opening law has an actual
written-order source execution with the same executable public terminal
bindings. This remains a support-level safety statement, not a strategy law. -/
theorem opening_source_public_outcome (secret : Bool)
    (next : image.application.State)
    (hnext : next ∈ (image.application.run (openingActions secret) initialExecution).support) :
    ∃ terminalEnv : VEnv simpleExpr compiled.terminalCtx,
      SmallStep.Star
        { ctx := source.Γ, env := source.env, cont := source.prog }
        { ctx := compiled.terminalCtx, env := terminalEnv,
          cont := .ret compiled.sourcePayoffs } ∧
      compiled.readPublicTerminal? next.application.memory =
        some terminalEnv.erasePubEnv := by
  exact applicationPlan.run_source_public_outcome DisclosureAccounting.persistentChecked
    (fun _ => 10) (openingActions secret) next hnext
    (opening_run_finished_of_support secret next hnext)

def firstRefusalSuffix : List image.application.Action :=
  [.submit 0 (.conditional 5 .decline), .include (0, 2),
    .submit 1 (.choice 7 ⟨.bool, false⟩), .include (1, 0)]

def rejectedOpeningSuffix (secret : Bool) : List image.application.Action :=
  [.submit 0 (.conditional 9 (.opening (0, 0) ⟨.bool, secret⟩)), .include (0, 3)]

def laterDeclineSuffix : List image.application.Action :=
  [.submit 0 (.conditional 9 .decline), .include (0, 4)]

def refusalSuffix (secret : Bool) : List image.application.Action :=
  firstRefusalSuffix ++ rejectedOpeningSuffix secret ++ laterDeclineSuffix

def afterFirstRefusal (secret signal : Bool) : image.application.State :=
  let sampled : image.application.State := { checkpoint secret with
    application := (checkpoint secret).application.sample signalCode signal }
  let refusalSubmitted : image.application.State := { sampled with
    pool := (sampled.pool.submit 0 (.conditional 5 .decline)).2 }
  let refused := image.application.includePending refusalSubmitted (0, 2)
  let responseSubmitted : image.application.State := { refused with
    pool := (refused.pool.submit 1 (.choice 7 ⟨.bool, false⟩)).2 }
  image.application.includePending responseSubmitted (1, 0)

def afterRejectedOpening (secret signal : Bool) : image.application.State :=
  let before := afterFirstRefusal secret signal
  let submitted : image.application.State := { before with
    pool := (before.pool.submit 0
      (.conditional 9 (.opening (0, 0) ⟨.bool, secret⟩))).2 }
  image.application.includePending submitted (0, 3)

private theorem first_refusal_suffix_law (secret signal : Bool) :
    image.application.run firstRefusalSuffix
      { checkpoint secret with
        application := (checkpoint secret).application.sample signalCode signal } =
      FinDist.pure (afterFirstRefusal secret signal) := by
  cases secret <;> cases signal <;>
    simp only [firstRefusalSuffix, MessageApplication.run_cons,
      MessageApplication.run_nil, MessageApplication.step, FinDist.pure_bind] <;> rfl

private theorem rejected_opening_suffix_law (secret signal : Bool) :
    image.application.run (rejectedOpeningSuffix secret) (afterFirstRefusal secret signal) =
      FinDist.pure (afterRejectedOpening secret signal) := by
  cases secret <;> cases signal <;>
    simp only [rejectedOpeningSuffix, MessageApplication.run_cons,
      MessageApplication.run_nil, MessageApplication.step, FinDist.pure_bind] <;> rfl

private theorem later_decline_suffix_result (secret signal : Bool) :
    ((image.application.run laterDeclineSuffix (afterRejectedOpening secret signal)).map
      (fun execution =>
        (Store.getAs (L := simpleExpr) execution.application.memory.store 5 (.option .bool),
          Store.getAs (L := simpleExpr) execution.application.memory.store 9 (.option .bool),
          execution.receipts, execution.application.memory.finished compiled.graph.nodeCount))) =
      FinDist.pure
        (some (none : Option Bool), some (none : Option Bool),
          [((0, 0), true), ((0, 1), true), ((0, 2), true), ((1, 0), true),
            ((0, 3), false), ((0, 4), true)], true) := by
  cases secret <;> cases signal <;>
    simp only [laterDeclineSuffix, MessageApplication.run_cons,
      MessageApplication.run_nil, MessageApplication.step, FinDist.pure_bind,
      FinDist.map_pure] <;> rfl

/-- After a first-site decline, a later opening of the retained snapshot is
rejected by the second source guard. The distinguished later decline remains
legal and completes the generated pair. -/
theorem refusal_rejects_later_opening (secret signal : Bool) :
    ((image.application.run (refusalSuffix secret)
      { checkpoint secret with
        application := (checkpoint secret).application.sample signalCode signal }).map
      (fun execution =>
        (Store.getAs (L := simpleExpr) execution.application.memory.store 5 (.option .bool),
          Store.getAs (L := simpleExpr) execution.application.memory.store 9 (.option .bool),
          execution.receipts, execution.application.memory.finished compiled.graph.nodeCount))) =
      FinDist.pure
        (some (none : Option Bool), some (none : Option Bool),
          [((0, 0), true), ((0, 1), true), ((0, 2), true), ((1, 0), true),
            ((0, 3), false), ((0, 4), true)], true) := by
  rw [refusalSuffix, List.append_assoc, MessageApplication.run_append,
    first_refusal_suffix_law, FinDist.pure_bind, MessageApplication.run_append,
    rejected_opening_suffix_law, FinDist.pure_bind, later_decline_suffix_result]

end VegasTests.GeneratedPersistentDisclosure

/-- info: 'VegasTests.GeneratedPersistentDisclosure.secondSpecification' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms VegasTests.GeneratedPersistentDisclosure.secondSpecification

/-- info: 'VegasTests.GeneratedPersistentDisclosure.applicationPlan' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms VegasTests.GeneratedPersistentDisclosure.applicationPlan

/-- info: 'VegasTests.GeneratedPersistentDisclosure.opening_public_result_law' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms VegasTests.GeneratedPersistentDisclosure.opening_public_result_law

/-- info: 'VegasTests.GeneratedPersistentDisclosure.refusal_rejects_later_opening' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms VegasTests.GeneratedPersistentDisclosure.refusal_rejects_later_opening

/-- info: 'VegasTests.GeneratedPersistentDisclosure.opening_source_public_outcome' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms VegasTests.GeneratedPersistentDisclosure.opening_source_public_outcome

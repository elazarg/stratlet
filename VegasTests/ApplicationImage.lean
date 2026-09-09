/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import Vegas.Compile.ApplicationImageRefinement
import Vegas.Compile.ApplicationPlanAllocation
import VegasTests.Game

/-! # A mixed-type generated public-choice image

Two adjacent source choice/reveal pairs compile into one runtime image.  The
first choice is a Boolean constrained by an initial public Boolean; the second
is an unrestricted optional Boolean owned by the other player.  The examples
exercise the shared message application's raw-traffic and replay boundaries.
-/

noncomputable section

namespace VegasTests.ApplicationImage

open Vegas Vegas.EventGraph Vegas.ToEventGraph Interaction
  GameTheory.Math.Probability

abbrev Player := Fin 2
abbrev InitialContext : VCtx Player simpleExpr := [(0, .pub .bool)]

def firstGuard :
    Expr ((1, .bool) :: eraseVCtx (viewVCtx (0 : Player) InitialContext)) .bool :=
  .eq (.var 1 .here) (.var 0 (.there .here))

abbrev FirstPublishedContext : VCtx Player simpleExpr :=
  [(2, .pub .bool), (1, .sealed 0 .bool), (0, .pub .bool)]

def secondGuard :
    Expr ((3, .option .bool) ::
      eraseVCtx (viewVCtx (1 : Player) FirstPublishedContext)) .bool :=
  .constBool true

def secondTail : VegasCore Player simpleExpr
    ((4, .pub (.option .bool)) :: (3, .sealed 1 (.option .bool)) ::
      FirstPublishedContext) :=
  .ret []

def firstTail : VegasCore Player simpleExpr
    ((2, .pub .bool) :: (1, .sealed 0 .bool) :: InitialContext) :=
  .commit 3 1 secondGuard (.reveal 4 1 3 .here secondTail)

def core : VegasCore Player simpleExpr InitialContext :=
  .commit 1 0 firstGuard (.reveal 2 0 1 .here firstTail)

def source : GraphProgram Player simpleExpr where
  Γ := InitialContext
  prog := core
  env := (VEnv.empty simpleExpr).cons true
  wctx := by simp [InitialContext, WFCtx]
  fresh := by simp [core, firstTail, secondTail, FreshBindings, Fresh]

def checked : WFProgram Player simpleExpr where
  core := source
  accounted := CommitmentAccounting.ofRevealComplete core source.fresh []
    (by simp) (by decide)
  legal := by
    change Legal core
    unfold core firstTail
    constructor
    · intro env
      exact ⟨env.get .here, by simp [evalGuard, firstGuard, evalExpr]⟩
    · constructor
      · intro _
        exact ⟨none, rfl⟩
      · trivial

def compilerInitial : BuildState Player simpleExpr source.Γ :=
  BuildState.fromInitial (initialState source.Γ source.env source.wctx)

def firstSite : PublicChoiceSite source.prog where
  context := InitialContext
  choiceName := 1
  publicName := 2
  owner := 0
  ty := .bool
  guard := firstGuard
  tail := firstTail
  decision := .here _ _
  adjacent := rfl

def secondSite : PublicChoiceSite source.prog where
  context := FirstPublishedContext
  choiceName := 3
  publicName := 4
  owner := 1
  ty := .option .bool
  guard := secondGuard
  tail := secondTail
  decision := .commit (.reveal (.here _ _))
  adjacent := rfl

theorem first_publicly_validatable :
    firstSite.PubliclyValidatable source.fresh compilerInitial := by
  intro ref href
  change ref ∈ ({({ field := 0, ty := .bool } : FieldRef simpleExpr)} :
    Finset (FieldRef simpleExpr)) at href
  have href' : ref = ({ field := 0, ty := .bool } : FieldRef simpleExpr) := by
    simpa using href
  subst ref
  exact ⟨⟨.bool, none, .initial true⟩, rfl, rfl, rfl⟩

theorem second_publicly_validatable :
    secondSite.PubliclyValidatable source.fresh compilerInitial := by
  intro ref href
  change ref ∈ (∅ : Finset (FieldRef simpleExpr)) at href
  simp at href

def applicationPlan : ApplicationPlan checked.accounted source.fresh compilerInitial := by
  apply ApplicationPlan.publicChoice
  · exact first_publicly_validatable
  apply ApplicationPlan.publicChoice
  · exact second_publicly_validatable
  apply ApplicationPlan.ret

def image : Vegas.ApplicationImage Player simpleExpr :=
  applicationPlan.image (fun _ => 0)

theorem generated_full_node_coverage :
    (applicationPlan.instructions (fun _ => 0)).flatMap
        ApplicationInstruction.coveredNodes = List.range 4 := by
  have hcoverage := applicationPlan.coveredNodes_eq_range (fun _ => 0)
  change _ = List.range 4 at hcoverage
  change List.range 0 ++ _ = List.range 4 at hcoverage
  simpa only [List.range_zero, List.nil_append] using hcoverage

/-- The public input occupies field zero; generated instructions allocate only
the four subsequent fields, with no separate handwritten allocation table. -/
theorem generated_full_field_allocation :
    (applicationPlan.instructions (fun _ => 0)).flatMap
        ApplicationInstruction.allocatedFields = [1, 2, 3, 4] := by
  rw [applicationPlan.allocatedFields_eq_map, generated_full_node_coverage]
  rfl

def firstCode : PublicChoiceCode Player simpleExpr :=
  firstSite.code source.fresh compilerInitial

def secondCode : PublicChoiceCode Player simpleExpr :=
  secondSite.code source.fresh compilerInitial

def firstAddress : Nat := firstCode.endpoint.publicationNode
def secondAddress : Nat := secondCode.endpoint.publicationNode

abbrev compiled := compileCore source.prog source.fresh compilerInitial

def initialMemory : Vegas.ApplicationImage.Memory Player simpleExpr :=
  Vegas.ApplicationImage.Memory.initial compiled.graph

theorem initial_represents : initialMemory.Represents (Config.initial compiled.graph) :=
  Vegas.ApplicationImage.Memory.initial_represents compiled.graph

def initialState : Vegas.ApplicationImage.State Player simpleExpr :=
  Vegas.ApplicationImage.State.initial initialMemory

def initialExecution : image.application.State :=
  MessageApplication.State.initial image.application initialState

def firstMessage : Message Player (Vegas.ApplicationImage.Payload Player simpleExpr) :=
  ⟨(0, 0), .choice firstAddress ⟨.bool, true⟩⟩

def firstSubmitted : image.application.State :=
  { initialExecution with pool := (initialExecution.pool.submit 0 firstMessage.payload).2 }

def firstIncluded : image.application.State :=
  image.application.includePending firstSubmitted (0, 0)

def secondMessage : Message Player (Vegas.ApplicationImage.Payload Player simpleExpr) :=
  ⟨(1, 0), .choice secondAddress ⟨.option .bool, some false⟩⟩

def secondSubmitted : image.application.State :=
  { firstIncluded with pool := (firstIncluded.pool.submit 1 secondMessage.payload).2 }

def finalExecution : image.application.State :=
  image.application.includePending secondSubmitted (1, 0)

def acceptedActions : List image.application.Action :=
  [.submit 0 firstMessage.payload, .include (0, 0),
    .submit 1 secondMessage.payload, .include (1, 0)]

theorem image_lookup_first : image.lookup firstAddress = some (.publicChoice firstCode) := by
  change (applicationPlan.image (fun _ => 0)).lookup
    (ApplicationInstruction.publicChoice firstCode).address =
      some (.publicChoice firstCode)
  apply applicationPlan.image_lookup_of_mem (fun _ => 0)
  change _ ∈ [_ , _]
  apply List.mem_cons.mpr
  left
  rfl

theorem image_lookup_second : image.lookup secondAddress = some (.publicChoice secondCode) := by
  change (applicationPlan.image (fun _ => 0)).lookup
    (ApplicationInstruction.publicChoice secondCode).address =
      some (.publicChoice secondCode)
  apply applicationPlan.image_lookup_of_mem (fun _ => 0)
  change _ ∈ [_ , _]
  apply List.mem_cons.mpr
  right
  apply List.mem_singleton.mpr
  rfl

theorem accepted_run :
    image.application.run acceptedActions initialExecution = FinDist.pure finalExecution := by
  rw [show acceptedActions = [.submit 0 firstMessage.payload, .include (0, 0),
    .submit 1 secondMessage.payload, .include (1, 0)] from rfl]
  simp only [MessageApplication.run_cons, MessageApplication.step, FinDist.pure_bind]
  rfl

/-- Both generated endpoints really accept: their distinct typed values are
stored at the choice and publication fields, and both native receipts succeed. -/
theorem accepted_postconditions :
    finalExecution.receipts = [((0, 0), true), ((1, 0), true)] ∧
      finalExecution.application.memory.store 0 = some ⟨.bool, true⟩ ∧
      finalExecution.application.memory.store 1 = some ⟨.bool, true⟩ ∧
      finalExecution.application.memory.store 2 = some ⟨.bool, true⟩ ∧
      finalExecution.application.memory.store 3 = some ⟨.option .bool, some false⟩ ∧
      finalExecution.application.memory.store 4 = some ⟨.option .bool, some false⟩ ∧
      finalExecution.application.memory.done 0 = true ∧
      finalExecution.application.memory.done 1 = true ∧
      finalExecution.application.memory.done 2 = true ∧
      finalExecution.application.memory.done 3 = true := by
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem unknown_address_rejected :
    image.handle initialState
      ⟨(0, 7), .choice 99 ⟨.bool, true⟩⟩ = none := by
  apply image.handle_unknown
  rfl

theorem wrong_dynamic_type_rejected :
    image.handle initialState
      ⟨(0, 7), .choice firstAddress ⟨.option .bool, some true⟩⟩ = none := by
  apply image.handle_wrong_type initialState firstAddress firstCode
  · exact image_lookup_first
  · decide

theorem guarded_value_rejected :
    image.handle initialState
      ⟨(0, 7), .choice firstAddress ⟨.bool, false⟩⟩ = none := by
  change image.handle initialState
    ⟨(0, 7), .choice firstAddress ⟨firstCode.guard.ty, false⟩⟩ = none
  rw [image.handle_choice initialState firstAddress firstCode image_lookup_first]
  rfl

theorem completed_endpoint_rejects_other_legal_value :
    image.handle (initialState.publish secondCode (some false))
      ⟨(1, 7), .choice secondAddress ⟨.option .bool, none⟩⟩ = none := by
  exact image.handle_choice_after_publication initialState secondAddress secondCode
    image_lookup_second (1, 7) (some false) none

def firstReplayed : image.application.State :=
  { firstIncluded with pool := (firstIncluded.pool.replay 0 (0, 0)).state }

def replayIncluded : image.application.State :=
  image.application.includePending firstReplayed (0, 0)

def replayActions : List image.application.Action :=
  [.replay 0 (0, 0), .include (0, 0)]

theorem replay_run :
    image.application.run replayActions firstIncluded = FinDist.pure replayIncluded := by
  rw [show replayActions = [.replay 0 (0, 0), .include (0, 0)] from rfl]
  simp only [MessageApplication.run_cons, MessageApplication.step, FinDist.pure_bind]
  rfl

/-- Replaying the already accepted, guard-valid message publishes raw traffic
again, but the closed endpoint rejects it and cannot change public memory. -/
theorem replay_cannot_overwrite :
    replayIncluded.application = firstIncluded.application ∧
      replayIncluded.receipts = [((0, 0), true), ((0, 0), false)] ∧
      replayIncluded.pool.ledger = [firstMessage, firstMessage] := by
  refine ⟨rfl, rfl, rfl⟩

def rejectedMessage : Message Player (Vegas.ApplicationImage.Payload Player simpleExpr) :=
  ⟨(0, 0), .choice firstAddress ⟨.bool, false⟩⟩

def rejectedSubmitted : image.application.State :=
  { initialExecution with
    pool := (initialExecution.pool.submit 0 rejectedMessage.payload).2 }

def rejectedDelivered : image.application.State :=
  { rejectedSubmitted with
    pool := (rejectedSubmitted.pool.deliver 1 (0, 0)).state }

def rejectedIncluded : image.application.State :=
  image.application.includePending rejectedDelivered (0, 0)

theorem delivered_rejection_stays_known :
    rejectedIncluded.application = initialState ∧
      rejectedIncluded.receipts = [((0, 0), false)] ∧
      rejectedIncluded.pool.inbox 1 = [rejectedMessage] := by
  have hlookup : rejectedDelivered.pool.lookup (0, 0) = some rejectedMessage := by
    rfl
  have hreject : image.handle initialState rejectedMessage = none := by
    exact guarded_value_rejected
  have hincluded := MessagePool.includeApplication_reject rejectedDelivered.pool
    initialState (0, 0) rejectedMessage image.handle hlookup hreject
  unfold rejectedIncluded
  simp only [MessageApplication.includePending, Vegas.ApplicationImage.application]
  rw [show rejectedDelivered.application = initialState by rfl, hincluded]
  refine ⟨rfl, rfl, ?_⟩
  rfl

def unsupportedSampleCore : VegasCore Player simpleExpr [] :=
  .sample 0 (.weighted (b := .bool) fairCoin) (.ret [])

theorem unsupportedSampleFresh : FreshBindings unsupportedSampleCore := by
  simp [unsupportedSampleCore, FreshBindings, Fresh]

def unsupportedSampleAccounting : CommitmentAccounting ∅ unsupportedSampleCore := by
  unfold unsupportedSampleCore
  apply CommitmentAccounting.sample
  exact CommitmentAccounting.ret rfl

def unsupportedSampleState : BuildState Player simpleExpr [] :=
  BuildState.fromInitial (ToEventGraph.initialState [] (VEnv.empty simpleExpr) (by simp))

/-- This is a backend-eligibility failure, not a source rejection: the current
application plan has no constructor that could silently discard a chance node. -/
theorem sample_requires_an_instruction :
    ¬Nonempty (ApplicationPlan unsupportedSampleAccounting unsupportedSampleFresh
      unsupportedSampleState) := by
  rintro ⟨plan⟩
  cases plan

end VegasTests.ApplicationImage

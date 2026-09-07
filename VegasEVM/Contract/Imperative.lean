/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import VegasEVM.Contract.State

/-!
# Ordered imperative contract requirements

This lowering introduces two operational details: graph readiness becomes an
ordered list of runtime requirements, then each requirement becomes a Boolean
read at a physical completion slot. Each action first checks that it has not
already completed and then checks its prerequisites in the canonical order of
the prerequisite `Finset`.

The generic short-circuit runner makes the successful prefix and first failure
observable. Physical evaluation is proved equivalent to graph readiness under
an explicit completion-reader agreement hypothesis.
-/

namespace Vegas.Machine.Contract.Imperative

open EventGraph

noncomputable section

variable {Player : Type} [DecidableEq Player]
variable {L : IExpr} {program : Program Player L}

/-- One pure control-flow requirement emitted before an action body. -/
inductive Requirement (program : Program Player L) where
  | notCompleted (node : Fin program.graph.nodeCount)
  | completed (node : Fin program.graph.nodeCount)

namespace Requirement

/-- Evaluate one requirement against semantic graph configuration state. -/
def evaluate (cfg : Config program.graph) : Requirement program → Bool
  | .notCompleted node => decide (node ∉ cfg.done)
  | .completed node => decide (node ∈ cfg.done)

end Requirement

/-- Evaluate a list of checks without retaining the failure observation. -/
def evaluateAll {Check : Type} (evaluate : Check → Bool)
    (checks : List Check) : Bool :=
  checks.all evaluate

/-- Observable result of short-circuit check evaluation. On success, `passed`
is the complete check list. On rejection, `passed` is exactly the successful
prefix and `failed` is the first failed check. Keeping
this information explicit lets a later pass state whether it exposes or hides
check order through gas use or revert data. -/
inductive CheckResult (Check : Type) where
  | accepted (passed : List Check)
  | rejected (passed : List Check) (failed : Check)

namespace CheckResult

/-- Whether short-circuit evaluation accepted the requirement list. -/
def succeeded {Check : Type} : CheckResult Check → Bool
  | .accepted _ => true
  | .rejected _ _ => false

/-- Number of requirements actually evaluated. The failed requirement counts
as one evaluated check. -/
def checkedCount {Check : Type} : CheckResult Check → Nat
  | .accepted passed => passed.length
  | .rejected passed _ => passed.length + 1

end CheckResult

/-- Evaluate requirements from left to right and retain the first-failure
observation produced by an imperative backend. -/
def runChecks {Check : Type} (evaluate : Check → Bool) :
    List Check → CheckResult Check
  | [] => .accepted []
  | requirement :: rest =>
      if evaluate requirement then
        match runChecks evaluate rest with
        | .accepted passed => .accepted (requirement :: passed)
        | .rejected passed failed =>
            .rejected (requirement :: passed) failed
      else
        .rejected [] requirement

/-- Retaining first-failure detail does not change whether the ordered checks
accept. -/
theorem runChecks_succeeded {Check : Type} (evaluate : Check → Bool)
    (checks : List Check) :
    (runChecks evaluate checks).succeeded = evaluateAll evaluate checks := by
  induction checks with
  | nil => rfl
  | cons requirement rest ih =>
      by_cases heval : evaluate requirement = true
      · cases hrest : runChecks evaluate rest with
        | accepted passed =>
            simpa [runChecks, heval, hrest, CheckResult.succeeded,
              evaluateAll] using ih
        | rejected passed failed =>
            simpa [runChecks, heval, hrest, CheckResult.succeeded,
              evaluateAll] using ih
      · have hevalFalse : evaluate requirement = false :=
          Bool.eq_false_of_not_eq_true heval
        simp [runChecks, hevalFalse, evaluateAll, CheckResult.succeeded]

/-- A rejection identifies a genuine prefix of successful checks followed by
the first failed check. -/
theorem runChecks_rejected_prefix {Check : Type} (evaluate : Check → Bool)
    {checks passed : List Check} {failed : Check}
    (hreject : runChecks evaluate checks = .rejected passed failed) :
    ∃ remaining,
      checks = passed ++ failed :: remaining ∧
      (∀ requirement ∈ passed, evaluate requirement = true) ∧
      evaluate failed = false := by
  induction checks generalizing passed failed with
  | nil => simp [runChecks] at hreject
  | cons requirement rest ih =>
      by_cases heval : evaluate requirement = true
      · simp only [runChecks, heval, ↓reduceIte] at hreject
        cases hrest : runChecks evaluate rest with
        | accepted restPassed => simp [hrest] at hreject
        | rejected restPassed restFailed =>
            simp only [hrest] at hreject
            cases hreject
            obtain ⟨remaining, hdecomp, hpassed, hfailed⟩ := ih hrest
            refine ⟨remaining, ?_, ?_, hfailed⟩
            · simp [hdecomp]
            · intro checked hmem
              simp only [List.mem_cons] at hmem
              rcases hmem with rfl | hmem
              · exact heval
              · exact hpassed checked hmem
      · have hevalFalse : evaluate requirement = false :=
          Bool.eq_false_of_not_eq_true heval
        simp only [runChecks, hevalFalse, Bool.false_eq_true, ↓reduceIte] at hreject
        cases hreject
        exact ⟨rest, by simp, by simp, hevalFalse⟩

/-- Canonical ordered requirements for one graph action. -/
def requirements (program : Program Player L)
    (node : Fin program.graph.nodeCount) : List (Requirement program) :=
  .notCompleted node ::
    (program.graph.prereqs node).toList.map Requirement.completed

/-- The ordered imperative requirements accept exactly ready graph nodes. -/
theorem evaluateAll_requirements_eq_true_iff
    (cfg : Config program.graph)
    (node : Fin program.graph.nodeCount) :
    evaluateAll (Requirement.evaluate cfg) (requirements program node) = true ↔
      Ready program.graph cfg node := by
  have hsubset :
      (∀ prior, prior ∈ program.graph.prereqs node → prior ∈ cfg.done) ↔
        program.graph.prereqs node ⊆ cfg.done := by
    constructor
    · intro hall prior hprior
      exact hall prior hprior
    · intro subset prior hprior
      exact subset hprior
  simp [evaluateAll, requirements, Requirement.evaluate, Ready, hsubset]

/-- Executable Boolean equality between ordered requirements and readiness. -/
theorem evaluateAll_requirements
    (cfg : Config program.graph)
    (node : Fin program.graph.nodeCount) :
    evaluateAll (Requirement.evaluate cfg) (requirements program node) =
      decide (Ready program.graph cfg node) := by
  apply Bool.eq_iff_iff.mpr
  rw [evaluateAll_requirements_eq_true_iff]
  simp

/-- The observable short-circuit runner accepts exactly ready graph nodes. -/
theorem runChecks_requirements_succeeded
    (cfg : Config program.graph)
    (node : Fin program.graph.nodeCount) :
    (runChecks (Requirement.evaluate cfg)
        (requirements program node)).succeeded =
      decide (Ready program.graph cfg node) := by
  rw [runChecks_succeeded, evaluateAll_requirements]

/-- One physical Boolean storage assertion. Missing or non-Boolean storage
fails the check. -/
structure StorageCheck where
  slot : Nat
  expected : Bool
deriving DecidableEq

namespace StorageCheck

/-- Evaluate one physical storage check through a completion-bit reader. -/
def evaluate (readCompleted : Nat → Option Bool)
    (check : StorageCheck) : Bool :=
  match readCompleted check.slot with
  | none => false
  | some actual => decide (actual = check.expected)

end StorageCheck

/-- Decode a completion bit at an already lowered physical slot. -/
def completionReader (codec : StorageCodec program) (store : RawStore codec)
    (slot : Nat) : Option Bool :=
  match store slot with
  | none => none
  | some word => codec.decodeCompleted word

/-- Lower a graph requirement to its physical completion slot. -/
def lowerRequirement (layout : Layout program) :
    Requirement program → StorageCheck
  | .notCompleted node =>
      { slot := layout.address (.completed node), expected := false }
  | .completed node =>
      { slot := layout.address (.completed node), expected := true }

/-- Lower an ordered logical requirement list without changing its order. -/
def lowerRequirements (layout : Layout program)
    (checks : List (Requirement program)) : List StorageCheck :=
  checks.map (lowerRequirement layout)

/-- A physical completion-bit reader agrees with one semantic graph
configuration at every completion slot. -/
def CompletionReaderAgrees (layout : Layout program)
    (cfg : Config program.graph) (readCompleted : Nat → Option Bool) : Prop :=
  ∀ node,
    readCompleted (layout.address (.completed node)) =
      some (decide (node ∈ cfg.done))

/-- Physical lowering preserves each individual readiness check. -/
theorem lowerRequirement_correct (layout : Layout program)
    (cfg : Config program.graph) (readCompleted : Nat → Option Bool)
    (hagrees : CompletionReaderAgrees layout cfg readCompleted)
    (requirement : Requirement program) :
    StorageCheck.evaluate readCompleted (lowerRequirement layout requirement) =
      Requirement.evaluate cfg requirement := by
  cases requirement with
  | notCompleted node =>
      simp [StorageCheck.evaluate, lowerRequirement, hagrees node,
        Requirement.evaluate]
  | completed node =>
      simp [StorageCheck.evaluate, lowerRequirement, hagrees node,
        Requirement.evaluate]

/-- Physical lowering preserves the acceptance result of the whole ordered
check list. -/
theorem evaluateAll_lowerRequirements (layout : Layout program)
    (cfg : Config program.graph) (readCompleted : Nat → Option Bool)
    (hagrees : CompletionReaderAgrees layout cfg readCompleted)
    (checks : List (Requirement program)) :
    evaluateAll (StorageCheck.evaluate readCompleted)
        (lowerRequirements layout checks) =
      evaluateAll (Requirement.evaluate cfg) checks := by
  induction checks with
  | nil => rfl
  | cons requirement rest ih =>
      have ih' :
          (rest.map (lowerRequirement layout)).all
              (StorageCheck.evaluate readCompleted) =
            rest.all (Requirement.evaluate cfg) := by
        simpa only [evaluateAll, lowerRequirements] using ih
      simp only [lowerRequirements, List.map_cons, evaluateAll, List.all_cons]
      rw [lowerRequirement_correct layout cfg readCompleted hagrees, ih']

/-- Canonically encoded semantic state supplies exactly the completion-bit
reader assumed by physical check lowering. -/
theorem completionReader_encodeState_agrees
    (codec : StorageCodec program) (state : program.State) :
    CompletionReaderAgrees (Layout.canonical program) state.1
      (completionReader codec (RawStore.encodeState codec state)) := by
  intro node
  exact RawStore.readCompleted_encodeSnapshot codec
    (StateSnapshot.ofConfig state.1) node

/-- One successful action-body operation. `realize` retains the typed semantic
event computation for a later expression/entropy lowering pass. The two write
operations expose the physical effect order without yet assigning gas or
rollback behavior. -/
inductive Operation (Player : Type) (L : IExpr) where
  | realize (row : EventNode Player L)
  | writeOutput (slot : Nat) (ty : L.Ty)
  | markCompleted (slot : Nat)

/-- The physical value slot written by a graph node. -/
def outputSlot (layout : Layout program)
    (node : Fin program.graph.nodeCount) : Nat :=
  layout.address
    (.value
      ⟨program.graph.nodeTarget node,
        StateSnapshot.nodeTarget_lt_fieldCount program.graph node⟩)

/-- The physical completion slot written after the node output. -/
def completionSlot (layout : Layout program)
    (node : Fin program.graph.nodeCount) : Nat :=
  layout.address (.completed node)

/-- A node's value write and completion write cannot alias under a certified
layout. -/
theorem outputSlot_ne_completionSlot (layout : Layout program)
    (node : Fin program.graph.nodeCount) :
    outputSlot layout node ≠ completionSlot layout node := by
  intro heq
  have hslots := layout.injective heq
  cases hslots

/-- Lower one successful action body. Event realization finishes before either
storage effect; completion is recorded only after the output write. -/
def compileBody (layout : Layout program)
    (node : Fin program.graph.nodeCount) : List (Operation Player L) :=
  let row := program.graph.nodeRow node
  [ .realize row,
    .writeOutput (outputSlot layout node) row.ty,
    .markCompleted (completionSlot layout node) ]

/-- One action in the first imperative contract IR. Expression and event code
remain in the source-independent machine row while layout and control checks
are made explicit. -/
structure ActionIR (program : Program Player L) where
  node : Fin program.graph.nodeCount
  authority : Authority Player
  inputType : Option L.Ty
  checks : List StorageCheck
  body : List (Operation Player L)

/-- Lower one stable graph action using the chosen certified storage layout. -/
def compileAction (layout : Layout program)
    (node : Fin program.graph.nodeCount) : ActionIR program where
  node := node
  authority := Action.authority program ⟨node⟩
  inputType := Action.inputType program ⟨node⟩
  checks := lowerRequirements layout (requirements program node)
  body := compileBody layout node

/-- Whole imperative contract inventory. Action order is the graph's stable
canonical node order; each action carries its ordered physical checks. -/
structure ContractIR (program : Program Player L) where
  storageSize : Nat
  actions : List (ActionIR program)

/-- Compile the machine manifest and a chosen physical layout to the first
imperative contract IR. -/
def compile (program : Program Player L) (layout : Layout program) :
    ContractIR program where
  storageSize := layout.slotCount
  actions := program.graph.nodeOrder.map (compileAction layout)

@[simp] theorem compile_actions_length (layout : Layout program) :
    (compile program layout).actions.length = program.graph.nodeCount := by
  simp [compile, Graph.nodeOrder]

/-- Every graph node has its compiled action in the imperative inventory. -/
theorem compileAction_mem (layout : Layout program)
    (node : Fin program.graph.nodeCount) :
    compileAction layout node ∈ (compile program layout).actions := by
  simp [compile, Graph.mem_nodeOrder]

@[simp] theorem compileAction_checks (layout : Layout program)
    (node : Fin program.graph.nodeCount) :
    (compileAction layout node).checks =
      lowerRequirements layout (requirements program node) :=
  rfl

@[simp] theorem compileAction_body (layout : Layout program)
    (node : Fin program.graph.nodeCount) :
    (compileAction layout node).body = compileBody layout node :=
  rfl

@[simp] theorem compileAction_body_length (layout : Layout program)
    (node : Fin program.graph.nodeCount) :
    (compileAction layout node).body.length = 3 := by
  simp [compileAction, compileBody]

/-- Compiled physical checks retain exactly the graph readiness check whenever
their completion-bit reader agrees with the semantic configuration. -/
theorem compileAction_checks_correct (layout : Layout program)
    (cfg : Config program.graph)
    (readCompleted : Nat → Option Bool)
    (hagrees : CompletionReaderAgrees layout cfg readCompleted)
    (node : Fin program.graph.nodeCount) :
    (runChecks (StorageCheck.evaluate readCompleted)
        (compileAction layout node).checks).succeeded =
      decide (Ready program.graph cfg node) := by
  rw [runChecks_succeeded, compileAction_checks,
    evaluateAll_lowerRequirements layout cfg readCompleted hagrees,
    evaluateAll_requirements]

end

end Vegas.Machine.Contract.Imperative

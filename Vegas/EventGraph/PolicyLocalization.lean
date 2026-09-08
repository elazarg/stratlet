/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import Vegas.EventGraph.KernelPolicy

/-! # Extracting declared-read decisions from graph policies

A legal policy choice at an active commitment determines a guarded value.
This file provides that extraction independently of any source language.
-/

noncomputable section

namespace Vegas.EventGraph

open GameTheory.Protocol GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr}

/-- Native availability validates the submitted typed value against any
matching canonical guard and declared read environment. -/
theorem CommitAvailable.valid_value {G : Graph Player L} {cfg : Config G}
    {who : Player} {action : CommitAction G who}
    (havailable : CommitAvailable G cfg who action) (guard : EventGuard L)
    (hsem : (G.nodeRow action.node).sem = .commit who guard)
    (reads : ReadEnv L guard.choiceReads)
    (hreads : ReadEnv.ofStore? cfg.store guard.choiceReads = some reads) :
    ∃ value : L.Val guard.ty, action.value.as? guard.ty = some value ∧
      guard.eval value reads = true := by
  obtain ⟨step⟩ := havailable
  cases step with
  | mk row actualGuard hrow hactual hready value hvalue env henv hguard =>
      have hrowEq := Option.some.inj ((G.nodes_get?_nodeRow action.node).symm.trans hrow)
      have heq := (NodeSem.commit.inj
        (hsem.symm.trans ((congrArg EventNode.sem hrowEq).trans hactual))).2
      subst actualGuard
      have henvEq := Option.some.inj (henv.symm.trans hreads)
      subst env
      exact ⟨value, hvalue, hguard⟩

/-- A legal frontier packet supplies the unique guarded value at every ready
owned commitment. -/
def FrontierAction.decisionValue {G : Graph Player L} {cfg : Config G}
    {who : Player} (action : FrontierAction G who)
    (havailable : FrontierAction.Available G cfg who action)
    (node : Fin G.nodeCount) (hready : ReadyCommitNode G cfg who node)
    (guard : EventGuard L) (hsem : (G.nodeRow node).sem = .commit who guard)
    (reads : ReadEnv L guard.choiceReads)
    (hreads : ReadEnv.ofStore? cfg.store guard.choiceReads = some reads) :
    {value : L.Val guard.ty // guard.eval value reads = true} := by
  classical
  have hnode := havailable node
  rw [dif_pos hready] at hnode
  let selected := Classical.choose hnode
  have hselected := Classical.choose_spec hnode
  have hvalid := hselected.2.valid_value guard hsem reads hreads
  exact ⟨Classical.choose hvalid, (Classical.choose_spec hvalid).2⟩

/-- Extraction returns the value actually present in the submitted packet. -/
theorem FrontierAction.decisionValue_typed {G : Graph Player L} {cfg : Config G}
    {who : Player} (action : FrontierAction G who)
    (havailable : FrontierAction.Available G cfg who action)
    (node : Fin G.nodeCount) (hready : ReadyCommitNode G cfg who node)
    (guard : EventGuard L) (hsem : (G.nodeRow node).sem = .commit who guard)
    (reads : ReadEnv L guard.choiceReads)
    (hreads : ReadEnv.ofStore? cfg.store guard.choiceReads = some reads) :
    some (⟨guard.ty,
      (action.decisionValue havailable node hready guard hsem reads hreads).1⟩ : TypedValue L) =
      (action.value? node).map (G.nodeTypedValue node) := by
  unfold FrontierAction.decisionValue
  extract_lets hnode selected hselected hvalid
  have heq := TypedValue.eq_mk_of_as?_eq_some (G.nodeTypedValue node selected)
    guard.ty (Classical.choose hvalid) (Classical.choose_spec hvalid).1
  exact (congrArg some heq.symm).trans
    (congrArg (Option.map (G.nodeTypedValue node)) hselected.1).symm

/-- A native information-local choice at an active realized state determines
the value of any ready commitment belonging to that player. -/
def decisionChoice [Fintype Player] {G : Graph Player L}
    (hwf : G.WF) (hguards : GuardLive G) (who : Player)
    {state : (toExecutionProtocol G hwf hguards).State}
    (trace : (toExecutionProtocol G hwf hguards).Trace state)
    (hactive : (toExecutionProtocol G hwf hguards).active state who)
    (node : Fin G.nodeCount) (hready : ReadyCommitNode G state.1 who node)
    (guard : EventGuard L) (hsem : (G.nodeRow node).sem = .commit who guard)
    (reads : ReadEnv L guard.choiceReads)
    (hreads : ReadEnv.ofStore? state.1.store guard.choiceReads = some reads)
    (choice : (toInformationModel G hwf hguards).Choice who
      ((toInfoSignals G hwf hguards).infoOf who trace)) :
    {value : L.Val guard.ty // guard.eval value reads = true} := by
  rcases choice with ⟨choice, hmenu⟩
  have hlegal := (toInformationModel G hwf hguards).menu_adequate
    who trace choice |>.mp hmenu
  cases choice with
  | none =>
      exact False.elim (hlegal hactive)
  | some action =>
      exact action.decisionValue hlegal.2 node hready guard hsem reads hreads

/-- The extracted value is the node coordinate of the actual native choice. -/
theorem decisionChoice_typed [Fintype Player] {G : Graph Player L}
    (hwf : G.WF) (hguards : GuardLive G) (who : Player)
    {state : (toExecutionProtocol G hwf hguards).State}
    (trace : (toExecutionProtocol G hwf hguards).Trace state)
    (hactive : (toExecutionProtocol G hwf hguards).active state who)
    (node : Fin G.nodeCount) (hready : ReadyCommitNode G state.1 who node)
    (guard : EventGuard L) (hsem : (G.nodeRow node).sem = .commit who guard)
    (reads : ReadEnv L guard.choiceReads)
    (hreads : ReadEnv.ofStore? state.1.store guard.choiceReads = some reads)
    (choice : (toInformationModel G hwf hguards).Choice who
      ((toInfoSignals G hwf hguards).infoOf who trace)) :
    some (⟨guard.ty,
      (decisionChoice hwf hguards who trace hactive node hready guard hsem reads hreads choice).1⟩ :
        TypedValue L) =
      choice.1.bind (fun action => (action.value? node).map (G.nodeTypedValue node)) := by
  rcases choice with ⟨choice, hmenu⟩
  have hlegal := (toInformationModel G hwf hguards).menu_adequate
    who trace choice |>.mp hmenu
  cases choice with
  | none =>
      exact False.elim (hlegal hactive)
  | some action =>
      simp only [decisionChoice, Option.bind_some]
      exact action.decisionValue_typed _ node hready guard hsem reads hreads

/-- The guarded marginal decision law of a native behavioral policy at a
realized active node. -/
def decisionLaw [Fintype Player] {G : Graph Player L}
    (hwf : G.WF) (hguards : GuardLive G) (who : Player)
    (policy : (toInformationModel G hwf hguards).BehavioralPolicy who)
    {state : (toExecutionProtocol G hwf hguards).State}
    (trace : (toExecutionProtocol G hwf hguards).Trace state)
    (hactive : (toExecutionProtocol G hwf hguards).active state who)
    (node : Fin G.nodeCount) (hready : ReadyCommitNode G state.1 who node)
    (guard : EventGuard L) (hsem : (G.nodeRow node).sem = .commit who guard)
    (reads : ReadEnv L guard.choiceReads)
    (hreads : ReadEnv.ofStore? state.1.store guard.choiceReads = some reads) :
    FinDist {value : L.Val guard.ty // guard.eval value reads = true} :=
  (policy ((toInfoSignals G hwf hguards).infoOf who trace)).map
    (decisionChoice hwf hguards who trace hactive node hready guard hsem reads hreads)

/-- The guarded marginal has exactly the node-coordinate law of the native
policy; guard and availability evidence do not change its distribution. -/
theorem decisionLaw_typed [Fintype Player] {G : Graph Player L}
    (hwf : G.WF) (hguards : GuardLive G) (who : Player)
    (policy : (toInformationModel G hwf hguards).BehavioralPolicy who)
    {state : (toExecutionProtocol G hwf hguards).State}
    (trace : (toExecutionProtocol G hwf hguards).Trace state)
    (hactive : (toExecutionProtocol G hwf hguards).active state who)
    (node : Fin G.nodeCount) (hready : ReadyCommitNode G state.1 who node)
    (guard : EventGuard L) (hsem : (G.nodeRow node).sem = .commit who guard)
    (reads : ReadEnv L guard.choiceReads)
    (hreads : ReadEnv.ofStore? state.1.store guard.choiceReads = some reads) :
    (decisionLaw hwf hguards who policy trace hactive node hready guard hsem reads hreads).map
        (fun value => some (⟨guard.ty, value.1⟩ : TypedValue L)) =
      (policy ((toInfoSignals G hwf hguards).infoOf who trace)).map
        (fun choice => choice.1.bind
          (fun action => (action.value? node).map (G.nodeTypedValue node))) := by
  simp only [decisionLaw, FinDist.map_comp, Function.comp_def]
  congr 1
  funext choice
  exact decisionChoice_typed hwf hguards who trace hactive node hready
    guard hsem reads hreads choice

/-- At equal information states, extracting the same guarded node gives the
same decision law, regardless of the representative execution history. -/
theorem decisionLaw_eq_of_info_eq [Fintype Player] {G : Graph Player L}
    (hwf : G.WF) (hguards : GuardLive G) (who : Player)
    (policy : (toInformationModel G hwf hguards).BehavioralPolicy who)
    {left right : (toExecutionProtocol G hwf hguards).State}
    (first : (toExecutionProtocol G hwf hguards).Trace left)
    (second : (toExecutionProtocol G hwf hguards).Trace right)
    (hactiveLeft : (toExecutionProtocol G hwf hguards).active left who)
    (hactiveRight : (toExecutionProtocol G hwf hguards).active right who)
    (node : Fin G.nodeCount)
    (hreadyLeft : ReadyCommitNode G left.1 who node)
    (hreadyRight : ReadyCommitNode G right.1 who node)
    (guard : EventGuard L) (hsem : (G.nodeRow node).sem = .commit who guard)
    (reads : ReadEnv L guard.choiceReads)
    (hreadsLeft : ReadEnv.ofStore? left.1.store guard.choiceReads = some reads)
    (hreadsRight : ReadEnv.ofStore? right.1.store guard.choiceReads = some reads)
    (hinfo : (toInfoSignals G hwf hguards).infoOf who first =
      (toInfoSignals G hwf hguards).infoOf who second) :
    decisionLaw hwf hguards who policy first hactiveLeft node hreadyLeft
        guard hsem reads hreadsLeft =
      decisionLaw hwf hguards who policy second hactiveRight node hreadyRight
        guard hsem reads hreadsRight := by
  apply FinDist.map_injective
    (f := fun value : {value : L.Val guard.ty // guard.eval value reads = true} =>
      some (⟨guard.ty, value.1⟩ : TypedValue L))
    (fun first second heq => by
      apply Subtype.ext
      simpa using heq)
  rw [decisionLaw_typed, decisionLaw_typed]
  change
    (policy ((toInfoSignals G hwf hguards).infoOf who first)).map
        (fun choice => choice.1.bind
          (fun action => (action.value? node).map (G.nodeTypedValue node))) =
      (policy ((toInfoSignals G hwf hguards).infoOf who second)).map
        (fun choice => choice.1.bind
          (fun action => (action.value? node).map (G.nodeTypedValue node)))
  exact congrArg (fun info => (policy info).map
    (fun choice => choice.1.bind
      (fun action => (action.value? node).map (G.nodeTypedValue node)))) hinfo

/-- Declared reads at an active node determine the player's entire information,
including its remembered decisions. This is a property of an information
model; source compilation can establish it from its visibility discipline. -/
def CommitInformationLocal [Fintype Player] (G : Graph Player L)
    (hwf : G.WF) (hguards : GuardLive G) : Prop :=
  ∀ who node guard, (G.nodeRow node).sem = .commit who guard →
    ∀ (reads : ReadEnv L guard.choiceReads) (left right : ReachableConfig G)
      (first : (toExecutionProtocol G hwf hguards).Trace left)
      (second : (toExecutionProtocol G hwf hguards).Trace right),
    (toExecutionProtocol G hwf hguards).active left who →
    (toExecutionProtocol G hwf hguards).active right who →
    ReadyCommitNode G left.1 who node → ReadyCommitNode G right.1 who node →
    ReadEnv.ofStore? left.1.store guard.choiceReads = some reads →
    ReadEnv.ofStore? right.1.store guard.choiceReads = some reads →
    (toInfoSignals G hwf hguards).infoOf who first =
      (toInfoSignals G hwf hguards).infoOf who second

/-- Restrict a native policy to declared-read decisions using representative
active histories. Inputs that occur at no active history use a legal guarded
default. Exactness at realized histories follows under `CommitInformationLocal`. -/
def CommitPolicy.fromBehavioral [Fintype Player] {G : Graph Player L}
    (hwf : G.WF) (hguards : GuardLive G) (who : Player)
    (policy : (toInformationModel G hwf hguards).BehavioralPolicy who) : CommitPolicy G who := by
  classical
  intro node guard hsem reads
  by_cases hrealizable : ∃ (state : ReachableConfig G)
      (trace : (toExecutionProtocol G hwf hguards).Trace state),
      (toExecutionProtocol G hwf hguards).active state who ∧
      ReadyCommitNode G state.1 who node ∧
      ReadEnv.ofStore? state.1.store guard.choiceReads = some reads
  · let state := Classical.choose hrealizable
    let trace := Classical.choose (Classical.choose_spec hrealizable)
    have hproperties := Classical.choose_spec (Classical.choose_spec hrealizable)
    exact decisionLaw hwf hguards who policy trace hproperties.1 node hproperties.2.1
      guard hsem reads hproperties.2.2
  · have hlive := hguards (G.nodes_get?_nodeRow node) hsem reads
    exact FinDist.pure ⟨Classical.choose hlive, Classical.choose_spec hlive⟩

/-- Localizing a native policy preserves every realized node decision law
when declared reads determine its full information. -/
theorem CommitPolicy.fromBehavioral_at [Fintype Player] {G : Graph Player L}
    (hwf : G.WF) (hguards : GuardLive G)
    (hlocal : CommitInformationLocal G hwf hguards) (who : Player)
    (policy : (toInformationModel G hwf hguards).BehavioralPolicy who)
    {state : (toExecutionProtocol G hwf hguards).State}
    (trace : (toExecutionProtocol G hwf hguards).Trace state)
    (hactive : (toExecutionProtocol G hwf hguards).active state who)
    (node : Fin G.nodeCount) (hready : ReadyCommitNode G state.1 who node)
    (guard : EventGuard L) (hsem : (G.nodeRow node).sem = .commit who guard)
    (reads : ReadEnv L guard.choiceReads)
    (hreads : ReadEnv.ofStore? state.1.store guard.choiceReads = some reads) :
    CommitPolicy.fromBehavioral hwf hguards who policy node guard hsem reads =
      decisionLaw hwf hguards who policy trace hactive node hready guard hsem reads hreads := by
  classical
  have hrealizable : ∃ (witness : ReachableConfig G)
      (prior : (toExecutionProtocol G hwf hguards).Trace witness),
      (toExecutionProtocol G hwf hguards).active witness who ∧
      ReadyCommitNode G witness.1 who node ∧
      ReadEnv.ofStore? witness.1.store guard.choiceReads = some reads :=
    ⟨state, trace, hactive, hready, hreads⟩
  let witness := Classical.choose hrealizable
  let prior := Classical.choose (Classical.choose_spec hrealizable)
  have hproperties := Classical.choose_spec (Classical.choose_spec hrealizable)
  have hinfo := hlocal who node guard hsem reads witness state prior trace
    hproperties.1 hactive hproperties.2.1 hready hproperties.2.2 hreads
  unfold CommitPolicy.fromBehavioral
  rw [dif_pos hrealizable]
  exact decisionLaw_eq_of_info_eq hwf hguards who policy prior trace hproperties.1 hactive
    node hproperties.2.1 hready guard hsem reads hproperties.2.2 hreads hinfo

end Vegas.EventGraph

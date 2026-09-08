/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import Vegas.EventGraph.PolicyLocalization

/-! # Exact policy localization for single-decision frontiers -/

noncomputable section

namespace Vegas.EventGraph

open GameTheory.Protocol GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr}

/-- A legal packet with only one ready node is determined by that coordinate. -/
theorem FrontierAction.eq_of_single_ready {G : Graph Player L} {cfg : Config G}
    {who : Player} (node : Fin G.nodeCount)
    (hsingle : ∀ other, ReadyCommitNode G cfg who other → other = node)
    (left right : FrontierAction G who)
    (hleft : FrontierAction.Available G cfg who left)
    (hright : FrontierAction.Available G cfg who right)
    (hvalue : left.value? node = right.value? node) : left = right := by
  classical
  have hvalues : left.value? = right.value? := by
    funext other
    by_cases hready : ReadyCommitNode G cfg who other
    · exact (hsingle other hready).symm ▸ hvalue
    · have hl := hleft other
      have hr := hright other
      rw [dif_neg hready] at hl hr
      exact hl.trans hr.symm
  cases left
  cases right
  cases hvalues
  rfl

/-- At an active single-decision frontier, the typed node projection is
injective on the native legal choice carrier. -/
theorem choice_node_injective [Fintype Player] {G : Graph Player L}
    (hwf : G.WF) (hguards : GuardLive G) (who : Player)
    {state : (toExecutionProtocol G hwf hguards).State}
    (trace : (toExecutionProtocol G hwf hguards).Trace state)
    (hactive : (toExecutionProtocol G hwf hguards).active state who)
    (node : Fin G.nodeCount)
    (hsingle : ∀ other, ReadyCommitNode G state.1 who other → other = node) :
    Function.Injective (fun choice : (toInformationModel G hwf hguards).Choice who
      ((toInfoSignals G hwf hguards).infoOf who trace) =>
        choice.1.bind (fun action => (action.value? node).map (G.nodeTypedValue node))) := by
  rintro ⟨first, hfirst⟩ ⟨second, hsecond⟩ heq
  have hlegalFirst := (toInformationModel G hwf hguards).menu_adequate
    who trace first |>.mp hfirst
  have hlegalSecond := (toInformationModel G hwf hguards).menu_adequate
    who trace second |>.mp hsecond
  apply Subtype.ext
  cases first with
  | none => exact False.elim (hlegalFirst hactive)
  | some left =>
      cases second with
      | none => exact False.elim (hlegalSecond hactive)
      | some right =>
          apply congrArg some
          apply left.eq_of_single_ready node hsingle right hlegalFirst.2 hlegalSecond.2
          change (left.value? node).map (G.nodeTypedValue node) =
            (right.value? node).map (G.nodeTypedValue node) at heq
          cases hl : left.value? node <;> cases hr : right.value? node <;>
            simp_all [Graph.nodeTypedValue]

/-- The frontier product has each declared commitment kernel as its marginal. -/
theorem frontierLaw_node {G : Graph Player L} (hwf : G.WF)
    (cfg : Config G) (hcoherent : StoreCoherent G cfg)
    (who : Player) (policy : CommitPolicy G who)
    (node : Fin G.nodeCount) (hready : ReadyCommitNode G cfg who node) :
    (frontierLaw hwf cfg hcoherent who policy).map
        (fun action => (action.1.value? node).map (G.nodeTypedValue node)) =
      (commitValueLaw hwf cfg hcoherent who policy node hready).map
        (fun value => some (G.nodeTypedValue node value.1)) := by
  classical
  let index : {node // ReadyCommitNode G cfg who node} := ⟨node, hready⟩
  let laws := fun entry : {node // ReadyCommitNode G cfg who node} =>
    commitValueLaw hwf cfg hcoherent who policy entry.1 entry.2
  have h := congrArg
    (FinDist.map (fun value => some (G.nodeTypedValue node value.1)))
    (FinDist.map_apply_pi index laws)
  rw [FinDist.map_comp] at h
  unfold frontierLaw
  rw [FinDist.map_comp]
  change (FinDist.pi laws).map
    (fun values => Option.map (G.nodeTypedValue node)
      (if h : ReadyCommitNode G cfg who node then some (values ⟨node, h⟩).1 else none)) = _
  simpa only [dif_pos hready, Option.map_some, Function.comp_def] using h

/-- Localizing and reimplementing an arbitrary native policy recovers its
whole choice law at an active single-decision frontier, not only its marginal. -/
theorem CommitPolicy.behavioral_fromBehavioral_at [Fintype Player] {G : Graph Player L}
    (hwf : G.WF) (hguards : GuardLive G)
    (hlocal : CommitInformationLocal G hwf hguards) (who : Player)
    (policy : (toInformationModel G hwf hguards).BehavioralPolicy who)
    {state : (toExecutionProtocol G hwf hguards).State}
    (trace : (toExecutionProtocol G hwf hguards).Trace state)
    (hactive : (toExecutionProtocol G hwf hguards).active state who)
    (node : Fin G.nodeCount) (hready : ReadyCommitNode G state.1 who node)
    (hsingle : ∀ other, ReadyCommitNode G state.1 who other → other = node)
    (guard : EventGuard L) (hsem : (G.nodeRow node).sem = .commit who guard)
    (reads : ReadEnv L guard.choiceReads)
    (hreads : ReadEnv.ofStore? state.1.store guard.choiceReads = some reads) :
    ((CommitPolicy.fromBehavioral hwf hguards who policy).behavioral hwf hguards)
        ((toInfoSignals G hwf hguards).infoOf who trace) =
      policy ((toInfoSignals G hwf hguards).infoOf who trace) := by
  classical
  let localized := CommitPolicy.fromBehavioral hwf hguards who policy
  apply FinDist.map_injective (choice_node_injective hwf hguards who trace hactive node hsingle)
  have hfront := congrArg
    (FinDist.map (fun choice : Option (FrontierAction G who) =>
      choice.bind (fun action => (action.value? node).map (G.nodeTypedValue node))))
    (localized.behavioral_at_active hwf hguards trace hactive)
  have hfront' :
      (localized.behavioral hwf hguards ((toInfoSignals G hwf hguards).infoOf who trace)).map
          (fun choice => choice.1.bind
            (fun action => (action.value? node).map (G.nodeTypedValue node))) =
        (frontierLaw hwf state.1 (reachable_storeCoherent hwf state.2) who localized).map
          (fun action => (action.1.value? node).map (G.nodeTypedValue node)) := by
    simp only [FinDist.map_comp, Function.comp_def, Option.bind_some] at hfront
    exact hfront
  rw [hfront', frontierLaw_node hwf state.1 _ who localized node hready]
  have htyped := congrArg (FinDist.map some)
    (commitValueLaw_typed hwf state.1 (reachable_storeCoherent hwf state.2)
      who localized node hready guard hsem reads hreads)
  simp only [FinDist.map_comp, Function.comp_def] at htyped
  rw [htyped]
  change (CommitPolicy.fromBehavioral hwf hguards who policy node guard hsem reads).map _ = _
  rw [CommitPolicy.fromBehavioral_at hwf hguards hlocal who policy
    trace hactive node hready guard hsem reads hreads]
  exact decisionLaw_typed hwf hguards who policy trace hactive node hready guard hsem reads hreads

/-- Native policy reconstruction is exact at every realized information state,
including inactive states whose menu contains only the idle choice. -/
theorem CommitPolicy.behavioral_fromBehavioral [Fintype Player] {G : Graph Player L}
    (hwf : G.WF) (hguards : GuardLive G)
    (hlocal : CommitInformationLocal G hwf hguards) (who : Player)
    (policy : (toInformationModel G hwf hguards).BehavioralPolicy who)
    {state : (toExecutionProtocol G hwf hguards).State}
    (trace : (toExecutionProtocol G hwf hguards).Trace state)
    (hsingle : ∀ first second, ReadyCommitNode G state.1 who first →
      ReadyCommitNode G state.1 who second → first = second) :
    ((CommitPolicy.fromBehavioral hwf hguards who policy).behavioral hwf hguards)
        ((toInfoSignals G hwf hguards).infoOf who trace) =
      policy ((toInfoSignals G hwf hguards).infoOf who trace) := by
  classical
  by_cases hactive : (toExecutionProtocol G hwf hguards).active state who
  · have hnodes := (Finset.mem_filter.mp hactive.2.2).2
    obtain ⟨node, hnode⟩ := hnodes
    have hready : ReadyCommitNode G state.1 who node := (Finset.mem_filter.mp hnode).2
    let localized := CommitPolicy.fromBehavioral hwf hguards who policy
    obtain ⟨value, _⟩ := (commitValueLaw hwf state.1
      (reachable_storeCoherent hwf state.2) who localized node hready).support_nonempty
    obtain ⟨step⟩ := value.2
    have hrow := Option.some.inj ((G.nodes_get?_nodeRow node).symm.trans step.row_get)
    have hsem : (G.nodeRow node).sem = .commit who step.guard :=
      (congrArg EventNode.sem hrow).trans step.sem_eq
    exact CommitPolicy.behavioral_fromBehavioral_at hwf hguards hlocal who policy trace
      hactive node hready (fun other hother => hsingle other node hother hready)
      step.guard hsem step.env step.env_ok
  · exact (toInformationModel G hwf hguards).behavioral_eq_of_not_active
      _ policy trace hactive

/-- Whole native history laws are preserved when every player's policy is
localized to declared reads and then implemented by frontier products. -/
theorem runBehavioralFrom_localized [Fintype Player] {G : Graph Player L}
    (hwf : G.WF) (hguards : GuardLive G)
    (hlocal : CommitInformationLocal G hwf hguards)
    (hsingle : ∀ (cfg : Config G) who first second,
      ReadyCommitNode G cfg who first → ReadyCommitNode G cfg who second → first = second)
    (profile : ∀ who, (toInformationModel G hwf hguards).BehavioralPolicy who)
    (fuel : Nat) (history : (toExecutionProtocol G hwf hguards).History) :
    (toInformationModel G hwf hguards).runBehavioralFrom
        (fun who => (CommitPolicy.fromBehavioral hwf hguards who (profile who)).behavioral
          hwf hguards) fuel history =
      (toInformationModel G hwf hguards).runBehavioralFrom profile fuel history := by
  apply (toInformationModel G hwf hguards).runBehavioralFrom_congr
  intro later _ _ who
  exact CommitPolicy.behavioral_fromBehavioral hwf hguards hlocal who (profile who)
    later.trace (hsingle later.state.1 who)

end Vegas.EventGraph

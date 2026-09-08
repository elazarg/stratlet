/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import Vegas.EventGraph.Protocol

/-! # Policies over declared commitment reads

These kernels expose exactly a node's declared decision information. The
frontier construction below samples their guarded values independently and
produces native legal graph actions. No ambient store is passed to a kernel.
-/

noncomputable section

namespace Vegas.EventGraph

open GameTheory.Protocol GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr}

/-- A ready commitment observes every declared typed read at its stored value. -/
theorem observe_value?_of_readyCommit {G : Graph Player L} (hwf : G.WF)
    {cfg : Config G} {who : Player} {node : Fin G.nodeCount}
    {guard : EventGuard L} (hsem : (G.nodeRow node).sem = .commit who guard)
    (hready : Ready G cfg node) (ref : FieldRef L) (href : ref ∈ guard.choiceReads) :
    (observe G cfg who).value? node ref = Store.getAs cfg.store ref.field ref.ty := by
  classical
  have hnodeWF := hwf node (G.nodeRow node) (G.nodes_get?_nodeRow node)
  unfold Graph.nodeWFAt at hnodeWF
  rw [hsem] at hnodeWF
  obtain ⟨spec, hfield, hty, _⟩ := hnodeWF.2.2.2 ref href
  have hlt := G.field_lt_fieldCount_of_field?_some hfield
  have hrow : G.fieldRow ⟨ref.field, hlt⟩ = spec :=
    G.fieldRow_eq_of_field?_some hfield hlt
  have htyRow : (G.fieldRow ⟨ref.field, hlt⟩).ty = ref.ty := hrow ▸ hty
  rcases ref with ⟨field, ty⟩
  dsimp only at htyRow hlt
  cases htyRow
  simp [Observation.value?, observe, hsem, hready, hlt, href]
  cases cfg.store.getAs field (G.fieldRow ⟨field, hlt⟩).ty <;> rfl

/-- Equal graph observations give equal declared-read environments for a ready
commitment, independently of the rest of the stores. -/
theorem readEnvOfStore_eq_of_observe_eq {G : Graph Player L} (hwf : G.WF)
    {left right : Config G} {who : Player} {node : Fin G.nodeCount}
    {guard : EventGuard L} (hsem : (G.nodeRow node).sem = .commit who guard)
    (hleft : ReadyCommitNode G left who node) (hright : ReadyCommitNode G right who node)
    (hobs : observe G left who = observe G right who)
    (reads : ReadEnv L guard.choiceReads)
    (hreads : ReadEnv.ofStore? left.store guard.choiceReads = some reads) :
    ReadEnv.ofStore? right.store guard.choiceReads = some reads := by
  apply ReadEnv.ofStore?_eq_of_getAs_eq hreads
  intro ref href
  rw [← observe_value?_of_readyCommit hwf hsem hleft.ready ref href,
    hobs, observe_value?_of_readyCommit hwf hsem hright.ready ref href]

/-- A player's guarded finite decision law at each of its commitment nodes. -/
@[reducible] def CommitPolicy (G : Graph Player L) (who : Player) :=
  ∀ (node : Fin G.nodeCount) (guard : EventGuard L),
    (G.nodeRow node).sem = .commit who guard →
      (reads : ReadEnv L guard.choiceReads) →
        FinDist {value : L.Val guard.ty // guard.eval value reads = true}

/-- Sampling a declared-read kernel produces a node-typed value with native
commit-availability evidence. -/
def commitValueLaw {G : Graph Player L} (hwf : G.WF)
    (cfg : Config G) (hcoherent : StoreCoherent G cfg)
    (who : Player) (policy : CommitPolicy G who)
    (node : Fin G.nodeCount) (hready : ReadyCommitNode G cfg who node) :
    FinDist {value : L.Val (G.nodeRow node).ty //
      CommitAvailable G cfg who { node := node, value := G.nodeTypedValue node value }} := by
  -- A ready-node witness includes its row and guard; use the canonical row
  -- below so equality transports remain local to this construction.
  have hguard : ∃ guard, (G.nodeRow node).sem = .commit who guard := by
    obtain ⟨row, guard, hrow, hsem, _⟩ := hready
    have hrowEq : G.nodeRow node = row :=
      Option.some.inj ((G.nodes_get?_nodeRow node).symm.trans hrow)
    exact ⟨guard, hrowEq.symm ▸ hsem⟩
  let guard := Classical.choose hguard
  have hsem := Classical.choose_spec hguard
  have hnodeWF := hwf node (G.nodeRow node) (G.nodes_get?_nodeRow node)
  unfold Graph.nodeWFAt at hnodeWF
  rw [hsem] at hnodeWF
  have hty : (G.nodeRow node).ty = guard.ty := hnodeWF.2.1
  have hex : ∃ reads, ReadEnv.ofStore? cfg.store guard.choiceReads = some reads := by
    exact hcoherent.readEnvOfReady hwf (G.nodes_get?_nodeRow node) hready.ready
      (fun ref href => by rw [hsem]; exact Finset.mem_image.mpr ⟨ref, href, rfl⟩)
      (fun ref href => by
        obtain ⟨spec, hspec, hty, _⟩ := hnodeWF.2.2.2 ref href
        exact ⟨spec, hspec, hty⟩)
  let reads := Classical.choose hex
  have hreads := Classical.choose_spec hex
  exact (policy node guard hsem reads).map fun choice =>
    ⟨cast (congrArg L.Val hty.symm) choice.1, ⟨{
      row := G.nodeRow node
      guard := guard
      row_get := G.nodes_get?_nodeRow node
      sem_eq := hsem
      ready := hready.ready
      value := choice.1
      value_ok := by
        have hcast : ∀ (ty : L.Ty) (heq : ty = guard.ty),
            (⟨ty, cast (congrArg L.Val heq.symm) choice.1⟩ : TypedValue L).as? guard.ty =
              some choice.1 := by
          intro ty heq
          subst ty
          simp [TypedValue.as?]
        exact hcast _ hty
      env := reads
      env_ok := hreads
      guard_ok := choice.2 }⟩⟩

private theorem typedValue_cast (left right : L.Ty) (hty : left = right)
    (hcast : L.Val left = L.Val right) (value : L.Val left) :
    (⟨right, cast hcast value⟩ : TypedValue L) = ⟨left, value⟩ := by
  subst right
  rfl

private theorem kernel_typed_law {G : Graph Player L} (hwf : G.WF)
    (cfg : Config G) (who : Player) (policy : CommitPolicy G who)
    (node : Fin G.nodeCount) (first second : EventGuard L)
    (hfirst : (G.nodeRow node).sem = .commit who first)
    (hsecond : (G.nodeRow node).sem = .commit who second)
    (readsFirst : ReadEnv L first.choiceReads) (readsSecond : ReadEnv L second.choiceReads)
    (hrFirst : ReadEnv.ofStore? cfg.store first.choiceReads = some readsFirst)
    (hrSecond : ReadEnv.ofStore? cfg.store second.choiceReads = some readsSecond)
    (hcast : L.Val first.ty = L.Val (G.nodeRow node).ty) :
    (policy node first hfirst readsFirst).map
        (fun value => G.nodeTypedValue node (cast hcast value.1)) =
      (policy node second hsecond readsSecond).map
        (fun value => (⟨second.ty, value.1⟩ : TypedValue L)) := by
  have heq := (NodeSem.commit.inj (hfirst.symm.trans hsecond)).2
  subst second
  have hreadEq := Option.some.inj (hrFirst.symm.trans hrSecond)
  subst readsSecond
  have hnodeWF := hwf node (G.nodeRow node) (G.nodes_get?_nodeRow node)
  unfold Graph.nodeWFAt at hnodeWF
  rw [hfirst] at hnodeWF
  congr 1
  funext value
  exact typedValue_cast first.ty (G.nodeRow node).ty hnodeWF.2.1.symm hcast value.1

/-- The native value law evaluates exactly the supplied guard kernel on the
unique declared reads. Canonical-row choices and typing evidence do not alter
the distribution of written values. -/
theorem commitValueLaw_typed {G : Graph Player L} (hwf : G.WF)
    (cfg : Config G) (hcoherent : StoreCoherent G cfg)
    (who : Player) (policy : CommitPolicy G who)
    (node : Fin G.nodeCount) (hready : ReadyCommitNode G cfg who node)
    (guard : EventGuard L) (hsem : (G.nodeRow node).sem = .commit who guard)
    (reads : ReadEnv L guard.choiceReads)
    (hreads : ReadEnv.ofStore? cfg.store guard.choiceReads = some reads) :
    (commitValueLaw hwf cfg hcoherent who policy node hready).map
        (fun value => G.nodeTypedValue node value.1) =
      (policy node guard hsem reads).map
        (fun value => (⟨guard.ty, value.1⟩ : TypedValue L)) := by
  unfold commitValueLaw
  extract_lets hguard chosenGuard hchosen nodeWF nodeTy henv chosenReads hchosenReads
  rw [FinDist.map_comp]
  exact kernel_typed_law hwf cfg who policy node _ guard
    hchosen hsem _ reads hchosenReads hreads _

/-- Native commitment value laws are determined by the player's observation. -/
theorem commitValueLaw_value_eq_of_observe_eq {G : Graph Player L} (hwf : G.WF)
    (left right : Config G)
    (hleftCoherent : StoreCoherent G left) (hrightCoherent : StoreCoherent G right)
    (who : Player) (policy : CommitPolicy G who)
    (node : Fin G.nodeCount)
    (hleft : ReadyCommitNode G left who node) (hright : ReadyCommitNode G right who node)
    (hobs : observe G left who = observe G right who) :
    (commitValueLaw hwf left hleftCoherent who policy node hleft).map Subtype.val =
      (commitValueLaw hwf right hrightCoherent who policy node hright).map Subtype.val := by
  obtain ⟨value, _⟩ :=
    (commitValueLaw hwf left hleftCoherent who policy node hleft).support_nonempty
  obtain ⟨step⟩ := value.2
  have hrowEq : G.nodeRow node = step.row :=
    Option.some.inj ((G.nodes_get?_nodeRow node).symm.trans step.row_get)
  have hsem : (G.nodeRow node).sem = .commit who step.guard :=
    (congrArg EventNode.sem hrowEq).trans step.sem_eq
  have hreads := readEnvOfStore_eq_of_observe_eq hwf hsem hleft hright hobs step.env step.env_ok
  apply FinDist.map_injective (f := G.nodeTypedValue node)
    (fun first second heq => by simpa [Graph.nodeTypedValue] using heq)
  simp only [FinDist.map_comp, Function.comp_def]
  rw [commitValueLaw_typed hwf left hleftCoherent who policy node hleft
      step.guard hsem step.env step.env_ok,
    commitValueLaw_typed hwf right hrightCoherent who policy node hright
      step.guard hsem step.env hreads]

private def packetOfNodeValues {G : Graph Player L} (who : Player)
    (ready : Fin G.nodeCount → Prop)
    (values : (node : {node // ready node}) → L.Val (G.nodeRow node.1).ty) :
    FrontierAction G who := by
  classical
  exact { value? node := if h : ready node then some (values ⟨node, h⟩) else none }

/-- Assemble all ready node values into the player's native frontier packet. -/
def frontierOfValues {G : Graph Player L} (cfg : Config G) (who : Player)
    (values : (node : {node : Fin G.nodeCount // ReadyCommitNode G cfg who node}) →
      {value : L.Val (G.nodeRow node.1).ty //
        CommitAvailable G cfg who {node := node.1, value := G.nodeTypedValue node.1 value}}) :
    {action : FrontierAction G who // FrontierAction.Available G cfg who action} := by
  classical
  let action := packetOfNodeValues who (ReadyCommitNode G cfg who) (fun node => (values node).1)
  refine ⟨action, ?_⟩
  intro node
  by_cases h : ReadyCommitNode G cfg who node
  · rw [dif_pos h]
    exact ⟨(values ⟨node, h⟩).1, by simp [action, packetOfNodeValues, h], (values ⟨node, h⟩).2⟩
  · rw [dif_neg h]
    simp [action, packetOfNodeValues, h]

/-- Independent declared-read decisions produce a legal simultaneous packet.
The indexing set contains all ready commitments, not a selected subset. -/
def frontierLaw {G : Graph Player L} (hwf : G.WF)
    (cfg : Config G) (hcoherent : StoreCoherent G cfg)
    (who : Player) (policy : CommitPolicy G who) :
    FinDist {action : FrontierAction G who // FrontierAction.Available G cfg who action} := by
  classical
  exact (FinDist.pi (fun node : {node : Fin G.nodeCount // ReadyCommitNode G cfg who node} =>
    commitValueLaw hwf cfg hcoherent who policy node.1 node.2)).map
      (frontierOfValues cfg who)

private theorem frontierLaw_raw {G : Graph Player L} (hwf : G.WF)
    (cfg : Config G) (hcoherent : StoreCoherent G cfg)
    (who : Player) (policy : CommitPolicy G who) :
    (frontierLaw hwf cfg hcoherent who policy).map Subtype.val =
      (FinDist.pi (fun node : {node // ReadyCommitNode G cfg who node} =>
        (commitValueLaw hwf cfg hcoherent who policy node.1 node.2).map Subtype.val)).map
          (packetOfNodeValues who (ReadyCommitNode G cfg who)) := by
  classical
  rw [FinDist.pi_map, FinDist.map_comp]
  simp only [frontierLaw, FinDist.map_comp, frontierOfValues, Function.comp_def]

private theorem packetLaw_congr {G : Graph Player L} (who : Player)
    (first second : Fin G.nodeCount → Prop) (hready : first = second)
    [hfirstDec : DecidablePred first] [hsecondDec : DecidablePred second]
    (left : (node : {node // first node}) → FinDist (L.Val (G.nodeRow node.1).ty))
    (right : (node : {node // second node}) → FinDist (L.Val (G.nodeRow node.1).ty))
    (hlaws : ∀ node hfirst hsecond, left ⟨node, hfirst⟩ = right ⟨node, hsecond⟩) :
    (FinDist.pi left).map (packetOfNodeValues who first) =
      (FinDist.pi right).map (packetOfNodeValues who second) := by
  subst second
  cases Subsingleton.elim hfirstDec hsecondDec
  have heq : left = right := funext fun node => hlaws node.1 node.2 node.2
  rw [heq]

/-- A player's entire sampled frontier packet depends only on the declared
graph observation, including its set of ready decisions. -/
theorem frontierLaw_eq_of_observe_eq {G : Graph Player L} (hwf : G.WF)
    (left right : Config G)
    (hleftCoherent : StoreCoherent G left) (hrightCoherent : StoreCoherent G right)
    (who : Player) (policy : CommitPolicy G who)
    (hobs : observe G left who = observe G right who) :
    (frontierLaw hwf left hleftCoherent who policy).map Subtype.val =
      (frontierLaw hwf right hrightCoherent who policy).map Subtype.val := by
  classical
  have hready : ReadyCommitNode G left who = ReadyCommitNode G right who := by
    funext node
    apply propext
    have heq := readyCommitNodes_eq_of_observe_eq hobs
    have hmem := congrArg (fun nodes => node ∈ nodes) heq
    simpa [readyCommitNodes] using (Iff.of_eq hmem)
  rw [frontierLaw_raw, frontierLaw_raw]
  apply packetLaw_congr who _ _ hready
  intro node hleft hright
  exact commitValueLaw_value_eq_of_observe_eq hwf left right
    hleftCoherent hrightCoherent who policy node hleft hright hobs

/-- Implement declared-read kernels as native information-local behavioral
policies. A realizable snapshot supplies availability evidence; impossible
snapshots use the information model's idle menu. The policy never receives
an execution history or an opponent's policy. -/
def CommitPolicy.behavioral [Fintype Player]
    {G : Graph Player L} (hwf : G.WF) (hguards : GuardLive G)
    {who : Player} (policy : CommitPolicy G who) :
    (toInformationModel G hwf hguards).BehavioralPolicy who := by
  classical
  intro info
  by_cases hrealizable : ∃ state : ReachableConfig G,
      publicObserve G state.1 = info.current.1 ∧
      observe G state.1 who = info.current.2
  · let state := Classical.choose hrealizable
    have hviews := Classical.choose_spec hrealizable
    by_cases hactive : (toExecutionProtocol G hwf hguards).active state who
    · exact (frontierLaw hwf state.1 (reachable_storeCoherent hwf state.2)
        who policy).map fun action => ⟨some action.1, by
          change some action.1 ∈ localMenu G hwf hguards who info
          rw [localMenu, dif_pos hrealizable]
          exact ⟨state, hviews.1, hviews.2, hactive, action.2⟩⟩
    · exact FinDist.pure ⟨none, by
        change none ∈ localMenu G hwf hguards who info
        rw [localMenu, dif_pos hrealizable]
        exact ⟨state, hviews.1, hviews.2, hactive⟩⟩
  · exact FinDist.pure ⟨none, by
      change none ∈ localMenu G hwf hguards who info
      simp [localMenu, hrealizable]⟩

/-- At an active realized information state, the native behavioral policy has
exactly the declared-read frontier law of the actual state. Its choice of a
representative snapshot contributes no extra behavior. -/
theorem CommitPolicy.behavioral_at_active [Fintype Player]
    {G : Graph Player L} (hwf : G.WF) (hguards : GuardLive G)
    {who : Player} (policy : CommitPolicy G who)
    {state : (toExecutionProtocol G hwf hguards).State}
    (trace : (toExecutionProtocol G hwf hguards).Trace state)
    (hactive : (toExecutionProtocol G hwf hguards).active state who) :
    (policy.behavioral hwf hguards
        ((toInfoSignals G hwf hguards).infoOf who trace)).map Subtype.val =
      (frontierLaw hwf state.1 (reachable_storeCoherent hwf state.2) who policy).map
        (fun action => some action.1) := by
  classical
  let info := (toInfoSignals G hwf hguards).infoOf who trace
  have hcurrent := infoOf_toInfoSignals_current G hwf hguards who trace
  have hrealizable : ∃ witness : ReachableConfig G,
      publicObserve G witness.1 = info.current.1 ∧
      observe G witness.1 who = info.current.2 :=
    ⟨state, by rw [hcurrent], by rw [hcurrent]⟩
  let witness := Classical.choose hrealizable
  have hviews := Classical.choose_spec hrealizable
  have hwitnessActive : (toExecutionProtocol G hwf hguards).active witness who := by
    by_contra hnot
    have hmenu : none ∈ localMenu G hwf hguards who info := by
      rw [localMenu, dif_pos hrealizable]
      exact ⟨witness, hviews.1, hviews.2, hnot⟩
    have hlegal := (toInformationModel G hwf hguards).menu_adequate who trace none |>.mp hmenu
    exact hlegal hactive
  have hobs : observe G witness.1 who = observe G state.1 who := by
    exact hviews.2.trans (congrArg Prod.snd hcurrent)
  have hlaw := congrArg (FinDist.map some)
    (frontierLaw_eq_of_observe_eq hwf witness.1 state.1
      (reachable_storeCoherent hwf witness.2) (reachable_storeCoherent hwf state.2)
      who policy hobs)
  unfold CommitPolicy.behavioral
  dsimp only
  rw [dif_pos hrealizable, dif_pos hwitnessActive]
  simpa only [FinDist.map_comp, Function.comp_def] using hlaw

end Vegas.EventGraph

/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import Vegas.Scheduled.Backtranslation

/-! # Complete behavioral laws across automatic settlement -/

noncomputable section

namespace Vegas.Scheduled

open GameTheory.Protocol GameTheory.Math.Probability

/-- Discarding the scheduler coordinate of independent simultaneous draws
leaves exactly the original players' independent draws. -/
theorem pi_players {Player : Type} [Fintype Player]
    {A : Participant Player → Type*} (laws : ∀ who, FinDist (A who)) :
    (FinDist.pi laws).map (fun draws who => draws (.player who)) =
      FinDist.pi (fun who => laws (.player who)) := by
  classical
  let equiv : Player ≃ {who : Participant Player // who ≠ .scheduler} :=
    { toFun := fun who => ⟨.player who, by simp⟩
      invFun := fun who => match who with
        | ⟨.player player, _⟩ => player
        | ⟨.scheduler, h⟩ => False.elim (h rfl)
      left_inv := fun _ => rfl
      right_inv := fun who => by
        rcases who with ⟨who, h⟩
        cases who
        · exact False.elim (h rfl)
        · rfl }
  rw [FinDist.pi_eq_map_product .scheduler laws, FinDist.map_comp]
  have hprojection : (fun draws who => draws (.player who)) ∘
      (Equiv.piSplitAt .scheduler A).symm =
        (fun draws who => draws (equiv who)) ∘ Prod.snd := by
    funext draws who
    simp [equiv]
  rw [hprojection, ← FinDist.map_comp, FinDist.map_snd_product]
  exact FinDist.pi_reindex (fun who : {who // who ≠ Participant.scheduler} => A who.1)
    equiv (fun who => laws who.1)

/-- Equal summary laws can be followed by any continuations that agree at
matching supported summaries. Neither side needs a deterministic inverse of
its summary map. -/
theorem bind_eq_of_map_eq {α β γ δ : Type*}
    (μ : FinDist α) (ν : FinDist β) (f : α → γ) (g : β → γ)
    (hmap : μ.map f = ν.map g) (F : α → FinDist δ) (H : β → FinDist δ)
    (hagree : ∀ a ∈ μ.support, ∀ b ∈ ν.support, f a = g b → F a = H b) :
    μ.bind F = ν.bind H := by
  classical
  let select := fun value : γ =>
    if hex : ∃ a ∈ μ.support, f a = value then Classical.choose hex
    else μ.support_nonempty.choose
  let kernel := fun value => F (select value)
  have hselect : ∀ value, value ∈ (μ.map f).support →
      select value ∈ μ.support ∧ f (select value) = value := by
    intro value hvalue
    have hex : ∃ a ∈ μ.support, f a = value := by
      simpa only [FinDist.support_map, Set.mem_image] using hvalue
    simpa only [select, dif_pos hex] using Classical.choose_spec hex
  have hright : ∀ b ∈ ν.support, H b = kernel (g b) := by
    intro b hb
    have hvalue : g b ∈ (μ.map f).support := by
      rw [hmap, FinDist.support_map]
      exact ⟨b, hb, rfl⟩
    exact (hagree _ (hselect _ hvalue).1 b hb (hselect _ hvalue).2).symm
  have hleft : ∀ a ∈ μ.support, F a = kernel (f a) := by
    intro a ha
    have hvalue : f a ∈ (ν.map g).support := by
      rw [← hmap, FinDist.support_map]
      exact ⟨a, ha, rfl⟩
    rw [FinDist.support_map] at hvalue
    obtain ⟨b, hb, hba⟩ := hvalue
    exact (hagree a ha b hb hba.symm).trans (hba ▸ hright b hb)
  calc
    μ.bind F = (μ.map f).bind kernel := by
      rw [FinDist.bind_map]
      exact FinDist.bind_congr hleft
    _ = (ν.map g).bind kernel := congrArg (fun law => law.bind kernel) hmap
    _ = ν.bind H := by
      rw [FinDist.bind_map]
      exact FinDist.bind_congr fun b hb => (hright b hb).symm

/-- A finite run either stops or has executed every requested step. -/
theorem runRandomizedFor_terminal_or_length
    {ι : Type*} {E : ExecutionProtocol ι} (chooser : E.RandomizedChooser)
    (fuel : Nat) (start next : E.History)
    (hnext : next ∈ (E.runRandomizedFor chooser fuel start).support) :
    E.terminal next.state ∨ start.trace.length + fuel ≤ next.trace.length := by
  induction fuel generalizing start with
  | zero =>
      rw [ExecutionProtocol.runRandomizedFor_zero, FinDist.mem_support_pure] at hnext
      subst next
      exact Or.inr (by omega)
  | succ fuel ih =>
      by_cases hterm : E.terminal start.state
      · rw [ExecutionProtocol.runRandomizedFor_of_terminal _ _ hterm,
          FinDist.mem_support_pure] at hnext
        subst next
        exact Or.inl hterm
      · rw [ExecutionProtocol.runRandomizedFor_succ_of_not_terminal _ _ hterm,
          FinDist.support_bind] at hnext
        obtain ⟨command, hcommand, hnext⟩ := Set.mem_iUnion₂.mp hnext
        rw [FinDist.support_bindOnSupport] at hnext
        obtain ⟨middle, hmiddle, hnext⟩ := Set.mem_iUnion₂.mp hnext
        rcases ih (start.extend command.2 hmiddle) hnext with hterminal | hlength
        · exact Or.inl hterminal
        · right
          change start.trace.length + 1 + fuel ≤ next.trace.length at hlength
          omega

theorem runBehavioralFrom_terminal_of_bound
    {ι : Type*} [Fintype ι] {E : ExecutionProtocol ι} (M : InformationModel E)
    (profile : (who : ι) → M.BehavioralPolicy who) {bound : Nat}
    (hbound : E.BoundedHorizon bound) (start next : E.History)
    (hnext : next ∈ (M.runBehavioralFrom profile bound start).support) :
    E.terminal next.state := by
  rcases runRandomizedFor_terminal_or_length (M.randomizedChooser profile) bound start next hnext
    with hterm | hlength
  · exact hterm
  · exact hbound next.state next.trace (by omega)

/-- Running beyond a certified horizon cannot change the history law. -/
theorem runBehavioralFrom_bound_add
    {ι : Type*} [Fintype ι] {E : ExecutionProtocol ι} (M : InformationModel E)
    (profile : (who : ι) → M.BehavioralPolicy who) {bound : Nat}
    (hbound : E.BoundedHorizon bound) (extra : Nat) (start : E.History) :
    M.runBehavioralFrom profile (bound + extra) start =
      M.runBehavioralFrom profile bound start := by
  rw [InformationModel.runBehavioralFrom_add]
  calc
    _ = (M.runBehavioralFrom profile bound start).bind FinDist.pure := by
      apply FinDist.bind_congr
      intro next hnext
      exact M.runBehavioralFrom_of_terminal profile extra
        (runBehavioralFrom_terminal_of_bound M profile hbound start next hnext)
    _ = _ := FinDist.bind_pure _

end Vegas.Scheduled

namespace Vegas.Machine.Program

open GameTheory.Protocol GameTheory.Math.Probability EventGraph

variable {Player : Type} [DecidableEq Player] [Fintype Player] {L : IExpr}

/-- Atomic execution never changes a field whose writer has already completed. -/
theorem executionStep_extends (program : Program Player L) (state : program.State)
    (command : {joint // program.execution.Legal state joint}) {next : program.State}
    (hnext : next ∈ (program.execution.step state command).support) :
    state.1.Extends next.1 := by
  classical
  change next ∈ ((toExecutionProtocol program.graph program.graphWF program.guardLive).step
    state command).support at hnext
  by_cases hinternal : (readyInternalNodes program.graph state.1).Nonempty
  · rw [EventGraph.toExecutionProtocol_step_eq_stepReadyInternal
      program.graph program.graphWF program.guardLive state command hinternal] at hnext
    exact extends_of_stepReadyInternal program.graphWF state hinternal hnext
  · rw [toExecutionProtocol_step_eq_pure_applyFrontier
      program.graph program.graphWF program.guardLive state command
        (Finset.not_nonempty_iff_eq_empty.mp hinternal), FinDist.mem_support_pure] at hnext
    subst next
    exact extends_applyFrontier_of_legal program.graph program.graphWF program.guardLive
      state command.1 command.2

/-- Every supported continuation preserves completed field values. -/
theorem runBehavioralFrom_extends (program : Program Player L)
    (profile : (who : Player) → program.information.BehavioralPolicy who)
    (fuel : Nat) (start next : program.execution.History)
    (hnext : next ∈ (program.information.runBehavioralFrom profile fuel start).support) :
    start.state.1.Extends next.state.1 := by
  induction fuel generalizing start with
  | zero =>
      change next ∈ (FinDist.pure start).support at hnext
      rw [FinDist.mem_support_pure] at hnext
      subst next
      exact Config.Extends.refl _
  | succ fuel ih =>
      by_cases hterm : program.execution.terminal start.state
      · rw [InformationModel.runBehavioralFrom_of_terminal _ _ _ hterm,
          FinDist.mem_support_pure] at hnext
        subst next
        exact Config.Extends.refl _
      · rw [InformationModel.runBehavioralFrom_succ_of_not_terminal _ _ _ hterm,
          FinDist.support_bind] at hnext
        obtain ⟨command, _, hnext⟩ := Set.mem_iUnion₂.mp hnext
        rw [FinDist.support_bindOnSupport] at hnext
        obtain ⟨middle, hmiddle, hnext⟩ := Set.mem_iUnion₂.mp hnext
        exact (program.executionStep_extends start.state command hmiddle).trans
          (ih (start.extend command.2 hmiddle) hnext)

/-- Compile the real players and supply the scheduler as an environment policy. -/
def compileSerializedBehavioralProfile (program : Program Player L)
    (scheduler : program.serializedArena.information.BehavioralPolicy .scheduler)
    (profile : (who : Player) → program.information.BehavioralPolicy who) :
    (who : Participant Player) → program.serializedArena.information.BehavioralPolicy who
  | .scheduler => scheduler
  | .player who => program.compileSerializedBehavioralPolicy who (profile who)

/-- Forget the execution coordinate of a legal runtime command. -/
def serializedSourceCommand (program : Program Player L)
    {state : program.State} {log : List (List Player)}
    (command : {joint // program.serializedArena.execution.Legal ⟨state, log⟩ joint}) :
    {joint // program.execution.Legal state joint} :=
  ⟨fun who => command.1 (.player who), program.serializedPlayers_legal command⟩

/-- At matching information, any behavioral scheduler gives the same source
joint-action law. Its current draw is simultaneous with the players' draws. -/
theorem behavioralJoint_compileSerialized (program : Program Player L)
    (scheduler : program.serializedArena.information.BehavioralPolicy .scheduler)
    (profile : (who : Player) → program.information.BehavioralPolicy who)
    (source : program.execution.History) (log : List (List Player))
    (trace : program.serializedArena.execution.Trace ⟨source.state, log⟩)
    (hinfo : ∀ who, program.information.infoOf who source.trace =
      program.eraseSerializedPlayerInformation who
        (program.serializedArena.information.infoOf (.player who) trace))
    (hterm : ¬ program.serializedArena.execution.terminal ⟨source.state, log⟩) :
    (program.serializedArena.information.behavioralJoint
      (program.compileSerializedBehavioralProfile scheduler profile) trace hterm).map
        program.serializedSourceCommand =
      program.information.behavioralJoint profile source.trace hterm := by
  apply FinDist.map_injective Subtype.val_injective
  simp only [InformationModel.behavioralJoint, FinDist.map_comp]
  rw [show (fun a => (a : {joint // program.execution.Legal source.state joint}).val) ∘
      program.serializedSourceCommand ∘ _ =
      (fun draws who => (draws who).val) ∘ (fun draws who => draws (.player who)) from rfl,
    ← FinDist.map_comp, Scheduled.pi_players, ← FinDist.pi_map]
  change _ = (FinDist.pi fun i => profile i (program.information.infoOf i source.trace)).map
    (fun draws i => (draws i).val)
  rw [← FinDist.pi_map]
  congr 1
  funext who
  simp only [compileSerializedBehavioralProfile, compileSerializedBehavioralPolicy,
    FinDist.map_comp]
  change (profile who (program.eraseSerializedPlayerInformation who
    (program.serializedArena.information.infoOf (.player who) trace))).map Subtype.val = _
  rw [← hinfo who]

/-- The canonical source continuation law on terminal graph states. -/
def terminalStateLaw (program : Program Player L)
    (profile : (who : Player) → program.information.BehavioralPolicy who)
    (history : program.execution.History) : FinDist program.State :=
  (program.information.runBehavioralFrom profile program.graph.nodeCount history).map
    ExecutionProtocol.History.state

theorem terminalStateLaw_of_terminal (program : Program Player L)
    (profile : (who : Player) → program.information.BehavioralPolicy who)
    (history : program.execution.History) (hterm : program.execution.terminal history.state) :
    program.terminalStateLaw profile history = FinDist.pure history.state := by
  rw [terminalStateLaw, InformationModel.runBehavioralFrom_of_terminal _ _ _ hterm,
    FinDist.map_pure]

/-- The terminal law satisfies the source game's one-step equation without
an artificial cutoff: the graph-node horizon already guarantees absorption. -/
theorem terminalStateLaw_step (program : Program Player L)
    (profile : (who : Player) → program.information.BehavioralPolicy who)
    (history : program.execution.History) (hterm : ¬ program.execution.terminal history.state) :
    program.terminalStateLaw profile history =
      (program.information.behavioralJoint profile history.trace hterm).bind fun command =>
        (program.execution.step history.state command).bindOnSupport fun _ realized =>
          program.terminalStateLaw profile (history.extend command.2 realized) := by
  unfold terminalStateLaw
  rw [← Scheduled.runBehavioralFrom_bound_add program.information profile
    program.boundedHorizon 1 history]
  rw [InformationModel.runBehavioralFrom_succ_of_not_terminal _ _ _ hterm,
    FinDist.map_bind]
  apply FinDist.bind_congr
  intro command _
  exact FinDist.map_bindOnSupport _ _ _

/-- Automatic source closure is neutral to every source continuation law. -/
theorem settleHistory_terminalStateLaw (program : Program Player L)
    (profile : (who : Player) → program.information.BehavioralPolicy who)
    (fuel : Nat) (history : program.execution.History) :
    (program.settleHistory fuel history).bind (program.terminalStateLaw profile) =
      program.terminalStateLaw profile history := by
  induction fuel generalizing history with
  | zero => exact FinDist.pure_bind _ _
  | succ fuel ih =>
      unfold settleHistory
      split
      next hinternal =>
        rw [FinDist.bind_bindOnSupport]
        have hterm := (EventGraph.sourceInternalCommand
          program.graphWF program.guardLive history.state hinternal).2.1
        rw [program.terminalStateLaw_step profile history hterm,
          InformationModel.behavioralJoint_eq_pure_of_no_active _ _ _ hterm
            (fun who hactive => (Finset.not_nonempty_iff_eq_empty.mpr hactive.2.1) hinternal),
          FinDist.pure_bind]
        exact FinDist.bindOnSupport_congr fun _ _ => ih _
      next _ => exact FinDist.pure_bind _ _

/-- One strategic frontier followed by automatic closure has the same final
law as the original atomic source game. -/
theorem expandRound_terminalStateLaw (program : Program Player L)
    (profile : (who : Player) → program.information.BehavioralPolicy who)
    (history : program.execution.History) (hterm : ¬ program.execution.terminal history.state) :
    (program.information.behavioralJoint profile history.trace hterm).bind
      (fun command => (program.expandRound history command.1 command.2).bind
        (program.terminalStateLaw profile)) = program.terminalStateLaw profile history := by
  unfold expandRound
  split
  next _ =>
    simp only [program.settleHistory_terminalStateLaw]
    exact FinDist.bind_const _ _
  next _ =>
    rw [program.terminalStateLaw_step profile history hterm]
    apply FinDist.bind_congr
    intro command _
    rw [FinDist.bind_bindOnSupport]
    exact FinDist.bindOnSupport_congr fun _ _ => program.settleHistory_terminalStateLaw profile _ _

/-- One compiled runtime round and one atomic source frontier with closure
agree on the joint state-and-information law, for any behavioral scheduler. -/
theorem compiledRound_map_summary (program : Program Player L)
    (scheduler : program.serializedArena.information.BehavioralPolicy .scheduler)
    (profile : (who : Player) → program.information.BehavioralPolicy who)
    (source : program.execution.History) (target : program.serializedArena.History)
    (hmatch : program.historySummary source = program.serializedHistorySummary target)
    (hterm : ¬ program.execution.terminal source.state) :
    ((program.information.behavioralJoint profile source.trace hterm).bind fun command =>
      program.expandRound source command.1 command.2).map program.historySummary =
    (program.serializedArena.information.runBehavioralFrom
      (program.compileSerializedBehavioralProfile scheduler profile) 1 target).map
        program.serializedHistorySummary := by
  obtain ⟨⟨base, log⟩, trace⟩ := target
  have hbase := congrArg Prod.fst hmatch
  change source.state = base at hbase
  subst base
  have hinfo := congrFun (congrArg Prod.snd hmatch)
  rw [program.serializedBehavioralRound_expands source log trace hinfo _ hterm,
    ← program.behavioralJoint_compileSerialized scheduler profile source log trace hinfo hterm,
    FinDist.bind_map]
  rfl

/-- A nonterminal one-round run always appends exactly one runtime step. -/
theorem serializedRound_length (program : Program Player L)
    (profile : (who : Participant Player) →
      program.serializedArena.information.BehavioralPolicy who)
    (start next : program.serializedArena.History)
    (hterm : ¬ program.serializedArena.execution.terminal start.state)
    (hnext : next ∈ (program.serializedArena.information.runBehavioralFrom
      profile 1 start).support) : next.trace.length = start.trace.length + 1 := by
  rw [InformationModel.runBehavioralFrom_succ_of_not_terminal _ _ _ hterm,
    FinDist.support_bind] at hnext
  obtain ⟨command, _, hnext⟩ := Set.mem_iUnion₂.mp hnext
  rw [FinDist.support_bindOnSupport] at hnext
  obtain ⟨middle, hmiddle, hnext⟩ := Set.mem_iUnion₂.mp hnext
  change next ∈ (FinDist.pure (start.extend command.2 hmiddle)).support at hnext
  rw [FinDist.mem_support_pure] at hnext
  subst next
  rfl

/-- The actual serialized execution of compiled source policies has exactly
the atomic game's terminal-state law, even with an arbitrary behavioral
scheduler observing public data. This is a complete-run statement. -/
theorem runBehavioralFrom_compileSerialized (program : Program Player L)
    (scheduler : program.serializedArena.information.BehavioralPolicy .scheduler)
    (profile : (who : Player) → program.information.BehavioralPolicy who)
    (fuel : Nat) (source : program.execution.History) (target : program.serializedArena.History)
    (hmatch : program.historySummary source = program.serializedHistorySummary target)
    (hcapacity : program.graph.nodeCount ≤ target.trace.length + fuel) :
    (program.serializedArena.information.runBehavioralFrom
      (program.compileSerializedBehavioralProfile scheduler profile) fuel target).map
        (fun history => history.state.base) = program.terminalStateLaw profile source := by
  have hbase : source.state = target.state.base := congrArg Prod.fst hmatch
  induction fuel generalizing source target with
  | zero =>
      have hterminal := (program.serializedGame (fun _ => 0)).bounded
        target.state target.trace (by exact hcapacity)
      have hsource : program.execution.terminal source.state := hbase ▸ hterminal
      rw [program.terminalStateLaw_of_terminal profile source hsource]
      change (FinDist.pure target).map _ = _
      rw [FinDist.map_pure, hbase]
  | succ fuel ih =>
      by_cases hterminal : program.serializedArena.execution.terminal target.state
      · have hsource : program.execution.terminal source.state := hbase ▸ hterminal
        rw [program.terminalStateLaw_of_terminal profile source hsource,
          InformationModel.runBehavioralFrom_of_terminal _ _ _ hterminal,
          FinDist.map_pure, hbase]
      · have hsource : ¬ program.execution.terminal source.state := by
          intro ht
          apply hterminal
          change program.execution.terminal target.state.base
          exact hbase ▸ ht
        let targetRound := program.serializedArena.information.runBehavioralFrom
          (program.compileSerializedBehavioralProfile scheduler profile) 1 target
        let sourceRound := (program.information.behavioralJoint profile source.trace hsource).bind
          fun command => program.expandRound source command.1 command.2
        have hround := program.compiledRound_map_summary scheduler profile source target
          hmatch hsource
        have hcontinuation : targetRound.bind (fun next =>
            (program.serializedArena.information.runBehavioralFrom
              (program.compileSerializedBehavioralProfile scheduler profile) fuel next).map
                (fun history => history.state.base)) =
            sourceRound.bind (program.terminalStateLaw profile) := by
          apply Scheduled.bind_eq_of_map_eq targetRound sourceRound
            program.serializedHistorySummary program.historySummary hround.symm
          intro next hnext middle _ heq
          apply ih middle next heq.symm
          · have hlength := program.serializedRound_length _ target next hterminal hnext
            omega
          · exact congrArg Prod.fst heq.symm
        rw [show fuel + 1 = 1 + fuel by omega,
          InformationModel.runBehavioralFrom_add, FinDist.map_bind]
        change targetRound.bind _ = _
        rw [hcontinuation]
        exact (FinDist.bind_bind _ _ _).trans
          (program.expandRound_terminalStateLaw profile source hsource)

/-- Honest compilation preserves the full terminal-state distribution from
initial play, uniformly over public-data behavioral scheduler policies. -/
theorem runBehavioral_compileSerialized (program : Program Player L)
    (scheduler : program.serializedArena.information.BehavioralPolicy .scheduler)
    (profile : (who : Player) → program.information.BehavioralPolicy who) :
    (program.serializedArena.information.runBehavioral
      (program.compileSerializedBehavioralProfile scheduler profile) program.graph.nodeCount).map
        (fun history => history.state.base) =
      (program.information.runBehavioral profile program.graph.nodeCount).map
        ExecutionProtocol.History.state := by
  exact program.runBehavioralFrom_compileSerialized scheduler profile _
    program.execution.initHistory program.serializedArena.execution.initHistory rfl (by simp)

end Vegas.Machine.Program

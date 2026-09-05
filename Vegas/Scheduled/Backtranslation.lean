/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import Vegas.Scheduled.Information

/-!
# Back-translating runtime policies to canonical source policies

Compact source information uniquely determines the full order-free runtime
information on legal traces. Replaying a fixed public-information scheduler
then reconstructs the player's actual runtime information. These operations
use only the source player's information and the fixed scheduler policy.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace Vegas.Machine.Program

open GameTheory.Protocol GameTheory.Math.Probability EventGraph

variable {Player : Type} [DecidableEq Player] [Fintype Player] {L : IExpr}

open Classical in
/-- Choose a legal runtime representative of compact information when one
exists. The fallback preserves the compact data and is used only outside the
runtime's reachable information states. Its invented order memory is discarded
before any scheduler replay. -/
def recoverSerializedInformation (program : Program Player L) (who : Player)
    (info : PlayerInformation program.graph who) :
    program.serializedSystem.RevealingInfo (.player who) :=
  if hex : ∃ history : program.serializedArena.History,
      program.eraseSerializedPlayerInformation who
        (program.serializedArena.information.infoOf (.player who) history.trace) = info then
    program.serializedArena.information.infoOf (.player who) (Classical.choose hex).trace
  else
    { current := info.current
      past := []
      own := info.own.map fun remembered => ((remembered.1, []), remembered.2) }

@[simp] theorem erase_recoverSerializedInformation (program : Program Player L) (who : Player)
    (info : PlayerInformation program.graph who) :
    program.eraseSerializedPlayerInformation who
      (program.recoverSerializedInformation who info) = info := by
  unfold recoverSerializedInformation
  split
  next hex => exact Classical.choose_spec hex
  next _ =>
    cases info
    simp [eraseSerializedPlayerInformation, List.map_map, Function.comp_def]

/-- The representative's order-free history is the unique history determined
by the compact information; arbitrary representative orders are irrelevant. -/
theorem recoverSerializedInformation_forget_at (program : Program Player L) (who : Player)
    {state : program.serializedArena.execution.State}
    (trace : program.serializedArena.execution.Trace state) :
    program.serializedSystem.forgetOrders (program.recoverSerializedInformation who
      (program.eraseSerializedPlayerInformation who
        (program.serializedArena.information.infoOf (.player who) trace))) =
      program.serializedSystem.blindSignals.infoOf (.player who) trace := by
  have hex : ∃ history : program.serializedArena.History,
      program.eraseSerializedPlayerInformation who
        (program.serializedArena.information.infoOf (.player who) history.trace) =
      program.eraseSerializedPlayerInformation who
        (program.serializedArena.information.infoOf (.player who) trace) :=
    ⟨⟨state, trace⟩, rfl⟩
  rw [recoverSerializedInformation, dif_pos hex]
  change program.serializedSystem.forgetOrders
    (program.serializedSystem.revealingSignals.infoOf (.player who)
      (Classical.choose hex).trace) = _
  rw [← program.serializedSystem.blind_infoOf_eq_forgetOrders]
  exact program.serializedBlindInfo_eq_of_compact_eq who _ trace (Classical.choose_spec hex)

/-- Reconstruct runtime information using only compact source information
and a fixed scheduler policy. The scheduler's public view is the public half
of the player's graph snapshot. -/
def reconstructSerializedInformation (program : Program Player L)
    (scheduler : program.serializedSystem.revealingInformation.Policy .scheduler)
    (who : Player) (info : PlayerInformation program.graph who) :
    program.serializedSystem.RevealingInfo (.player who) :=
  program.serializedSystem.replayPlayerInfo scheduler Prod.fst
    (program.serializedSystem.forgetOrders (program.recoverSerializedInformation who info))

@[simp] theorem erase_reconstructSerializedInformation (program : Program Player L)
    (scheduler : program.serializedSystem.revealingInformation.Policy .scheduler)
    (who : Player) (info : PlayerInformation program.graph who) :
    program.eraseSerializedPlayerInformation who
      (program.reconstructSerializedInformation scheduler who info) = info := by
  have herase : program.eraseSerializedPlayerInformation who
      (program.reconstructSerializedInformation scheduler who info) =
        program.eraseSerializedPlayerInformation who
          (program.recoverSerializedInformation who info) := by
    simp [reconstructSerializedInformation, ScheduledSystem.replayPlayerInfo,
      ScheduledSystem.forgetOrders, eraseSerializedPlayerInformation, List.map_map,
      Function.comp_def]
  exact herase.trans (program.erase_recoverSerializedInformation who info)

/-- On every actual trace following the scheduler, reconstruction returns the
player's exact runtime information, including order history and own decisions. -/
theorem reconstructSerializedInformation_at (program : Program Player L)
    (scheduler : program.serializedSystem.revealingInformation.Policy .scheduler)
    (who : Player) {state : program.serializedArena.execution.State}
    (trace : program.serializedArena.execution.Trace state)
    (hfollows : program.serializedSystem.SchedulerFollows scheduler trace) :
    program.reconstructSerializedInformation scheduler who
      (program.eraseSerializedPlayerInformation who
        (program.serializedArena.information.infoOf (.player who) trace)) =
      program.serializedArena.information.infoOf (.player who) trace := by
  rw [reconstructSerializedInformation, program.recoverSerializedInformation_forget_at]
  exact (program.serializedSystem.revealing_info_eq_replayPlayerInfo scheduler Prod.fst
    (fun _ => rfl) trace hfollows).symm

/-- Back-translate an arbitrary behavioral runtime player into the *canonical*
source information model. The translation is independent of opponents'
policies and is defined at every source information value. -/
def backtranslateSerializedBehavioralPolicy (program : Program Player L)
    (scheduler : program.serializedSystem.revealingInformation.Policy .scheduler)
    (who : Player)
    (policy : program.serializedArena.information.BehavioralPolicy (.player who)) :
    program.information.BehavioralPolicy who :=
  fun info => (policy (program.reconstructSerializedInformation scheduler who info)).map
    fun ⟨choice, hmenu⟩ => ⟨choice, by
      rw [program.serializedPlayerMenu_eq, program.erase_reconstructSerializedInformation] at hmenu
      exact hmenu⟩

/-- Exact action laws for canonical-source back-translation, including all
behavioral deviations and all chance outcomes under the fixed scheduler. -/
theorem backtranslateSerializedBehavioralPolicy_law (program : Program Player L)
    (scheduler : program.serializedSystem.revealingInformation.Policy .scheduler)
    (who : Player)
    (policy : program.serializedArena.information.BehavioralPolicy (.player who))
    {state : program.serializedArena.execution.State}
    (trace : program.serializedArena.execution.Trace state)
    (hfollows : program.serializedSystem.SchedulerFollows scheduler trace) :
    (program.compileSerializedBehavioralPolicy who
      (program.backtranslateSerializedBehavioralPolicy scheduler who policy)
      (program.serializedArena.information.infoOf (.player who) trace)).map Subtype.val =
        (policy (program.serializedArena.information.infoOf (.player who) trace)).map
          Subtype.val := by
  simp only [compileSerializedBehavioralPolicy, backtranslateSerializedBehavioralPolicy,
    FinDist.map_comp]
  change (policy (program.reconstructSerializedInformation scheduler who
    (program.eraseSerializedPlayerInformation who
      (program.serializedArena.information.infoOf (.player who) trace)))).map Subtype.val = _
  rw [program.reconstructSerializedInformation_at scheduler who trace hfollows]

/-- Already compiled source players remain exactly their original source
policies. In particular, translating a unilateral deviator leaves honest
opponents unchanged and does not make them scheduler-dependent. -/
theorem backtranslateSerializedBehavioralPolicy_compile (program : Program Player L)
    (scheduler : program.serializedSystem.revealingInformation.Policy .scheduler)
    (who : Player) (policy : program.information.BehavioralPolicy who) :
    program.backtranslateSerializedBehavioralPolicy scheduler who
      (program.compileSerializedBehavioralPolicy who policy) = policy := by
  funext info
  apply FinDist.map_injective Subtype.val_injective
  simp only [backtranslateSerializedBehavioralPolicy, compileSerializedBehavioralPolicy,
    FinDist.map_comp]
  change (policy (program.eraseSerializedPlayerInformation who
    (program.reconstructSerializedInformation scheduler who info))).map Subtype.val =
      (policy info).map Subtype.val
  rw [program.erase_reconstructSerializedInformation]

end Vegas.Machine.Program

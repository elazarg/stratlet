/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import Interaction.SealedTimeoutHiding
import Interaction.SealedTimeoutLaws
import VegasTests.PendingTimeout

/-! # Non-vacuous timed hiding through expiration -/

namespace VegasTests.PendingTimeoutHiding

open Interaction Interaction.SealedTimeout Interaction.SealedProgram
open VegasTests.PendingSource VegasTests.PendingExecution VegasTests.PendingTimeout

abbrev Value := Option Bool

private theorem commitPrefix_service (left right : Value) :
    (commitPrefix left right).application.service =
      (((PendingTimeout.empty.application.service.sealValue 0 0 left).state
        |>.sealValue 1 1 right).state) := by
  unfold commitPrefix
  simp only [SealedTimeout.run_cons, SealedTimeout.run_nil, SealedTimeout.step]
  rw [SealedTimeout.includePending_preserves_service]
  rw [SealedTimeout.includePending_preserves_service]

theorem commitPrefix_related (left right common : Value) :
    HidingRelated (Value := Value) (0 : PendingSource.Player)
      (commitPrefix left common) (commitPrefix right common) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have base := SealedProgram.submitCommit_empty_related
        (Value := Value) (0 : PendingSource.Player) 0 left right
    have extended := ServiceAgreement.seal_other _ _ base.service
      (1 : PendingSource.Player) 1 common (by decide)
    rw [commitPrefix_service, commitPrefix_service]
    exact extended
  · fin_cases left <;> fin_cases right <;> fin_cases common <;> rfl
  · fin_cases left <;> fin_cases right <;> fin_cases common <;> rfl
  · fin_cases left <;> fin_cases right <;> fin_cases common <;> rfl
  · rfl
  · fin_cases left <;> fin_cases right <;> fin_cases common <;> rfl
  · have safe0 : MessagePool.Satisfies (SealedTimeout.MessageSafe (Value := Value) 0)
        (PendingTimeout.empty.pool.submit 0
          (.protocol (.commitment 0 (0, 0)))).2 :=
      MessagePool.Satisfies.submit MessagePool.Satisfies.empty 0 _ (by trivial)
    have included0 := safe0.includePending (0, 0)
    have safe1 := included0.submit 1 (.protocol (.commitment 1 (1, 1))) (by trivial)
    have included1 := safe1.includePending (1, 0)
    have hpool : (commitPrefix left common).pool =
        ((((PendingTimeout.empty.pool.submit 0
          (.protocol (.commitment 0 (0, 0)))).2.includePending (0, 0)).state.submit 1
          (.protocol (.commitment 1 (1, 1)))).2.includePending (1, 0)).state := by
      fin_cases left <;> fin_cases common <;> rfl
    rw [hpool]
    exact included1

theorem protected_binding_differs :
    (commitPrefix (some false) none).application.service.lookup (0, 0) =
        some (some false) ∧
      (commitPrefix (some true) none).application.service.lookup (0, 0) =
        some (some true) := by
  exact ⟨rfl, rfl⟩

def expiryActions : List (SealedTimeout.Action PendingSource.Player Value) :=
  [.advance 11, .submit 1 .expire, .include (1, 1)]

theorem expiryActions_allowed (action : SealedTimeout.Action PendingSource.Player Value)
    (hmem : action ∈ expiryActions) :
    SealedTimeout.AllowedBeforeDisclosure (Value := Value)
      (0 : PendingSource.Player) action := by
  simp only [expiryActions, List.mem_cons, List.not_mem_nil, or_false] at hmem
  rcases hmem with rfl | rfl | rfl <;>
    simp [SealedTimeout.AllowedBeforeDisclosure]

theorem expired_views_equal (left right common : Value) (recipient : PendingSource.Player) :
    ((timed.run (commitPrefix left common) expiryActions).observe recipient) =
      ((timed.run (commitPrefix right common) expiryActions).observe recipient) := by
  have related := commitPrefix_related left right common
  exact (related.run timed expiryActions expiryActions_allowed).observe_eq recipient

theorem expiry_result_public (left common : Value) :
    (timed.run (commitPrefix left common) expiryActions).application.resolution = .expired ∧
      (timed.run (commitPrefix left common) expiryActions).receipts =
        [((0, 0), true), ((1, 0), true), ((1, 1), true)] := by
  fin_cases left <;> fin_cases common <;> decide

end VegasTests.PendingTimeoutHiding

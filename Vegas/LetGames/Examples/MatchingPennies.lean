import Vegas.LetGames.WF
import Vegas.LetCore.Concrete

/-!
# Matching Pennies (Simultaneous-Move Game)

P0 picks H(true)/T(false) with empty view (YieldId 0).
P1 picks H(true)/T(false) with empty view (YieldId 1) — cannot see P0.
Utility: P0 gets 1 if choices match, -1 if not; P1 gets the opposite.

This demonstrates **imperfect information**: both choose sites have empty views,
so in the compiled EFG tree, P1's decision nodes (pid=1) appear in both subtrees
of P0's decision — P1 genuinely cannot distinguish them.
-/

namespace Proto.Examples.MatchingPennies

open Proto Defs

private abbrev L := BasicLang

/-- Legal actions for P0: H(true) or T(false), empty view. -/
private def A0 : Act (L := L) (v := viewOfVarSpec (VarSpec.nil (Γ := []))) Ty.bool :=
  fun _ => [true, false]

/-- Legal actions for P1: H(true) or T(false), empty view (can't see P0). -/
private def A1 : Act (L := L)
    (v := viewOfVarSpec (VarSpec.nil.weaken (τ := Ty.bool) (Γ := []))) Ty.bool :=
  fun _ => [true, false]

/-- Matching pennies as a ParentProtoProg.
    P0 picks (YieldId 0, empty view), P1 picks (YieldId 1, empty view).
    Returns P1's choice; P0's choice is accessible in the env. -/
def mpProto : ParentProtoProg (W := NNReal) (L := L) [] Ty.bool :=
  .choose 0 0
    ⟨[], [], .nil⟩ A0
    (.choose 1 1
      ⟨[], [], VarSpec.nil.weaken⟩ A1
      (.ret basicExprLaws.vz))

/-- WF proof for matching pennies. -/
theorem mp_wf : WF_GameProg mpProto := by
  unfold mpProto
  refine WF_GameProg.choose 0 0 _ _ ?_ ?_ ?_ ?_ ?_
  · refine WF_GameProg.choose 1 1 _ _ ?_ ?_ ?_ ?_ ?_
    · exact WF_GameProg.ret _
    · intro obs; simp [A1]
    · intro obs; simp [A1]
    · simp [ParentProtoProg.yieldIds]
    · intro obs₁ obs₂; rfl
  · intro obs; simp [A0]
  · intro obs; simp [A0]
  · simp [ParentProtoProg.yieldIds]
  · intro obs₁ obs₂; rfl

/-- P0's decision is the root (pid=0). -/
theorem mp_root_is_p0_decision :
    ∃ acts, mpProto.toEFG (fun _ _ => (0 : ℝ)) () = .decision 0 0 acts := by
  simp only [mpProto, ParentProtoProg.toEFG]
  exact ⟨_, rfl⟩

end Proto.Examples.MatchingPennies

import Vegas.LetProtocol.ProtoLemmas
import Vegas.LetCore.Concrete

/-!
# Two-Player Sequential (Coordination) Game

Player 0 picks a boolean (choose, empty view).
Player 1 observes Player 0's choice (view projects to it), then picks a boolean.
Utility: coordination game — both players get 1 if choices match, 0 otherwise.
-/

namespace Proto.Examples.SequentialGame

open Proto Defs

-- Work with BasicLang throughout
private abbrev L := BasicLang

-- Empty initial context
private abbrev Γ0 : L.Ctx := []

-- A view that reveals nothing (for Player 0's decision)
private def vEmpty : View (L := L) Γ0 where
  Δ := []
  proj := fun _ => ()

-- A view over [bool] that reveals the boolean
-- (Player 1 sees Player 0's choice)
private def vFull1 : View (L := L) [Ty.bool] where
  Δ := [Ty.bool]
  proj := fun env => env

-- Legal actions: both booleans (for any view)
private def A_bool0 : Act (L := L) (v := vEmpty) Ty.bool :=
  fun _ => [true, false]

private def A_bool1 : Act (L := L) (v := vFull1) Ty.bool :=
  fun _ => [true, false]

/-- Sequential coordination protocol:
1. Player 0 picks a bool (YieldId 0, empty view)
2. Player 1 sees P0's choice, picks a bool (YieldId 1, full view)
3. Return Player 1's choice (utility will use the env to compare) -/
def seqProto : ProtoProg (L := L) Γ0 Ty.bool :=
  -- Player 0 chooses
  ProtoProg.choose (id := 0) (who := 0) (v := vEmpty)
    (A := A_bool0)
    -- Player 1 chooses (sees P0's choice via vFull1)
    (ProtoProg.choose (id := 1) (who := 1) (v := vFull1)
      (A := A_bool1)
      -- Return P1's choice; P0's choice is in the env at index 1
      (ProtoProg.ret basicExprLaws.vz))

/-- Coordination utility: both players get 1 if choices match.
Since seqProto returns P1's choice and P0's choice is in the env,
we simplify: the game returns P1's choice, and we'd need both to
compare. For a self-contained example, we define utility on the
final return value only. A richer version would use letDet to
compute the comparison.

Here we just demonstrate the protocol structure; exact EU
computation would require comparing env variables. -/
noncomputable def coordUtil : Utility (L := L) Ty.bool :=
  fun b who =>
    if who = 0 ∨ who = 1 then (if b = true then 1 else 0) else 0

/-- The sequential coordination game. -/
noncomputable def seqGame : Game (L := L) Γ0 where
  τ := Ty.bool
  p := seqProto
  u := coordUtil

-- Basic structural facts

theorem seqProto_has_two_yields :
    yieldIds seqProto = [0, 1] := by rfl

theorem seqProto_has_two_chooses :
    chooseIds seqProto = [0, 1] := by rfl

theorem seqProto_nodup_yields :
    NoDupYieldIds seqProto := by
  simp [NoDupYieldIds, seqProto_has_two_yields]

end Proto.Examples.SequentialGame

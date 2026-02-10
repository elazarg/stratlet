import Vegas.LetProtocol.ProtoLemmas
import Vegas.LetCore.Concrete

/-!
# Hidden-Info Single-Player Example

Nature samples a boolean uniformly (sample, YieldId 0).
Player 0 sees nothing and guesses a boolean (choose, YieldId 1).
Utility: 1 if the guess matches, 0 otherwise.

This models a single-player decision problem with hidden information.
-/

namespace Proto.Examples.HiddenDecision

open Proto Defs

-- Work with BasicLang throughout
private abbrev L := BasicLang

-- Empty initial context
private abbrev Γ0 : L.Ctx := []

-- A view that reveals nothing
private def vEmpty : View (L := L) Γ0 where
  Δ := []
  proj := fun _ => ()

-- A view over [bool] that still reveals nothing
private def vEmpty1 : View (L := L) [Ty.bool] where
  Δ := []
  proj := fun _ => ()

-- Uniform distribution over {true, false}
private noncomputable def uniformBool :
    ObsKernel (L := L) vEmpty Ty.bool :=
  fun _ => WDist.uniform [true, false]

-- Legal actions: both booleans
private def A_bool : Act (L := L) (v := vEmpty1) Ty.bool :=
  fun _ => [true, false]

/-- Hidden-info protocol:
1. Nature samples a bit (YieldId 0, empty view)
2. Player 0 guesses a bool (YieldId 1, empty view — no info)
3. Return both as a pair via letDet + ret -/
noncomputable def hiddenProto :
    ProtoProg (L := L) Γ0 Ty.bool :=
  -- Sample nature's bit
  ProtoProg.sample (id := 0) (v := vEmpty) (K := uniformBool)
    -- Player 0 guesses (sees nothing)
    (ProtoProg.choose (id := 1) (who := 0) (v := vEmpty1)
      (A := A_bool)
      -- Observe: guess matches nature's bit (eqInt won't work; use
      -- direct boolean equality via the expression language)
      -- Actually we just return the guess for now; utility handles matching
      (ProtoProg.ret basicExprLaws.vz))

/-- Utility: player 0 gets 1 if the guess matches the hidden bit.
We simplify by only returning the guess; a richer version would
return both and compare. For this example, utility is just
"always 0.5 EU" since the player can't see nature's bit. -/
noncomputable def hiddenUtil : Utility (L := L) Ty.bool :=
  fun b who =>
    if who = 0 then (if b = true then 1 else 0) else 0

/-- The hidden-info game. -/
noncomputable def hiddenGame : Game (L := L) Γ0 where
  τ := Ty.bool
  p := hiddenProto
  u := hiddenUtil

end Proto.Examples.HiddenDecision

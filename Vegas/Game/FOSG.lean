/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import GameTheory.Languages.FOSG.Kuhn
import Vegas.Game.Basic

/-! # Optional FOSG presentation of bounded Vegas analyses -/

noncomputable section

namespace Vegas.BoundedGame

open GameTheory.Languages

universe uPlayer uGame

/-- Present the same execution and information objects as a FOSG.  This adds
no runner, policy carrier, or outcome law. -/
def toFOSG {Player : Type uPlayer} (game : BoundedGame.{uPlayer, uGame} Player) :
    FOSG.Game.{uPlayer, uGame, uGame, uGame, uGame, uGame} Player where
  execution := game.execution
  information := game.information

/-- The optional FOSG presentation compiles to the same pure strategic form. -/
@[simp] theorem toFOSG_toGameForm {Player : Type uPlayer}
    (game : BoundedGame.{uPlayer, uGame} Player) :
    game.toFOSG.toGameForm game.horizon = game.pureForm := rfl

/-- The optional FOSG presentation also compiles to the same behavioral form. -/
@[simp] theorem toFOSG_toBehavioralGameForm {Player : Type uPlayer}
    [Fintype Player] (game : BoundedGame.{uPlayer, uGame} Player) :
    game.toFOSG.toBehavioralGameForm game.horizon = game.behavioralForm := rfl

end Vegas.BoundedGame

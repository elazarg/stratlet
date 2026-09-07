/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import GameTheory
import GameTheory.Analysis.Protocol
import GameTheory.Languages.FOSG.Kuhn
import GameTheory.Languages.FOSG.Values
import GameTheory.Languages.Bridges.FOSGToEFGStrategic
import Vegas.Core
import Vegas.EventGraph
import Vegas.Language
import Vegas.Compile
import Vegas.Machine
import Vegas.Game
import Vegas.Runtime
import Vegas.Scheduled

/-!
# Vegas

Public root for the checked source language, event-graph compiler, canonical
informed stochastic-game denotation, GameTheory analysis, and runtime adequacy
interface.
-/

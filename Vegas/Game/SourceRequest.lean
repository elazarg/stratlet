/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import Vegas.Game.Kuhn
import Vegas.Runtime.RequestCompiler

/-! # Request-game certificates for checked source programs

The compiler covers every decision of every checked core program. A source
timeout policy must supply an existing legal action at each information state.
This annotation cannot manufacture quitting semantics: if the source omits a
quit action or a reveal-withholding decision, this pass does not add it.

The behavioral certificate composes the finite-site Kuhn theorem with the
whole-protocol request compiler. Target strategies are finite private mixtures
of controllers with their complete own request histories. There is no scheduler,
public request side channel, transaction fee, or censorship in this target.
-/

noncomputable section

namespace Vegas.WFProgram

open GameTheory Vegas.Runtime

variable {Player : Type} [Fintype Player] [DecidableEq Player] {L : IExpr}
variable (source : WFProgram Player L) {Request : Player → Type}
variable (interface : RequestCompiler.Interface source.boundedGame.information Request)

def requestGame : UtilityGame Player :=
  (RequestCompiler.targetGame source.boundedGame.information interface
    source.boundedGame.horizon source.boundedGame.utility).mixed

/-- Uniform compilation for every checked core program with source-designated
timeout actions. All source-history laws, not merely payoffs, are preserved. -/
def mixedRequestAdequacy : DeviationAdequacy source.boundedGame.mixedPure
    (source.requestGame interface) :=
  RequestCompiler.mixedAdequacy source.boundedGame.information interface
    (Machine.compile source).perfectRecall source.boundedGame.horizon source.boundedGame.utility

/-- Finite-domain source behavioral games are preserved against every target
controller mixture, including deviations in both game choices and retry logic. -/
def behavioralRequestAdequacy [FiniteDomains source] :
    DeviationAdequacy source.boundedGame.behavioral (source.requestGame interface) :=
  source.behavioralToMixedPureAdequacy.trans (source.mixedRequestAdequacy interface)

theorem request_nash_iff [FiniteDomains source]
    (profile : Profile source.boundedGame.behavioral.form.sig) :
    IsNash (source.requestGame interface).form
      (euPreference (source.requestGame interface).utility)
      ((source.behavioralRequestAdequacy interface).compileProfile profile) ↔
    IsNash source.boundedGame.behavioral.form
      (euPreference source.boundedGame.behavioral.utility) profile :=
  (source.behavioralRequestAdequacy interface).isNash_compileProfile_iff profile

end Vegas.WFProgram

/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import Vegas.Compile.SealedRefinement
import Vegas.Compile.SourceAdequacy

/-! # Checked source through graph compilation to native messages

Every finite native run of a supported checked core program decodes to a
reachable prefix of its canonical compiled graph. If that prefix is terminal,
the existing graph-to-written-source support theorem reconstructs an actual
source execution with the same terminal bindings and payout evaluation.

The terminal premise is explicit. The theorem does not guarantee that a
withholding run settles, or compare policies or outcome distributions.
-/

namespace Vegas.WFProgram

open EventGraph Interaction

variable {Player : Type} [DecidableEq Player] {L : IExpr}

/-- End-to-end support-level correctness for the sealed-message backend
fragment. Native actions include arbitrary payloads, registration, delivery,
and inclusion; the reconstructed source run uses the original checked term. -/
theorem sealed_run_source (source : WFProgram Player L) (ty : L.Ty)
    [DecidableEq (L.Val ty)]
    (supported : SealedFragment (ToEventGraph.compile source.core).graph ty)
    (actions : List (SealedProgram.Action Player (L.Val ty))) :
    ∃ cfg : Config (ToEventGraph.compile source.core).graph,
      (ToEventGraph.compile source.core).graph.decodeSealed ty
        (SealedProgram.run supported.compile
          (SealedProgram.State.empty Player (L.Val ty)) actions) = some cfg ∧
      Reachable (ToEventGraph.compile source.core).graph cfg ∧
      (Terminal (ToEventGraph.compile source.core).graph cfg →
        ∃ terminalEnv : VEnv L (ToEventGraph.compile source.core).terminalCtx,
          SmallStep.Star
            { ctx := source.core.Γ, env := source.core.env, cont := source.core.prog }
            { ctx := (ToEventGraph.compile source.core).terminalCtx,
              env := terminalEnv, cont := .ret (ToEventGraph.compile source.core).sourcePayoffs } ∧
          evalPayoffs? (ToEventGraph.compile source.core).payoffs cfg.store =
            some (evalPayoffs (ToEventGraph.compile source.core).sourcePayoffs terminalEnv) ∧
          ∀ {name bindTy}
            (h : VHasVar (ToEventGraph.compile source.core).terminalCtx name bindTy),
            Store.getAs cfg.store
              ((ToEventGraph.compile source.core).terminalState.fieldOf h) bindTy.base =
                some (terminalEnv.get h)) := by
  obtain ⟨cfg, hdecode, hreachable⟩ := supported.run_refines actions
  exact ⟨cfg, hdecode, hreachable,
    fun hterminal => ToEventGraph.compile_sourceStar source.core cfg hreachable hterminal⟩

end Vegas.WFProgram

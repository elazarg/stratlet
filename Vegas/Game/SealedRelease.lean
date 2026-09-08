/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import Interaction.SealedController
import Vegas.Compile.SealedRules

/-! # Compiled opening release barrier

The generic opening controller can submit for a compiled reveal node only after
every graph prerequisite of that node is complete in its public runtime view.
-/

namespace Vegas.EventGraph.SealedFragment

open Interaction

variable {Player : Type} [DecidableEq Player] {L : IExpr}
variable {G : Graph Player L} {ty : L.Ty}

/-- Any non-wait opening command for a compiled node certifies completion of
all of that graph node's prerequisites in the controller's public view. -/
theorem openingCommand_prerequisites (supported : SealedFragment G ty)
    (owner : Player) (node : Fin G.nodeCount) (value : L.Val ty)
    (view : SealedProgram.View Player (L.Val ty))
    (hnonwait : SealedProgram.openingCommand supported.compile owner node.val value view ≠
      .wait) :
    ∀ prior, prior ∈ G.prereqs node →
      SealedProgram.done view.events prior.val = true := by
  obtain ⟨source, requires, _hcommand, hrule, _hnotDone, hrequires, _haccepted⟩ :=
    SealedProgram.openingCommand_ne_wait_sound supported.compile owner node.val value view
      hnonwait
  have hcompiled := supported.compile_rule node
  have hruleEq : G.sealedRule node =
      { kind := .reveal owner source, requires := requires } :=
    Option.some.inj (hcompiled.symm.trans hrule)
  have hrequiresEq : G.messagePrerequisites node = requires :=
    congrArg SealedRule.requires hruleEq
  rw [← hrequiresEq] at hrequires
  intro prior hprior
  apply List.all_eq_true.mp hrequires prior.val
  exact (G.mem_messagePrerequisites node prior).2 hprior

end Vegas.EventGraph.SealedFragment

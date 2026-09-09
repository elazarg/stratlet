/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import Vegas.Compile.PublicChoiceValidation
import VegasTests.DisclosureAccounting

/-! # Public guard validation boundaries -/

noncomputable section

namespace VegasTests.PublicGuard

open Vegas Vegas.EventGraph Vegas.ToEventGraph

abbrev Player := Fin 2

def publicDependencyGuard : EventGuard simpleExpr where
  ty := .bool
  code :=
    { actionName := 1
      Context := [(0, .bool)]
      expr := .eq (.var 1 .here) (.var 0 (.there .here))
      fieldOf := fun binding => match binding with
        | .here => 0 }
  choiceReads := {{ field := 0, ty := .bool }}
  read_mem := by
    intro name ty binding
    cases binding with
    | here => simp [GuardCode.ref]
    | there binding => nomatch binding

def publicGraph : Graph Player simpleExpr where
  initialFields := [{ ty := .bool, owner := none, value := true }]
  nodes := []

def storedTrue : Store simpleExpr
  | 0 => some ⟨.bool, true⟩
  | _ => none

def missingStore : Store simpleExpr := fun _ => none

example : publicDependencyGuard.PubliclyValidatable publicGraph := by
  have hreads : publicDependencyGuard.validationReads =
      {{ field := 0, ty := simpleExpr.bool }} := rfl
  intro ref href
  rw [hreads] at href
  simp only [Finset.mem_singleton] at href
  subst ref
  exact ⟨_, rfl, rfl, rfl⟩

example : publicDependencyGuard.validate storedTrue true = true := by
  decide

example : publicDependencyGuard.validate storedTrue false = false := by
  decide

example : publicDependencyGuard.validate missingStore true = false := by
  decide

namespace PrivateDependency

open VegasTests.OptionalDisclosure

/-- Structural adjacency does not imply that the retained guard can be
evaluated from public fields. This site reads the owner's sealed input. -/
def occurrence : PublicChoiceSite source.prog where
  context := OpeningContext
  choiceName := 4
  publicName := 5
  owner := 0
  ty := .option .bool
  guard := openingGuard
  tail := .commit 6 1 (.constBool true)
    (.reveal 7 1 6 .here (.ret [(0, payoff)]))
  decision := .commit (.commit (.reveal (.sample (.here _ _))))
  adjacent := rfl

def compilerInitial : BuildState TestPlayer simpleExpr source.Γ :=
  BuildState.fromInitial (initialState source.Γ source.env source.wctx)

example : ¬ occurrence.PubliclyValidatable source.fresh compilerInitial := by
  intro hpublic
  let ref : FieldRef simpleExpr := { field := 0, ty := .bool }
  have href : ref ∈
      (occurrence.compiledGuard source.fresh compilerInitial).validationReads := by
    decide
  rcases hpublic ref href with ⟨spec, hfield, _, howner⟩
  have : spec.owner = some 0 := by
    simpa [ref, occurrence, compilerInitial, source] using
      (congrArg FieldSpec.owner (Option.some.inj hfield)).symm
  simp [this] at howner

end PrivateDependency

end VegasTests.PublicGuard

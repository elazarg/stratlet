/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import VegasTests.Game

/-! # Two disclosure checkpoints in the existing core

The second guard removes the opening choice after an earlier public refusal.
This is a checked graph-level encoding probe, not a timeout realization or a
claim that administrative polling is strategically invisible.
-/

noncomputable section

namespace VegasTests.PersistentDisclosure

open Vegas EventGraph

abbrev Player := TestPlayer

abbrev FirstContext : VCtx Player simpleExpr :=
  [(3, .pub .bool), (2, .pub .bool), (1, .sealed 0 .bool), (0, .sealed 0 .bool)]

def firstGuard :
    Expr ((4, .option .bool) :: eraseVCtx (viewVCtx (0 : Player) FirstContext)) .bool :=
  .ite (.isNone (.var 4 .here)) (.constBool true)
    (.eq (.var 4 .here)
      (.some (.var 0 (.there (.there (.there (.there .here)))))))

abbrev SecondContext : VCtx Player simpleExpr :=
  [(7, .pub .bool), (6, .sealed 1 .bool), (5, .pub (.option .bool)),
   (4, .sealed 0 (.option .bool))] ++ FirstContext

private def orBool {Γ : CtxSimple} (left right : Expr Γ .bool) : Expr Γ .bool :=
  .notBool (.andBool (.notBool left) (.notBool right))

def secondGuard :
    Expr ((8, .option .bool) :: eraseVCtx (viewVCtx (0 : Player) SecondContext)) .bool :=
  .ite (.isNone (.var 5 (.there (.there .here))))
    (.isNone (.var 8 .here))
    (orBool (.isNone (.var 8 .here))
      (.eq (.var 8 .here) (.some (.var 0
        (.there (.there (.there (.there (.there (.there (.there .here)))))))))))

abbrev PayoffContext : CtxSimple :=
  [(9, .option .bool), (7, .bool), (5, .option .bool), (3, .bool), (2, .bool)]

def payoff : Expr PayoffContext .int :=
  .ite (.isNone (.var 9 .here)) (.constInt (-1)) (.constInt 1)

def core : VegasCore Player simpleExpr [] :=
  .commit 0 0 (.constBool true)
    (.commit 1 0 (.notBool (.var 1 .here))
      (.reveal 2 0 1 .here
        (.sample 3 (.weighted (b := .bool) fairCoin)
          (.commit 4 0 firstGuard
            (.reveal 5 0 4 .here
              (.commit 6 1 (.constBool true)
                (.reveal 7 1 6 .here
                  (.commit 8 0 secondGuard
                    (.reveal 9 0 8 .here (.ret [(0, payoff)]))))))))))

def source : GraphProgram Player simpleExpr where
  Γ := []
  prog := core
  env := VEnv.empty simpleExpr
  wctx := by simp
  fresh := by simp [core, FreshBindings, Fresh]

theorem legal : Legal source.prog := by
  unfold source core
  constructor
  · intro _
    exact ⟨false, rfl⟩
  · constructor
    · intro _
      exact ⟨false, rfl⟩
    · constructor
      · intro _
        exact ⟨none, rfl⟩
      · constructor
        · intro _
          exact ⟨false, rfl⟩
        · constructor
          · intro _
            exact ⟨none, by simp [evalGuard, secondGuard, orBool, evalExpr]⟩
          · trivial

abbrev compiled := ToEventGraph.compile source
abbrev graph := compiled.graph
def node (index : Fin 10) : Fin graph.nodeCount := index

theorem nodeCount : graph.nodeCount = 10 := rfl

theorem second_after_first_and_response :
    node 5 ∈ graph.prereqs (node 8) ∧ node 7 ∈ graph.prereqs (node 8) := by
  decide

def firstEnv (secret signal : Bool) : VEnv simpleExpr FirstContext :=
  ((((VEnv.empty simpleExpr).cons secret).cons false).cons false).cons signal

theorem first_guard_iff (secret signal : Bool) (opening : Option Bool) :
    evalGuard (Player := Player) (L := simpleExpr) firstGuard opening
      ((firstEnv secret signal).toView 0).eraseEnv = true ↔
        opening = none ∨ opening = some secret := by
  cases secret <;> cases signal <;> fin_cases opening <;> decide

def secondEnv (secret signal : Bool) (first : Option Bool) (response : Bool) :
    VEnv simpleExpr SecondContext :=
  ((((firstEnv secret signal).cons first).cons first).cons response).cons response

theorem second_guard_iff (secret signal response : Bool)
    (first later : Option Bool) :
    evalGuard (Player := Player) (L := simpleExpr) secondGuard later
      ((secondEnv secret signal first response).toView 0).eraseEnv = true ↔
      (first = none ∧ later = none) ∨
        (first ≠ none ∧ (later = none ∨ later = some secret)) := by
  cases secret <;> cases signal <;> cases response <;>
    fin_cases first <;> fin_cases later <;> decide

theorem refusal_forces_later_refusal (secret signal response : Bool) (later : Option Bool)
    (hlegal : evalGuard (Player := Player) (L := simpleExpr) secondGuard later
      ((secondEnv secret signal none response).toView 0).eraseEnv = true) :
    later = none := by
  exact (((second_guard_iff secret signal response none later).mp hlegal).resolve_right
    (by simp)).2

/-- The second guard permits only decline or the retained binding, for every
source environment rather than just the canonical execution environments. -/
theorem second_guard_sound (env : VEnv simpleExpr SecondContext) (chosen : Option Bool)
    (hlegal : evalGuard (Player := Player) (L := simpleExpr) secondGuard chosen
      ((env.toView 0).eraseEnv) = true) :
    chosen = none ∨ chosen = some (env.get
      (.there (.there (.there (.there (.there (.there (.there .here)))))))) := by
  change (if (env.get (.there (.there .here))).isNone then chosen.isNone
    else !(!chosen.isNone && !decide (chosen = some (env.get
      (.there (.there (.there (.there (.there (.there (.there .here))))))))))) = true at hlegal
  generalize env.get (.there (.there .here)) = first at hlegal
  generalize env.get
    (.there (.there (.there (.there (.there (.there (.there .here))))))) = secret
      at hlegal ⊢
  fin_cases chosen <;> fin_cases first <;> fin_cases secret <;> simp_all

/-- Decline remains legal at the later site, independently of earlier choices. -/
theorem second_decline_legal (env : VEnv simpleExpr SecondContext) :
    evalGuard (Player := Player) (L := simpleExpr) secondGuard none
      ((env.toView 0).eraseEnv) = true := by
  simp [evalGuard, secondGuard, orBool, evalExpr]

instance fieldCountNeZero : NeZero graph.fieldCount := ⟨by decide⟩

theorem original_not_read_by_responder (index : Fin graph.nodeCount)
    (guard : EventGuard simpleExpr)
    (hsem : graph.node? index = some (.commit (1 : Player) guard)) :
    ({ field := 0, ty := .bool } : FieldRef simpleExpr) ∉ guard.choiceReads := by
  fin_cases index <;> cases hsem
  decide

theorem original_absent_from_response (cfg : Config graph)
    (index : Fin graph.nodeCount) :
    (observe graph cfg (1 : Player)).fieldValue? index 0 = none := by
  have hty : (graph.fieldRow 0).ty = .bool := rfl
  have hfield : (0 : Fin graph.fieldCount).val = 0 := rfl
  cases hnode : graph.node? index with
  | none => simp only [observe, hnode]
  | some sem =>
    cases sem with
    | sample dist => simp only [observe, hnode]
    | reveal source => simp only [observe, hnode]
    | commit actor guard =>
      by_cases hactor : actor = (1 : Player)
      · subst actor
        simp only [observe, hnode, hty, hfield]
        simp [original_not_read_by_responder index guard hnode]
      · simp only [observe, hnode, dif_neg hactor]

theorem original_absent_from_public (cfg : Config graph) :
    (publicObserve graph cfg).fieldValue? 0 = none := by
  have howner : (graph.fieldRow 0).owner = some (0 : Player) := rfl
  simp [publicObserve, howner]

theorem not_reveal_complete : ¬RevealComplete [] core := by decide

end VegasTests.PersistentDisclosure

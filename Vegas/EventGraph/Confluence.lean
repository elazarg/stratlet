/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import Vegas.EventGraph.Execution

/-!
# Confluent coarsening of the event graph

The source small-step semantics executes the written program order
(see `Vegas.Core.SmallStep`).
The event graph deliberately does *not*: `EventGraph.Execution` exposes available
events without choosing an order. This module justifies that move at the level
of the raw graph configuration.

A *schedule* is an order in which nodes are completed. `Config.completeNodes`
folds a list of `(node, value)` writes in that order, and `Config.scheduleComplete`
specialises to a fixed per-node value assignment. The headline results are:

* `completeNodes_perm` / `scheduleComplete_perm` — **conservativity**: permuting
  the schedule (with the per-node values held fixed) does not change the
  resulting configuration. This is the diamond `completeNode_comm` closed under
  arbitrary reordering, i.e. the order-independence at the heart of the
  confluent-coarsening picture.
This is the unconditional, outcome-level half of the justification. Lifting it
to *per-player views* at intermediate cuts is a separate, finer obligation.
-/

namespace Vegas

namespace EventGraph

variable {Player : Type} [DecidableEq Player] {L : IExpr}

namespace Config

variable {G : Graph Player L}

/-- If a field is not the target of any scheduled node, completing the schedule
does not change the typed read at that field. -/
theorem completeNodes_getAs_of_not_targets (cfg : Config G)
    (steps : List (Fin G.nodeCount × TypedValue L))
    {field : Nat} {ty : L.Ty}
    (hnot :
      ∀ step, step ∈ steps → field ≠ G.nodeTarget step.1) :
    Store.getAs (cfg.completeNodes steps).store field ty =
      Store.getAs cfg.store field ty := by
  induction steps generalizing cfg with
  | nil =>
      rfl
  | cons step rest ih =>
      rw [completeNodes_cons, ih]
      · exact Store.getAs_set_ne cfg.store (hnot step (by simp)) step.2 ty
      · intro tailStep htailStep
        exact hnot tailStep (by simp [htailStep])

/-- Reading the target of a scheduled node after a duplicate-free schedule
returns the value assigned to that node. -/
theorem completeNodes_getAs_of_mem (cfg : Config G)
    (steps : List (Fin G.nodeCount × TypedValue L))
    (hnodup : (steps.map Prod.fst).Nodup)
    {node : Fin G.nodeCount} {value : TypedValue L}
    (hmem : (node, value) ∈ steps) (ty : L.Ty) :
    Store.getAs (cfg.completeNodes steps).store (G.nodeTarget node) ty =
      value.as? ty := by
  induction steps generalizing cfg with
  | nil =>
      simp at hmem
  | cons step rest ih =>
      rcases step with ⟨headNode, headValue⟩
      simp only [List.map_cons, List.nodup_cons] at hnodup
      simp only [List.mem_cons] at hmem
      cases hmem with
      | inl hhead =>
          have hnotTail :
              ∀ tailStep, tailStep ∈ rest →
                G.nodeTarget node ≠ G.nodeTarget tailStep.1 := by
            intro tailStep htailStep
            have hnodeNe : node ≠ tailStep.1 := by
              intro hnode
              have hnodeHead : node = headNode :=
                congrArg Prod.fst hhead
              exact hnodup.1 (by
                have hheadTail : headNode = tailStep.1 := by
                  rw [← hnodeHead, hnode]
                rw [hheadTail]
                exact List.mem_map_of_mem (f := Prod.fst) htailStep)
            exact Config.nodeTarget_ne_of_ne (G := G) hnodeNe
          rw [completeNodes_cons,
            completeNodes_getAs_of_not_targets _ rest hnotTail]
          cases hhead
          simp [Config.completeNode, Store.getAs]
      | inr htail =>
          exact ih (cfg.completeNode headNode headValue) hnodup.2 htail

/-! ## Conservativity: schedules commute -/

/-- **Conservativity of the coarsening.** Permuting the schedule, with the
per-node values held fixed, leaves the resulting configuration unchanged. The
distinctness hypothesis (the touched nodes are `Nodup`) is what licenses each
transposition via the `completeNode` diamond. -/
theorem completeNodes_perm (cfg : Config G)
    {steps₁ steps₂ : List (Fin G.nodeCount × TypedValue L)}
    (hperm : List.Perm steps₁ steps₂) :
    (steps₁.map Prod.fst).Nodup →
      cfg.completeNodes steps₁ = cfg.completeNodes steps₂ := by
  induction hperm generalizing cfg with
  | nil => intro _; rfl
  | cons s _p ih =>
      intro hnodup
      simp only [List.map_cons, List.nodup_cons] at hnodup
      simp only [completeNodes_cons]
      exact ih (cfg.completeNode s.1 s.2) hnodup.2
  | swap s t l =>
      intro hnodup
      simp only [List.map_cons] at hnodup
      have hne : t.1 ≠ s.1 := by
        intro heq
        apply (List.nodup_cons.mp hnodup).1
        rw [heq]
        exact List.mem_cons_self
      simp only [completeNodes_cons]
      rw [Config.completeNode_comm cfg (left := t.1) (right := s.1) t.2 s.2 hne]
  | trans p₁ _p₂ ih₁ ih₂ =>
      intro hnodup
      exact (ih₁ cfg hnodup).trans
        (ih₂ cfg ((p₁.map Prod.fst).nodup_iff.mp hnodup))

/-! ## A fixed value assignment scheduled in any order -/

/-- Complete the nodes listed in `order`, writing each its assigned value `w`.

`w` is a store-level assignment of an arbitrary `TypedValue` to each node; the
order-independence results below hold for any such `w`, with no typing
requirement. Type coherence (a node's written value matching its declared type)
is a separate concern handled by `StoreCoherent.completeNodeTyped`. -/
def scheduleComplete (cfg : Config G) (w : Fin G.nodeCount → TypedValue L)
    (order : List (Fin G.nodeCount)) : Config G :=
  cfg.completeNodes (order.map (fun node => (node, w node)))

/-- The nodes touched by `scheduleComplete w order` are exactly `order`. -/
@[simp] theorem map_fst_pair (order : List (Fin G.nodeCount))
    (w : Fin G.nodeCount → TypedValue L) :
    (order.map (fun node => (node, w node))).map Prod.fst = order := by
  induction order with
  | nil => rfl
  | cons _ _ ih => simp [ih]

theorem scheduleComplete_done (cfg : Config G)
    (w : Fin G.nodeCount → TypedValue L) (order : List (Fin G.nodeCount)) :
    (cfg.scheduleComplete w order).done = cfg.done ∪ order.toFinset := by
  unfold scheduleComplete
  rw [completeNodes_done, map_fst_pair]

/-- **Schedule-invariance for a fixed value assignment.** Two orderings of the
same node set, completing each node with the same value, reach the same
configuration. -/
theorem scheduleComplete_perm (cfg : Config G)
    (w : Fin G.nodeCount → TypedValue L)
    {o₁ o₂ : List (Fin G.nodeCount)}
    (hperm : List.Perm o₁ o₂) (hnodup : o₁.Nodup) :
    cfg.scheduleComplete w o₁ = cfg.scheduleComplete w o₂ := by
  unfold scheduleComplete
  refine completeNodes_perm cfg (hperm.map _) ?_
  rw [map_fst_pair]
  exact hnodup

/-- A schedule that lists every node drives the initial configuration to a
terminal one. -/
theorem scheduleComplete_terminal (w : Fin G.nodeCount → TypedValue L)
    {order : List (Fin G.nodeCount)} (hcover : ∀ node, node ∈ order) :
    Terminal G ((Config.initial G).scheduleComplete w order) := by
  intro node
  rw [scheduleComplete_done]
  simp only [Config.initial, Finset.empty_union, List.mem_toFinset]
  exact hcover node

end Config

end EventGraph

end Vegas

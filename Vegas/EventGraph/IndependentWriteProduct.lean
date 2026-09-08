/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import Vegas.EventGraph.IndependentWrites

/-! # Product characterization of fixed-law graph writes -/

noncomputable section
namespace Vegas.EventGraph
open GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr}

private theorem runDependent_apply_of_not_mem
    {ι A : Type} [DecidableEq ι] (laws : ι → FinDist A)
    (indices : List ι) (assignment : ι → A) (index : ι)
    (hnot : index ∉ indices) (result : ι → A)
    (hresult : result ∈ (FinDist.runDependent laws indices assignment).support) :
    result index = assignment index := by
  induction indices generalizing assignment with
  | nil =>
      have heq : result = assignment := by
        simpa [FinDist.runDependent] using hresult
      exact congrFun heq index
  | cons head tail ih =>
      rw [FinDist.runDependent, FinDist.support_bind] at hresult
      simp only [Set.mem_iUnion] at hresult
      obtain ⟨value, _, hvalue⟩ := hresult
      have hne : index ≠ head := by
        intro heq
        exact hnot (by simp [heq])
      have htail : index ∉ tail := by
        intro hmem
        exact hnot (by simp [hmem])
      rw [ih (FinDist.DependentAssignment.setOne assignment ⟨head, value⟩)
        htail hvalue]
      exact FinDist.DependentAssignment.setOne_apply_of_ne assignment value hne

private def defaultAssignment {G : Graph Player L}
    (laws : Fin G.nodeCount → FinDist (TypedValue L)) :
    Fin G.nodeCount → TypedValue L :=
  fun node => Classical.choose (laws node).support_nonempty

private def applyAssignment {G : Graph Player L} (cfg : Config G)
    (order : List (Fin G.nodeCount))
    (assignment : Fin G.nodeCount → TypedValue L) : Config G :=
  cfg.completeNodes (order.map fun node => (node, assignment node))

private theorem runIndependentWrites_eq_runDependent {G : Graph Player L}
    (laws : Fin G.nodeCount → FinDist (TypedValue L))
    (cfg : Config G) (order : List (Fin G.nodeCount)) (hnodup : order.Nodup)
    (assignment : Fin G.nodeCount → TypedValue L) :
    runIndependentWrites laws cfg order =
      (FinDist.runDependent laws order assignment).map
        (applyAssignment cfg order) := by
  induction order generalizing cfg assignment with
  | nil => simp [runIndependentWrites, FinDist.runDependent, applyAssignment]
  | cons head tail ih =>
      have hhead : head ∉ tail := (List.nodup_cons.mp hnodup).1
      have htail := (List.nodup_cons.mp hnodup).2
      rw [runIndependentWrites_cons, FinDist.runDependent, FinDist.map_bind]
      apply FinDist.bind_congr
      intro value _
      rw [ih (cfg := cfg.completeNode head value)
        (assignment := FinDist.DependentAssignment.setOne assignment ⟨head, value⟩)
        htail]
      apply FinDist.map_congr_of_eq_on_support
      intro result hresult
      have hvalue := runDependent_apply_of_not_mem laws tail
        (FinDist.DependentAssignment.setOne assignment ⟨head, value⟩)
        head hhead result hresult
      rw [FinDist.DependentAssignment.setOne_apply_self] at hvalue
      simp only [applyAssignment, List.map_cons, Config.completeNodes_cons]
      rw [hvalue]

/-- A duplicate-free fixed-law execution is the independent product of the
listed node laws, mapped through the corresponding graph writes. -/
theorem runIndependentWrites_eq_pi {G : Graph Player L}
    (laws : Fin G.nodeCount → FinDist (TypedValue L))
    (cfg : Config G) (order : List (Fin G.nodeCount)) (hnodup : order.Nodup) :
    runIndependentWrites laws cfg order =
      (FinDist.pi fun node : {node // node ∈ order.toFinset} => laws node.1).map
        (fun draw => cfg.completeNodes
          (order.attach.map fun node =>
            (node.1, draw ⟨node.1, List.mem_toFinset.mpr node.2⟩))) := by
  rw [runIndependentWrites_eq_runDependent laws cfg order hnodup
    (defaultAssignment laws)]
  rw [FinDist.runDependent_eq_pi_subtype laws order hnodup
    (defaultAssignment laws), FinDist.map_comp]
  apply FinDist.map_congr_of_eq_on_support
  intro draw _
  simp only [applyAssignment, Function.comp_apply]
  apply congrArg cfg.completeNodes
  apply List.ext_get
  · simp
  · intro index hleft hright
    simp only [List.get_eq_getElem, List.getElem_map,
      List.getElem_attach]
    congr 1
    apply FinDist.DependentAssignment.resolve_of_mem

end Vegas.EventGraph

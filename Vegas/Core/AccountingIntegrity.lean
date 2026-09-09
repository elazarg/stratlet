/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import Vegas.Core.WellFormed

/-! # Linear integrity of commitment accounting

An accounting derivation discharges exactly the initially pending names and
the names introduced by source commitments. Under source freshness and scoped
initial pending names, no name is discharged twice. This is a resource-counting
statement, not a secrecy or noninterference theorem.
-/

namespace Vegas

variable {P : Type} {L : IExpr}

/-- Every initially sealed name is a name in its source context. -/
theorem mem_context_names_of_mem_sealedVars {Γ : VCtx P L} {name : VarId}
    (hname : name ∈ SealedVars Γ) : name ∈ Γ.map Prod.fst := by
  induction Γ with
  | nil => simp [SealedVars] at hname
  | cons binding Γ ih =>
      rcases binding with ⟨x, ty, visibility⟩
      cases visibility with
      | pub =>
          exact List.mem_cons_of_mem x (ih hname)
      | sealed who =>
          simp only [SealedVars, List.mem_cons] at hname
          rcases hname with rfl | hname
          · exact List.mem_cons_self
          · exact List.mem_cons_of_mem x (ih hname)

/-- The canonical pending set of an initial context is scoped by that context. -/
theorem sealedVars_toFinset_scoped {Γ : VCtx P L} :
    ∀ name ∈ (SealedVars Γ).toFinset, name ∈ Γ.map Prod.fst := by
  intro name hname
  exact mem_context_names_of_mem_sealedVars (List.mem_toFinset.mp hname)

namespace CommitmentAccounting

variable [DecidableEq P]

/-- The discharge sequence. An optional opening discharges both its adjacent
copy commitment and the earlier binding named by its certificate. -/
def resolvedSources : {Γ : VCtx P L} → {pending : Finset VarId} →
    {prog : VegasCore P L Γ} → CommitmentAccounting pending prog → List VarId
  | _, _, _, .ret _ => []
  | _, _, _, .sample tail => tail.resolvedSources
  | _, _, _, .commit _ tail => tail.resolvedSources
  | _, _, _, .reveal (x := x) _ tail => x :: tail.resolvedSources
  | _, _, _, .opening (copyName := copyName) spec _ _ tail =>
      copyName :: spec.source :: tail.resolvedSources

/-- Each name is discharged exactly once for initial membership and once for
each syntactic commitment bearing that name. -/
theorem count_resolvedSources {Γ : VCtx P L} {pending : Finset VarId}
    {prog : VegasCore P L Γ} (plan : CommitmentAccounting pending prog)
    (name : VarId) :
    plan.resolvedSources.count name =
      (if name ∈ pending then 1 else 0) + (CommittedVars prog).count name := by
  induction plan with
  | ret hempty => simp [resolvedSources, CommittedVars, hempty]
  | sample plan ih => simpa [resolvedSources, CommittedVars] using ih
  | @commit Γ pending x who ty guard tail hfresh plan ih =>
      by_cases heq : name = x
      · subst name
        simpa [resolvedSources, CommittedVars, hfresh, Nat.add_comm] using ih
      · have hne : x ≠ name := Ne.symm heq
        simpa [resolvedSources, CommittedVars, heq, hne] using ih
  | @reveal Γ pending publicName sourceName who ty source tail hunresolved plan ih =>
      by_cases heq : name = sourceName
      · subst name
        simpa [resolvedSources, CommittedVars, hunresolved, Nat.add_comm] using ih
      · have hne : sourceName ≠ name := Ne.symm heq
        simpa [resolvedSources, CommittedVars, heq, hne] using ih
  | @opening Γ pending copyName publicName who copyTy guard tail spec hunresolved hfresh plan ih =>
      by_cases hcopy : name = copyName
      · subst name
        have hne : copyName ≠ spec.source := by
          intro heq
          exact hfresh (heq ▸ hunresolved)
        simpa [resolvedSources, CommittedVars, hfresh, hne, Ne.symm hne,
          Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using ih
      · by_cases hsource : name = spec.source
        · subst name
          have hcopy' : copyName ≠ spec.source := Ne.symm hcopy
          simpa [resolvedSources, CommittedVars, hcopy, hcopy', hunresolved,
            Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using ih
        · have hcopy' : copyName ≠ name := Ne.symm hcopy
          have hsource' : spec.source ≠ name := Ne.symm hsource
          simpa [resolvedSources, CommittedVars, hcopy, hcopy', hsource, hsource'] using ih

private theorem fresh_committedVars
    {Γ : VCtx P L} {prog : VegasCore P L Γ} (fresh : FreshBindings prog) :
    (CommittedVars prog).Nodup ∧
      ∀ name ∈ Γ.map Prod.fst, name ∉ CommittedVars prog := by
  induction prog with
  | ret => simp [CommittedVars]
  | sample x dist tail ih =>
      exact ⟨ih fresh.2 |>.1, fun name hname =>
        (ih fresh.2).2 name (List.mem_cons_of_mem x hname)⟩
  | commit x who guard tail ih =>
      have htail := ih fresh.2
      constructor
      · simp only [CommittedVars, List.nodup_cons]
        exact ⟨htail.2 x List.mem_cons_self, htail.1⟩
      · intro name hname
        simp only [CommittedVars, List.mem_cons, not_or]
        exact ⟨fun heq => fresh.1 (heq ▸ hname),
          htail.2 name (List.mem_cons_of_mem x hname)⟩
  | reveal publicName who source binding tail ih =>
      exact ⟨(ih fresh.2).1, fun name hname =>
        (ih fresh.2).2 name (List.mem_cons_of_mem publicName hname)⟩

/-- A fresh source program with initially scoped pending names never
discharges the same identifier twice. -/
theorem resolvedSources_nodup {Γ : VCtx P L} {pending : Finset VarId}
    {prog : VegasCore P L Γ} (plan : CommitmentAccounting pending prog)
    (fresh : FreshBindings prog)
    (hscope : ∀ name ∈ pending, name ∈ Γ.map Prod.fst) :
    plan.resolvedSources.Nodup := by
  rw [List.nodup_iff_count_le_one]
  intro name
  rw [plan.count_resolvedSources name]
  have hcommitted := fresh_committedVars fresh
  by_cases hpending : name ∈ pending
  · simp only [if_pos hpending]
    have hnot : name ∉ CommittedVars prog := hcommitted.2 name (hscope name hpending)
    simp [List.count_eq_zero.mpr hnot]
  · simp only [if_neg hpending, zero_add]
    exact List.nodup_iff_count_le_one.mp hcommitted.1 name

end CommitmentAccounting

namespace WFProgram

variable [DecidableEq P]

/-- A checked program accounts each initial or introduced commitment at one
and only one resolution site. -/
theorem resolutions_nodup (program : WFProgram P L) :
    program.accounted.resolvedSources.Nodup :=
  program.accounted.resolvedSources_nodup program.core.fresh
    sealedVars_toFinset_scoped

end WFProgram

end Vegas

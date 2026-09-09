/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import Vegas.Core.ConditionalOpening
import Vegas.Core.Obligations

/-! # Explicit accounting for sealed source bindings

An accounting plan follows existing core syntax. An ordinary reveal discharges
its pending binding. A certified adjacent optional choice and reveal can also
resolve an earlier binding: it publishes either that binding's value or an
explicit decline. The newly chosen copy is discharged by its own reveal.

Plans are data, so a compiler can inspect the typed resolution certificate and
its public site. They do not change source execution. Source scope/freshness
checks remain separate: pending identifiers are a finite set, and checked
programs additionally prohibit reuse of names in the source context.

An explicit disposition concerns one binding; persistent role-wide quitting
needs the source's continuation guards. The owner retains knowledge of the
original binding and may use it in later choices. Accounting therefore proves
neither erasure nor confidentiality of later traffic, and a plan is not itself
a public-message implementation.
-/

namespace Vegas

variable {P : Type} [DecidableEq P] {L : IExpr}

/-- A typed, inspectable resolution plan over unchanged core syntax. -/
inductive CommitmentAccounting :
    {Γ : VCtx P L} → Finset VarId → VegasCore P L Γ → Type where
  | ret {Γ : VCtx P L} {pending : Finset VarId}
      {payoffs : List (P × L.Expr (erasePubVCtx Γ) L.int)}
      (empty : pending = ∅) : CommitmentAccounting pending (.ret payoffs)
  | sample {Γ : VCtx P L} {pending : Finset VarId} {x : VarId} {b : L.Ty}
      {dist : L.DistExpr (erasePubVCtx Γ) b}
      {tail : VegasCore P L ((x, .pub b) :: Γ)}
      (accounted : CommitmentAccounting pending tail) :
      CommitmentAccounting pending (.sample x dist tail)
  | commit {Γ : VCtx P L} {pending : Finset VarId} {x : VarId} {who : P} {b : L.Ty}
      {guard : L.Expr ((x, b) :: eraseVCtx (viewVCtx who Γ)) L.bool}
      {tail : VegasCore P L ((x, .sealed who b) :: Γ)}
      (fresh : x ∉ pending)
      (accounted : CommitmentAccounting (insert x pending) tail) :
      CommitmentAccounting pending (.commit x who guard tail)
  | reveal {Γ : VCtx P L} {pending : Finset VarId} {y x : VarId} {who : P} {b : L.Ty}
      {source : VHasVar Γ x (.sealed who b)}
      {tail : VegasCore P L ((y, .pub b) :: Γ)}
      (unresolved : x ∈ pending)
      (accounted : CommitmentAccounting (pending.erase x) tail) :
      CommitmentAccounting pending (.reveal y who x source tail)
  | opening {Γ : VCtx P L} {pending : Finset VarId} {copyName publicName : VarId}
      {who : P} {copyTy : L.Ty}
      {guard : L.Expr ((copyName, copyTy) :: eraseVCtx (viewVCtx who Γ)) L.bool}
      {tail : VegasCore P L
        ((publicName, .pub copyTy) :: (copyName, .sealed who copyTy) :: Γ)}
      (spec : ConditionalOpening guard)
      (unresolved : spec.source ∈ pending)
      (fresh : copyName ∉ pending)
      (accounted : CommitmentAccounting (pending.erase spec.source) tail) :
      CommitmentAccounting pending
        (.commit copyName who guard (.reveal publicName who copyName .here tail))

namespace CommitmentAccounting

/-- Construct the ordinary accounting plan for a program that literally
reveals every pending binding. Scope and freshness exclude name aliasing. -/
def ofRevealComplete : {Γ : VCtx P L} → (prog : VegasCore P L Γ) →
    (fresh : FreshBindings prog) → (pending : List VarId) →
    (scope : ∀ x ∈ pending, x ∈ Γ.map Prod.fst) →
    (reveals : RevealComplete pending prog) →
    CommitmentAccounting pending.toFinset prog
  | _, .ret _, _, pending, _, reveals =>
      .ret (by rw [show pending = [] from reveals]; rfl)
  | _, .sample _ _ tail, fresh, pending, scope, reveals =>
      .sample (ofRevealComplete tail fresh.2 pending
        (fun name hname => List.mem_cons_of_mem _ (scope name hname)) reveals)
  | _, .commit x _ _ tail, fresh, pending, scope, reveals => by
      apply CommitmentAccounting.commit
      · exact fun hname => fresh.1 (scope x (List.mem_toFinset.mp hname))
      · simpa only [List.toFinset_cons] using ofRevealComplete tail fresh.2 (x :: pending)
          (by
            intro name hname
            rcases List.mem_cons.mp hname with rfl | hname
            · exact List.mem_cons_self
            · exact List.mem_cons_of_mem _ (scope name hname)) reveals
  | _, .reveal _ _ x _ tail, fresh, pending, scope, reveals => by
      apply CommitmentAccounting.reveal (List.mem_toFinset.mpr reveals.1)
      have hsets : (pending.filter (· ≠ x)).toFinset = pending.toFinset.erase x := by
        ext name
        simp only [List.mem_toFinset, List.mem_filter, decide_eq_true_eq, Finset.mem_erase]
        tauto
      rw [← hsets]
      exact ofRevealComplete tail fresh.2 (pending.filter (· ≠ x))
        (fun name hname => List.mem_cons_of_mem _
          (scope name (List.mem_filter.mp hname).1)) reveals.2

/-- Bindings explicitly resolved by optional publication rather than a direct
reveal of the original binding. The plan itself retains the richer certificate. -/
def dispositions : {Γ : VCtx P L} → {pending : Finset VarId} →
    {prog : VegasCore P L Γ} → CommitmentAccounting pending prog → Finset VarId
  | _, _, _, .ret _ => ∅
  | _, _, _, .sample tail => tail.dispositions
  | _, _, _, .commit _ tail => tail.dispositions
  | _, _, _, .reveal _ tail => tail.dispositions
  | _, _, _, .opening spec _ _ tail => insert spec.source tail.dispositions

/-- Public output names for the optional resolutions. Ordinary reveals already
identify their public aliases in the source syntax. -/
def publicationSites : {Γ : VCtx P L} → {pending : Finset VarId} →
    {prog : VegasCore P L Γ} → CommitmentAccounting pending prog → List (VarId × VarId)
  | _, _, _, .ret _ => []
  | _, _, _, .sample tail => tail.publicationSites
  | _, _, _, .commit _ tail => tail.publicationSites
  | _, _, _, .reveal _ tail => tail.publicationSites
  | _, _, _, .opening (publicName := name) spec _ _ tail =>
      (spec.source, name) :: tail.publicationSites

/-- No pending or newly committed identifier disappears from an accounting
plan: it has a literal reveal or a certified optional resolution. -/
theorem pending_or_committed_resolved {Γ : VCtx P L} {pending : Finset VarId}
    {prog : VegasCore P L Γ} (plan : CommitmentAccounting pending prog)
    (name : VarId) (hname : name ∈ pending ∨ name ∈ CommittedVars prog) :
    name ∈ RevealedSources prog ∨ name ∈ plan.dispositions := by
  induction plan with
  | ret hempty =>
      simp_all [CommittedVars]
  | sample plan ih =>
      exact ih hname
  | commit hfresh plan ih =>
      apply ih
      simp only [CommittedVars, List.mem_cons] at hname
      simp only [Finset.mem_insert]
      tauto
  | @reveal Γ pending publicName sourceName who ty source tail hsource plan ih =>
      by_cases heq : name = sourceName
      · subst name
        exact Or.inl (by simp [RevealedSources])
      · have hremaining : name ∈ pending.erase sourceName ∨ name ∈ CommittedVars tail := by
          rcases hname with hpending | hcommitted
          · exact Or.inl (Finset.mem_erase.mpr ⟨heq, hpending⟩)
          · exact Or.inr hcommitted
        rcases ih hremaining with hliteral | hdisposition
        · exact Or.inl (List.mem_cons_of_mem _ hliteral)
        · exact Or.inr hdisposition
  | @opening Γ pending copyName publicName who copyTy guard tail spec hsource hfresh plan ih =>
      by_cases hcopy : name = copyName
      · subst name
        exact Or.inl (by simp [RevealedSources])
      · by_cases hresolved : name = spec.source
        · subst name
          exact Or.inr (Finset.mem_insert_self _ _)
        · have hremaining : name ∈ pending.erase spec.source ∨ name ∈ CommittedVars tail := by
            rcases hname with hpending | hcommitted
            · exact Or.inl (Finset.mem_erase.mpr ⟨hresolved, hpending⟩)
            · exact Or.inr (by
                simpa only [CommittedVars, List.mem_cons, hcopy, false_or] using hcommitted)
          rcases ih hremaining with hliteral | hdisposition
          · exact Or.inl (List.mem_cons_of_mem _ hliteral)
          · exact Or.inr (Finset.mem_insert_of_mem hdisposition)

/-- Every new commitment is accounted for, including the auxiliary copy at an
optional resolution site. -/
theorem committed_resolved {Γ : VCtx P L} {pending : Finset VarId}
    {prog : VegasCore P L Γ} (plan : CommitmentAccounting pending prog)
    (name : VarId) (hname : name ∈ CommittedVars prog) :
    name ∈ RevealedSources prog ∨ name ∈ plan.dispositions :=
  plan.pending_or_committed_resolved name (Or.inr hname)

/-- Every initial pending binding is accounted for by the same rule as a new
commitment; inputs do not receive an implicit abandonment convention. -/
theorem pending_resolved {Γ : VCtx P L} {pending : Finset VarId}
    {prog : VegasCore P L Γ} (plan : CommitmentAccounting pending prog)
    (name : VarId) (hname : name ∈ pending) :
    name ∈ RevealedSources prog ∨ name ∈ plan.dispositions :=
  plan.pending_or_committed_resolved name (Or.inl hname)

/-- A closed return cannot leave even one named binding unresolved. -/
theorem pending_empty_at_return {Γ : VCtx P L} {pending : Finset VarId}
    {payoffs : List (P × L.Expr (erasePubVCtx Γ) L.int)}
    (plan : CommitmentAccounting pending (.ret payoffs)) : pending = ∅ := by
  cases plan with
  | ret hempty => exact hempty

end CommitmentAccounting

end Vegas

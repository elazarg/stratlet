/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import Vegas.Core.Accounting
import Vegas.Core.Strategy

/-! # Syntactic locations of accounted conditional openings -/

namespace Vegas

variable {P : Type} [DecidableEq P] {L : IExpr}

/-- One `opening` constructor occurring in an accounting derivation. -/
inductive CommitmentAccounting.OpeningSite :
    {Γ : VCtx P L} → {pending : Finset VarId} → {prog : VegasCore P L Γ} →
      (plan : CommitmentAccounting pending prog) → Type where
  | here {Γ : VCtx P L} {pending : Finset VarId} {copyName publicName : VarId}
      {who : P} {copyTy : L.Ty}
      {guard : L.Expr ((copyName, copyTy) :: eraseVCtx (viewVCtx who Γ)) L.bool}
      {tail : VegasCore P L
        ((publicName, .pub copyTy) :: (copyName, .sealed who copyTy) :: Γ)}
      (spec : ConditionalOpening guard) (unresolved : spec.source ∈ pending)
      (fresh : copyName ∉ pending)
      (accounted : CommitmentAccounting (pending.erase spec.source) tail) :
      OpeningSite (.opening spec unresolved fresh accounted)
  | sample {Γ : VCtx P L} {pending : Finset VarId} {x : VarId} {ty : L.Ty}
      {dist : L.DistExpr (erasePubVCtx Γ) ty}
      {tail : VegasCore P L ((x, .pub ty) :: Γ)}
      {accounted : CommitmentAccounting pending tail}
      (site : OpeningSite accounted) :
      OpeningSite (.sample (x := x) (b := ty) (dist := dist) accounted)
  | commit {Γ : VCtx P L} {pending : Finset VarId} {x : VarId} {who : P}
      {ty : L.Ty}
      {guard : L.Expr ((x, ty) :: eraseVCtx (viewVCtx who Γ)) L.bool}
      {tail : VegasCore P L ((x, .sealed who ty) :: Γ)} {fresh : x ∉ pending}
      {accounted : CommitmentAccounting (insert x pending) tail}
      (site : OpeningSite accounted) :
      OpeningSite (.commit (x := x) (who := who) (b := ty) (guard := guard) fresh accounted)
  | reveal {Γ : VCtx P L} {pending : Finset VarId} {y x : VarId} {who : P}
      {ty : L.Ty} {source : VHasVar Γ x (.sealed who ty)}
      {tail : VegasCore P L ((y, .pub ty) :: Γ)} {unresolved : x ∈ pending}
      {accounted : CommitmentAccounting (pending.erase x) tail}
      (site : OpeningSite accounted) :
      OpeningSite (.reveal (y := y) (who := who) (b := ty) (source := source)
        unresolved accounted)
  | openingTail {Γ : VCtx P L} {pending : Finset VarId}
      {copyName publicName : VarId} {who : P} {copyTy : L.Ty}
      {guard : L.Expr ((copyName, copyTy) :: eraseVCtx (viewVCtx who Γ)) L.bool}
      {tail : VegasCore P L
        ((publicName, .pub copyTy) :: (copyName, .sealed who copyTy) :: Γ)}
      {spec : ConditionalOpening guard} {unresolved : spec.source ∈ pending}
      {fresh : copyName ∉ pending}
      {accounted : CommitmentAccounting (pending.erase spec.source) tail}
      (site : OpeningSite accounted) :
      OpeningSite (.opening spec unresolved fresh accounted)

/-- Typed source metadata retained at an accounted opening occurrence. -/
structure CommitmentAccounting.OpeningData {Γ : VCtx P L}
    (prog : VegasCore P L Γ) where
  context : VCtx P L
  copyName : VarId
  publicName : VarId
  owner : P
  copyTy : L.Ty
  guard : L.Expr ((copyName, copyTy) :: eraseVCtx (viewVCtx owner context)) L.bool
  tail : VegasCore P L
    ((publicName, .pub copyTy) :: (copyName, .sealed owner copyTy) :: context)
  specification : ConditionalOpening guard
  decision : SourceDecisionSite owner prog context copyName copyTy guard

namespace CommitmentAccounting.OpeningSite

/-- Recover the typed opening certificate and its structural source decision. -/
def data {Γ : VCtx P L} {pending : Finset VarId} {prog : VegasCore P L Γ}
    {plan : CommitmentAccounting pending prog} :
    OpeningSite plan → CommitmentAccounting.OpeningData prog
  | .here (Γ := Γ) (copyName := copyName) (publicName := publicName)
      (who := who) (copyTy := copyTy) (guard := guard) (tail := tail)
      spec _ _ _ =>
      { context := Γ
        copyName := copyName
        publicName := publicName
        owner := who
        copyTy := copyTy
        guard := guard
        tail := tail
        specification := spec
        decision := .here guard (.reveal publicName who copyName .here tail) }
  | .sample site =>
      let found := site.data
      { found with decision := .sample found.decision }
  | .commit site =>
      let found := site.data
      { found with decision := .commit found.decision }
  | .reveal site =>
      let found := site.data
      { found with decision := .reveal found.decision }
  | .openingTail site =>
      let found := site.data
      { found with decision := .commit (.reveal found.decision) }

/-- Freshness evidence specialized to the adjacent commit/reveal at the site. -/
theorem siteFresh {Γ : VCtx P L} {pending : Finset VarId} {prog : VegasCore P L Γ}
    {plan : CommitmentAccounting pending prog} (site : OpeningSite plan)
    (fresh : FreshBindings prog) :
    let found := site.data
    FreshBindings (.commit found.copyName found.owner found.guard
      (.reveal found.publicName found.owner found.copyName .here found.tail)) := by
  induction site with
  | here => exact fresh
  | sample site ih => exact ih fresh.2
  | commit site ih => exact ih fresh.2
  | reveal site ih => exact ih fresh.2
  | openingTail site ih => exact ih fresh.2.2

end CommitmentAccounting.OpeningSite

end Vegas

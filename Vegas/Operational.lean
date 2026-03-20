import Vegas.Core

/-!
# Operational profiles

This file contains the evaluator-facing strategy objects used by the raw Vegas
semantics.

These are not the game-theoretic notions of pure/behavioral/mixed strategy.
They are operational kernels indexed by commit sites and consumed directly by
the denotational and trace semantics.
-/

namespace Vegas

/-- Generic commit kernels: given the full erased environment, produce a
    distribution over action values. Visibility is a side condition on the
    kernel's dependency set, not a type constraint. -/
abbrev CommitKernel (Player : Type) [DecidableEq Player] (L : IExpr)
    (_who : Player) (Γ : VCtx Player L) (b : L.Ty) : Type :=
  Env L.Val (eraseVCtx Γ) → FDist (L.Val b)

/-- Operational profiles for Vegas commit nodes. These are evaluator inputs,
not the paper-facing strategic objects. -/
structure OperationalProfile (Player : Type) [DecidableEq Player]
    (L : IExpr) where
  commit : {Γ : VCtx Player L} → {b : L.Ty} → (who : Player) →
    (x : VarId) →
    (R : L.Expr ((x, b) :: eraseVCtx Γ) L.bool) →
    CommitKernel Player L who Γ b

/-- Partial operational profiles with optional commit kernels. -/
structure PartialOperationalProfile (Player : Type) [DecidableEq Player]
    (L : IExpr) where
  commit? : {Γ : VCtx Player L} → {b : L.Ty} → (who : Player) →
    (x : VarId) →
    (R : L.Expr ((x, b) :: eraseVCtx Γ) L.bool) →
    Option (CommitKernel Player L who Γ b)

def PartialOperationalProfile.toOperationalProfile
    {Player : Type} [DecidableEq Player] {L : IExpr}
    (π : PartialOperationalProfile Player L)
    (fallback : OperationalProfile Player L) :
    OperationalProfile Player L where
  commit := fun {Γ} {b} who x R env =>
    match π.commit? (Γ := Γ) (b := b) who x R with
    | some k => k env
    | none => fallback.commit who x R env

/-- Backward-compatible alias for evaluator-facing profiles. Prefer
`OperationalProfile` in new code. -/
abbrev Profile := OperationalProfile

/-- Backward-compatible alias for partial evaluator-facing profiles. Prefer
`PartialOperationalProfile` in new code. -/
abbrev PProfile := PartialOperationalProfile

/-- Backward-compatible alias for partial-profile completion. Prefer
`PartialOperationalProfile.toOperationalProfile`. -/
def PProfile.toProfile {Player : Type} [DecidableEq Player] {L : IExpr}
    (π : PProfile Player L) (fallback : Profile Player L) :
    Profile Player L :=
  π.toOperationalProfile fallback

end Vegas

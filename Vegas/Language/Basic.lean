/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import Vegas.Core.Obligations

noncomputable section

/-!
# Surface Vegas language

`VegasLang` is a small surface syntax over the concrete `ExprSimple` language
that lowers to the generic `VegasCore simpleExpr`. This concrete
specialization is deliberate: nullable yields rely on `BaseTy.option`,
`CommitPayloadTy`, and `DefaultVal`.

The surface keeps the existing core actions, adds administrative `let`
bindings, and lowers guarded public `yield`s through internal `option T`
commitments. User-written commit payloads are restricted by `CommitPayloadTy`,
so a surface program cannot explicitly commit an optional value.

This is an elaborated typed layer: yield nodes already name the internal
sealed commitment and the public reveal. A thinner parser-level language can
instead generate the sealed commitment name during elaboration/lowering,
translate ordinary reads to the public reveal, translate owner-private reads to
the sealed commitment, and emit `VegasCore` directly.

Quit handlers are deliberately not part of this syntax yet.
-/

namespace Vegas

variable {P : Type} [DecidableEq P]

/-- Surface Vegas syntax. This specializes the protocol core to
`simpleExpr`, adds administrative `let` bindings, and nullable yield sugar. -/
inductive VegasLang (P : Type) [DecidableEq P] :
    VCtx P simpleExpr → Type where
  /-- Terminate with public payoff expressions. -/
  | ret {Γ : VCtx P simpleExpr}
      (payoffs : List (P × Expr (erasePubVCtx Γ) .int)) :
      VegasLang P Γ
  /-- Deterministic public binding. This is erased by lowering; it is not a
  core protocol event. -/
  | letExpr {Γ : VCtx P simpleExpr} (x : VarId) {b : BaseTy}
      (e : Expr (erasePubVCtx Γ) b)
      (k : VegasLang P ((x, .pub b) :: Γ)) :
      VegasLang P Γ
  /-- Public sample. -/
  | sample {Γ : VCtx P simpleExpr} (x : VarId) {b : BaseTy}
      (D : DistExpr (erasePubVCtx Γ) b)
      (k : VegasLang P ((x, .pub b) :: Γ)) :
      VegasLang P Γ
  /-- Strategic sealed commitment whose guard is accepted as-is. Surface
  payloads cannot be explicitly nullable. -/
  | commit {Γ : VCtx P simpleExpr} (x : VarId) (who : P) {b : BaseTy}
      [CommitPayloadTy b]
      (R : Expr ((x, b) :: eraseVCtx (viewVCtx who Γ)) .bool)
      (k : VegasLang P ((x, .sealed who b) :: Γ)) :
      VegasLang P Γ
  /-- Public strategic move, lowered as a nullable sealed commitment followed
  by a public reveal of the optional value. The two names are separate because
  `VegasCore` contexts are SSA-style: the revealed public alias must be fresh
  rather than reusing the sealed commitment name. A source elaborator may
  generate the sealed name and keep it invisible to ordinary source reads. -/
  | yield {Γ : VCtx P simpleExpr} (secret pubVar : VarId) (who : P)
      {b : BaseTy} [CommitPayloadTy b] [DefaultVal b]
      (R : Expr ((secret, b) :: eraseVCtx (viewVCtx who Γ)) .bool)
      (k : VegasLang P
        ((pubVar, .pub (BaseTy.option b)) ::
          (secret, .sealed who (BaseTy.option b)) :: Γ)) :
      VegasLang P Γ
  /-- Reveal a sealed commitment as a fresh public alias. -/
  | reveal {Γ : VCtx P simpleExpr} (y : VarId) (who : P) (x : VarId)
      {b : BaseTy}
      (hx : VHasVar Γ x (.sealed who b))
      (k : VegasLang P ((y, .pub b) :: Γ)) :
      VegasLang P Γ
end Vegas

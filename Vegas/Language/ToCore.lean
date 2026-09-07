/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import Vegas.Language.Basic

/-!
# Surface-to-core lowering

This module implements the intrinsically typed `VegasLang -> VegasCore`
translation. Constructing its result establishes core typing. It does not
construct `WFProgram`, prove the additional well-formedness obligations used by
that admission boundary, or establish operational or strategic preservation.
-/

namespace Vegas

variable {P : Type} [DecidableEq P]

namespace VegasLang

/-- Typed substitution environment used while lowering surface syntax. Public
administrative bindings translate to expressions, while sealed variables must
remain stored core bindings so that later reveals can open them. -/
structure LowerEnv (P : Type) [DecidableEq P]
    (Γ Δ : VCtx P simpleExpr) where
  pub : {x : VarId} → {b : BaseTy} →
    HasVar (erasePubVCtx Γ) x b → Expr (erasePubVCtx Δ) b
  view : (who : P) → {x : VarId} → {b : BaseTy} →
    HasVar (eraseVCtx (viewVCtx who Γ)) x b →
      Expr (eraseVCtx (viewVCtx who Δ)) b
  sealed : {x : VarId} → {who : P} → {b : BaseTy} →
    VHasVar Γ x (.sealed who b) → VHasVar Δ x (.sealed who b)

namespace LowerEnv

def id (Γ : VCtx P simpleExpr) : LowerEnv P Γ Γ where
  pub := fun {x} {_} h => .var x h
  view := fun _ {x} {_} h => .var x h
  sealed := fun h => h

def expr {Γ Δ : VCtx P simpleExpr} (env : LowerEnv P Γ Δ)
    {b : BaseTy} (e : Expr (erasePubVCtx Γ) b) : Expr (erasePubVCtx Δ) b :=
  e.substVars env.pub

def dist {Γ Δ : VCtx P simpleExpr} (env : LowerEnv P Γ Δ)
    {b : BaseTy} (D : DistExpr (erasePubVCtx Γ) b) : DistExpr (erasePubVCtx Δ) b :=
  D.substVars env.pub

def actionExpr {Γ Δ : VCtx P simpleExpr} (env : LowerEnv P Γ Δ)
    (who : P) {x : VarId} {a b : BaseTy}
    (e : Expr ((x, a) :: eraseVCtx (viewVCtx who Γ)) b) :
    Expr ((x, a) :: eraseVCtx (viewVCtx who Δ)) b :=
  e.substVars (by
    intro y ty h
    cases h with
    | here => exact .var x .here
    | there htail => exact (env.view who htail).weaken)

def consPublic {Γ Δ : VCtx P simpleExpr} (env : LowerEnv P Γ Δ)
    (x : VarId) {b : BaseTy} :
    LowerEnv P ((x, .pub b) :: Γ) ((x, .pub b) :: Δ) where
  pub := by
    intro y ty h
    cases h with
    | here => exact .var x .here
    | there htail => exact (env.pub htail).weaken
  view := by
    intro who y ty h
    simp only [viewVCtx, canSee, Visibility.canSee_pub, if_true, eraseVCtx_cons] at h ⊢
    cases h with
    | here => exact .var x .here
    | there htail => exact (env.view who htail).weaken
  sealed := by
    intro y who ty h
    cases h with
    | there htail => exact .there (env.sealed htail)

def consHidden {Γ Δ : VCtx P simpleExpr} (env : LowerEnv P Γ Δ)
    (x : VarId) (owner : P) {b : BaseTy} :
    LowerEnv P ((x, .sealed owner b) :: Γ) ((x, .sealed owner b) :: Δ) where
  pub := fun h => env.pub h
  view := by
    intro who y ty h
    by_cases hsee : canSee who (BindTy.sealed (L := simpleExpr) owner b)
    · simp only [viewVCtx, hsee, if_true, eraseVCtx_cons] at h ⊢
      cases h with
      | here => exact .var x .here
      | there htail => exact (env.view who htail).weaken
    · simp only [viewVCtx, hsee] at h ⊢
      exact env.view who h
  sealed := by
    intro y who ty h
    cases h with
    | here => exact .here
    | there htail => exact .there (env.sealed htail)

def aliasPublic {Γ Δ : VCtx P simpleExpr} (env : LowerEnv P Γ Δ)
    (x : VarId) {b : BaseTy} (e : Expr (erasePubVCtx Δ) b) :
    LowerEnv P ((x, .pub b) :: Γ) Δ where
  pub := by
    intro y ty h
    cases h with
    | here => exact e
    | there htail => exact env.pub htail
  view := by
    intro who y ty h
    simp only [viewVCtx, canSee, Visibility.canSee_pub, if_true, eraseVCtx_cons] at h
    cases h with
    | here => exact e.publicToView who
    | there htail => exact env.view who htail
  sealed := by
    intro y who ty h
    cases h with
    | there htail => exact env.sealed htail

end LowerEnv

/-- Lower surface syntax to core syntax, substituting administrative lets. -/
def lowerWith : {Γ Δ : VCtx P simpleExpr} → LowerEnv P Γ Δ →
    VegasLang P Γ → VegasCore P simpleExpr Δ
  | _, _, env, .ret payoffs =>
      .ret (payoffs.map fun payoff => (payoff.1, env.expr payoff.2))
  | _, _, env, .letExpr x e k => lowerWith (env.aliasPublic x (env.expr e)) k
  | _, _, env, .sample x D k =>
      .sample x (env.dist D) (lowerWith (env.consPublic x) k)
  | _, _, env, @VegasLang.commit _ _ _ x who _ _ R k =>
      .commit x who (env.actionExpr who R) (lowerWith (env.consHidden x who) k)
  | _, _, env, @VegasLang.yield _ _ _ secret pubVar who b _ _ R k =>
      .commit secret who (b := BaseTy.option b)
        (Expr.nullableCommitGuard (env.actionExpr who R))
        (.reveal pubVar who secret .here
          (lowerWith ((env.consHidden secret who).consPublic pubVar) k))
  | _, _, env, .reveal y who x hx k =>
      .reveal y who x (env.sealed hx) (lowerWith (env.consPublic y) k)

/-- Lower surface Vegas to an intrinsically typed core term. -/
def lower {Γ : VCtx P simpleExpr} (p : VegasLang P Γ) :
    VegasCore P simpleExpr Γ :=
  lowerWith (LowerEnv.id Γ) p

end VegasLang

end Vegas

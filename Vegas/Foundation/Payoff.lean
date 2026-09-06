/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import Vegas.Foundation.Env

/-!
# Integer payouts and payoff/guard evaluation

`Payout`, payoff construction (`payoffAt`, `mkPayout`), and the program-facing
`evalPayoffs` / `evalGuard` evaluators.
-/

namespace Vegas

/-! ## Payouts and payoff/guard evaluation -/

/-- A finitely-supported integer payout vector, not the game's outcome type
or a compulsory utility model. An economic outcome may additionally describe
allocation, disclosure, or other settlement data; utilities value that outcome.

The `Finsupp` representation is load-bearing: it aggregates per-player
contributions by summing on matching keys. Players absent from a `.support`
default to payoff `0`, which matches the "only named players are paid"
semantics. -/
abbrev Payout (Player : Type) [DecidableEq Player] := Player →₀ Int

/-- Sum of payoff contributions for player `p` across a payoff list.
Duplicates of `p` in the list are added. Defined recursively so that
`evalPayoffs` can be built without invoking `Finsupp.single` or
`Finsupp.(+)`, which are both `noncomputable` in Mathlib. -/
def payoffAt {Player : Type} [DecidableEq Player]
    (p : Player) : List (Player × Int) → Int
  | [] => 0
  | (q, v) :: rest => (if q = p then v else 0) + payoffAt p rest

/-- Build a `Payout` directly from a list of `(player, payoff)` entries,
summing duplicates. Sidesteps `Finsupp.single` and `Finsupp.(+)` (which
are noncomputable in Mathlib despite `[DecidableEq]` being available) by
constructing the underlying `Finsupp` record in one shot. -/
def mkPayout {Player : Type} [DecidableEq Player]
    (entries : List (Player × Int)) : Payout Player where
  support := (entries.map Prod.fst).toFinset.filter (fun p => payoffAt p entries ≠ 0)
  toFun p := payoffAt p entries
  mem_support_toFun p := by
    rw [Finset.mem_filter]
    refine ⟨fun h => h.2, fun hne => ⟨?_, hne⟩⟩
    simp only [List.mem_toFinset, List.mem_map]
    induction entries with
    | nil => simp [payoffAt] at hne
    | cons hd tl ih =>
        simp only [payoffAt] at hne
        by_cases h : hd.1 = p
        · exact ⟨hd, by simp, h⟩
        · have htail : payoffAt p tl ≠ 0 := by
            intro hzero
            apply hne
            simp [h, hzero]
          rcases ih htail with ⟨entry, hmem, heq⟩
          exact ⟨entry, List.mem_cons_of_mem hd hmem, heq⟩

/-- Evaluate a list of per-player payoff expressions into a payout vector. -/
def evalPayoffs {Player : Type} [DecidableEq Player]
    {L : IExpr} {Γ : VCtx Player L}
    (payoffs : List (Player × L.Expr (erasePubVCtx Γ) L.int))
    (env : VEnv L Γ) : Payout Player :=
  mkPayout (payoffs.map
    (fun pe => (pe.1, L.toInt (L.eval pe.2 (VEnv.erasePubEnv env)))))

/-- Evaluate a commit guard against a proposed action and an erased current
environment. Core commit guards are instantiated with the acting player's view
context, so visibility is enforced by the type of `R`. -/
def evalGuard {Player : Type} [DecidableEq Player] {L : IExpr}
    {Γ : VCtx Player L} {b : L.Ty}
    {x : VarId}
    (R : L.Expr ((x, b) :: eraseVCtx Γ) L.bool)
    (a : L.Val b) (env : Env L.Val (eraseVCtx Γ)) : Bool :=
  L.toBool (L.eval R (Env.cons a env))


end Vegas

/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import VegasTests.DisclosurePayoff

/-! # A finite sealed-offer escrow

The seller binds a price (one or two) before a fair public value signal (one
or two), then opens or quits. The buyer accepts or rejects after disclosure.
Quitting costs the seller one; rejection has zero utility. A sale transfers
the price to the seller and gives the buyer value minus price. These are net
utilities, not a proof of ledger balances, escrow funding, or asset delivery.
Initial and buyer quitting are not decisions of this finite model.
-/

noncomputable section

namespace VegasTests.SealedOffer

open Vegas EventGraph GameTheory GameTheory.Protocol GameTheory.Math.Probability
open OptionalDisclosure

def highPrice : Expr PayoffContext .bool :=
  .getD (.var 5 (.there .here)) (.constBool false)

def sellerPayoff : Expr PayoffContext .int :=
  .ite (.isNone (.var 5 (.there .here))) (.constInt (-1))
    (.ite (.var 7 .here) (.ite highPrice (.constInt 2) (.constInt 1)) (.constInt 0))

def buyerPayoff : Expr PayoffContext .int :=
  .ite (.isNone (.var 5 (.there .here))) (.constInt 0)
    (.ite (.var 7 .here)
      (.ite highPrice
        (.ite (.var 3 (.there (.there .here))) (.constInt 0) (.constInt (-1)))
        (.ite (.var 3 (.there (.there .here))) (.constInt 1) (.constInt 0)))
      (.constInt 0))

def payouts : Payouts := [(0, sellerPayoff), (1, buyerPayoff)]

abbrev machine := programWithPayoffs payouts

def amount (high : Bool) : ℝ := if high then 2 else 1

def utility (data : RunData) (who : TestPlayer) : ℝ :=
  match data.opening with
  | none => if who = 0 then -1 else 0
  | some high => if data.response then
      if who = 0 then amount high else amount data.signal - amount high
    else 0

theorem utility_eq (data : RunData) (who : TestPlayer) :
    finiteUtility payouts data who = utility data who := by
  rcases data with ⟨secret, signal, opening, response⟩
  cases opening with
  | none =>
    fin_cases who
    · change ((-1 : Int) : ℝ) = -1
      norm_num
    · change ((0 : Int) : ℝ) = 0
      norm_num
  | some high =>
    cases high <;> cases signal <;> cases response <;> fin_cases who <;>
      norm_num [finiteUtility, payouts, sellerPayoff, buyerPayoff, highPrice,
        utility, amount, evalPayoffs, evalExpr, mkOutcome, payoffAt,
        terminalEnv, responseEnv, openingEnv, VEnv.erasePubEnv, VEnv.get,
        VEnv.cons, Env.get, Env.cons]

def game : UtilityGame TestPlayer where
  form := finiteForm
  utility := utility

def pairProfile (seller : SenderStrategy) (buyer : ResponderStrategy) : Profile finiteForm.sig
  | 0 => seller
  | 1 => buyer

def accept (signal : Bool) : Option Bool → Bool
  | none => false
  | some high => !high || signal

def honestBuyer : ResponderStrategy := fun signal opening =>
  FinDist.pure (accept signal opening)

def honestSeller : SenderStrategy where
  binding := FinDist.pure false
  complete := fun _ _ => FinDist.pure true

def honestProfile : Profile finiteForm.sig := pairProfile honestSeller honestBuyer

theorem buyer_nonnegative (secret signal : Bool) (opening : Option Bool) :
    0 ≤ utility ⟨secret, signal, opening, accept signal opening⟩ 1 := by
  cases opening with
  | none => norm_num [utility]
  | some high => cases high <;> cases signal <;> norm_num [utility, accept, amount]

theorem buyer_optimal (secret signal : Bool) (opening : Option Bool) (response : Bool) :
    utility ⟨secret, signal, opening, response⟩ 1 ≤
      utility ⟨secret, signal, opening, accept signal opening⟩ 1 := by
  cases opening with
  | none => norm_num [utility]
  | some high => cases high <;> cases signal <;> cases response <;>
      norm_num [utility, accept, amount]

def revenueCap (secret signal : Bool) : ℝ :=
  if secret then if signal then 2 else 0 else 1

theorem seller_completion_bound (secret signal complete : Bool) :
    utility ⟨secret, signal, if complete then some secret else none,
      accept signal (if complete then some secret else none)⟩ 0 ≤
        revenueCap secret signal := by
  cases secret <;> cases signal <;> cases complete <;>
    norm_num [utility, accept, amount, revenueCap]

theorem coin_expect (observable : Bool → ℝ) :
    fairCoin.denote.expect observable = (observable false + observable true) / 2 := by
  rw [FinDist.expect_eq_sum]
  simp [RationalLaw.prob_denote, fairCoin, Fin.sum_univ_two]
  ring

theorem expected_revenue_cap (secret : Bool) :
    fairCoin.denote.expect (revenueCap secret) = 1 := by
  rw [coin_expect]
  cases secret <;> norm_num [revenueCap]

end VegasTests.SealedOffer

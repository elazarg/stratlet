/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import Interaction.IdealCommitments
import Interaction.MessagePool
import GameTheory.Math.Probability.FinDist

/-! # Commitment traffic in a native pending-message experiment

The sender privately registers one bit with an explicit ideal functionality,
then submits an ordinary observable handle. Cleartext and value-bearing
opening messages use the same pool. The opponent can inspect pending traffic;
the entire wire pool, not merely its delivered view, is independent of the
registered bit before opening. The bounded experiment exposes only the wire
pool to continuation policies. Its opening handler checks the owner on
messages submitted through the native sender capability.

These are bounded protocol tests, not a source-compiler theorem or a
cryptographic realization. There is no release barrier, forced opening,
settlement guarantee, or assertion that traffic existence is hidden.
-/

namespace InteractionTests.Commitment

open Interaction GameTheory.Math.Probability

inductive Wire where
  | plain (value : Bool)
  | commit (handle : CommitmentHandle Bool Unit)
  | opening (handle : CommitmentHandle Bool Unit) (claimed : Bool)
  | malformed
  deriving DecidableEq

abbrev Pool := MessagePool Bool Wire

structure Setup where
  service : IdealCommitments Bool Unit Bool
  pool : Pool

/-- Private ideal registration and public handle transmission are separate
operations. The wire message contains no private registration argument. -/
def honestSetup (value : Bool) : Setup where
  service := (IdealCommitments.empty.sealValue false () value).state
  pool := ((MessagePool.empty Bool Wire).submit false (.commit (false, ()))).2

def expose (setup : Setup) : Setup :=
  { setup with pool := (setup.pool.deliver true (false, 0)).state }

def plainPool (value : Bool) : Pool :=
  let pool := ((MessagePool.empty Bool Wire).submit false (.plain value)).2
  (pool.deliver true (false, 0)).state

/-- Submission and delivery precede ledger inclusion. -/
theorem cleartext_pending_ledger (value : Bool) :
    (plainPool value).ledger = [] := rfl

/-- A legal cleartext submission reveals the bit while it is still pending. -/
theorem cleartext_views_distinct :
    (plainPool false).observe true ≠ (plainPool true).observe true := by
  intro heq
  have hvalues := congrArg
    (fun view : MessagePool.View Bool Wire => view.inbox.map Message.payload) heq
  change [Wire.plain false] = [Wire.plain true] at hvalues
  have hpayload := (List.cons.inj hvalues).1
  cases hpayload

/-- Even a scheduler inspecting the complete wire pool sees the same state.
The private ideal table is deliberately not part of this observation. -/
theorem sealed_pool_eq (first second : Bool) :
    (honestSetup first).pool = (honestSetup second).pool := rfl

theorem delivered_commitment_view_eq (first second : Bool) :
    (expose (honestSetup first)).pool.observe true =
      (expose (honestSetup second)).pool.observe true := rfl

/-- Any subsequent computation that receives only the wire pool has the same
law. This excludes access to the private table or an authorized opening; it
does not establish security for an unrestricted ideal-service context. -/
theorem wire_continuation_law {Outcome : Type}
    (continueWith : Pool → FinDist Outcome) (first second : Bool) :
    continueWith (expose (honestSetup first)).pool =
      continueWith (expose (honestSetup second)).pool := rfl

/-- Giving a context unrestricted access to the ideal verifier would disclose
the bit with one query. The wire-only context boundary is essential. -/
theorem unrestricted_verifier_reveals (value : Bool) :
    (honestSetup value).service.verify ⟨(false, ()), true⟩ = value := by
  cases value <;> rfl

/-- Check that an opening handle belongs to the message's declared sender.
Provenance requires a message produced through the native submission
capability; the public `Message` constructor alone does not authenticate it. -/
def openingAccepted (setup : Setup) (message : Message Bool Wire) : Bool :=
  match message.payload with
  | .opening handle claimed =>
      (message.sender == handle.1) && setup.service.verify ⟨handle, claimed⟩
  | _ => false

/-- In this one-slot experiment the opponent cannot probe the sender's bit,
even by submitting arbitrary malformed, copied, or guessed opening bodies. -/
theorem opponent_attempt_rejected (value : Bool) (wire : Wire) (serial : Nat) :
    openingAccepted (honestSetup value) ⟨(true, serial), wire⟩ = false := by
  cases wire with
  | plain value => rfl
  | commit handle => rfl
  | malformed => rfl
  | opening handle claimed =>
      rcases handle with ⟨owner, slot⟩
      cases owner <;> cases slot <;> rfl

/-- The same rejection applies to the actual message produced by an opponent
submission, not only to a manually constructed envelope. -/
theorem opponent_submission_rejected (value : Bool) (wire : Wire) :
    let submitted := (honestSetup value).pool.submit true wire
    (submitted.2.lookup submitted.1).any (openingAccepted (honestSetup value)) = false := by
  change openingAccepted (honestSetup value) ⟨(true, 0), wire⟩ = false
  exact opponent_attempt_rejected value wire 0

/-- Opening transmission carries the claimed value before its inclusion. -/
def submitOpening (value : Bool) : Setup :=
  let setup := expose (honestSetup value)
  { setup with pool :=
      (setup.pool.submit false (.opening (false, ()) value)).2 }

def deliverOpening (value : Bool) : Setup :=
  let setup := submitOpening value
  { setup with pool := (setup.pool.deliver true (false, 1)).state }

theorem opening_still_pending (value : Bool) :
    (deliverOpening value).pool.ledger = [] := rfl

/-- Hiding cannot extend past observation of the value-bearing opening,
even if the scheduler has not included any message yet. -/
theorem opening_views_distinct :
    (deliverOpening false).pool.observe true ≠
      (deliverOpening true).pool.observe true := by
  intro heq
  have hvalues := congrArg
    (fun view : MessagePool.View Bool Wire => view.inbox.map Message.payload) heq
  change [Wire.commit (false, ()), Wire.opening (false, ()) false] =
    [Wire.commit (false, ()), Wire.opening (false, ()) true] at hvalues
  have hpayload := (List.cons.inj (List.cons.inj hvalues).2).1
  cases hpayload

/-- Inclusion uses the native pool operation; application validation uses its
returned preexisting message, with no fresh sender consultation. -/
def includeOpening (value : Bool) : Bool × Pool :=
  let setup := deliverOpening value
  let committed := setup.pool.includePending (false, 0)
  let result := committed.state.includePending (false, 1)
  (result.message.any (openingAccepted setup), result.state)

theorem honest_opening_accepted (value : Bool) :
    (includeOpening value).1 = true := by
  cases value <;> rfl

theorem honest_opening_published (value : Bool) :
    (includeOpening value).2.ledger =
      [⟨(false, 0), Wire.commit (false, ())⟩,
        ⟨(false, 1), Wire.opening (false, ()) value⟩] := rfl

theorem published_ledger_shared (value : Bool) :
    ((includeOpening value).2.observe false).ledger =
      ((includeOpening value).2.observe true).ledger := rfl

/-- An alternative claimed value is rejected even with the correct owner. -/
theorem accepted_claim_eq (value claimed : Bool) (serial : Nat)
    (haccepted : openingAccepted (honestSetup value)
      ⟨(false, serial), .opening (false, ()) claimed⟩ = true) :
    claimed = value := by
  cases value <;> cases claimed <;> first | rfl | cases haccepted

end InteractionTests.Commitment

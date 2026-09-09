/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import Interaction.ChoiceController
import Interaction.MessageRouting

/-! # Endpoint-separated choice encodings

Canonical decoding determines which wire values belong to one encoding.
Distinct endpoint tags additionally make the accepted domains disjoint, even
when both endpoints use the same underlying request representation.
-/

namespace Interaction.MessageApplication.ChoiceEncoding

universe uValue uWire uEndpoint

variable {Value : Type uValue} {Wire : Type uWire} {Endpoint : Type uEndpoint}

/-- Compose two canonical partial encodings. -/
def trans {NextWire : Type*} (first : ChoiceEncoding Value Wire)
    (second : ChoiceEncoding Wire NextWire) : ChoiceEncoding Value NextWire where
  encode value := second.encode (first.encode value)
  decode wire := (second.decode wire).bind first.decode
  decode_encode value := by simp [second.decode_encode, first.decode_encode]
  decode_sound wire value hdecode := by
    cases hmiddle : second.decode wire with
    | none => simp [hmiddle] at hdecode
    | some middle =>
        have hfirst : first.decode middle = some value := by simpa [hmiddle] using hdecode
        have hwire := second.decode_sound wire middle hmiddle
        rw [first.decode_sound middle value hfirst] at hwire
        exact hwire

/-- Change the abstract choice representation by a certified equivalence,
without changing the wire domain. -/
def reindex {OtherValue : Type*} (encoding : ChoiceEncoding Value Wire)
    (representation : OtherValue ≃ Value) : ChoiceEncoding OtherValue Wire where
  encode value := encoding.encode (representation value)
  decode wire := (encoding.decode wire).map representation.symm
  decode_encode value := by simp [encoding.decode_encode]
  decode_sound wire value hdecode := by
    cases hdecoded : encoding.decode wire with
    | none => simp [hdecoded] at hdecode
    | some decoded =>
        have hvalue : representation.symm decoded = value := by simpa [hdecoded] using hdecode
        subst value
        simpa using encoding.decode_sound wire decoded hdecoded

/-- Add a checked routing tag to the wire representation of a choice. -/
def atEndpoint [DecidableEq Endpoint] (encoding : ChoiceEncoding Value Wire)
    (endpoint : Endpoint) : ChoiceEncoding Value (Endpoint × Wire) where
  encode value := (endpoint, encoding.encode value)
  decode packet := if packet.1 = endpoint then encoding.decode packet.2 else none
  decode_encode value := by simp [encoding.decode_encode]
  decode_sound packet value hdecode := by
    rcases packet with ⟨actual, wire⟩
    by_cases hendpoint : actual = endpoint
    · subst actual
      simp only [if_true] at hdecode
      exact congrArg (fun payload => (endpoint, payload)) (encoding.decode_sound _ _ hdecode)
    · simp [hendpoint] at hdecode

@[simp]
theorem atEndpoint_decode_other [DecidableEq Endpoint] (encoding : ChoiceEncoding Value Wire)
    (endpoint other : Endpoint) (wire : Wire) (hne : other ≠ endpoint) :
    (encoding.atEndpoint endpoint).decode (other, wire) = none := by
  simp [atEndpoint, hne]

/-- No wire packet is accepted by two differently tagged endpoints. The
underlying encodings and even their value types may differ. -/
theorem atEndpoint_disjoint [DecidableEq Endpoint] {OtherValue : Type*}
    (left : ChoiceEncoding Value Wire) (right : ChoiceEncoding OtherValue Wire)
    (first second : Endpoint) (hne : first ≠ second) (packet : Endpoint × Wire)
    (value : Value) (other : OtherValue)
    (hfirst : (left.atEndpoint first).decode packet = some value)
    (hsecond : (right.atEndpoint second).decode packet = some other) : False := by
  have hleft := congrArg Prod.fst ((left.atEndpoint first).decode_sound _ _ hfirst)
  have hright := congrArg Prod.fst ((right.atEndpoint second).decode_sound _ _ hsecond)
  exact hne (hleft.symm.trans hright)

end Interaction.MessageApplication.ChoiceEncoding

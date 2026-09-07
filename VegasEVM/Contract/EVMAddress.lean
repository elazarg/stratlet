/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import VegasEVM.Contract.EVMWord
import VegasEVM.Contract.Wire

/-!
# EVM caller addresses

`CALLER` produces a 160-bit account address. Classical deployment backends
therefore carry a lossless codec from their abstract address type to this
concrete representation; calldata player identifiers remain separate 256-bit
words.
-/

namespace Vegas.Machine.Contract.EVM

/-- Native EVM account address returned by `CALLER`. -/
abbrev AddressWord := BitVec 160

/-- Lossless representation of an abstract deployment address as an EVM
account address. -/
abbrev AddressCodec (Address : Type) := WireCodec Address AddressWord

/-- Evidence that an abstract address type represents every raw EVM caller.
Losslessness alone only covers callers in the encoder's image; whole-runtime
refinement requires this additional total representation. -/
structure TotalAddressRepresentation {Address : Type}
    (codec : AddressCodec Address) where
  abstract : AddressWord → Address
  encode_abstract : ∀ caller, codec.encode (abstract caller) = caller

namespace TotalAddressRepresentation

/-- Native EVM addresses represent themselves totally. -/
def identity :
    TotalAddressRepresentation (WireCodec.identity AddressWord) where
  abstract := id
  encode_abstract := by intro; rfl

end TotalAddressRepresentation

/-- A finite address family fits in the EVM's 160-bit address space. -/
def IndexFitsAddress (count : Nat) : Prop := count ≤ 2 ^ 160

/-- Encode a bounded address index. -/
def encodeAddressIndex {count : Nat} (index : Fin count) : AddressWord :=
  BitVec.ofNat 160 index

/-- Decode an EVM address only when it names an index below `count`. -/
def decodeAddressIndex (count : Nat) (address : AddressWord) :
    Option (Fin count) :=
  if h : address.toNat < count then
    some ⟨address.toNat, h⟩
  else
    none

@[simp] theorem decodeAddressIndex_encodeAddressIndex
    {count : Nat} (fits : IndexFitsAddress count) (index : Fin count) :
    decodeAddressIndex count (encodeAddressIndex index) = some index := by
  have haddress : (index : Nat) < 2 ^ 160 :=
    lt_of_lt_of_le index.isLt fits
  have hnat : (encodeAddressIndex index).toNat = index := by
    rw [encodeAddressIndex, BitVec.toNat_ofNat, Nat.mod_eq_of_lt haddress]
  simp [decodeAddressIndex, hnat, index.isLt]

/-- Lossless 160-bit address codec for a bounded finite index family. -/
def indexAddressCodec (count : Nat) (fits : IndexFitsAddress count) :
    AddressCodec (Fin count) where
  encode := encodeAddressIndex
  decode := decodeAddressIndex count
  decode_encode := decodeAddressIndex_encodeAddressIndex fits

end Vegas.Machine.Contract.EVM

/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import VegasEVM.Contract.Entropy

/-!
# Uniform finite entropy realization

This module specializes the general entropy-realization boundary to one fixed,
nonempty uniform finite seed space. That is the certificate expected from a
denominator-clearing sampler or a bounded on-chain entropy protocol.

Neither GameTheory nor this module currently constructs such a sampler from an
arbitrary `RationalLaw`. GameTheory supplies `FinDist.uniformFin` and the
pushforward laws used in the certificate, but a constructive exact partition
of a uniform seed space remains compiler work.
-/

noncomputable section

namespace Vegas.Machine.Contract.Blockchain

open GameTheory.Math.Probability

/-- A positive finite cardinality, packaged so its `NeZero` instance follows
the value through dependent entropy types. -/
structure PositiveCardinality where
  count : Nat
  positive : 0 < count

namespace PositiveCardinality

instance (cardinality : PositiveCardinality) : NeZero cardinality.count where
  out := Nat.ne_of_gt cardinality.positive

/-- Canonical uniform law on the packaged finite seed space. -/
def uniform (cardinality : PositiveCardinality) :
    FinDist (Fin cardinality.count) :=
  FinDist.uniformFin cardinality.count

end PositiveCardinality

/-- Exact realization of a stochastic contract from one fixed uniform finite
seed space. Public call data may affect how the seed is interpreted, but not
its assumed uniform law or cardinality. -/
structure UniformEntropyRealization
    {Address Message State Action : Type}
    (contract : StochasticContract Address Message State Action) where
  seedCardinality : PositiveCardinality
  receive :
    ChainView → CallContext Address → State → Message →
      Fin seedCardinality.count → DeterministicResult State Action
  law :
    ∀ chain context state message,
      seedCardinality.uniform.map
          (receive chain context state message) =
        (contract.receive chain context state message).outcomeLaw

namespace UniformEntropyRealization

variable {Address Message State Action : Type}
variable {contract : StochasticContract Address Message State Action}

/-- Forget the uniformity specialization and recover the general entropy
realization certificate. -/
def toEntropyRealization (realization : UniformEntropyRealization contract) :
    EntropyRealization contract where
  Entropy := Fin realization.seedCardinality.count
  entropyLaw := fun _chain _context _state _message =>
    realization.seedCardinality.uniform
  receive := realization.receive
  law := realization.law

/-- Cardinality condition under which modulo reduction of a truly uniform
256-bit word can be unbiased. This condition alone does not establish that a
real chain supplies an unpredictable uniform word. -/
def EVMWordCompatible (realization : UniformEntropyRealization contract) :
    Prop :=
  realization.seedCardinality.count ∣ 2 ^ 256

end UniformEntropyRealization

end Vegas.Machine.Contract.Blockchain

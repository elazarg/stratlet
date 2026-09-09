/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import Vegas.Compile.ApplicationImage

/-! # Supported chance invocations

Successful chance invocations expose the actual fixed-kernel draw to proofs.
Rejected invocations leave state unchanged. The public native action still
supplies only an address, not the value appearing in the support witness.
-/

namespace Vegas.ApplicationImage

open EventGraph GameTheory.Math.Probability

variable {P : Type} {L : IExpr}

/-- Every supported chance invocation either leaves state unchanged or draws
from the exact retained distribution at a ready instruction. -/
theorem sample_support (image : ApplicationImage P L) (state : State P L)
    (address : Nat) (next : State P L)
    (hnext : next ∈ (image.sample state address).support) :
    next = state ∨
      ∃ (code : SampleCode L) (reads : ReadEnv L code.dist.reads)
          (value : L.Val code.dist.ty),
        image.lookup address = some (.sample code) ∧
        state.memory.done code.node = false ∧ code.requires.all state.memory.done = true ∧
        ReadEnv.ofStoreExec? state.memory.store code.dist.reads = some reads ∧
        value ∈ (code.dist.eval reads).support ∧ next = state.sample code value := by
  cases hlookup : image.lookup address with
  | none =>
      exact Or.inl (by simpa only [sample, hlookup, FinDist.mem_support_pure] using hnext)
  | some instruction =>
      cases instruction with
      | publicChoice code | bind code | conditional code =>
          exact Or.inl (by simpa only [sample, hlookup, FinDist.mem_support_pure] using hnext)
      | sample code =>
          simp only [sample, hlookup] at hnext
          split at hnext
          · rename_i hready
            have hready' : state.memory.done code.node = false ∧
                code.requires.all state.memory.done = true := by
              simpa only [Bool.and_eq_true, Bool.not_eq_true'] using hready
            cases hreads : ReadEnv.ofStoreExec? state.memory.store code.dist.reads with
            | none =>
                exact Or.inl (by simpa only [hreads, FinDist.mem_support_pure] using hnext)
            | some reads =>
                simp only [hreads, FinDist.support_map, Set.mem_image] at hnext
                obtain ⟨value, hvalue, rfl⟩ := hnext
                exact Or.inr ⟨code, reads, value, rfl, hready'.1, hready'.2,
                  hreads, hvalue, rfl⟩
          · exact Or.inl (FinDist.mem_support_pure.mp hnext)

end Vegas.ApplicationImage

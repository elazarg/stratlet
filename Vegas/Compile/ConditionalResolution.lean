/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import Interaction.ConditionalPublication
import Vegas.Core.ConditionalOpening

/-! # Source meaning of a successful conditional publication

This module connects the small runtime classifier to an existing conditional
commit/reveal certificate.  The application-level `canOpen` predicate remains
an explicit correspondence premise: neither the ideal commitment service nor
the accounting certificate implements the source guard by itself.
-/

namespace Vegas

open Interaction

variable {P : Type} [DecidableEq P] {L : IExpr}
variable {Γ : VCtx P L}
variable {copyName : VarId} {who : P} {copyTy : L.Ty}
variable {guard : L.Expr ((copyName, copyTy) :: eraseVCtx (viewVCtx who Γ)) L.bool}

namespace ConditionalOpening

/-- Every legal certified source choice has an accepted canonical runtime
request, provided the application predicate admits the certified stored value
whenever its corresponding source opening is legal.  This is a local
implementation obligation, not a scheduling or liveness theorem. -/
theorem legal_choice_resolves
    (opening : ConditionalOpening guard)
    (site : Interaction.ConditionalPublication P)
    (howner : site.owner = who)
    (now : Nat)
    (service : IdealCommitments P Nat (L.Val opening.secretTy))
    (accepted : Option (CommitmentHandle P Nat)) (done : Nat → Bool)
    (canOpen : L.Val opening.secretTy → Bool)
    (env : VEnv L Γ)
    (hstored : service.lookup (site.owner, site.sourceSlot) =
      some (env.get opening.binding))
    (hready : site.ready accepted done = true)
    (hcanOpen :
      evalGuard guard
          (opening.encoding.symm (some (env.get opening.binding)))
          ((env.toView who).eraseEnv) = true →
        canOpen (env.get opening.binding) = true)
    (serial : Nat) (chosen : L.Val copyTy)
    (hlegal : evalGuard guard chosen ((env.toView who).eraseEnv) = true) :
    site.resolve? now service accepted done canOpen
        ⟨(who, serial), site.requestPayload (opening.encoding chosen)⟩ =
      some (opening.encoding chosen) := by
  subst who
  rcases opening.sound env chosen hlegal with hdecline | hopen
  · rw [hdecline]
    exact (site.resolve_requestPayload now service accepted done canOpen hready serial none).mpr
      trivial
  · rw [hopen]
    apply (site.resolve_requestPayload now service accepted done canOpen hready serial
      (some (env.get opening.binding))).mpr
    constructor
    · simp [IdealCommitments.verify, hstored]
    · apply hcanOpen
      have hchosen : chosen =
          opening.encoding.symm (some (env.get opening.binding)) := by
        apply opening.encoding.injective
        simpa only [Equiv.apply_symm_apply] using hopen
      rw [← hchosen]
      exact hlegal

/-- Every accepted runtime result encodes a legal source choice.  Opening
legality is needed only at the value already stored in the certified binding;
commitment verification rejects every other claimed value first. -/
theorem runtime_resolution_legal
    (opening : ConditionalOpening guard)
    (site : Interaction.ConditionalPublication P)
    (howner : site.owner = who)
    (now : Nat)
    (service : IdealCommitments P Nat (L.Val opening.secretTy))
    (accepted : Option (CommitmentHandle P Nat)) (done : Nat → Bool)
    (canOpen : L.Val opening.secretTy → Bool)
    (message : Message P
      (Interaction.ConditionalPublication.Payload P (L.Val opening.secretTy)))
    (env : VEnv L Γ)
    (hstored : service.lookup (site.owner, site.sourceSlot) =
      some (env.get opening.binding))
    (hcanOpen : canOpen (env.get opening.binding) = true →
      evalGuard guard (opening.encoding.symm (some (env.get opening.binding)))
        ((env.toView who).eraseEnv) = true)
    (result : Option (L.Val opening.secretTy))
    (hresolve : site.resolve? now service accepted done canOpen message =
      some result) :
    (result = none ∨ result = some (env.get opening.binding)) ∧
      evalGuard guard (opening.encoding.symm result)
        ((env.toView who).eraseEnv) = true := by
  subst who
  have hresult := site.resolve_value now service accepted done canOpen message
    (env.get opening.binding) hstored result hresolve
  refine ⟨hresult, ?_⟩
  rcases hresult with rfl | rfl
  · exact opening.decline_legal env
  · apply hcanOpen
    exact site.resolve_some_canOpen now service accepted done canOpen message
      (env.get opening.binding) hresolve

/-- An accepted runtime resolution follows the existing adjacent source
commit/reveal steps and retains the original certified binding. -/
theorem runtime_resolution_steps
    (opening : ConditionalOpening guard)
    (site : Interaction.ConditionalPublication P)
    (howner : site.owner = who)
    (now : Nat)
    (service : IdealCommitments P Nat (L.Val opening.secretTy))
    (accepted : Option (CommitmentHandle P Nat)) (done : Nat → Bool)
    (canOpen : L.Val opening.secretTy → Bool)
    (message : Message P
      (Interaction.ConditionalPublication.Payload P (L.Val opening.secretTy)))
    (env : VEnv L Γ)
    (hstored : service.lookup (site.owner, site.sourceSlot) =
      some (env.get opening.binding))
    (hcanOpen : canOpen (env.get opening.binding) = true →
      evalGuard guard (opening.encoding.symm (some (env.get opening.binding)))
        ((env.toView who).eraseEnv) = true)
    (result : Option (L.Val opening.secretTy))
    (hresolve : site.resolve? now service accepted done canOpen message = some result)
    (publicName : VarId)
    (tail : VegasCore P L
      ((publicName, .pub copyTy) :: (copyName, .sealed who copyTy) :: Γ)) :
    (result = none ∨ result = some (env.get opening.binding)) ∧
      SmallStep.Star
        ⟨Γ, env, .commit copyName who guard
          (.reveal publicName who copyName .here tail)⟩
        ⟨(publicName, .pub copyTy) :: (copyName, .sealed who copyTy) :: Γ,
          (env.cons (opening.encoding.symm result)).cons
            (opening.encoding.symm result), tail⟩ ∧
      ((env.cons (opening.encoding.symm result)).cons
          (opening.encoding.symm result)).get
        (VHasVar.there (VHasVar.there opening.binding) :
          VHasVar
            ((publicName, .pub copyTy) :: (copyName, .sealed who copyTy) :: Γ)
            opening.source (.sealed who opening.secretTy)) =
        env.get opening.binding := by
  subst who
  have hlegal := opening.runtime_resolution_legal site rfl now service accepted done
    canOpen message env hstored hcanOpen result hresolve
  refine ⟨hlegal.1, ?_, ?_⟩
  · apply opening.commit_reveal_steps
    exact hlegal.2
  · exact opening.original_binding_after_commit_reveal publicName env
      (opening.encoding.symm result)

end ConditionalOpening

end Vegas

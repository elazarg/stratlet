/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import Vegas.Compile.ConditionalImage
import Vegas.Compile.ConditionalExecution
import Vegas.Compile.ApplicationImageBindings
import Vegas.Compile.ApplicationImageRefinement
import Vegas.Compile.ApplicationGuardSoundness

/-! # Source refinement for generated conditional instructions

These lemmas connect the dynamically typed application image to the accounted
source opening at one generated endpoint.  They are local transaction laws:
they assume the represented public checkpoint and do not assert scheduling or
whole-program strategy correspondence.
-/

noncomputable section

namespace Vegas.CommitmentAccounting.OpeningSite

open Vegas.EventGraph Vegas.ToEventGraph Interaction

variable {P : Type} [DecidableEq P] {L : IExpr}
variable {Γ : VCtx P L} {pending : Finset VarId} {prog : VegasCore P L Γ}
variable {plan : CommitmentAccounting pending prog}

/-- An actually resolved generated conditional endpoint advances both the
public application memory and a represented reachable graph checkpoint.  The
source environment is needed only to inhabit hidden context for the certified
decline branch.  A successful opening instead uses the frozen value's weak
consistency with the represented graph store and the generated public
validator; no full source-store agreement is assumed. -/
theorem conditional_resolution_refines
    (site : plan.OpeningSite) (fresh : FreshBindings prog)
    (build : BuildState P L Γ) (sourceSlot deadline : Nat)
    (initial : VEnv L Γ) (legal : Legal prog)
    (native : ApplicationImage.State P L)
    (cfg : Config (compileCore prog fresh build).graph)
    (hrep : native.memory.Represents cfg)
    (hreachable : Reachable (compileCore prog fresh build).graph cfg)
    (heligible : site.PubliclyValidatable fresh build)
    (hbinding : ∀ value,
      (native.frozen (site.sourceField fresh build)).bind
          (fun typed => typed.as? site.data.specification.secretTy) = some value →
        Store.getAs cfg.store (site.sourceField fresh build)
          site.data.specification.secretTy = some value)
    (message : Message P
      (ConditionalPublication.Payload P (L.Val site.data.specification.secretTy)))
    (result : Option (L.Val site.data.specification.secretTy))
    (hresolve : (site.code fresh build sourceSlot deadline).endpoint.resolve?
      native.memory.clock (native.verify (site.code fresh build sourceSlot deadline))
      (native.memory.accepted (site.sourceField fresh build)) native.memory.done
      ((site.code fresh build sourceSlot deadline).canOpen native.memory.store)
      message = some result) :
    (native.publishConditional (site.code fresh build sourceSlot deadline) result).memory.Represents
        (site.completePublication fresh build cfg result) ∧
      Reachable (compileCore prog fresh build).graph
        (site.completePublication fresh build cfg result) := by
  let G := (compileCore prog fresh build).graph
  let choice := site.choiceNode fresh build
  let publication := site.publicationNode fresh build
  let guard := site.compiledGuard fresh build
  let code := site.code fresh build sourceSlot deadline
  have hruntimeReady := code.endpoint.resolve_success_inversion native.memory.clock
    (native.verify code) (native.memory.accepted code.sourceField) native.memory.done
    (code.canOpen native.memory.store) message result hresolve
  have hreadiness := G.conditionalPublication_ready cfg site.data.owner sourceSlot
    choice publication deadline (native.memory.accepted code.sourceField)
    native.memory.done hrep.completed hruntimeReady
  have hrow : G.nodes[choice]? = some
      ((decisionSiteState site.data.decision fresh build).commitEvent
        site.data.owner site.data.guard) := site.choiceNode_row fresh build
  have hcoherent : StoreCoherent G cfg :=
    reachable_storeCoherent (compileCore prog fresh build).graphWF hreachable
  have hnodeWF := (compileCore prog fresh build).graphWF choice
    ((decisionSiteState site.data.decision fresh build).commitEvent
      site.data.owner site.data.guard) hrow
  have hguardSem :
      ((decisionSiteState site.data.decision fresh build).commitEvent
        site.data.owner site.data.guard).sem = .commit site.data.owner guard := rfl
  have hexReads := hcoherent.readEnvOfReady
    (compileCore prog fresh build).graphWF hrow hreadiness.1
    (refs := guard.choiceReads)
    (by
      intro ref href
      rw [hguardSem]
      exact Finset.mem_image.mpr ⟨ref, href, rfl⟩)
    (by
      intro ref href
      unfold Graph.nodeWFAt at hnodeWF
      rw [hguardSem] at hnodeWF
      rcases hnodeWF.2.2.2 ref href with ⟨spec, hfield, hty, _⟩
      exact ⟨spec, hfield, hty⟩)
  rcases hexReads with ⟨reads, hreads⟩
  have hguard : guard.eval (site.data.specification.encoding.symm result) reads = true := by
    cases result with
    | none => exact site.decline_guard_eval fresh build initial legal reads
    | some claimed =>
        have hverified := code.endpoint.resolve_some_verified native.memory.clock
          (native.verify code) (native.memory.accepted code.sourceField) native.memory.done
          (code.canOpen native.memory.store) message claimed hresolve
        have hfrozen : (native.frozen (site.sourceField fresh build)).bind
            (fun typed => typed.as? site.data.specification.secretTy) = some claimed := by
          simpa [ApplicationImage.State.verify, code,
            CommitmentAccounting.OpeningSite.code] using hverified
        have hclaimed := hbinding claimed hfrozen
        have hcanOpen := code.endpoint.resolve_some_canOpen native.memory.clock
          (native.verify code) (native.memory.accepted code.sourceField) native.memory.done
          (code.canOpen native.memory.store) message claimed hresolve
        change site.canOpen fresh build native.memory.store claimed = true at hcanOpen
        rw [site.canOpen_eq_eval fresh build cfg.store native.memory.store reads hreads
          heligible hrep.publicFields claimed hclaimed] at hcanOpen
        exact hcanOpen
  let written : TypedValue L :=
    ⟨site.data.copyTy, site.data.specification.encoding.symm result⟩
  have hstep : CommitStep G cfg site.data.owner ⟨choice, written⟩ := by
    have hguardType : guard.ty = site.data.copyTy := by rfl
    exact
      { row := (decisionSiteState site.data.decision fresh build).commitEvent
          site.data.owner site.data.guard
        guard := guard
        row_get := hrow
        sem_eq := rfl
        ready := hreadiness.1
        value := site.data.specification.encoding.symm result
        value_ok := by simp [TypedValue.as?, hguardType, written]
        env := reads
        env_ok := hreads
        guard_ok := hguard }
  have hpublication : Ready G (cfg.completeNode choice written) publication :=
    publication_ready_after_choice cfg choice publication written
      (site.publicationNode_ne_choiceNode fresh build)
      hreadiness.2.1 hreadiness.2.2
  have hnext := reachable_choice_publication cfg site.data.owner choice publication written
    (site.publicationNode_type fresh build).symm hstep
    (site.publicationNode_sem fresh build) hpublication hreachable
  constructor
  · exact native.publishConditional_represents cfg hrep code choice publication
      rfl rfl rfl rfl result
  · exact hnext

/-- A legal source choice produces a canonical dynamically typed packet that
the generated application image accepts. The frozen premise is deliberately
typed: it states that binding admission captured the represented source
binding. -/
theorem canonical_request_accepted
    (image : ApplicationImage P L) (site : plan.OpeningSite)
    (fresh : FreshBindings prog)
    (state : BuildState P L Γ) (sourceSlot deadline : Nat)
    (address : Nat)
    (hcode : image.lookup address =
      some (.conditional (site.code fresh state sourceSlot deadline)))
    (native : ApplicationImage.State P L) (representedStore : Store L)
    (env : VEnv L site.data.context)
    (heligible : site.PubliclyValidatable fresh state)
    (hagrees : (decisionSiteState site.data.decision fresh state).Agrees
      representedStore env)
    (hpublicStore : ∀ ref, (compileCore prog fresh state).graph.fieldRefPublic ref →
      Store.getAs native.memory.store ref.field ref.ty =
        Store.getAs representedStore ref.field ref.ty)
    (hready : (site.code fresh state sourceSlot deadline).endpoint.ready
      (native.memory.accepted (site.sourceField fresh state)) native.memory.done = true)
    (chosen : L.Val site.data.copyTy)
    (hlegal : evalGuard site.data.guard chosen
      ((env.toView site.data.owner).eraseEnv) = true)
    (hfrozen : native.frozen (site.sourceField fresh state) =
      some ⟨site.data.specification.secretTy,
        env.get site.data.specification.binding⟩)
    (serial : Nat) :
    let code := site.code fresh state sourceSlot deadline
    image.handle native
        ⟨(code.endpoint.owner, serial), .conditional address
          (code.requestPayload (site.data.specification.encoding chosen))⟩ =
      some (native.publishConditional code
        (site.data.specification.encoding chosen)) := by
  let code := site.code fresh state sourceSlot deadline
  have hresolve : code.endpoint.resolve? native.memory.clock (native.verify code)
      (native.memory.accepted code.sourceField) native.memory.done
      (code.canOpen native.memory.store)
      ⟨(code.endpoint.owner, serial),
        code.endpoint.requestPayload (site.data.specification.encoding chosen)⟩ =
        some (site.data.specification.encoding chosen) := by
    apply (code.endpoint.resolve_requestPayload native.memory.clock (native.verify code)
      (native.memory.accepted code.sourceField) native.memory.done
      (code.canOpen native.memory.store) hready serial
      (site.data.specification.encoding chosen)).2
    cases hresult : site.data.specification.encoding chosen with
    | none => trivial
    | some value =>
        have hvalue := site.data.specification.successful_value_eq_binding
          env chosen value hlegal hresult
        constructor
        · simp [ApplicationImage.State.verify, code,
            CommitmentAccounting.OpeningSite.code, hfrozen, hvalue, TypedValue.as?]
        · change site.canOpen fresh state native.memory.store value = true
          rw [site.canOpen_source fresh state representedStore native.memory.store env
            heligible hagrees hpublicStore value hvalue]
          have hchosen : site.data.specification.encoding.symm (some value) = chosen := by
            rw [← hresult]
            exact site.data.specification.encoding.symm_apply_apply chosen
          rw [hchosen]
          exact hlegal
  have hhandle := image.handle_conditional native address code hcode
    (code.endpoint.owner, serial) (code.requestPayload
      (site.data.specification.encoding chosen))
    (code.endpoint.requestPayload (site.data.specification.encoding chosen))
    (code.decode_requestPayload (site.data.specification.encoding chosen))
  rw [hresolve, Option.map_some] at hhandle
  exact hhandle

/-- Inclusion of any dynamically decoded packet at a generated conditional
instruction has both the exact native message-runtime effects and the source
commit/reveal trace.  The weak snapshot premise also covers declines and
expiry from a missing or ill-typed frozen value: it constrains only a value
that the verifier can actually recover. -/
theorem include_conditional_source_steps
    (image : ApplicationImage P L)
    (site : plan.OpeningSite) (fresh : FreshBindings prog)
    (build : BuildState P L Γ) (sourceSlot deadline address : Nat)
    (hcode : image.lookup address =
      some (.conditional (site.code fresh build sourceSlot deadline)))
    (state : image.application.State) (representedStore : Store L)
    (env : VEnv L site.data.context)
    (heligible : site.PubliclyValidatable fresh build)
    (hagrees : (decisionSiteState site.data.decision fresh build).Agrees
      representedStore env)
    (hpublicStore : ∀ ref, (compileCore prog fresh build).graph.fieldRefPublic ref →
      Store.getAs state.application.memory.store ref.field ref.ty =
        Store.getAs representedStore ref.field ref.ty)
    (hbinding : ∀ value,
      (state.application.frozen (site.sourceField fresh build)).bind
          (fun typed => typed.as? site.data.specification.secretTy) = some value →
        value = env.get site.data.specification.binding)
    (id : MessageId P)
    (payload : ConditionalPublication.Payload P (TypedValue L))
    (decoded : ConditionalPublication.Payload P
      (L.Val site.data.specification.secretTy))
    (hdecode : (site.code fresh build sourceSlot deadline).decode payload = some decoded)
    (result : Option (L.Val site.data.specification.secretTy))
    (hlookup : state.pool.lookup id = some ⟨id, .conditional address payload⟩)
    (hresolve : (site.code fresh build sourceSlot deadline).endpoint.resolve?
      state.application.memory.clock
      (state.application.verify (site.code fresh build sourceSlot deadline))
      (state.application.memory.accepted (site.sourceField fresh build))
      state.application.memory.done
      ((site.code fresh build sourceSlot deadline).canOpen
        state.application.memory.store)
      ⟨id, decoded⟩ = some result) :
    let code := site.code fresh build sourceSlot deadline
    let next := image.application.includePending state id
    next.application = state.application.publishConditional code result ∧
      next.receipts = state.receipts ++ [(id, true)] ∧
      next.pool.ledger = state.pool.ledger ++ [⟨id, .conditional address payload⟩] ∧
      next.pool.sent = state.pool.sent ∧
      next.pool.inbox = state.pool.inbox ∧
      SmallStep.Star
        ⟨site.data.context, env, .commit site.data.copyName site.data.owner
          site.data.guard (.reveal site.data.publicName site.data.owner
            site.data.copyName .here site.data.tail)⟩
        ⟨(site.data.publicName, .pub site.data.copyTy) ::
            (site.data.copyName, .sealed site.data.owner site.data.copyTy) ::
            site.data.context,
          (env.cons (site.data.specification.encoding.symm result)).cons
            (site.data.specification.encoding.symm result),
          site.data.tail⟩ := by
  let code := site.code fresh build sourceSlot deadline
  have hincluded := image.include_conditional state address code hcode id payload decoded
    hdecode result hlookup hresolve
  have hsource := site.code_resolution_source_legal fresh build sourceSlot deadline
    state.application representedStore env heligible hagrees hpublicStore hbinding
    ⟨id, decoded⟩ result hresolve
  refine ⟨hincluded.1, hincluded.2.1, hincluded.2.2.1,
    hincluded.2.2.2.1, hincluded.2.2.2.2, ?_⟩
  exact site.data.specification.commit_reveal_steps site.data.publicName site.data.tail env
    (site.data.specification.encoding.symm result) hsource.2

end Vegas.CommitmentAccounting.OpeningSite

/-- info: 'Vegas.CommitmentAccounting.OpeningSite.canonical_request_accepted'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.CommitmentAccounting.OpeningSite.canonical_request_accepted

/-- info: 'Vegas.CommitmentAccounting.OpeningSite.conditional_resolution_refines'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.CommitmentAccounting.OpeningSite.conditional_resolution_refines

/-- info: 'Vegas.CommitmentAccounting.OpeningSite.include_conditional_source_steps'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.CommitmentAccounting.OpeningSite.include_conditional_source_steps

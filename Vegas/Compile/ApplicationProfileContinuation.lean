/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import Vegas.Compile.ApplicationPolicy
import Vegas.Compile.ApplicationImageStateRefinement

/-! # Structural continuations of lifted source profiles

A continuation retains the original plan and source profile while traversing
their existing sample, commitment, and publication constructors. It is a
proof-side relation: runtime policies still receive only their own histories
and observations. Completed public flags make the original lifted policy agree
with the corresponding suffix policy in the same ambient application.
-/

noncomputable section

namespace Vegas.ApplicationPlan

open EventGraph ToEventGraph Interaction Interaction.MessageApplication

variable {P : Type} [DecidableEq P] {L : IExpr}

/-- A source-profile continuation obtained by traversing actual constructors
of an application plan. No alternative profile can be substituted at a suffix. -/
inductive ProfileContinuation
    {rootContext : VCtx P L} {rootPending : Finset VarId}
    {rootProg : VegasCore P L rootContext}
    {rootAccounted : CommitmentAccounting rootPending rootProg}
    {rootFresh : FreshBindings rootProg} {rootState : BuildState P L rootContext}
    (root : ApplicationPlan rootAccounted rootFresh rootState)
    (rootProfile : SourceBehavioralProfile rootProg) :
    {Γ : VCtx P L} → {pending : Finset VarId} → {prog : VegasCore P L Γ} →
      {accounted : CommitmentAccounting pending prog} → {fresh : FreshBindings prog} →
      {state : BuildState P L Γ} → ApplicationPlan accounted fresh state →
        SourceBehavioralProfile prog → Prop where
  | refl : ProfileContinuation root rootProfile root rootProfile
  | sample {Γ : VCtx P L} {pending : Finset VarId} {name : VarId} {ty : L.Ty}
      {dist : L.DistExpr (erasePubVCtx Γ) ty}
      {tail : VegasCore P L ((name, .pub ty) :: Γ)}
      {accounted : CommitmentAccounting pending tail}
      {fresh : FreshBindings (.sample name dist tail)} {state : BuildState P L Γ}
      {next : ApplicationPlan accounted fresh.2 (state.addSampleEvent name dist fresh.1).1}
      {profile : SourceBehavioralProfile (.sample name dist tail)}
      (previous : ProfileContinuation root rootProfile
        (.sample (fresh := fresh) next) profile) :
      ProfileContinuation root rootProfile next profile.afterSample
  | binding {Γ : VCtx P L} {pending : Finset VarId} {name : VarId} {who : P}
      {ty : L.Ty} {guard : L.Expr ((name, ty) :: eraseVCtx (viewVCtx who Γ)) L.bool}
      {tail : VegasCore P L ((name, .sealed who ty) :: Γ)}
      {newName : name ∉ pending} {accounted : CommitmentAccounting (insert name pending) tail}
      {fresh : FreshBindings (.commit name who guard tail)} {state : BuildState P L Γ}
      {unrestricted : UnrestrictedBinding guard}
      {next : ApplicationPlan accounted fresh.2 (state.addCommitEvent name who guard fresh.1).1}
      {profile : SourceBehavioralProfile (.commit name who guard tail)}
      (previous : ProfileContinuation root rootProfile
        (.binding (newName := newName) (fresh := fresh) unrestricted next) profile) :
      ProfileContinuation root rootProfile next profile.afterCommit
  | publicChoice {Γ : VCtx P L} {pending : Finset VarId} {name publicName : VarId}
      {who : P} {ty : L.Ty}
      {guard : L.Expr ((name, ty) :: eraseVCtx (viewVCtx who Γ)) L.bool}
      {tail : VegasCore P L ((publicName, .pub ty) :: (name, .sealed who ty) :: Γ)}
      {newName : name ∉ pending} {unresolved : name ∈ insert name pending}
      {accounted : CommitmentAccounting ((insert name pending).erase name) tail}
      {fresh : FreshBindings (.commit name who guard (.reveal publicName who name .here tail))}
      {state : BuildState P L Γ}
      {publicGuard : (PublicChoiceSite.atHead name publicName who guard tail).PubliclyValidatable
        fresh state}
      {next : ApplicationPlan accounted fresh.2.2
        (((state.addCommitEvent name who guard fresh.1).1).addRevealEvent
          publicName who .here fresh.2.1).1}
      {profile : SourceBehavioralProfile
        (.commit name who guard (.reveal publicName who name .here tail))}
      (previous : ProfileContinuation root rootProfile
        (.publicChoice (newName := newName) (unresolved := unresolved)
          (fresh := fresh) publicGuard next) profile) :
      ProfileContinuation root rootProfile next profile.afterCommit.afterReveal
  | conditional {Γ : VCtx P L} {pending : Finset VarId} {name publicName : VarId}
      {who : P} {ty : L.Ty}
      {guard : L.Expr ((name, ty) :: eraseVCtx (viewVCtx who Γ)) L.bool}
      {tail : VegasCore P L ((publicName, .pub ty) :: (name, .sealed who ty) :: Γ)}
      {spec : ConditionalOpening guard} {unresolved : spec.source ∈ pending}
      {newName : name ∉ pending}
      {accounted : CommitmentAccounting (pending.erase spec.source) tail}
      {fresh : FreshBindings (.commit name who guard (.reveal publicName who name .here tail))}
      {state : BuildState P L Γ}
      {publicGuard : ConditionalPublicationSite.PubliclyValidatable
        (ConditionalPublicationSite.atHead name publicName who guard tail spec) fresh state}
      {next : ApplicationPlan accounted fresh.2.2
        (((state.addCommitEvent name who guard fresh.1).1).addRevealEvent
          publicName who .here fresh.2.1).1}
      {profile : SourceBehavioralProfile
        (.commit name who guard (.reveal publicName who name .here tail))}
      (previous : ProfileContinuation root rootProfile
        (.conditional (unresolved := unresolved) (newName := newName)
          (fresh := fresh) publicGuard next) profile) :
      ProfileContinuation root rootProfile next profile.afterCommit.afterReveal
  | conditionalCopy {Γ : VCtx P L} {pending : Finset VarId} {name publicName : VarId}
      {who : P} {ty : L.Ty}
      {guard : L.Expr ((name, ty) :: eraseVCtx (viewVCtx who Γ)) L.bool}
      {tail : VegasCore P L ((publicName, .pub ty) :: (name, .sealed who ty) :: Γ)}
      {spec : ConditionalOpening guard}
      {newName : name ∉ pending} {unresolved : name ∈ insert name pending}
      {accounted : CommitmentAccounting ((insert name pending).erase name) tail}
      {fresh : FreshBindings (.commit name who guard (.reveal publicName who name .here tail))}
      {state : BuildState P L Γ}
      {publicGuard : ConditionalPublicationSite.PubliclyValidatable
        (ConditionalPublicationSite.atHead name publicName who guard tail spec) fresh state}
      {next : ApplicationPlan accounted fresh.2.2
        (((state.addCommitEvent name who guard fresh.1).1).addRevealEvent
          publicName who .here fresh.2.1).1}
      {profile : SourceBehavioralProfile
        (.commit name who guard (.reveal publicName who name .here tail))}
      (previous : ProfileContinuation root rootProfile
        (.conditionalCopy (newName := newName) (unresolved := unresolved) (fresh := fresh)
          spec publicGuard next) profile) :
      ProfileContinuation root rootProfile next profile.afterCommit.afterReveal

namespace ProfileContinuation

variable {rootContext Γ : VCtx P L} {rootPending pending : Finset VarId}
variable {rootProg : VegasCore P L rootContext} {prog : VegasCore P L Γ}
variable {rootAccounted : CommitmentAccounting rootPending rootProg}
variable {accounted : CommitmentAccounting pending prog}
variable {rootFresh : FreshBindings rootProg} {fresh : FreshBindings prog}
variable {rootState : BuildState P L rootContext} {state : BuildState P L Γ}
variable {root : ApplicationPlan rootAccounted rootFresh rootState}
variable {plan : ApplicationPlan accounted fresh state}
variable {rootProfile : SourceBehavioralProfile rootProg}
variable {profile : SourceBehavioralProfile prog}

/-- The emitted suffix occurs literally in the original image. This supplies
the static instruction offset for an environment's own invocation history. -/
theorem instructions_suffix
    (continuation : ProfileContinuation root rootProfile plan profile)
    (deadlineOf : Nat → Nat) :
    ∃ before, root.instructions deadlineOf = before ++ plan.instructions deadlineOf := by
  induction continuation with
  | refl => exact ⟨[], rfl⟩
  | sample _ ih | binding _ ih | publicChoice _ ih | conditional _ ih
  | conditionalCopy _ ih =>
      obtain ⟨before, hbefore⟩ := ih
      simp only [instructions] at hbefore
      exact ⟨_, hbefore.trans (List.append_assoc _ [_] _).symm⟩

/-- A structural continuation compiles to the same final graph and readout. -/
theorem compile_eq (continuation : ProfileContinuation root rootProfile plan profile) :
    compileCore rootProg rootFresh rootState = compileCore prog fresh state := by
  induction continuation with
  | refl => rfl
  | sample _ ih | binding _ ih | publicChoice _ ih | conditional _ ih
  | conditionalCopy _ ih => exact ih

/-- If every compiler node before the suffix is complete, dispatch through
the original source profile equals dispatch through its actual continuation.
The history and complete native observation are unchanged. -/
theorem liftProfileIn_eq
    (continuation : ProfileContinuation root rootProfile plan profile)
    (image : ApplicationImage P L) (deadlineOf : Nat → Nat) (player : P)
    (history : List image.application.PlayerEntry) (view : image.application.View)
    (hdone : ∀ node, node < state.nodes.length → view.application.done node = true) :
    root.liftProfileIn image deadlineOf rootProfile player history view =
      plan.liftProfileIn image deadlineOf profile player history view := by
  revert hdone
  induction continuation with
  | refl => intro _; rfl
  | sample _ ih =>
      intro hdone
      simp only [BuildState.addSampleEvent_nodes, List.length_append,
        List.length_singleton] at hdone
      rw [ih (fun node hnode => hdone node (by omega))]
      simp only [liftProfileIn]
      apply if_pos
      exact hdone _ (by omega)
  | binding _ ih =>
      intro hdone
      simp only [BuildState.addCommitEvent_nodes, List.length_append,
        List.length_singleton] at hdone
      rw [ih (fun node hnode => hdone node (by omega))]
      simp only [liftProfileIn]
      apply if_pos
      exact hdone _ (by omega)
  | publicChoice _ ih | conditional _ ih | conditionalCopy _ ih =>
      intro hdone
      simp only [BuildState.addRevealEvent_nodes, BuildState.addCommitEvent_nodes,
        List.length_append, List.length_singleton] at hdone
      rw [ih (fun node hnode => hdone node (by omega))]
      simp only [liftProfileIn]
      apply if_pos
      exact hdone _ (by omega)

/-- Native refinement at the exact source prefix supplies every completion
flag needed to dispatch the fixed original profile to its continuation.
This holds for every local history, without exposing the proof-side source
environment or compiler cursor to the policy. -/
theorem liftProfileIn_eq_of_refines
    (continuation : ProfileContinuation root rootProfile plan profile)
    (image : ApplicationImage P L) (deadlineOf : Nat → Nat)
    (current : CoupledAt (compileCore prog fresh state).graph state)
    (native : image.application.State)
    (hrefines : native.application.Refines current.current.graph.1)
    (player : P) (history : List image.application.PlayerEntry) :
    root.liftProfileIn image deadlineOf rootProfile player history
        (MessageApplication.State.observe image.application native player) =
      plan.liftProfileIn image deadlineOf profile player history
        (MessageApplication.State.observe image.application native player) := by
  apply continuation.liftProfileIn_eq image deadlineOf player history
  have hbound : state.nodes.length ≤
      (compileCore prog fresh state).graph.nodeCount := by
    change state.nodes.length ≤ (compileCore prog fresh state).nodes.length
    exact (compileCore_nodes_prefix prog fresh state).length_le
  intro node hnode
  change native.application.memory.done node = true
  let index : Fin (compileCore prog fresh state).graph.nodeCount :=
    ⟨node, Nat.lt_of_lt_of_le hnode hbound⟩
  exact (hrefines.memory.completed index).mpr ((current.completedPrefix index).mpr hnode)

end ProfileContinuation

end Vegas.ApplicationPlan

/-- info: 'Vegas.ApplicationPlan.ProfileContinuation.instructions_suffix' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.ApplicationPlan.ProfileContinuation.instructions_suffix

/-- info: 'Vegas.ApplicationPlan.ProfileContinuation.compile_eq' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.ApplicationPlan.ProfileContinuation.compile_eq

/-- info: 'Vegas.ApplicationPlan.ProfileContinuation.liftProfileIn_eq' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.ApplicationPlan.ProfileContinuation.liftProfileIn_eq

/-- info: 'Vegas.ApplicationPlan.ProfileContinuation.liftProfileIn_eq_of_refines' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.ApplicationPlan.ProfileContinuation.liftProfileIn_eq_of_refines

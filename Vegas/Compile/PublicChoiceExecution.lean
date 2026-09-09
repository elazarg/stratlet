/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import Vegas.Compile.PublicChoiceSite
import Vegas.Compile.SourceLaw

/-! # Executing a compiled public-choice site

A runtime-accepted public choice corresponds to the adjacent source commit and
reveal steps and to the same two generated graph nodes.  Validator agreement
with the source guard remains an explicit local premise; this file introduces
no runtime state, runner, scheduler, or native validator generator.
-/

noncomputable section

namespace Vegas.PublicChoiceSite

open EventGraph ToEventGraph Interaction GameTheory.Math.Probability

variable {P : Type} [DecidableEq P] {L : IExpr}
variable {Γ : VCtx P L} {prog : VegasCore P L Γ}

/-- Proof-facing effect of completing the generated choice and its immediate
public reveal with the same value. -/
def completePublication (site : PublicChoiceSite prog) (fresh : FreshBindings prog)
    (state : BuildState P L Γ) (cfg : Config (compileCore prog fresh state).graph)
    (value : L.Val site.ty) : Config (compileCore prog fresh state).graph :=
  let typed : TypedValue L := ⟨site.ty, value⟩
  (cfg.completeNode (choiceNode site fresh state) typed).completeNode
    (publicationNode site fresh state) typed

/-- A legal source value performs exactly the adjacent commit and reveal in
the represented source program. -/
theorem completePublication_source_steps
    (site : PublicChoiceSite prog) (env : VEnv L site.context)
    (value : L.Val site.ty)
    (hlegal : evalGuard site.guard value ((env.toView site.owner).eraseEnv) = true) :
    SmallStep.Star
      ⟨site.context, env,
        .commit site.choiceName site.owner site.guard site.decision.continuation⟩
      ⟨(site.publicName, .pub site.ty) ::
          (site.choiceName, .sealed site.owner site.ty) :: site.context,
        (env.cons value).cons value, site.tail⟩ := by
  rw [site.adjacent]
  exact (SmallStep.Star.single (SmallStep.commit site.guard _ value hlegal)).trans
    (SmallStep.Star.single (SmallStep.reveal .here site.tail))

/-- A ready generated site and a legal source value justify the exact decoded
graph macro via the compiled source guard, without assuming a `CommitStep`. -/
theorem completePublication_reachable
    (site : PublicChoiceSite prog) (fresh : FreshBindings prog)
    (state : BuildState P L Γ) (cfg : Config (compileCore prog fresh state).graph)
    (env : VEnv L site.context)
    (hagrees : (siteState site fresh state).Agrees cfg.store env)
    (done : Nat → Bool)
    (hcompleted : ∀ node : Fin (compileCore prog fresh state).graph.nodeCount,
      done node.val = true ↔ node ∈ cfg.done)
    (hready : (runtimeSite site fresh state).ready done = true)
    (value : L.Val site.ty)
    (hlegal : evalGuard site.guard value ((env.toView site.owner).eraseEnv) = true)
    (hreachable : Reachable (compileCore prog fresh state).graph cfg) :
    Reachable (compileCore prog fresh state).graph
      (completePublication site fresh state cfg value) := by
  let G := (compileCore prog fresh state).graph
  let choice := choiceNode site fresh state
  let publication := publicationNode site fresh state
  have hreadiness := G.publicChoice_ready cfg site.owner choice publication done
    hcompleted hready
  let written : TypedValue L := ⟨site.ty, value⟩
  have step : CommitStep G cfg site.owner
      ⟨choice, written⟩ := by
    exact (siteState site fresh state).sourceCommitStep site.owner site.guard cfg env
      hagrees choice (choiceNode_row site fresh state) hreadiness.1 value hlegal
  have hpublication : Ready G
      (cfg.completeNode choice written) publication :=
    publication_ready_after_choice cfg choice publication _
      (publicationNode_ne_choiceNode site fresh state) hreadiness.2.1 hreadiness.2.2
  exact reachable_choice_publication cfg site.owner choice publication written
    (publicationNode_type site fresh state).symm step
    (publicationNode_sem site fresh state) hpublication hreachable

/-- Under validator completeness, every legal source value is accepted by its
canonical owner-authored runtime request at a ready generated site. -/
theorem legal_choice_resolves
    (site : PublicChoiceSite prog) (fresh : FreshBindings prog)
    (state : BuildState P L Γ) (env : VEnv L site.context)
    (done : Nat → Bool) (valid : L.Val site.ty → Bool)
    (hready : (runtimeSite site fresh state).ready done = true)
    (hcomplete : ∀ value,
      evalGuard site.guard value ((env.toView site.owner).eraseEnv) = true →
        valid value = true)
    (serial : Nat) (value : L.Val site.ty)
    (hlegal : evalGuard site.guard value ((env.toView site.owner).eraseEnv) = true) :
    (runtimeSite site fresh state).resolve? done valid
      ⟨(site.owner, serial), value⟩ = some value := by
  exact ((runtimeSite site fresh state).resolve_request done valid serial value).2
    ⟨hready, hcomplete value hlegal⟩

/-- A canonical request is accepted exactly for a legal source value when the
public validator is equivalent to the source guard. -/
theorem canonical_request_resolves_iff_source_legal
    (site : PublicChoiceSite prog) (fresh : FreshBindings prog)
    (state : BuildState P L Γ) (env : VEnv L site.context)
    (done : Nat → Bool) (valid : L.Val site.ty → Bool)
    (hready : (runtimeSite site fresh state).ready done = true)
    (hvalidator : ∀ value, valid value = true ↔
      evalGuard site.guard value ((env.toView site.owner).eraseEnv) = true)
    (serial : Nat) (value : L.Val site.ty) :
    (runtimeSite site fresh state).resolve? done valid
        ⟨(site.owner, serial), value⟩ = some value ↔
      evalGuard site.guard value ((env.toView site.owner).eraseEnv) = true := by
  change (runtimeSite site fresh state).resolve? done valid
      ⟨((runtimeSite site fresh state).owner, serial), value⟩ = some value ↔ _
  rw [(runtimeSite site fresh state).resolve_request done valid serial value]
  simp only [hready, true_and]
  exact hvalidator value

/-- Validator soundness turns an accepted request into the exact adjacent
source commit/reveal execution. -/
theorem runtime_resolution_source_steps
    (site : PublicChoiceSite prog) (fresh : FreshBindings prog)
    (state : BuildState P L Γ) (env : VEnv L site.context)
    (done : Nat → Bool) (valid : L.Val site.ty → Bool)
    (message : Message P (L.Val site.ty)) (value : L.Val site.ty)
    (hsound : ∀ value, valid value = true →
      evalGuard site.guard value ((env.toView site.owner).eraseEnv) = true)
    (hresolve : (runtimeSite site fresh state).resolve? done valid message = some value) :
    SmallStep.Star
      ⟨site.context, env,
        .commit site.choiceName site.owner site.guard site.decision.continuation⟩
      ⟨(site.publicName, .pub site.ty) ::
          (site.choiceName, .sealed site.owner site.ty) :: site.context,
        (env.cons value).cons value, site.tail⟩ := by
  have haccepted := ((runtimeSite site fresh state).resolve_iff done valid message value).1
    hresolve
  exact completePublication_source_steps site env value (hsound value haccepted.2.2.1)

/-- A runtime-accepted choice executes the generated graph macro when the
completion readout represents the graph state and validator soundness supplies
the source guard certificate. -/
theorem runtime_resolution_reachable
    (site : PublicChoiceSite prog) (fresh : FreshBindings prog)
    (state : BuildState P L Γ) (cfg : Config (compileCore prog fresh state).graph)
    (env : VEnv L site.context)
    (hagrees : (siteState site fresh state).Agrees cfg.store env)
    (done : Nat → Bool) (valid : L.Val site.ty → Bool)
    (message : Message P (L.Val site.ty))
    (hcompleted : ∀ node : Fin (compileCore prog fresh state).graph.nodeCount,
      done node.val = true ↔ node ∈ cfg.done)
    (hsound : ∀ value, valid value = true →
      evalGuard site.guard value ((env.toView site.owner).eraseEnv) = true)
    (value : L.Val site.ty)
    (hresolve : (runtimeSite site fresh state).resolve? done valid message = some value)
    (hreachable : Reachable (compileCore prog fresh state).graph cfg) :
    Reachable (compileCore prog fresh state).graph
      (completePublication site fresh state cfg value) := by
  have haccepted := ((runtimeSite site fresh state).resolve_iff done valid message value).1
    hresolve
  exact completePublication_reachable site fresh state cfg env hagrees done hcompleted
    haccepted.1 value (hsound value haccepted.2.2.1) hreachable

end Vegas.PublicChoiceSite

/-- info: 'Vegas.PublicChoiceSite.runtime_resolution_reachable' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.PublicChoiceSite.runtime_resolution_reachable

/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import Vegas.Compile.SealedMessages

/-! # Inversion laws for compiled sealed-message rules -/

namespace Vegas.EventGraph

open Interaction

variable {Player : Type} [DecidableEq Player] {L : IExpr}
variable {G : Graph Player L} {ty : L.Ty}

namespace SealedFragment

/-- Every successfully indexed compiled rule comes from the graph node at that
same numeric index. -/
theorem ruleAt_exists_node (supported : SealedFragment G ty) {index : Nat}
    {rule : SealedRule Player}
    (hrule : supported.compile.rules[index]? = some rule) :
    ∃ node : Fin G.nodeCount,
      node.val = index ∧ rule = G.sealedRule node := by
  have hget := getElem?_eq_some_iff.mp hrule
  rcases hget with ⟨hindex, heq⟩
  have hlt : index < G.nodeCount := by
    simpa [SealedFragment.compile, Graph.nodeOrder] using hindex
  let node : Fin G.nodeCount := ⟨index, hlt⟩
  refine ⟨node, rfl, ?_⟩
  simpa [SealedFragment.compile, Graph.nodeOrder, node] using heq.symm

/-- A compiled commit rule reflects an actual commit row with the same owner. -/
theorem ruleAt_commit (supported : SealedFragment G ty) {index : Nat}
    {rule : SealedRule Player} {owner : Player}
    (hrule : supported.compile.rules[index]? = some rule)
    (hkind : rule.kind = .commit owner) :
    ∃ (node : Fin G.nodeCount) (guard : EventGuard L),
      node.val = index ∧ (G.nodeRow node).sem = .commit owner guard := by
  rcases supported.ruleAt_exists_node hrule with ⟨node, rfl, rfl⟩
  change (match (G.nodeRow node).sem with
    | .commit actualOwner _ => SealedRuleKind.commit actualOwner
    | .reveal field =>
        let producer := field - G.initialFields.length
        match G.node? producer with
        | some (.commit actualOwner _) => SealedRuleKind.reveal actualOwner producer
        | _ => SealedRuleKind.disabled
    | .sample _ => SealedRuleKind.disabled) = SealedRuleKind.commit owner at hkind
  cases hsem : (G.nodeRow node).sem with
  | sample dist => simp [hsem] at hkind
  | commit who guard =>
      have : who = owner := by
        simpa [hsem] using hkind
      subst who
      exact ⟨node, guard, rfl, hsem⟩
  | reveal source =>
      simp only [hsem] at hkind
      split at hkind
      next sem hget =>
        cases sem
        all_goals contradiction
      next => contradiction

/-- A compiled reveal rule reflects a reveal of the exact indicated commit
producer, whose row has the same owner. -/
theorem ruleAt_reveal (supported : SealedFragment G ty) {index : Nat}
    {rule : SealedRule Player} {owner : Player} {source : Nat}
    (hrule : supported.compile.rules[index]? = some rule)
    (hkind : rule.kind = .reveal owner source) :
    ∃ (node producer : Fin G.nodeCount) (guard : EventGuard L),
      node.val = index ∧ producer.val = source ∧
      (G.nodeRow node).sem = .reveal (G.nodeTarget producer) ∧
      (G.nodeRow producer).sem = .commit owner guard := by
  rcases supported.ruleAt_exists_node hrule with ⟨node, rfl, rfl⟩
  change (match (G.nodeRow node).sem with
    | .commit actualOwner _ => SealedRuleKind.commit actualOwner
    | .reveal field =>
        let producer := field - G.initialFields.length
        match G.node? producer with
        | some (.commit actualOwner _) => SealedRuleKind.reveal actualOwner producer
        | _ => SealedRuleKind.disabled
    | .sample _ => SealedRuleKind.disabled) = SealedRuleKind.reveal owner source at hkind
  cases hsem : (G.nodeRow node).sem with
  | sample dist => simp [hsem] at hkind
  | commit who guard => simp [hsem] at hkind
  | reveal sourceField =>
      rcases supported.revealSource node sourceField hsem with
        ⟨producer, producerOwner, guard, hsourceField, hproducer⟩
      have hcompiled :
          (G.sealedRule node).kind = .reveal producerOwner producer.val :=
        G.sealedRule_reveal node producer producerOwner guard
          (hsourceField ▸ hsem) hproducer
      have hkinds :
          SealedRuleKind.reveal producerOwner producer.val =
            .reveal owner source := hcompiled.symm.trans hkind
      have howner : producerOwner = owner := (SealedRuleKind.reveal.inj hkinds).1
      have hsource : producer.val = source := (SealedRuleKind.reveal.inj hkinds).2
      subst producerOwner
      exact ⟨node, producer, guard, rfl, hsource,
        hsourceField ▸ hsem, hproducer⟩

end SealedFragment

end Vegas.EventGraph

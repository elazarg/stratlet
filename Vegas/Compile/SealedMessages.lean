/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import Vegas.EventGraph.Execution
import Interaction.SealedProgram

/-! # Compiling a homogeneous commit/reveal fragment to public messages

The input is an existing event graph with a separate supported-fragment
certificate. Core well-formedness is unchanged. The emitted application rules
retain graph owners, producer indices, and prerequisite edges. Supported
commitments have unrestricted guards; samples and private initial-field
disclosures are outside this fragment.

The target uses an explicit ideal commitment service. This module does not
identify missing openings with a source value or prove settlement under
withholding. Decoding is a proof operation, not an application observation.
-/

namespace Vegas.EventGraph

open Interaction GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr}

/-- Admission to this backend fragment is separate from source admission.
All commits accept every value of the common type. Graph prerequisites still
determine when each commitment and reveal may be accepted. -/
structure SealedFragment (G : Graph Player L) (ty : L.Ty) : Prop where
  graphWF : G.WF
  rowType : ∀ node, (G.nodeRow node).ty = ty
  noSamples : ∀ node dist, (G.nodeRow node).sem ≠ .sample dist
  commitType : ∀ node who guard, (G.nodeRow node).sem = .commit who guard → guard.ty = ty
  commitReads : ∀ node who guard, (G.nodeRow node).sem = .commit who guard →
    guard.choiceReads = ∅
  commitGuard : ∀ node who guard, (G.nodeRow node).sem = .commit who guard →
    ∀ value env, guard.eval value env = true
  revealSource : ∀ node source, (G.nodeRow node).sem = .reveal source →
    ∃ (producer : Fin G.nodeCount) (who : Player) (guard : EventGuard L),
      source = G.nodeTarget producer ∧ (G.nodeRow producer).sem = .commit who guard

namespace Graph

/-- Executable prerequisite enumeration uses the graph's existing dependency
test, in canonical node order. No dependency is inferred from message order. -/
def messagePrerequisites (G : Graph Player L) (node : Fin G.nodeCount) : List Nat :=
  (G.nodeOrder.filter fun prior => decide (prior ∈ G.prereqs node)).map Fin.val

private def sealedRuleKind (G : Graph Player L) (node : Fin G.nodeCount) :
    SealedRuleKind Player :=
  match (G.nodeRow node).sem with
  | .commit owner _ => .commit owner
  | .reveal field =>
      let producer := field - G.initialFields.length
      match G.node? producer with
      | some (.commit owner _) => .reveal owner producer
      | _ => .disabled
  | .sample _ => .disabled

def sealedRule (G : Graph Player L) (node : Fin G.nodeCount) : SealedRule Player :=
  ⟨sealedRuleKind G node, G.messagePrerequisites node⟩

end Graph

namespace SealedFragment

variable {G : Graph Player L} {ty : L.Ty}

/-- Lower the admitted graph's reified event metadata to the message
application. The certificate is erased; the emitted rules remain data. -/
def compile (_supported : SealedFragment G ty) : SealedProgram Player where
  rules := G.nodeOrder.map G.sealedRule

theorem compile_rules (supported : SealedFragment G ty) :
    supported.compile.rules = G.nodeOrder.map G.sealedRule := rfl

@[simp] theorem compile_rule (supported : SealedFragment G ty)
    (node : Fin G.nodeCount) :
    supported.compile.rules[node.val]? = some (G.sealedRule node) := by
  simp [compile, Graph.nodeOrder]

end SealedFragment

namespace Graph

theorem mem_messagePrerequisites (G : Graph Player L)
    (node prior : Fin G.nodeCount) :
    prior.val ∈ G.messagePrerequisites node ↔ prior ∈ G.prereqs node := by
  simp only [messagePrerequisites, List.mem_map, List.mem_filter,
    mem_nodeOrder, true_and, decide_eq_true_eq]
  constructor
  · rintro ⟨candidate, hcandidate, heq⟩
    exact Fin.ext heq ▸ hcandidate
  · intro hprior
    exact ⟨prior, hprior, rfl⟩

theorem sealedRule_commit (G : Graph Player L) (node : Fin G.nodeCount)
    (owner : Player) (guard : EventGuard L)
    (hnode : (G.nodeRow node).sem = .commit owner guard) :
    (G.sealedRule node).kind = .commit owner := by
  simp [sealedRule, sealedRuleKind, hnode]

theorem sealedRule_reveal (G : Graph Player L)
    (node producer : Fin G.nodeCount) (owner : Player) (guard : EventGuard L)
    (hnode : (G.nodeRow node).sem = .reveal (G.nodeTarget producer))
    (hproducer : (G.nodeRow producer).sem = .commit owner guard) :
    (G.sealedRule node).kind = .reveal owner producer.val := by
  simp [sealedRule, sealedRuleKind, hnode, nodeTarget, hproducer]

theorem sealedRule_commit_eq (G : Graph Player L) (node : Fin G.nodeCount)
    (owner : Player) (guard : EventGuard L)
    (hnode : (G.nodeRow node).sem = .commit owner guard) :
    G.sealedRule node = ⟨.commit owner, G.messagePrerequisites node⟩ := by
  simp [sealedRule, sealedRuleKind, hnode]

theorem sealedRule_reveal_eq (G : Graph Player L)
    (node producer : Fin G.nodeCount) (owner : Player) (guard : EventGuard L)
    (hnode : (G.nodeRow node).sem = .reveal (G.nodeTarget producer))
    (hproducer : (G.nodeRow producer).sem = .commit owner guard) :
    G.sealedRule node = ⟨.reveal owner producer.val, G.messagePrerequisites node⟩ := by
  simp [sealedRule, sealedRuleKind, hnode, nodeTarget, hproducer]

end Graph

end Vegas.EventGraph

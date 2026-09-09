/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import Interaction.MessageApplication
import Interaction.PublicChoice
import Vegas.Compile.PublicGuard
import Vegas.EventGraph.Execution

/-! # Public-message application images

An image contains executable endpoint code and public storage, independently
of source environments and graph configurations. Its first instruction kind
is an ordinary guarded choice with an atomic public reveal. The shared message
runtime supplies submission, local delivery, replay, inclusion, and receipts.

This carrier does not implement sealed bindings, conditional openings, chance,
or timeouts. Those require further instructions and their compiler proofs;
they are not simulated by storing a hidden source configuration here.
-/

namespace Vegas

open EventGraph Interaction GameTheory.Math.Probability

variable {P : Type} [DecidableEq P] {L : IExpr}

/-- Executable code for an ordinary public choice. The guard determines the
payload type; the two field addresses are allocated by the source compiler. -/
structure PublicChoiceCode (P : Type) (L : IExpr) where
  endpoint : PublicChoice P
  guard : EventGuard L
  choiceField : Nat
  publicationField : Nat

/-- A finite dispatch artifact. Source occurrence certificates generate its
entries; its interpreter does not inspect those certificates. -/
structure ApplicationImage (P : Type) (L : IExpr) where
  choices : List (PublicChoiceCode P L)

namespace ApplicationImage

/-- Only public application data. Unopened source values have no storage
location in this carrier. The completion map is operational, not a proof. -/
structure Memory (L : IExpr) where
  store : Store L
  done : Nat → Bool

inductive Payload (L : IExpr) where
  | choice (address : Nat) (value : TypedValue L)
  | malformed (data : List Nat)

/-- Initialize only publicly declared graph fields. A source's sealed initial
values are not copied into this publicly observed runtime memory. -/
def Memory.initial (graph : Graph P L) : Memory L where
  store field :=
    if (graph.field? field).any (fun spec => spec.owner.isNone) then
      graph.initialStore field
    else none
  done _ := false

theorem Memory.initial_private (graph : Graph P L) (field : Nat)
    (spec : FieldSpec P L) (hfield : graph.field? field = some spec)
    (hprivate : spec.owner.isSome = true) :
    (Memory.initial graph).store field = none := by
  obtain ⟨owner, howner⟩ := Option.isSome_iff_exists.mp hprivate
  simp [Memory.initial, hfield, howner]

/-- Complete a public pair and store its now-public value at both addresses.
The choice's source binding is sealed syntactically, but its value has just
been disclosed by this transaction. -/
def Memory.publish (memory : Memory L) (code : PublicChoiceCode P L)
    (value : L.Val code.guard.ty) : Memory L where
  store := (memory.store.set code.choiceField ⟨code.guard.ty, value⟩).set
    code.publicationField ⟨code.guard.ty, value⟩
  done node := node == code.endpoint.choiceNode ||
    node == code.endpoint.publicationNode || memory.done node

def lookup (image : ApplicationImage P L) (address : Nat) :
    Option (PublicChoiceCode P L) :=
  image.choices.find? fun code => code.endpoint.publicationNode == address

/-- Decode the message's claimed type before running the generated guard.
Unknown addresses, wrong types, and malformed data all remain raw traffic. -/
def handle (image : ApplicationImage P L) (memory : Memory L)
    (message : Message P (Payload L)) : Option (Memory L) := do
  match message.payload with
  | .malformed _ => none
  | .choice address typed =>
      let code ← image.lookup address
      let value ← typed.as? code.guard.ty
      let accepted ← code.endpoint.resolve? memory.done
        (code.guard.validate memory.store) ⟨message.id, value⟩
      pure (memory.publish code accepted)

/-- The image uses the one native message interpreter. It has no private or
environment-triggered instructions at this instruction subset. -/
noncomputable def application (image : ApplicationImage P L) : MessageApplication P where
  Application := Memory L
  Payload := Payload L
  PrivateCommand := Empty
  EnvironmentCommand := Empty
  PlayerView := Memory L
  EnvironmentView := Memory L
  privateStep _ _ command := nomatch command
  environmentStep _ command := nomatch command
  handle := image.handle
  observePlayer memory _ := memory
  observeEnvironment memory := memory

theorem handle_choice (image : ApplicationImage P L) (memory : Memory L)
    (address : Nat) (code : PublicChoiceCode P L)
    (hcode : image.lookup address = some code) (id : MessageId P)
    (value : L.Val code.guard.ty) :
    image.handle memory ⟨id, .choice address ⟨code.guard.ty, value⟩⟩ =
      (code.endpoint.resolve? memory.done (code.guard.validate memory.store)
        ⟨id, value⟩).map (memory.publish code) := by
  simp only [handle, hcode, Option.bind_eq_bind, Option.bind_some, TypedValue.as?,
    ↓reduceDIte, cast_eq]
  cases code.endpoint.resolve? memory.done (code.guard.validate memory.store) ⟨id, value⟩ <;>
    rfl

theorem handle_unknown (image : ApplicationImage P L) (memory : Memory L)
    (address : Nat) (typed : TypedValue L) (id : MessageId P)
    (hunknown : image.lookup address = none) :
    image.handle memory ⟨id, .choice address typed⟩ = none := by
  simp [handle, hunknown]

theorem handle_wrong_type (image : ApplicationImage P L) (memory : Memory L)
    (address : Nat) (code : PublicChoiceCode P L) (typed : TypedValue L)
    (id : MessageId P) (hcode : image.lookup address = some code)
    (htype : typed.ty ≠ code.guard.ty) :
    image.handle memory ⟨id, .choice address typed⟩ = none := by
  simp [handle, hcode, TypedValue.as?, htype]

theorem handle_malformed (image : ApplicationImage P L) (memory : Memory L)
    (id : MessageId P) (data : List Nat) :
    image.handle memory ⟨id, .malformed data⟩ = none := rfl

omit [DecidableEq P] in
theorem publish_done (memory : Memory L) (code : PublicChoiceCode P L)
    (value : L.Val code.guard.ty) (node : Nat) :
    (memory.publish code value).done node = true ↔
      node = code.endpoint.choiceNode ∨ node = code.endpoint.publicationNode ∨
        memory.done node = true := by
  simp [Memory.publish, or_assoc]

/-- Replayed traffic cannot execute a completed pair again. -/
theorem handle_choice_after_publication (image : ApplicationImage P L)
    (memory : Memory L) (address : Nat) (code : PublicChoiceCode P L)
    (hcode : image.lookup address = some code) (id : MessageId P)
    (prior value : L.Val code.guard.ty) :
    image.handle (memory.publish code prior)
      ⟨id, .choice address ⟨code.guard.ty, value⟩⟩ = none := by
  rw [image.handle_choice _ address code hcode id value]
  simp [PublicChoice.resolve?, PublicChoice.ready, Memory.publish]

/-- Actual native inclusion, including the public ledger, receipt, and
unchanged local message knowledge. It requires a pending message, not a
fresh source action supplied to the interpreter. -/
theorem include_choice (image : ApplicationImage P L)
    (state : image.application.State) (address : Nat) (code : PublicChoiceCode P L)
    (hcode : image.lookup address = some code) (id : MessageId P)
    (value : L.Val code.guard.ty)
    (hlookup : state.pool.lookup id =
      some ⟨id, .choice address ⟨code.guard.ty, value⟩⟩)
    (hresolve : code.endpoint.resolve? state.application.done
      (code.guard.validate state.application.store) ⟨id, value⟩ = some value) :
    let next := image.application.includePending state id
    next.application = state.application.publish code value ∧
      next.receipts = state.receipts ++ [(id, true)] ∧
      next.pool.ledger = state.pool.ledger ++
        [⟨id, .choice address ⟨code.guard.ty, value⟩⟩] ∧
      next.pool.sent = state.pool.sent ∧ next.pool.inbox = state.pool.inbox := by
  have hhandle := image.handle_choice state.application address code hcode id value
  rw [hresolve, Option.map_some] at hhandle
  have hincluded := MessagePool.includeApplication_accept state.pool state.application
    (state.application.publish code value) id
    ⟨id, .choice address ⟨code.guard.ty, value⟩⟩ image.handle hlookup hhandle
  dsimp only
  simp only [MessageApplication.includePending, application, hincluded]
  refine ⟨True.intro, True.intro, MessagePool.include_ledger_of_lookup _ _ _ hlookup, ?_, ?_⟩
  · funext who
    exact MessagePool.include_preserves_sent _ _ who
  · funext who
    exact MessagePool.include_preserves_inbox _ _ who

end ApplicationImage

end Vegas

/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import Interaction.MessageApplication
import Interaction.PublicChoice
import Interaction.ConditionalPublication
import Vegas.Compile.PublicGuard
import Vegas.EventGraph.Execution

/-! # Public-message application images

An image contains executable endpoint code, public storage, and an ideal private
commitment service, independently of source environments and graph configurations.
The shared message runtime supplies submission, local delivery, replay, inclusion,
and receipts. Binding inclusion freezes its verifier without inspecting whether
the handle can open. Public clock advancement permits explicit expiry requests;
it supplies neither delivery fairness nor automatic timeout transactions.
Chance instructions use a fixed exact distribution kernel once their public
dependencies are ready. The environment selects when to invoke an instruction,
not its outcome; realizing this entropy capability is a separate target edge.
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

/-- An opaque binding instruction. Acceptance tests public readiness and
authentication, not private registration, value type, or a source guard. -/
structure BindingCode (P : Type) where
  owner : P
  node : Nat
  sourceField : Nat
  sourceSlot : Nat
  requires : List Nat

/-- A public chance instruction retaining the source compiler's distribution
code. The environment can trigger this fixed kernel but cannot supply a draw. -/
structure SampleCode (L : IExpr) where
  node : Nat
  outputField : Nat
  requires : List Nat
  dist : EventDist L

/-- Conditional publication of a previously bound value. The source encoding
determines the stored optional result; guard validation uses the public store
with the verified, now-public claim inserted at the original source field. -/
structure ConditionalCode (P : Type) (L : IExpr) where
  endpoint : ConditionalPublication P
  guard : EventGuard L
  secretTy : L.Ty
  sourceField : Nat
  encoding : L.Val guard.ty ≃ Option (L.Val secretTy)
  choiceField : Nat
  publicationField : Nat

def ConditionalCode.canOpen (code : ConditionalCode P L) (publicStore : Store L)
    (claimed : L.Val code.secretTy) : Bool :=
  code.guard.validate (publicStore.set code.sourceField ⟨code.secretTy, claimed⟩)
    (code.encoding.symm (some claimed))

/-- Dynamic decoding does not consult private state. Cleartext and malformed
requests remain possible public traffic but are never valid openings. -/
def ConditionalCode.decode (code : ConditionalCode P L) :
    ConditionalPublication.Payload P (TypedValue L) →
      Option (ConditionalPublication.Payload P (L.Val code.secretTy))
  | .opening handle typed => (typed.as? code.secretTy).map (.opening handle)
  | .decline => some .decline
  | .expire => some .expire
  | .cleartext _ | .malformed => none

inductive ApplicationInstruction (P : Type) (L : IExpr) where
  | sample (code : SampleCode L)
  | publicChoice (code : PublicChoiceCode P L)
  | bind (code : BindingCode P)
  | conditional (code : ConditionalCode P L)

def ApplicationInstruction.address : ApplicationInstruction P L → Nat
  | .sample code => code.node
  | .publicChoice code => code.endpoint.publicationNode
  | .bind code => code.node
  | .conditional code => code.endpoint.publicationNode

/-- A finite dispatch artifact. Source occurrence certificates generate its
entries; its interpreter does not inspect those certificates. -/
structure ApplicationImage (P : Type) (L : IExpr) where
  instructions : List (ApplicationInstruction P L)

namespace ApplicationImage

/-- Only public application data. Unopened source values have no storage
location in this carrier. The completion map is operational, not a proof. -/
structure Memory (P : Type) (L : IExpr) where
  store : Store L
  done : Nat → Bool
  accepted : Nat → Option (CommitmentHandle P Nat)
  clock : Nat

inductive Payload (P : Type) (L : IExpr) where
  | choice (address : Nat) (value : TypedValue L)
  | binding (address : Nat) (handle : CommitmentHandle P Nat)
  | conditional (address : Nat) (payload : ConditionalPublication.Payload P (TypedValue L))
  | malformed (data : List Nat)

/-- Private registration is authenticated by the runtime's principal capability.
An arbitrary typed value may be registered, including the wrong endpoint type. -/
inductive PrivateCommand (L : IExpr) where
  | register (slot : Nat) (value : TypedValue L)

inductive EnvironmentCommand where
  | advance (clock : Nat)
  | sample (address : Nat)

/-- The public projection and ideal service state are separate. Frozen values
are indexed by source field; `memory.accepted` distinguishes an unbound field
from an accepted handle whose frozen value is absent. -/
structure State (P : Type) (L : IExpr) where
  memory : Memory P L
  prepared : IdealCommitments P Nat (TypedValue L)
  frozen : Nat → Option (TypedValue L)

def State.initial (memory : Memory P L) : State P L where
  memory := memory
  prepared := IdealCommitments.empty
  frozen _ := none

/-- Initialize only publicly declared graph fields. A source's sealed initial
values are not copied into this publicly observed runtime memory. -/
def Memory.initial (graph : Graph P L) : Memory P L where
  store field :=
    if (graph.field? field).any (fun spec => spec.owner.isNone) then
      graph.initialStore field
    else none
  done _ := false
  accepted _ := none
  clock := 0

theorem Memory.initial_private (graph : Graph P L) (field : Nat)
    (spec : FieldSpec P L) (hfield : graph.field? field = some spec)
    (hprivate : spec.owner.isSome = true) :
    (Memory.initial graph).store field = none := by
  obtain ⟨owner, howner⟩ := Option.isSome_iff_exists.mp hprivate
  simp [Memory.initial, hfield, howner]

/-- Complete a public pair and store its now-public value at both addresses.
The choice's source binding is sealed syntactically, but its value has just
been disclosed by this transaction. -/
def Memory.publish (memory : Memory P L) (code : PublicChoiceCode P L)
    (value : L.Val code.guard.ty) : Memory P L := { memory with
  store := (memory.store.set code.choiceField ⟨code.guard.ty, value⟩).set
    code.publicationField ⟨code.guard.ty, value⟩
  done node := node == code.endpoint.choiceNode ||
    node == code.endpoint.publicationNode || memory.done node }

def State.publish (state : State P L) (code : PublicChoiceCode P L)
    (value : L.Val code.guard.ty) : State P L :=
  { state with memory := state.memory.publish code value }

/-- Registration cannot change an accepted verifier or public observations. -/
def State.register (state : State P L) (who : P) (slot : Nat)
    (value : TypedValue L) : State P L :=
  { state with prepared := (state.prepared.sealValue who slot value).state }

def State.advance (state : State P L) (clock : Nat) : State P L :=
  { state with memory := { state.memory with clock := max state.memory.clock clock } }

/-- Install the result of a single chance invocation as public application
state. The completed flag prevents a subsequent invocation from rerolling. -/
def State.sample (state : State P L) (code : SampleCode L)
    (value : L.Val code.dist.ty) : State P L :=
  { state with memory := { state.memory with
      store := state.memory.store.set code.outputField ⟨code.dist.ty, value⟩
      done node := node == code.node || state.memory.done node } }

def State.bind (state : State P L) (code : BindingCode P)
    (handle : CommitmentHandle P Nat) : State P L :=
  { state with
    memory := { state.memory with
      accepted field := if field = code.sourceField then some handle
        else state.memory.accepted field
      done node := node == code.node || state.memory.done node }
    frozen field := if field = code.sourceField then state.prepared.lookup handle
      else state.frozen field }

def State.publishConditional (state : State P L) (code : ConditionalCode P L)
    (result : Option (L.Val code.secretTy)) : State P L :=
  let typed : TypedValue L := ⟨code.guard.ty, code.encoding.symm result⟩
  { state with memory := { state.memory with
      store := (state.memory.store.set code.choiceField typed).set code.publicationField typed
      done node := node == code.endpoint.choiceNode ||
        node == code.endpoint.publicationNode || state.memory.done node } }

def State.verify (state : State P L) (code : ConditionalCode P L)
    (opening : IdealCommitments.Opening
      (Principal := P) (Slot := Nat) (Value := L.Val code.secretTy)) : Bool :=
  opening.handle == (code.endpoint.owner, code.endpoint.sourceSlot) &&
    ((state.frozen code.sourceField).bind (fun typed => typed.as? code.secretTy)) ==
      some opening.claimed

def lookup (image : ApplicationImage P L) (address : Nat) :
    Option (ApplicationInstruction P L) :=
  image.instructions.find? fun code => code.address == address

/-- Invoke a ready chance instruction atomically. Missing code, unavailable
public dependencies, and already completed instructions leave state unchanged.
Neither the environment command nor a player message can select the draw. -/
noncomputable def sample (image : ApplicationImage P L) (state : State P L)
    (address : Nat) : FinDist (State P L) :=
  match image.lookup address with
  | some (.sample code) =>
      if !state.memory.done code.node && code.requires.all state.memory.done then
        match ReadEnv.ofStoreExec? state.memory.store code.dist.reads with
        | some reads => (code.dist.eval reads).map (state.sample code)
        | none => FinDist.pure state
      else FinDist.pure state
  | _ => FinDist.pure state

/-- Decode the message's claimed type before running the generated guard.
Unknown addresses, wrong types, and malformed data all remain raw traffic. -/
def handle (image : ApplicationImage P L) (state : State P L)
    (message : Message P (Payload P L)) : Option (State P L) := do
  match message.payload with
  | .malformed _ => none
  | .choice address typed =>
      let .publicChoice code ← image.lookup address | none
      let value ← typed.as? code.guard.ty
      let accepted ← code.endpoint.resolve? state.memory.done
        (code.guard.validate state.memory.store) ⟨message.id, value⟩
      pure (state.publish code accepted)
  | .binding address handle =>
      let .bind code ← image.lookup address | none
      if message.sender = code.owner ∧ handle = (code.owner, code.sourceSlot) ∧
          state.memory.accepted code.sourceField = none ∧
          state.memory.done code.node = false ∧ code.requires.all state.memory.done then
        pure (state.bind code handle)
      else none
  | .conditional address payload =>
      let .conditional code ← image.lookup address | none
      let decoded ← code.decode payload
      let result ← code.endpoint.resolve? state.memory.clock (state.verify code)
        (state.memory.accepted code.sourceField) state.memory.done
        (code.canOpen state.memory.store) ⟨message.id, decoded⟩
      pure (state.publishConditional code result)

/-- The image uses the shared native message interpreter. Neither public view
exposes the preparation table or the frozen verifier. -/
noncomputable def application (image : ApplicationImage P L) : MessageApplication P where
  Application := State P L
  Payload := Payload P L
  PrivateCommand := PrivateCommand L
  EnvironmentCommand := EnvironmentCommand
  PlayerView := Memory P L
  EnvironmentView := Memory P L
  privateStep state who command := match command with
    | .register slot value => state.register who slot value
  environmentStep state command := match command with
    | .advance clock => FinDist.pure (state.advance clock)
    | .sample address => image.sample state address
  handle := image.handle
  observePlayer state _ := state.memory
  observeEnvironment state := state.memory

omit [DecidableEq P] in
/-- Successful chance invocation has exactly the retained distribution law,
followed by the public write. No normalized restriction of its support is used. -/
theorem sample_law (image : ApplicationImage P L) (state : State P L)
    (address : Nat) (code : SampleCode L)
    (hcode : image.lookup address = some (.sample code))
    (hnotDone : state.memory.done code.node = false)
    (hrequires : code.requires.all state.memory.done = true)
    (reads : ReadEnv L code.dist.reads)
    (hreads : ReadEnv.ofStoreExec? state.memory.store code.dist.reads = some reads) :
    image.sample state address = (code.dist.eval reads).map (state.sample code) := by
  simp [sample, hcode, hnotDone, hrequires, hreads]

omit [DecidableEq P] in
/-- A repeated chance invocation cannot redraw or replace an installed value. -/
theorem sample_after_completion (image : ApplicationImage P L) (state : State P L)
    (address : Nat) (code : SampleCode L)
    (hcode : image.lookup address = some (.sample code))
    (value : L.Val code.dist.ty) :
    image.sample (state.sample code value) address = FinDist.pure (state.sample code value) := by
  simp [sample, hcode, State.sample]

theorem handle_choice (image : ApplicationImage P L) (state : State P L)
    (address : Nat) (code : PublicChoiceCode P L)
    (hcode : image.lookup address = some (.publicChoice code)) (id : MessageId P)
    (value : L.Val code.guard.ty) :
    image.handle state ⟨id, .choice address ⟨code.guard.ty, value⟩⟩ =
      (code.endpoint.resolve? state.memory.done (code.guard.validate state.memory.store)
        ⟨id, value⟩).map (state.publish code) := by
  simp only [handle, hcode, Option.bind_eq_bind, Option.bind_some, TypedValue.as?,
    ↓reduceDIte, cast_eq]
  cases code.endpoint.resolve? state.memory.done
    (code.guard.validate state.memory.store) ⟨id, value⟩ <;> rfl

theorem handle_unknown (image : ApplicationImage P L) (state : State P L)
    (address : Nat) (typed : TypedValue L) (id : MessageId P)
    (hunknown : image.lookup address = none) :
    image.handle state ⟨id, .choice address typed⟩ = none := by
  simp [handle, hunknown]

theorem handle_wrong_type (image : ApplicationImage P L) (state : State P L)
    (address : Nat) (code : PublicChoiceCode P L) (typed : TypedValue L)
    (id : MessageId P) (hcode : image.lookup address = some (.publicChoice code))
    (htype : typed.ty ≠ code.guard.ty) :
    image.handle state ⟨id, .choice address typed⟩ = none := by
  simp [handle, hcode, TypedValue.as?, htype]

theorem handle_malformed (image : ApplicationImage P L) (state : State P L)
    (id : MessageId P) (data : List Nat) :
    image.handle state ⟨id, .malformed data⟩ = none := rfl

omit [DecidableEq P] in
theorem publish_done (memory : Memory P L) (code : PublicChoiceCode P L)
    (value : L.Val code.guard.ty) (node : Nat) :
    (memory.publish code value).done node = true ↔
      node = code.endpoint.choiceNode ∨ node = code.endpoint.publicationNode ∨
        memory.done node = true := by
  simp [Memory.publish, or_assoc]

/-- Replayed traffic cannot execute a completed pair again. -/
theorem handle_choice_after_publication (image : ApplicationImage P L)
    (state : State P L) (address : Nat) (code : PublicChoiceCode P L)
    (hcode : image.lookup address = some (.publicChoice code)) (id : MessageId P)
    (prior value : L.Val code.guard.ty) :
    image.handle (state.publish code prior)
      ⟨id, .choice address ⟨code.guard.ty, value⟩⟩ = none := by
  rw [image.handle_choice _ address code hcode id value]
  simp [PublicChoice.resolve?, PublicChoice.ready, State.publish, Memory.publish]

/-- Actual native inclusion, including the public ledger, receipt, and
unchanged local message knowledge. It requires a pending message, not a
fresh source action supplied to the interpreter. -/
theorem include_accepted (image : ApplicationImage P L)
    (state : image.application.State) (id : MessageId P)
    (message : Message P image.application.Payload) (updated : State P L)
    (hlookup : state.pool.lookup id = some message)
    (hhandle : image.handle state.application message = some updated) :
    let next := image.application.includePending state id
    next.application = updated ∧
      next.receipts = state.receipts ++ [(id, true)] ∧
      next.pool.ledger = state.pool.ledger ++ [message] ∧
      next.pool.sent = state.pool.sent ∧ next.pool.inbox = state.pool.inbox := by
  have hincluded := MessagePool.includeApplication_accept state.pool state.application
    updated id message image.handle hlookup hhandle
  dsimp only
  simp only [MessageApplication.includePending, application, hincluded]
  refine ⟨True.intro, True.intro, MessagePool.include_ledger_of_lookup _ _ _ hlookup, ?_, ?_⟩
  · funext who
    exact MessagePool.include_preserves_sent _ _ who
  · funext who
    exact MessagePool.include_preserves_inbox _ _ who

/-- A resolved ordinary choice is included with its exact public effects. -/
theorem include_choice (image : ApplicationImage P L)
    (state : image.application.State) (address : Nat) (code : PublicChoiceCode P L)
    (hcode : image.lookup address = some (.publicChoice code)) (id : MessageId P)
    (value : L.Val code.guard.ty)
    (hlookup : state.pool.lookup id =
      some ⟨id, .choice address ⟨code.guard.ty, value⟩⟩)
    (hresolve : code.endpoint.resolve? state.application.memory.done
      (code.guard.validate state.application.memory.store) ⟨id, value⟩ = some value) :
    let next := image.application.includePending state id
    next.application = state.application.publish code value ∧
      next.receipts = state.receipts ++ [(id, true)] ∧
      next.pool.ledger = state.pool.ledger ++
        [⟨id, .choice address ⟨code.guard.ty, value⟩⟩] ∧
      next.pool.sent = state.pool.sent ∧ next.pool.inbox = state.pool.inbox := by
  have hhandle := image.handle_choice state.application address code hcode id value
  rw [hresolve, Option.map_some] at hhandle
  exact image.include_accepted state id
    ⟨id, .choice address ⟨code.guard.ty, value⟩⟩
    (state.application.publish code value) hlookup hhandle

end ApplicationImage

end Vegas

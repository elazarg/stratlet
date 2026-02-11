import Vegas.LetProtocol.Step

/-!
# Play: Concrete IO runners for ProtoProg

- `runWithSeed`: Deterministic evaluation with fixed choices
- `runInteractive`: Interactive evaluation prompting the user
-/

namespace Proto

open Defs Prog

variable {L : Language}
variable {W : Type} [WeightModel W]

/-- Look up an element in a list by index, defaulting to `head?`. -/
private def listAt {α : Type} (xs : List α) (i : Nat) : Option α :=
  match xs, i with
  | [], _ => none
  | x :: _, 0 => some x
  | _ :: xs, n + 1 => listAt xs n

/-- Look up a Nat by index in a list, defaulting to 0. -/
private def natListGet (xs : List Nat) (i : Nat) : Nat :=
  match listAt xs i with
  | some n => n
  | none => 0

/-- A deterministic handler that uses pre-specified choices.
    Samples always pick the first element of the distribution;
    choices follow a list indexed by yield id. -/
def deterministicHandler
    (choices : List Nat) : ProtoHandler L W where
  onSample := fun _id dist =>
    match dist.weights.head? with
    | some (v, _) => pure v
    | none => throw (IO.userError "Empty distribution")
  onChoose := fun id _who actions => do
    let idx := natListGet choices id
    match listAt actions idx with
    | some v => pure v
    | none =>
      match actions.head? with
      | some v => pure v
      | none => throw (IO.userError "No actions available")

/-- Run a protocol program deterministically with fixed choices. -/
def runWithSeed {Γ τ} (choices : List Nat)
    (p : ProtoProg (L := L) (W := W) Γ τ)
    (env : L.Env Γ) : IO (L.Val τ) :=
  stepProto (deterministicHandler choices) p env

/-- Print action indices for a choice prompt. -/
private def printActions (n : Nat) (i : Nat := 0) : IO Unit :=
  if i < n then do
    IO.println s!"  {i}: (action {i})"
    printActions n (i + 1)
  else pure ()

/-- An interactive handler that prompts the user for choices.
    Samples pick the first element; choices prompt via stdin. -/
def interactiveHandler : ProtoHandler L W where
  onSample := fun id dist =>
    match dist.weights.head? with
    | some (v, _) => do
        IO.println s!"[Sample {id}] Sampled (first from dist)"
        pure v
    | none => throw (IO.userError "Empty distribution")
  onChoose := fun id who actions => do
    let hi := actions.length - 1
    IO.println s!"[Choose {id}] Player {who}, pick (0-{hi}):"
    printActions actions.length
    let input ← (← IO.getStdin).getLine
    let idx := input.trimAscii.toString.toNat?.getD 0
    match listAt actions idx with
    | some v => pure v
    | none =>
      match actions.head? with
      | some v => pure v
      | none => throw (IO.userError "No actions available")

/-- Run a protocol program interactively, prompting for decisions. -/
def runInteractive {Γ τ} (p : ProtoProg (L := L) (W := W) Γ τ)
    (env : L.Env Γ) : IO (L.Val τ) :=
  stepProto interactiveHandler p env

/-- Determinism: `runWithSeed` with same inputs gives same result. -/
theorem runWithSeed_deterministic {Γ τ} (choices : List Nat)
    (p : ProtoProg (L := L) (W := W) Γ τ) (env : L.Env Γ) :
    runWithSeed choices p env = runWithSeed choices p env := rfl

end Proto

import GameTheory.Languages.MAID.Syntax
import GameTheory.Languages.MAID.Prefix

/-!
# Factored-Observation MAID (VegasMAID)

A `VegasMAID` is a restricted MAID where the information structure is
*factored*: every node's value is either fully public or private to exactly
one player. There is no partial sharing ("A sees it but B doesn't, even
though both are downstream"). This matches the factored-observation model
of Kovarik et al. (2019, "Rethinking Formal Models of Partially Observable
Multiagent Decision Making").

## Key structural property

In a general MAID, `obsParents ⊆ parents` with possible strict inclusion at
decision nodes (hidden parents the player can't observe). In a VegasMAID,
**`obsParents = parents` for all nodes** — a decision node only depends on
what its player can observe. The DAG edges *are* the information flow.

## Visibility model

Each node has a *reveal time* (`revealedAt`):

- **Chance nodes**: public immediately (`revealedAt = nd`)
- **Decision nodes**: private to the deciding player (`revealedAt > nd`),
  potentially revealed later (`revealedAt = some k` for some `k > nd`)
  or never (`revealedAt = ⊤`)
- **Utility nodes**: terminal — no observation role

A node `i` is *visible to player `p` at decision `d`* iff:
- `revealedAt i ≤ d` (public by then), or
- `kind i = .decision p` (own private decision)

The **factored-observation invariant** (`parents_visible`) requires that
every parent of a decision node is visible to the deciding player. Since
non-decision nodes have `obsParents = parents` by the MAID axiom
`obs_eq_nondec`, this makes `obsParents = parents` universally.
-/

namespace Vegas

open MAID

/-- A factored-observation MAID: the subclass of MAIDs producible by Vegas
compilation. Observation parents are not stored — they equal `parents` by
construction. The visibility schedule `revealedAt` governs which nodes are
public vs. private. -/
structure VegasMAID (Player : Type) [DecidableEq Player] [Fintype Player]
    (n : Nat) where
  /-- Node kind: chance, decision (for a player), or utility (for a player). -/
  kind : Fin n → NodeKind Player
  /-- Data-dependency parents. For decision nodes, this equals the observation
      parents — the player sees everything the node depends on. -/
  parents : Fin n → Finset (Fin n)
  /-- Value domain at each node. -/
  Val : Fin n → Type
  instFintype : ∀ nd, Fintype (Val nd)
  instDecidableEq : ∀ nd, DecidableEq (Val nd)
  instInhabited : ∀ nd, Inhabited (Val nd)
  /-- Utility nodes have a unique (trivial) value. -/
  utility_unique : ∀ nd a, kind nd = .utility a → Unique (Val nd)
  /-- Visibility schedule: when each node becomes public.
      - `↑nd.val` — immediately public (chance nodes)
      - `↑k` for `k > nd.val` — revealed at step `k`
      - `⊤` — never revealed (stays private forever) -/
  revealedAt : Fin n → WithTop Nat
  /-- **Natural ordering**: all parents have strictly smaller indices. -/
  natural_order : ∀ (nd : Fin n), ∀ p ∈ parents nd, p.val < nd.val
  /-- Chance nodes are immediately public. -/
  chance_public : ∀ (nd : Fin n),
    kind nd = .chance → revealedAt nd = ↑nd.val
  /-- Decision nodes are not immediately public (private at creation). -/
  decision_private : ∀ (nd : Fin n) (p : Player),
    kind nd = .decision p → (nd.val : WithTop Nat) < revealedAt nd
  /-- **Factored-observation invariant**: every parent of a decision node is
      visible to the deciding player. Combined with `obs_eq_nondec` for
      non-decision nodes, this ensures `obsParents = parents` universally. -/
  parents_visible : ∀ (d : Fin n) (p : Player),
    kind d = .decision p →
    ∀ i ∈ parents d,
      revealedAt i ≤ ↑d.val ∨ (∃ q, kind i = .decision q ∧ q = p)

variable {Player : Type} [DecidableEq Player] [Fintype Player] {n : Nat}

namespace VegasMAID

variable (M : VegasMAID Player n)

instance (nd : Fin n) : Fintype (M.Val nd) := M.instFintype nd
instance (nd : Fin n) : DecidableEq (M.Val nd) := M.instDecidableEq nd
instance (nd : Fin n) : Inhabited (M.Val nd) := M.instInhabited nd

/-! ## Visibility -/

/-- Node `i` is visible to player `p` at time `d`. -/
def visibleTo (i d : Fin n) (p : Player) : Prop :=
  M.revealedAt i ≤ ↑d.val ∨ (∃ q, M.kind i = .decision q ∧ q = p)

/-- Chance nodes are visible to everyone at any later time. -/
theorem chance_visibleTo {i d : Fin n} {p : Player}
    (hc : M.kind i = .chance) (hle : i.val ≤ d.val) :
    M.visibleTo i d p := by
  left
  rw [M.chance_public i hc]
  exact WithTop.coe_le_coe.mpr hle

/-- A player's own decisions are always visible to them. -/
theorem own_decision_visibleTo {i d : Fin n} {p : Player}
    (hk : M.kind i = .decision p) :
    M.visibleTo i d p :=
  Or.inr ⟨p, hk, rfl⟩

/-! ## Conversion to MAID.Struct -/

/-- Acyclicity follows from the natural ordering: parent indices strictly
    decrease, so no directed cycle can exist. -/
theorem acyclic : DAG.Acyclic (fun (a b : Fin n) => a ∈ M.parents b) := by
  intro x hx
  -- In the transitive closure, values strictly decrease at each step
  have : ∀ a b, Relation.TransGen (fun a b => a ∈ M.parents b) a b → a.val < b.val := by
    intro a b hab
    induction hab with
    | single h => exact M.natural_order _ _ h
    | tail _ hbc ih => exact Nat.lt_trans ih (M.natural_order _ _ hbc)
  exact Nat.lt_irrefl x.val (this x x hx)

/-- Convert to a standard `MAID.Struct`. The key: `obsParents := parents`. -/
noncomputable def toStruct : Struct Player n where
  kind := M.kind
  parents := M.parents
  obsParents := M.parents
  Val := M.Val
  instFintype := M.instFintype
  instDecidableEq := M.instDecidableEq
  instInhabited := M.instInhabited
  obs_sub := fun _ => Finset.Subset.refl _
  obs_eq_nondec := fun _ _ => rfl
  utility_unique := M.utility_unique
  acyclic := M.acyclic

@[simp] theorem toStruct_kind (nd : Fin n) :
    M.toStruct.kind nd = M.kind nd := rfl

@[simp] theorem toStruct_parents (nd : Fin n) :
    M.toStruct.parents nd = M.parents nd := rfl

@[simp] theorem toStruct_Val (nd : Fin n) :
    M.toStruct.Val nd = M.Val nd := rfl

/-- The defining structural property: observation parents equal parents. -/
@[simp] theorem toStruct_obsParents_eq_parents (nd : Fin n) :
    M.toStruct.obsParents nd = M.toStruct.parents nd := rfl

/-- The compiled structure is in natural order. -/
theorem toStruct_naturalOrder : M.toStruct.NaturalOrder :=
  fun nd p hp => M.natural_order nd p hp

/-! ## Simplified info sets

In a VegasMAID, since `obsParents = parents`, an info set is just a
decision node together with a configuration of its parents (not a
potentially-different observation subset). -/

/-- Info set in a VegasMAID: decision node + parent configuration.
    Equivalent to `MAID.Infoset M.toStruct p` since `obsParents = parents`. -/
abbrev Infoset (p : Player) := MAID.Infoset M.toStruct p

end VegasMAID

end Vegas

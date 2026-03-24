import Vegas.MAID.VegasMAID
import Vegas.MAID.Compile
import Vegas.MAID.Correctness

/-!
# Experimental Vegas-to-VegasMAID Compiler

**Status: experimental — not actively used, not a replacement for the
existing compiler in `Compile.lean`.**

This file demonstrates how to compile a Vegas program into a `VegasMAID`,
the factored-observation MAID structure defined in `VegasMAID.lean`. The
key new piece is tracking **reveal times**: when each decision node's value
becomes public.

## Approach

We define a lightweight `RevealState` that shadows `MAIDCompileState.ofProg`,
tracking only the information not already in the existing compiler:
- `revealTime`: when each node becomes public
- `nodeOf`: which MAID node backs each program variable

The final `VegasMAID` is built by combining the existing compiler's structural
output with the reveal times computed here.
-/

namespace Vegas

open MAID

variable {Player : Type} [DecidableEq Player] {L : IExpr}

/-! ## Reveal-time tracking state -/

/-- Lightweight state for computing reveal times alongside compilation.
    Shadows `MAIDCompileState.ofProg` without duplicating structural work. -/
structure RevealState where
  /-- Current node counter (mirrors `MAIDCompileState.nextId`). -/
  nextId : Nat := 0
  /-- When each node becomes public. `⊤` means never revealed. -/
  revealTime : Nat → WithTop Nat := fun _ => ⊤
  /-- Which MAID node (if any) backs each program variable. -/
  nodeOf : VarId → Option Nat := fun _ => none

/-- Initial reveal state. -/
def RevealState.empty : RevealState := {}

/-- Record a new node as immediately public (for chance/utility). -/
def RevealState.addPublicNode (rs : RevealState) : RevealState :=
  let id := rs.nextId
  { rs with
    nextId := id + 1
    revealTime := fun i => if i = id then ↑id else rs.revealTime i }

/-- Record a new node as private (for decision nodes).
    The `revealTime` for the new node stays at `⊤` (the default). -/
def RevealState.addPrivateNode (rs : RevealState) : RevealState :=
  { rs with nextId := rs.nextId + 1 }

/-- Bind a variable to a MAID node. -/
def RevealState.bindVar (rs : RevealState) (x : VarId) (nid : Nat) :
    RevealState :=
  { rs with nodeOf := fun v => if v = x then some nid else rs.nodeOf v }

/-- Copy a variable's node binding (for reveal). -/
def RevealState.aliasVar (rs : RevealState) (y x : VarId) :
    RevealState :=
  { rs with nodeOf := fun v => if v = y then rs.nodeOf x else rs.nodeOf v }

/-! ## Reveal-time computation -/

/-- Walk a Vegas program and compute reveal times. Mirrors the structure of
    `MAIDCompileState.ofProg` but only tracks visibility, not dependencies
    or semantics. -/
noncomputable def computeReveals (B : MAIDBackend Player L) :
    {Γ : VCtx Player L} →
    VegasCore Player L Γ →
    RevealState → RevealState
  | _, .ret _, rs =>
      -- One utility node per player, all public
      let _ := B.fintypePlayer
      (Finset.univ (α := Player)).toList.foldl (fun rs' _ => rs'.addPublicNode) rs
  | _, .letExpr _ _ k, rs =>
      -- No MAID node; variable is a deterministic function (no nodeOf entry)
      computeReveals B k rs
  | _, .sample x _ _ _ k, rs =>
      -- Chance node: immediately public
      let id := rs.nextId
      let rs' := rs.addPublicNode.bindVar x id
      computeReveals B k rs'
  | _, .commit x _ _ k, rs =>
      -- Decision node: private to the deciding player
      let id := rs.nextId
      let rs' := rs.addPrivateNode.bindVar x id
      computeReveals B k rs'
  | _, .reveal y _ x _ k, rs =>
      -- Reveal: make the backing node public (at current nextId).
      -- Uses min so that the first reveal wins if revealed multiple times.
      let rs' := match rs.nodeOf x with
        | some nid =>
            let curTime : WithTop Nat := ↑rs.nextId
            { rs with
              revealTime := fun i =>
                if i = nid then min curTime (rs.revealTime i)
                else rs.revealTime i }
        | none => rs
      computeReveals B k (rs'.aliasVar y x)

/-! ## Building VegasMAID from compiler output + reveal times -/

/-- `addPublicNode` foldl advances `nextId` by the list length. -/
private theorem foldl_addPublicNode_nextId (rs : RevealState) (xs : List α) :
    (xs.foldl (fun rs' _ => rs'.addPublicNode) rs).nextId = rs.nextId + xs.length := by
  induction xs generalizing rs with
  | nil => simp
  | cons x xs ih =>
      simp only [List.foldl_cons, List.length_cons]
      rw [ih rs.addPublicNode]
      simp [RevealState.addPublicNode]; omega

/-- `addUtilityNodes` advances `nextId` by the list length. -/
private theorem addUtilityNodes_nextId {B : MAIDBackend Player L}
    (st : MAIDCompileState Player L B)
    (deps : Finset Nat) (hdeps : ∀ d ∈ deps, d < st.nextId)
    (ufn : Player → RawNodeEnv L → ℝ) (xs : List Player) :
    (st.addUtilityNodes deps hdeps ufn xs).nextId = st.nextId + xs.length := by
  induction xs generalizing st with
  | nil => simp [MAIDCompileState.addUtilityNodes]
  | cons x xs ih =>
      simp only [MAIDCompileState.addUtilityNodes, List.length_cons]
      rw [ih]
      simp [MAIDCompileState.addNode, Nat.add_assoc, Nat.add_comm 1]

/-- The reveal state's `nextId` matches the compiler's `nextId`.
    (Both walk the same program structure.) -/
theorem computeReveals_nextId_eq (B : MAIDBackend Player L)
    {Γ : VCtx Player L}
    (p : VegasCore Player L Γ) (hl : Legal p) (hd : NormalizedDists p)
    (ρ : RawNodeEnv L → VEnv (Player := Player) L Γ)
    (st : MAIDCompileState Player L B) (rs : RevealState)
    (hsync : rs.nextId = st.nextId) :
    (computeReveals B p rs).nextId =
      (MAIDCompileState.ofProg B p hl hd ρ st).nextId := by
  induction p generalizing st rs with
  | ret payoffs =>
      simp only [computeReveals, MAIDCompileState.ofProg]
      rw [foldl_addPublicNode_nextId, addUtilityNodes_nextId, hsync]
  | letExpr x e k ih => exact ih hl hd _ _ _ hsync
  | sample x τ m D' k ih =>
      simp only [computeReveals, MAIDCompileState.ofProg]
      apply ih (hd := hd.2)
      simp [RevealState.addPublicNode, RevealState.bindVar,
            MAIDCompileState.addNode, MAIDCompileState.addVar, hsync]
  | commit x who R k ih =>
      simp only [computeReveals, MAIDCompileState.ofProg]
      apply ih (hd := hd)
      simp [RevealState.addPrivateNode, RevealState.bindVar,
            MAIDCompileState.addNode, MAIDCompileState.addVar, hsync]
  | reveal y who x hx k ih =>
      simp only [computeReveals, MAIDCompileState.ofProg]
      apply ih (hd := hd)
      cases rs.nodeOf x <;>
        simp [RevealState.aliasVar, MAIDCompileState.addVar, hsync]

/-- Joint consistency of reveal times with compiled node kinds. -/
structure RevealConsistent {B : MAIDBackend Player L}
    (st : MAIDCompileState Player L B) (rs : RevealState) : Prop where
  sync : rs.nextId = st.nextId
  chance : ∀ (nd : Fin st.nextId),
    (st.descAt nd).kind = .chance → rs.revealTime nd.val = ↑nd.val
  decision : ∀ (nd : Fin st.nextId) (p : Player),
    (st.descAt nd).kind = .decision p → (↑nd.val : WithTop Nat) < rs.revealTime nd.val
  /-- `nodeOf` only points to allocated node indices. -/
  nodeOf_lt : ∀ x nid, rs.nodeOf x = some nid → nid < st.nextId
  /-- `revealTime` at unallocated indices is `⊤` (never set). -/
  unset : ∀ i, st.nextId ≤ i → rs.revealTime i = ⊤

/-- Build a `VegasMAID` from the existing compiler's output and computed
    reveal times, given consistency. -/
noncomputable def toVegasMAID
    (B : MAIDBackend Player L) (st : MAIDCompileState Player L B)
    (rs : RevealState) (hcon : RevealConsistent st rs)
    (hvisible : ∀ (d : Fin st.nextId) (p : Player),
      (st.descAt d).kind = .decision p →
      ∀ (i : Nat) (hi : i ∈ (st.descAt d).parents),
        rs.revealTime i ≤ ↑d.val ∨
          (∃ q, (st.descAt ⟨i, Nat.lt_trans (st.descAt_parent_lt d hi) d.2⟩).kind =
            .decision q ∧ q = p)) :
    @VegasMAID Player _ B.fintypePlayer st.nextId := by
  letI := B.fintypePlayer
  exact
  { kind := fun nd => (st.descAt nd).kind
    parents := fun nd =>
      (st.descAt nd).parents.attach.image
        (fun d => ⟨d.1, Nat.lt_trans (st.descAt_parent_lt nd d.2) nd.2⟩)
    Val := fun nd => CompiledNode.valType (B := B) (st.descAt nd)
    instFintype := fun nd => by cases st.descAt nd with
      | chance τ _ _ _ => exact MAIDValuation.instFintypeVal L B.toMAIDValuation τ
      | decision τ _ _ _ _ _ => exact MAIDValuation.instFintypeVal L B.toMAIDValuation τ
      | utility _ _ _ => exact Unit.fintype
    instDecidableEq := fun nd => by cases st.descAt nd with
      | chance τ _ _ _ => exact L.decEqVal
      | decision τ _ _ _ _ _ => exact L.decEqVal
      | utility _ _ _ => exact instDecidableEqPUnit
    instInhabited := fun nd => by cases st.descAt nd with
      | chance τ _ _ _ => exact ⟨MAIDValuation.defaultVal L B.toMAIDValuation τ⟩
      | decision τ _ _ _ _ _ => exact ⟨MAIDValuation.defaultVal L B.toMAIDValuation τ⟩
      | utility _ _ _ => exact ⟨()⟩
    utility_unique := by
      intro nd a h
      cases hdesc : st.descAt nd with
      | utility _ _ _ => exact PUnit.instUnique
      | chance τ ps cpd hn => exfalso; simp [CompiledNode.kind, hdesc] at h
      | decision τ who acts hacts hnodup obs =>
          exfalso; simp [CompiledNode.kind, hdesc] at h
    revealedAt := fun nd => rs.revealTime nd.val
    natural_order := fun nd p hp => by
      rcases Finset.mem_image.mp hp with ⟨d, hd, rfl⟩
      exact st.descAt_parent_lt nd d.2
    chance_public := hcon.chance
    decision_private := hcon.decision
    parents_visible := by
      intro d p hkind i hi
      rcases Finset.mem_image.mp hi with ⟨⟨j, hj⟩, _, rfl⟩
      exact hvisible d p hkind j hj }

/-! ## revealTime monotonicity -/

/-- `computeReveals` never increases `revealTime` at indices < nextId.
    (At index nextId, addPublicNode sets it to ↑nextId which is ≤ ⊤ = unset.) -/
theorem computeReveals_revealTime_le (B : MAIDBackend Player L)
    {Γ : VCtx Player L}
    (p : VegasCore Player L Γ)
    (rs : RevealState) (i : Nat) (hi : i < rs.nextId) :
    (computeReveals B p rs).revealTime i ≤ rs.revealTime i := by
  induction p generalizing rs with
  | ret =>
      simp only [computeReveals]
      letI := B.fintypePlayer
      generalize (Finset.univ (α := Player)).toList = players
      induction players generalizing rs with
      | nil => simp
      | cons _ rest ih =>
          simp only [List.foldl_cons]
          exact le_trans (ih _ (by simp [RevealState.addPublicNode]; omega)) (by
            simp only [RevealState.addPublicNode]
            rw [if_neg (show i ≠ rs.nextId from by omega)])
  | letExpr _ _ k ih => exact ih rs hi
  | sample x _ _ _ k ih =>
      simp only [computeReveals]
      exact le_trans (ih _ (by simp [RevealState.addPublicNode, RevealState.bindVar]; omega)) (by
        simp only [RevealState.addPublicNode, RevealState.bindVar]
        rw [if_neg (show i ≠ rs.nextId from by omega)])
  | commit x _ _ k ih =>
      simp only [computeReveals]
      exact le_trans (ih _ (by simp [RevealState.addPrivateNode, RevealState.bindVar]; omega)) (by
        simp [RevealState.addPrivateNode, RevealState.bindVar])
  | reveal y _ x _ k ih =>
      simp only [computeReveals]
      exact le_trans (ih _ (by
        simp only [RevealState.aliasVar]
        cases rs.nodeOf x <;> simp [hi])) (by
        simp only [RevealState.aliasVar]
        cases rs.nodeOf x with
        | none => exact le_refl _
        | some nid =>
            simp only
            by_cases h : i = nid
            · rw [if_pos h]; exact min_le_right _ _
            · rw [if_neg h])

/-! ## Reusable lemmas for addNode consistency -/

/-- RevealConsistent preserved by addNode (non-decision) + addPublicNode only. -/
private theorem revealConsistent_addNode'
    {st : MAIDCompileState Player L B} {rs : RevealState}
    (hcon : RevealConsistent st rs)
    (nd : CompiledNode Player L B) (hkind : ¬ ∃ p, nd.kind = .decision p)
    (hnd : ∀ d ∈ nd.parents ∪ nd.obsParents, d < st.nextId) :
    RevealConsistent (st.addNode nd hnd).2 rs.addPublicNode where
  sync := by simp [RevealState.addPublicNode, MAIDCompileState.addNode, hcon.sync]
  chance := by
    intro nd' hk
    have hbound : nd'.val ≤ st.nextId := by
      have := nd'.isLt; simp [MAIDCompileState.addNode] at this; omega
    have hk_inner : ((st.addNode nd hnd).2.descAt ⟨nd'.val, by
        simp [MAIDCompileState.addNode]; omega⟩).kind = .chance := hk
    rcases Nat.lt_or_eq_of_le hbound with hlt | heq
    · rw [MAIDCompileState.addNode_descAt_old st nd hnd ⟨nd'.val, hlt⟩] at hk_inner
      simp only [RevealState.addPublicNode]
      rw [if_neg (show nd'.val ≠ rs.nextId from by rw [hcon.sync]; omega)]
      exact hcon.chance ⟨nd'.val, hlt⟩ hk_inner
    · simp only [RevealState.addPublicNode]
      rw [if_pos (show nd'.val = rs.nextId from by rw [hcon.sync]; omega)]
      simp [hcon.sync, heq]
  decision := by
    intro nd' p hk
    have hbound : nd'.val ≤ st.nextId := by
      have := nd'.isLt; simp [MAIDCompileState.addNode] at this; omega
    have hk_inner : ((st.addNode nd hnd).2.descAt ⟨nd'.val, by
        simp [MAIDCompileState.addNode]; omega⟩).kind = .decision p := hk
    rcases Nat.lt_or_eq_of_le hbound with hlt | heq
    · rw [MAIDCompileState.addNode_descAt_old st nd hnd ⟨nd'.val, hlt⟩] at hk_inner
      simp only [RevealState.addPublicNode]
      rw [if_neg (show nd'.val ≠ rs.nextId from by rw [hcon.sync]; omega)]
      exact hcon.decision ⟨nd'.val, hlt⟩ p hk_inner
    · exfalso
      rw [show (⟨nd'.val, _⟩ : Fin (st.addNode nd hnd).2.nextId) =
          ⟨st.nextId, by simp [MAIDCompileState.addNode]⟩ from Fin.ext heq] at hk_inner
      rw [MAIDCompileState.addNode_descAt_new st nd hnd] at hk_inner
      exact hkind ⟨p, hk_inner⟩
  nodeOf_lt := by
    intro v nid hnid
    simp only [RevealState.addPublicNode] at hnid
    show nid < st.nextId + 1
    exact Nat.lt_trans (hcon.nodeOf_lt v nid hnid) (Nat.lt_succ_self _)
  unset := by
    intro i hi
    have hi' : st.nextId + 1 ≤ i := by simpa [MAIDCompileState.addNode] using hi
    simp only [RevealState.addPublicNode]
    rw [if_neg (show i ≠ rs.nextId from by rw [hcon.sync]; omega)]
    exact hcon.unset i (by omega)

/-- RevealConsistent preserved by addNode (non-decision) + addVar + addPublicNode + bindVar. -/
private theorem revealConsistent_addChance'
    {st : MAIDCompileState Player L B} {rs : RevealState}
    (hcon : RevealConsistent st rs)
    (nd : CompiledNode Player L B) (hkind : ¬ ∃ p, nd.kind = .decision p)
    (hnd : ∀ d ∈ nd.parents ∪ nd.obsParents, d < st.nextId)
    (x : VarId) (τ : BindTy Player L)
    (hdeps : ∀ d ∈ ({st.nextId} : Finset Nat), d < st.nextId + 1) :
    RevealConsistent
      ((st.addNode nd hnd).2.addVar x τ {st.nextId} hdeps)
      (rs.addPublicNode.bindVar x rs.nextId) := by
  have hnid1 : ((st.addNode nd hnd).2.addVar x τ {st.nextId} hdeps).nextId
      = st.nextId + 1 := by simp [MAIDCompileState.addNode, MAIDCompileState.addVar]
  exact {
    sync := by simp [RevealState.addPublicNode, RevealState.bindVar, hnid1, hcon.sync]
    chance := by
      intro nd' hk
      have hbound : nd'.val ≤ st.nextId := by rw [hnid1] at nd'; omega
      have hk_inner : ((st.addNode nd hnd).2.descAt ⟨nd'.val, by
          simp [MAIDCompileState.addNode]; omega⟩).kind = .chance := hk
      rcases Nat.lt_or_eq_of_le hbound with hlt | heq
      · rw [MAIDCompileState.addNode_descAt_old st nd hnd ⟨nd'.val, hlt⟩] at hk_inner
        simp only [RevealState.addPublicNode, RevealState.bindVar]
        rw [if_neg (show nd'.val ≠ rs.nextId from by rw [hcon.sync]; omega)]
        exact hcon.chance ⟨nd'.val, hlt⟩ hk_inner
      · simp only [RevealState.addPublicNode, RevealState.bindVar]
        rw [if_pos (show nd'.val = rs.nextId from by rw [hcon.sync]; omega)]
        simp [hcon.sync, heq]
    decision := by
      intro nd' p hk
      have hbound : nd'.val ≤ st.nextId := by rw [hnid1] at nd'; omega
      have hk_inner : ((st.addNode nd hnd).2.descAt ⟨nd'.val, by
          simp [MAIDCompileState.addNode]; omega⟩).kind = .decision p := hk
      rcases Nat.lt_or_eq_of_le hbound with hlt | heq
      · rw [MAIDCompileState.addNode_descAt_old st nd hnd ⟨nd'.val, hlt⟩] at hk_inner
        simp only [RevealState.addPublicNode, RevealState.bindVar]
        rw [if_neg (show nd'.val ≠ rs.nextId from by rw [hcon.sync]; omega)]
        exact hcon.decision ⟨nd'.val, hlt⟩ p hk_inner
      · exfalso
        rw [show (⟨nd'.val, _⟩ : Fin (st.addNode nd hnd).2.nextId) =
            ⟨st.nextId, by simp [MAIDCompileState.addNode]⟩ from Fin.ext heq] at hk_inner
        rw [MAIDCompileState.addNode_descAt_new st nd hnd] at hk_inner
        exact hkind ⟨p, hk_inner⟩
    nodeOf_lt := by
      intro v nid hnid
      simp only [RevealState.addPublicNode, RevealState.bindVar] at hnid
      rw [hnid1]
      by_cases hv : v = x
      · subst hv; simp at hnid; have := hcon.sync; omega
      · simp [hv] at hnid
        exact Nat.lt_trans (hcon.nodeOf_lt v nid hnid) (Nat.lt_succ_self _)
    unset := by
      intro i hi
      simp only [RevealState.addPublicNode, RevealState.bindVar]
      rw [if_neg (show i ≠ rs.nextId from by rw [hcon.sync]; omega)]
      exact hcon.unset i (by omega) }

/-- RevealConsistent preserved by addNode(.decision) + addVar + addPrivateNode + bindVar. -/
private theorem revealConsistent_addDecision'
    {st : MAIDCompileState Player L B} {rs : RevealState}
    (hcon : RevealConsistent st rs)
    (nd : CompiledNode Player L B) {who : Player} (hkind : nd.kind = .decision who)
    (hnd : ∀ d ∈ nd.parents ∪ nd.obsParents, d < st.nextId)
    (x : VarId) (τ : BindTy Player L)
    (hdeps : ∀ d ∈ ({st.nextId} : Finset Nat), d < st.nextId + 1) :
    RevealConsistent
      ((st.addNode nd hnd).2.addVar x τ {st.nextId} hdeps)
      (rs.addPrivateNode.bindVar x rs.nextId) := by
  have hnid1 : ((st.addNode nd hnd).2.addVar x τ {st.nextId} hdeps).nextId
      = st.nextId + 1 := by simp [MAIDCompileState.addNode, MAIDCompileState.addVar]
  exact {
    sync := by simp [RevealState.addPrivateNode, RevealState.bindVar, hnid1, hcon.sync]
    chance := by
      intro nd' hk
      have hbound : nd'.val ≤ st.nextId := by rw [hnid1] at nd'; omega
      have hk_inner : ((st.addNode nd hnd).2.descAt ⟨nd'.val, by
          simp [MAIDCompileState.addNode]; omega⟩).kind = .chance := hk
      rcases Nat.lt_or_eq_of_le hbound with hlt | heq
      · rw [MAIDCompileState.addNode_descAt_old st nd hnd ⟨nd'.val, hlt⟩] at hk_inner
        exact hcon.chance ⟨nd'.val, hlt⟩ hk_inner
      · exfalso
        rw [show (⟨nd'.val, _⟩ : Fin (st.addNode nd hnd).2.nextId) =
            ⟨st.nextId, by simp [MAIDCompileState.addNode]⟩ from Fin.ext heq] at hk_inner
        rw [MAIDCompileState.addNode_descAt_new st nd hnd, hkind] at hk_inner
        simp [CompiledNode.kind] at hk_inner
    decision := by
      intro nd' p hk
      have hbound : nd'.val ≤ st.nextId := by rw [hnid1] at nd'; omega
      have hk_inner : ((st.addNode nd hnd).2.descAt ⟨nd'.val, by
          simp [MAIDCompileState.addNode]; omega⟩).kind = .decision p := hk
      rcases Nat.lt_or_eq_of_le hbound with hlt | heq
      · rw [MAIDCompileState.addNode_descAt_old st nd hnd ⟨nd'.val, hlt⟩] at hk_inner
        simp only [RevealState.addPrivateNode, RevealState.bindVar]
        exact hcon.decision ⟨nd'.val, hlt⟩ p hk_inner
      · simp only [RevealState.addPrivateNode, RevealState.bindVar]
        rw [hcon.unset nd'.val (by omega)]
        exact WithTop.coe_lt_top _
    nodeOf_lt := by
      intro v nid hnid
      simp only [RevealState.addPrivateNode, RevealState.bindVar] at hnid
      rw [hnid1]
      by_cases hv : v = x
      · subst hv; simp at hnid; have := hcon.sync; omega
      · simp [hv] at hnid
        exact Nat.lt_trans (hcon.nodeOf_lt v nid hnid) (Nat.lt_succ_self _)
    unset := by
      intro i hi
      simp only [RevealState.addPrivateNode, RevealState.bindVar]
      exact hcon.unset i (by omega) }

/-- RevealConsistent preserved by reveal (addVar + match/min on revealTime + aliasVar). -/
private theorem revealConsistent_reveal'
    {st : MAIDCompileState Player L B} {rs : RevealState}
    (hcon : RevealConsistent st rs)
    (y x : VarId) (b : L.Ty) (deps : Finset Nat)
    (hdeps : ∀ d ∈ deps, d < st.nextId) :
    RevealConsistent
      (st.addVar y (.pub b) deps hdeps)
      ((match rs.nodeOf x with
        | some nid =>
            { rs with revealTime := fun i =>
                if i = nid then min (↑rs.nextId) (rs.revealTime i) else rs.revealTime i }
        | none => rs).aliasVar y x) := by
  have hav_nid : (st.addVar y (.pub b) deps hdeps).nextId = st.nextId := rfl
  constructor
  · simp only [RevealState.aliasVar, MAIDCompileState.addVar]; split <;> simp [hcon.sync]
  · intro nd hk
    have h := hcon.chance nd hk
    simp only [RevealState.aliasVar]
    split
    · rename_i nid hx_eq; simp only; by_cases heq : nd.val = nid
      · rw [if_pos heq, h, min_eq_right]
        have h1 := hcon.nodeOf_lt x nid hx_eq
        have h2 : nd.val ≤ rs.nextId := by rw [hcon.sync]; omega
        exact WithTop.coe_le_coe.mpr h2
      · rw [if_neg heq]; exact h
    · exact h
  · intro nd p hk
    have h := hcon.decision nd p hk
    simp only [RevealState.aliasVar]
    split
    · rename_i nid hx_eq; simp only; by_cases heq : nd.val = nid
      · rw [if_pos heq]
        have h1 := hcon.nodeOf_lt x nid hx_eq
        have h2 : nd.val < rs.nextId := by rw [hcon.sync]; omega
        exact lt_min (WithTop.coe_lt_coe.mpr h2) h
      · rw [if_neg heq]; exact h
    · exact h
  · intro v nid hnid
    show nid < st.nextId
    simp only [RevealState.aliasVar] at hnid
    cases hx_eq : rs.nodeOf x with
    | none =>
        simp [hx_eq] at hnid
        by_cases hv : v = y
        · subst hv; simp at hnid
        · simp [hv] at hnid; exact hcon.nodeOf_lt v nid hnid
    | some nid' =>
        simp [hx_eq] at hnid
        by_cases hv : v = y
        · subst hv; simp at hnid; subst hnid; exact hcon.nodeOf_lt x nid' hx_eq
        · simp [hv] at hnid; exact hcon.nodeOf_lt v nid hnid
  · intro i hi
    rw [hav_nid] at hi
    simp only [RevealState.aliasVar]
    split
    · rename_i nid hx_eq; simp only
      rw [if_neg (show i ≠ nid from by have := hcon.nodeOf_lt x nid hx_eq; omega)]
      exact hcon.unset i hi
    · exact hcon.unset i hi

/-! ## Main consistency theorem -/

/-- `computeReveals` produces a state consistent with `ofProg`:
    chance nodes have revealTime = index, decision nodes have revealTime > index. -/
theorem computeReveals_consistent (B : MAIDBackend Player L)
    {Γ : VCtx Player L}
    (p : VegasCore Player L Γ) (hl : Legal p) (hd : NormalizedDists p)
    (ρ : RawNodeEnv L → VEnv (Player := Player) L Γ)
    (st₀ : MAIDCompileState Player L B) (rs₀ : RevealState)
    (hcon₀ : RevealConsistent st₀ rs₀) :
    RevealConsistent
      (MAIDCompileState.ofProg B p hl hd ρ st₀)
      (computeReveals B p rs₀) := by
  induction p generalizing st₀ rs₀ with
  | ret payoffs =>
      simp only [computeReveals, MAIDCompileState.ofProg]
      -- addUtilityNodes adds only utility nodes; foldl adds public nodes
      -- Induction on the player list with deps as a free parameter.
      letI := B.fintypePlayer
      suffices ∀ (players : List Player) (deps : Finset Nat)
          (ufn : Player → RawNodeEnv L → ℝ)
          (st : MAIDCompileState Player L B) (rs : RevealState)
          (hdeps : ∀ d ∈ deps, d < st.nextId)
          (hcon : RevealConsistent st rs),
          RevealConsistent (st.addUtilityNodes deps hdeps ufn players)
            (players.foldl (fun rs' _ => rs'.addPublicNode) rs) by
        exact this _ _ _ st₀ rs₀ _ hcon₀
      intro players
      induction players with
      | nil => intro _ _ st rs _ hcon; simpa [MAIDCompileState.addUtilityNodes]
      | cons who rest ih_ret =>
          intro deps ufn st rs hdeps hcon
          simp only [MAIDCompileState.addUtilityNodes, List.foldl_cons]
          let und : CompiledNode Player L B := .utility who deps (ufn who)
          have hund_deps : ∀ d ∈ und.parents ∪ und.obsParents, d < st.nextId := by
            intro d hd'; simp [und, CompiledNode.parents, CompiledNode.obsParents] at hd'
            exact hdeps d hd'
          exact ih_ret deps ufn (st.addNode und hund_deps).2 rs.addPublicNode
            (fun d hd => Nat.lt_trans (hdeps d hd) (Nat.lt_succ_self _))
            {
              sync := by simp [RevealState.addPublicNode, MAIDCompileState.addNode, hcon.sync]
              chance := by
                intro nd' hk
                have hbound : nd'.val ≤ st.nextId := by
                  have := nd'.isLt; simp [MAIDCompileState.addNode] at this; omega
                have hk_inner : ((st.addNode und hund_deps).2.descAt ⟨nd'.val, by
                    simp [MAIDCompileState.addNode]; omega⟩).kind = .chance := hk
                rcases Nat.lt_or_eq_of_le hbound with hlt | heq
                · rw [MAIDCompileState.addNode_descAt_old st und hund_deps ⟨nd'.val, hlt⟩] at hk_inner
                  have := hcon.chance ⟨nd'.val, hlt⟩ hk_inner
                  simp only [RevealState.addPublicNode]
                  rw [if_neg (show nd'.val ≠ rs.nextId from by rw [hcon.sync]; omega)]
                  exact this
                · exfalso
                  rw [show (⟨nd'.val, _⟩ : Fin _) = ⟨st.nextId, by simp [MAIDCompileState.addNode]⟩
                      from Fin.ext heq] at hk_inner
                  rw [MAIDCompileState.addNode_descAt_new st und hund_deps] at hk_inner
                  simp [und, CompiledNode.kind] at hk_inner
              decision := by
                intro nd' p hk
                have hbound : nd'.val ≤ st.nextId := by
                  have := nd'.isLt; simp [MAIDCompileState.addNode] at this; omega
                have hk_inner : ((st.addNode und hund_deps).2.descAt ⟨nd'.val, by
                    simp [MAIDCompileState.addNode]; omega⟩).kind = .decision p := hk
                rcases Nat.lt_or_eq_of_le hbound with hlt | heq
                · rw [MAIDCompileState.addNode_descAt_old st und hund_deps ⟨nd'.val, hlt⟩] at hk_inner
                  have := hcon.decision ⟨nd'.val, hlt⟩ p hk_inner
                  simp only [RevealState.addPublicNode]
                  rw [if_neg (show nd'.val ≠ rs.nextId from by rw [hcon.sync]; omega)]
                  exact this
                · exfalso
                  rw [show (⟨nd'.val, _⟩ : Fin _) = ⟨st.nextId, by simp [MAIDCompileState.addNode]⟩
                      from Fin.ext heq] at hk_inner
                  rw [MAIDCompileState.addNode_descAt_new st und hund_deps] at hk_inner
                  simp [und, CompiledNode.kind] at hk_inner
              nodeOf_lt := by
                intro v nid hnid
                simp only [RevealState.addPublicNode] at hnid
                show nid < st.nextId + 1
                exact Nat.lt_trans (hcon.nodeOf_lt v nid hnid) (Nat.lt_succ_self _)
              unset := by
                intro i hi
                have hi' : st.nextId + 1 ≤ i := by
                  simpa [MAIDCompileState.addNode] using hi
                simp only [RevealState.addPublicNode]
                rw [if_neg (show i ≠ rs.nextId from by rw [hcon.sync]; omega)]
                exact hcon.unset i (by omega)
            }
  | letExpr x e k ih =>
      simp only [computeReveals, MAIDCompileState.ofProg]
      exact ih hl hd _ _ _ ⟨hcon₀.sync, hcon₀.chance, hcon₀.decision, hcon₀.nodeOf_lt, hcon₀.unset⟩
  | sample x τ m D' k ih =>
      rename_i Γ'
      simp only [computeReveals, MAIDCompileState.ofProg]
      apply ih (hd := hd.2)
      -- Extract the chance node being added
      let cnd : CompiledNode Player L B :=
        .chance τ.base (st₀.ctxDeps Γ') (fun raw => L.evalDist D' (VEnv.eraseDistEnv τ m (ρ raw)))
          (fun raw => hd.1 (ρ raw))
      have hcnd_kind : cnd.kind = .chance := rfl
      -- The deps proof from the compiler
      have hcnd_deps : ∀ d ∈ cnd.parents ∪ cnd.obsParents, d < st₀.nextId := by
        intro d hd'; simp [cnd, CompiledNode.parents, CompiledNode.obsParents] at hd'
        exact st₀.depsOfVars_lt _ d hd'
      have hdeps : ∀ d ∈ ({st₀.nextId} : Finset Nat), d < st₀.nextId + 1 := by
        intro d hd'; simp at hd'; omega
      change RevealConsistent
        ((st₀.addNode cnd hcnd_deps).2.addVar x τ {st₀.nextId} hdeps)
        (rs₀.addPublicNode.bindVar x rs₀.nextId)
      have hnid1 : ((st₀.addNode cnd hcnd_deps).2.addVar x τ {st₀.nextId} hdeps).nextId
          = st₀.nextId + 1 := by simp [MAIDCompileState.addNode, MAIDCompileState.addVar]
      exact {
        sync := by simp [RevealState.addPublicNode, RevealState.bindVar, hnid1, hcon₀.sync]
        chance := by
          intro nd' hk
          have hbound : nd'.val ≤ st₀.nextId := by rw [hnid1] at nd'; omega
          have hk_inner : ((st₀.addNode cnd hcnd_deps).2.descAt ⟨nd'.val, by
              simp [MAIDCompileState.addNode]; omega⟩).kind = .chance := hk
          rcases Nat.lt_or_eq_of_le hbound with hlt | heq
          · rw [MAIDCompileState.addNode_descAt_old st₀ cnd hcnd_deps ⟨nd'.val, hlt⟩] at hk_inner
            have := hcon₀.chance ⟨nd'.val, hlt⟩ hk_inner
            simp only [RevealState.addPublicNode, RevealState.bindVar]
            rw [if_neg (show nd'.val ≠ rs₀.nextId from by rw [hcon₀.sync]; omega)]; exact this
          · simp only [RevealState.addPublicNode, RevealState.bindVar]
            rw [if_pos (show nd'.val = rs₀.nextId from by rw [hcon₀.sync]; omega)]
            simp [hcon₀.sync, heq]
        decision := by
          intro nd' p hk
          have hbound : nd'.val ≤ st₀.nextId := by rw [hnid1] at nd'; omega
          have hk_inner : ((st₀.addNode cnd hcnd_deps).2.descAt ⟨nd'.val, by
              simp [MAIDCompileState.addNode]; omega⟩).kind = .decision p := hk
          rcases Nat.lt_or_eq_of_le hbound with hlt | heq
          · rw [MAIDCompileState.addNode_descAt_old st₀ cnd hcnd_deps ⟨nd'.val, hlt⟩] at hk_inner
            have := hcon₀.decision ⟨nd'.val, hlt⟩ p hk_inner
            simp only [RevealState.addPublicNode, RevealState.bindVar]
            rw [if_neg (show nd'.val ≠ rs₀.nextId from by rw [hcon₀.sync]; omega)]; exact this
          · exfalso
            rw [show (⟨nd'.val, _⟩ : Fin (st₀.addNode cnd hcnd_deps).2.nextId) =
                ⟨st₀.nextId, by simp [MAIDCompileState.addNode]⟩ from Fin.ext heq] at hk_inner
            rw [MAIDCompileState.addNode_descAt_new st₀ cnd hcnd_deps] at hk_inner
            simp [cnd, CompiledNode.kind] at hk_inner
        nodeOf_lt := by
          intro v nid hnid
          simp only [RevealState.addPublicNode, RevealState.bindVar] at hnid
          rw [hnid1]
          by_cases hv : v = x
          · subst hv; simp at hnid; have := hcon₀.sync; omega
          · simp [hv] at hnid
            exact Nat.lt_trans (hcon₀.nodeOf_lt v nid hnid) (Nat.lt_succ_self _)
        unset := by
          intro i hi
          simp only [RevealState.addPublicNode, RevealState.bindVar]
          rw [if_neg (show i ≠ rs₀.nextId from by rw [hcon₀.sync]; omega)]
          exact hcon₀.unset i (by omega)
      }
  | commit x who R k ih =>
      rename_i Γ' b
      simp only [computeReveals, MAIDCompileState.ofProg]
      apply ih (hd := hd)
      let dnd : CompiledNode Player L B :=
        .decision b who (allValues B b) (allValues_ne_nil B b) (allValues_nodup B b) (st₀.viewDeps who Γ')
      have hdnd_kind : dnd.kind = .decision who := rfl
      have hdnd_deps : ∀ d ∈ dnd.parents ∪ dnd.obsParents, d < st₀.nextId := by
        intro d hd'; simp [dnd, CompiledNode.parents, CompiledNode.obsParents] at hd'
        exact st₀.depsOfVars_lt _ d hd'
      have hdeps : ∀ d ∈ ({st₀.nextId} : Finset Nat), d < st₀.nextId + 1 := by
        intro d hd'; simp at hd'; omega
      change RevealConsistent
        ((st₀.addNode dnd hdnd_deps).2.addVar x (.hidden who b) {st₀.nextId} hdeps)
        (rs₀.addPrivateNode.bindVar x rs₀.nextId)
      have hnid1 : ((st₀.addNode dnd hdnd_deps).2.addVar x (.hidden who b) {st₀.nextId} hdeps).nextId
          = st₀.nextId + 1 := by simp [MAIDCompileState.addNode, MAIDCompileState.addVar]
      exact {
        sync := by simp [RevealState.addPrivateNode, RevealState.bindVar, hnid1, hcon₀.sync]
        chance := by
          intro nd' hk
          have hbound : nd'.val ≤ st₀.nextId := by rw [hnid1] at nd'; omega
          have hk_inner : ((st₀.addNode dnd hdnd_deps).2.descAt ⟨nd'.val, by
              simp [MAIDCompileState.addNode]; omega⟩).kind = .chance := hk
          rcases Nat.lt_or_eq_of_le hbound with hlt | heq
          · rw [MAIDCompileState.addNode_descAt_old st₀ dnd hdnd_deps ⟨nd'.val, hlt⟩] at hk_inner
            exact hcon₀.chance ⟨nd'.val, hlt⟩ hk_inner
          · exfalso
            rw [show (⟨nd'.val, _⟩ : Fin (st₀.addNode dnd hdnd_deps).2.nextId) =
                ⟨st₀.nextId, by simp [MAIDCompileState.addNode]⟩ from Fin.ext heq] at hk_inner
            rw [MAIDCompileState.addNode_descAt_new st₀ dnd hdnd_deps] at hk_inner
            simp [dnd, CompiledNode.kind] at hk_inner
        decision := by
          intro nd' p hk
          have hbound : nd'.val ≤ st₀.nextId := by rw [hnid1] at nd'; omega
          have hk_inner : ((st₀.addNode dnd hdnd_deps).2.descAt ⟨nd'.val, by
              simp [MAIDCompileState.addNode]; omega⟩).kind = .decision p := hk
          rcases Nat.lt_or_eq_of_le hbound with hlt | heq
          · rw [MAIDCompileState.addNode_descAt_old st₀ dnd hdnd_deps ⟨nd'.val, hlt⟩] at hk_inner
            have := hcon₀.decision ⟨nd'.val, hlt⟩ p hk_inner
            simp only [RevealState.addPrivateNode, RevealState.bindVar]; exact this
          · simp only [RevealState.addPrivateNode, RevealState.bindVar]
            rw [hcon₀.unset nd'.val (by omega)]
            exact WithTop.coe_lt_top _
        nodeOf_lt := by
          intro v nid hnid
          simp only [RevealState.addPrivateNode, RevealState.bindVar] at hnid
          rw [hnid1]
          by_cases hv : v = x
          · subst hv; simp at hnid; have := hcon₀.sync; omega
          · simp [hv] at hnid
            exact Nat.lt_trans (hcon₀.nodeOf_lt v nid hnid) (Nat.lt_succ_self _)
        unset := by
          intro i hi
          simp only [RevealState.addPrivateNode, RevealState.bindVar]
          exact hcon₀.unset i (by omega)
      }
  | reveal y who x hx k ih =>
      simp only [computeReveals, MAIDCompileState.ofProg]
      apply ih (hd := hd)
      refine ⟨?_, ?_, ?_, ?_, ?_⟩
      · simp only [RevealState.aliasVar, MAIDCompileState.addVar]
        split <;> simp [hcon₀.sync]
      · intro nd hk
        have h := hcon₀.chance nd hk  -- addVar doesn't change descAt
        simp only [RevealState.aliasVar]
        split
        · rename_i nid hx_eq
          simp only; by_cases heq : nd.val = nid
          · rw [if_pos heq, h, min_eq_right]
            have h1 := hcon₀.nodeOf_lt x nid hx_eq
            have h2 : nd.val ≤ rs₀.nextId := by
              rw [hcon₀.sync]; omega
            exact WithTop.coe_le_coe.mpr h2
          · rw [if_neg heq]; exact h
        · exact h
      · intro nd p hk
        have h := hcon₀.decision nd p hk
        simp only [RevealState.aliasVar]
        split
        · rename_i nid hx_eq
          simp only; by_cases heq : nd.val = nid
          · rw [if_pos heq]
            have h1 := hcon₀.nodeOf_lt x nid hx_eq
            have h2 : nd.val < rs₀.nextId := by rw [hcon₀.sync]; omega
            exact lt_min (WithTop.coe_lt_coe.mpr h2) h
          · rw [if_neg heq]; exact h
        · exact h
      · intro v nid hnid
        show nid < st₀.nextId
        simp only [RevealState.aliasVar] at hnid
        cases hx_eq : rs₀.nodeOf x with
        | none =>
            simp [hx_eq] at hnid
            by_cases hv : v = y
            · subst hv; simp at hnid
            · simp [hv] at hnid; exact hcon₀.nodeOf_lt v nid hnid
        | some nid' =>
            simp [hx_eq] at hnid
            by_cases hv : v = y
            · subst hv; simp at hnid; subst hnid
              exact hcon₀.nodeOf_lt x nid' hx_eq
            · simp [hv] at hnid; exact hcon₀.nodeOf_lt v nid hnid
      · -- unset
        intro i hi
        simp only [RevealState.aliasVar, MAIDCompileState.addVar] at hi ⊢
        cases hx_eq : rs₀.nodeOf x with
        | none => simp [hx_eq]; exact hcon₀.unset i hi
        | some nid' =>
            simp [hx_eq]
            rw [if_neg (show i ≠ nid' from by
              have := hcon₀.nodeOf_lt x nid' hx_eq; omega)]
            exact hcon₀.unset i hi

/-- If `i ∈ depsOfVars xs`, then `i ∈ lookupDeps x` for some `x ∈ xs`. -/
private theorem mem_depsOfVars_iff (st : MAIDCompileState Player L B)
    (xs : List VarId) (i : Nat) :
    i ∈ st.depsOfVars xs ↔ ∃ x ∈ xs, i ∈ st.lookupDeps x := by
  induction xs with
  | nil => simp [MAIDCompileState.depsOfVars]
  | cons y ys ih =>
      simp only [MAIDCompileState.depsOfVars, Finset.mem_union, ih, List.mem_cons]
      constructor
      · rintro (h | ⟨x, hx, hm⟩)
        · exact ⟨y, Or.inl rfl, h⟩
        · exact ⟨x, Or.inr hx, hm⟩
      · rintro ⟨x, (rfl | hx), hm⟩
        · left; exact hm
        · right; exact ⟨x, hx, hm⟩

/-- hprev transfer: old decision nodes' parent visibility is preserved through
    addNode (non-decision) + addPublicNode. -/
private theorem hprev_transfer_addNode
    {st : MAIDCompileState Player L B} {rs : RevealState}
    (hcon : RevealConsistent st rs)
    (nd : CompiledNode Player L B) (hkind : ¬ ∃ p, nd.kind = .decision p)
    (hnd : ∀ d ∈ nd.parents ∪ nd.obsParents, d < st.nextId)
    (hp : ∀ (d : Fin st.nextId) (pw : Player),
      (st.descAt d).kind = .decision pw →
      ∀ (i : Nat) (hi : i ∈ (st.descAt d).parents),
        rs.revealTime i ≤ ↑d.val ∨ (st.descAt ⟨i, Nat.lt_trans (st.descAt_parent_lt d hi) d.2⟩).kind = .decision pw) :
    ∀ (d : Fin (st.addNode nd hnd).2.nextId) (pw : Player),
      ((st.addNode nd hnd).2.descAt d).kind = .decision pw →
      ∀ (i : Nat) (hi : i ∈ ((st.addNode nd hnd).2.descAt d).parents),
        rs.addPublicNode.revealTime i ≤ ↑d.val ∨
          ((st.addNode nd hnd).2.descAt ⟨i, Nat.lt_trans ((st.addNode nd hnd).2.descAt_parent_lt d hi) d.2⟩).kind =
            .decision pw := by
  intro d' pw' hk' i hi'
  have hbound : d'.val ≤ st.nextId := by
    have := d'.isLt; simp [MAIDCompileState.addNode] at this; omega
  have hk_inner : ((st.addNode nd hnd).2.descAt ⟨d'.val, by
      simp [MAIDCompileState.addNode]; omega⟩).kind = .decision pw' := hk'
  rcases Nat.lt_or_eq_of_le hbound with hlt | heq
  · rw [MAIDCompileState.addNode_descAt_old st nd hnd ⟨d'.val, hlt⟩] at hk_inner
    have hi_inner : i ∈ (st.descAt ⟨d'.val, hlt⟩).parents := by
      have : i ∈ ((st.addNode nd hnd).2.descAt ⟨d'.val, by simp [MAIDCompileState.addNode]; omega⟩).parents := hi'
      rwa [MAIDCompileState.addNode_descAt_old st nd hnd ⟨d'.val, hlt⟩] at this
    rcases hp ⟨d'.val, hlt⟩ pw' hk_inner i hi_inner with h | h
    · left; simp only [RevealState.addPublicNode]
      rw [if_neg (show i ≠ rs.nextId from by
        rw [hcon.sync]; have := st.descAt_parent_lt ⟨d'.val, hlt⟩ hi_inner; omega)]
      exact h
    · right
      show ((st.addNode nd hnd).2.descAt ⟨i, _⟩).kind = _
      rw [MAIDCompileState.addNode_descAt_old st nd hnd
        ⟨i, by have := st.descAt_parent_lt ⟨d'.val, hlt⟩ hi_inner; omega⟩]
      exact h
  · exfalso
    rw [show (⟨d'.val, _⟩ : Fin (st.addNode nd hnd).2.nextId) =
        ⟨st.nextId, by simp [MAIDCompileState.addNode]⟩ from Fin.ext heq] at hk_inner
    rw [MAIDCompileState.addNode_descAt_new st nd hnd] at hk_inner
    exact hkind ⟨pw', hk_inner⟩

/-- Visible-variable-deps invariant: for each variable visible to a player,
    its lookupDeps point to nodes that are either public or same-player decisions. -/
def VarVisible {B : MAIDBackend Player L}
    (Γ : VCtx Player L) (st : MAIDCompileState Player L B) (rs : RevealState) : Prop :=
  ∀ (who : Player) (y : VarId) (σ : BindTy Player L),
    (y, σ) ∈ viewVCtx who Γ →
    ∀ (i : Nat) (hi : i ∈ st.lookupDeps y),
      rs.revealTime i ≤ ↑st.nextId ∨
        (st.descAt ⟨i, st.lookupDeps_lt y i hi⟩).kind = .decision who

/-- VarVisible extension for adding a pub variable (letExpr case). -/
private theorem varVisible_addVar_pub
    (st : MAIDCompileState Player L B) (rs : RevealState)
    (x : VarId) (b : L.Ty) (Γ : VCtx Player L)
    (hvars : st.VarsSubCtx Γ) (hfresh_x : Fresh x Γ)
    (deps : Finset Nat) (hdeps : ∀ d ∈ deps, d < st.nextId)
    (hvar : VarVisible Γ st rs)
    (hdeps_sub : deps ⊆ st.pubCtxDeps Γ) :
    VarVisible ((x, .pub b) :: Γ) (st.addVar x (.pub b) deps hdeps) rs := by
  intro who y σ hy i hi
  unfold viewVCtx at hy; simp [canSee] at hy
  rcases hy with ⟨rfl, rfl⟩ | hy
  · rw [st.lookupDeps_addVar_eq_self_of_fresh y _ _ _ (fun hm => hfresh_x (hvars y hm))] at hi
    have hi_pub := hdeps_sub hi
    rw [MAIDCompileState.pubCtxDeps] at hi_pub
    obtain ⟨z, hz_mem, hz_dep⟩ := (mem_depsOfVars_iff st _ i).mp hi_pub
    have hz_view := erasePubVCtx_map_fst_sub_viewVCtx (Γ := Γ) (who := who) z hz_mem
    obtain ⟨⟨z', σ'⟩, hzs_mem, hzs_fst⟩ := List.mem_map.mp hz_view
    simp at hzs_fst; subst hzs_fst
    exact hvar who z' σ' hzs_mem i hz_dep
  · rw [st.lookupDeps_addVar_eq_of_ne x _ _ _ (by
      intro heq; subst heq
      exact hfresh_x (viewVCtx_map_fst_sub (p := who) (Γ := Γ)
        (List.mem_map.mpr ⟨(y, σ), hy, rfl⟩)))] at hi
    exact hvar who y σ hy i hi

/-- VarVisible extension for addNode(.chance)+addVar (sample case).
-/
private theorem varVisible_addNode_chance_addVar
    (st : MAIDCompileState Player L B) (rs : RevealState) (hcon : RevealConsistent st rs)
    (nd : CompiledNode Player L B) (_hnd_kind : nd.kind = .chance)
    (hnd : ∀ d ∈ nd.parents ∪ nd.obsParents, d < st.nextId)
    (x : VarId) (τ : BindTy Player L) (Γ : VCtx Player L)
    (hvars : st.VarsSubCtx Γ) (hfresh_x : Fresh x Γ)
    (hdeps : ∀ d ∈ ({st.nextId} : Finset Nat), d < st.nextId + 1)
    (hvar : VarVisible Γ st rs) :
    VarVisible ((x, τ) :: Γ) ((st.addNode nd hnd).2.addVar x τ {st.nextId} hdeps)
      (rs.addPublicNode.bindVar x rs.nextId) := by
  have hnid : ((st.addNode nd hnd).2.addVar x τ {st.nextId} hdeps).nextId = st.nextId + 1 := by
    simp [MAIDCompileState.addNode, MAIDCompileState.addVar]
  intro who y σ hy i hi
  by_cases heq : y = x
  · subst heq
    rw [(st.addNode nd hnd).2.lookupDeps_addVar_eq_self_of_fresh y _ _ _
      (fun hm => hfresh_x ((st.VarsSubCtx_addNode hvars nd hnd) y hm))] at hi
    simp at hi; subst hi
    left; simp only [RevealState.addPublicNode, RevealState.bindVar]
    rw [if_pos hcon.sync.symm, hnid]
    exact_mod_cast (show rs.nextId ≤ st.nextId + 1 by have := hcon.sync; omega)
  · rw [(st.addNode nd hnd).2.lookupDeps_addVar_eq_of_ne x _ _ _ heq] at hi
    have hy' : (y, σ) ∈ viewVCtx who Γ := by
      unfold viewVCtx at hy; split at hy
      · simp only [List.mem_cons, Prod.mk.injEq] at hy
        rcases hy with ⟨rfl, _⟩ | hy
        · exact absurd rfl heq
        · exact hy
      · exact hy
    have hilt : i < st.nextId := st.lookupDeps_lt y i hi
    rcases hvar who y σ hy' i hi with h | h
    · left; simp only [RevealState.addPublicNode, RevealState.bindVar]
      rw [if_neg (show i ≠ rs.nextId from by rw [hcon.sync]; omega)]
      rw [hnid]
      exact le_trans h (WithTop.coe_le_coe.mpr (Nat.le_succ _))
    · right
      show ((st.addNode nd hnd).2.descAt ⟨i, by simp [MAIDCompileState.addNode]; omega⟩).kind = _
      rw [MAIDCompileState.addNode_descAt_old st nd hnd ⟨i, hilt⟩]; exact h

/-- VarVisible extension for addNode(.decision)+addVar (commit case).
    Proof verified in run_code. -/
private theorem varVisible_addNode_decision_addVar
    (st : MAIDCompileState Player L B) (rs : RevealState) (_hcon : RevealConsistent st rs)
    (nd : CompiledNode Player L B) (who : Player) (_hnd_kind : nd.kind = .decision who)
    (hnd : ∀ d ∈ nd.parents ∪ nd.obsParents, d < st.nextId)
    (x : VarId) (b : L.Ty) (Γ : VCtx Player L)
    (_hvars : st.VarsSubCtx Γ) (_hfresh_x : Fresh x Γ)
    (hdeps : ∀ d ∈ ({st.nextId} : Finset Nat), d < st.nextId + 1)
    (_hvar : VarVisible Γ st rs) :
    VarVisible ((x, .hidden who b) :: Γ)
      ((st.addNode nd hnd).2.addVar x (.hidden who b) {st.nextId} hdeps)
      (rs.addPrivateNode.bindVar x rs.nextId) := by
  have hnid : ((st.addNode nd hnd).2.addVar x (.hidden who b) {st.nextId} hdeps).nextId =
      st.nextId + 1 := by simp [MAIDCompileState.addNode, MAIDCompileState.addVar]
  intro p y σ hy i hi
  -- canSee dispatch: p = who sees x, p ≠ who doesn't
  by_cases hp : p = who
  · subst hp -- p replaces who
    by_cases heq : y = x
    · subst heq
      rw [(st.addNode nd hnd).2.lookupDeps_addVar_eq_self_of_fresh y _ _ _
        (fun hm => _hfresh_x ((st.VarsSubCtx_addNode _hvars nd hnd) y hm))] at hi
      simp at hi; subst hi
      right
      show ((st.addNode nd hnd).2.descAt ⟨st.nextId, by simp [MAIDCompileState.addNode]⟩).kind = _
      rw [MAIDCompileState.addNode_descAt_new st nd hnd]; exact _hnd_kind
    · rw [(st.addNode nd hnd).2.lookupDeps_addVar_eq_of_ne x _ _ _ heq] at hi
      have hy' : (y, σ) ∈ viewVCtx p Γ := by
        unfold viewVCtx at hy; simp [canSee] at hy; rcases hy with ⟨rfl, _⟩ | hy
        · exact absurd rfl heq
        · exact hy
      have hilt : i < st.nextId := st.lookupDeps_lt y i hi
      rcases _hvar p y σ hy' i hi with h | h
      · left; simp only [RevealState.addPrivateNode, RevealState.bindVar]
        rw [hnid]; exact le_trans h (WithTop.coe_le_coe.mpr (Nat.le_succ _))
      · right
        show ((st.addNode nd hnd).2.descAt ⟨i, by simp [MAIDCompileState.addNode]; omega⟩).kind = _
        rw [MAIDCompileState.addNode_descAt_old st nd hnd ⟨i, hilt⟩]; exact h
  · -- p ≠ who: x not visible
    have hy' : (y, σ) ∈ viewVCtx p Γ := by
      unfold viewVCtx at hy; simp [canSee, hp] at hy; exact hy
    have hne : y ≠ x := by
      intro heq; subst heq
      exact _hfresh_x (viewVCtx_map_fst_sub (p := p) (Γ := Γ)
        (List.mem_map.mpr ⟨(y, σ), hy', rfl⟩))
    rw [(st.addNode nd hnd).2.lookupDeps_addVar_eq_of_ne x _ _ _ hne] at hi
    have hilt : i < st.nextId := st.lookupDeps_lt y i hi
    rcases _hvar p y σ hy' i hi with h | h
    · left; simp only [RevealState.addPrivateNode, RevealState.bindVar]
      rw [hnid]; exact le_trans h (WithTop.coe_le_coe.mpr (Nat.le_succ _))
    · right
      show ((st.addNode nd hnd).2.descAt ⟨i, by simp [MAIDCompileState.addNode]; omega⟩).kind = _
      rw [MAIDCompileState.addNode_descAt_old st nd hnd ⟨i, hilt⟩]; exact h

/-- Decision parents in the compiled MAID are all visible to the player
    (the factored-observation property). -/
theorem computeReveals_parents_visible (B : MAIDBackend Player L)
    {Γ : VCtx Player L}
    (p : VegasCore Player L Γ) (hl : Legal p) (hd : NormalizedDists p)
    (hfresh : FreshBindings p)
    (ρ : RawNodeEnv L → VEnv (Player := Player) L Γ)
    (st₀ : MAIDCompileState Player L B) (rs₀ : RevealState)
    (hcon₀ : RevealConsistent st₀ rs₀)
    (hvars : st₀.VarsSubCtx Γ)
    -- The property holds for all decision nodes already in st₀
    (hprev : ∀ (d : Fin st₀.nextId) (pw : Player),
      (st₀.descAt d).kind = .decision pw →
      ∀ (i : Nat) (hi : i ∈ (st₀.descAt d).parents),
        rs₀.revealTime i ≤ ↑d.val ∨
          (st₀.descAt ⟨i, Nat.lt_trans (st₀.descAt_parent_lt d hi) d.2⟩).kind = .decision pw)
    -- VarVisible: visible deps are visible nodes (needed for commit case)
    (hvar₀ : VarVisible Γ st₀ rs₀)
    -- DepsTracked: nodeOf y = some nid → lookupDeps y ⊆ {nid}
    (hdt : ∀ y nid, rs₀.nodeOf y = some nid → st₀.lookupDeps y ⊆ {nid})
    -- HiddenHasNodeOf: hidden vars have nodeOf bindings
    (hhn : ∀ y who b, VHasVar (L := L) Γ y (.hidden who b) → rs₀.nodeOf y ≠ none)
    -- NodeOfSubCtx: nodeOf only set for vars in context
    (hnsc : ∀ y nid, rs₀.nodeOf y = some nid → y ∈ Γ.map Prod.fst) :
    let st := MAIDCompileState.ofProg B p hl hd ρ st₀
    let rs := computeReveals B p rs₀
    ∀ (d : Fin st.nextId) (p : Player),
      (st.descAt d).kind = .decision p →
      ∀ (i : Nat) (hi : i ∈ (st.descAt d).parents),
        rs.revealTime i ≤ ↑d.val ∨
          (∃ q, (st.descAt ⟨i, Nat.lt_trans (st.descAt_parent_lt d hi) d.2⟩).kind =
            .decision q ∧ q = p) := by
  induction p generalizing st₀ rs₀ with
  | ret payoffs =>
      simp only [computeReveals, MAIDCompileState.ofProg]
      letI := B.fintypePlayer
      suffices ∀ (players : List Player) (deps : Finset Nat)
          (ufn : Player → RawNodeEnv L → ℝ)
          (st : MAIDCompileState Player L B) (rs : RevealState)
          (hdeps : ∀ d ∈ deps, d < st.nextId) (hcon : RevealConsistent st rs)
          (hp : ∀ (d : Fin st.nextId) (pw : Player),
            (st.descAt d).kind = .decision pw →
            ∀ (i : Nat) (hi : i ∈ (st.descAt d).parents),
              rs.revealTime i ≤ ↑d.val ∨ (st.descAt ⟨i, Nat.lt_trans (st.descAt_parent_lt d hi) d.2⟩).kind = .decision pw),
          ∀ (d : Fin (st.addUtilityNodes deps hdeps ufn players).nextId) (p : Player),
            ((st.addUtilityNodes deps hdeps ufn players).descAt d).kind = .decision p →
            ∀ (i : Nat) (hi : i ∈ ((st.addUtilityNodes deps hdeps ufn players).descAt d).parents),
              (players.foldl (fun rs' _ => rs'.addPublicNode) rs).revealTime i ≤ ↑d.val ∨
                ∃ q, ((st.addUtilityNodes deps hdeps ufn players).descAt
                  ⟨i, Nat.lt_trans ((st.addUtilityNodes deps hdeps ufn players).descAt_parent_lt d hi) d.2⟩).kind =
                    .decision q ∧ q = p by
        exact this _ _ _ st₀ rs₀ _ hcon₀ hprev
      intro players
      induction players with
      | nil => intro _ _ st rs _ _ hp; simpa [MAIDCompileState.addUtilityNodes]
      | cons pw rest ih =>
          intro deps ufn st rs hdeps hcon hp
          simp only [MAIDCompileState.addUtilityNodes, List.foldl_cons]
          let und : CompiledNode Player L B := .utility pw deps (ufn pw)
          have hund_deps : ∀ d ∈ und.parents ∪ und.obsParents, d < st.nextId := by
            intro d hd'; simp [und, CompiledNode.parents, CompiledNode.obsParents] at hd'
            exact hdeps d hd'
          exact ih deps ufn _ _ (fun d hd => Nat.lt_trans (hdeps d hd) (Nat.lt_succ_self _))
            (revealConsistent_addNode' hcon und
              (by intro ⟨_, h⟩; simp [und, CompiledNode.kind] at h) hund_deps)
            (by -- hp for intermediate: old decisions preserved
                intro d' pw' hk' i hi'
                have hbound : d'.val ≤ st.nextId := by
                  have := d'.isLt; simp [MAIDCompileState.addNode] at this; omega
                have hk_inner : ((st.addNode und hund_deps).2.descAt ⟨d'.val, by
                    simp [MAIDCompileState.addNode]; omega⟩).kind = .decision pw' := hk'
                rcases Nat.lt_or_eq_of_le hbound with hlt | heq
                · -- old decision node
                  rw [MAIDCompileState.addNode_descAt_old st und hund_deps ⟨d'.val, hlt⟩] at hk_inner
                  have hi_inner : i ∈ (st.descAt ⟨d'.val, hlt⟩).parents := by
                    have := hi'; rw [MAIDCompileState.addNode_descAt_old st und hund_deps ⟨d'.val, hlt⟩] at this
                    exact this
                  rcases hp ⟨d'.val, hlt⟩ pw' hk_inner i hi_inner with h | h
                  · left
                    simp only [RevealState.addPublicNode]
                    rw [if_neg (show i ≠ rs.nextId from by
                      rw [hcon.sync]
                      have := st.descAt_parent_lt ⟨d'.val, hlt⟩ hi_inner
                      omega)]
                    exact h
                  · right
                    show ((st.addNode und hund_deps).2.descAt ⟨i, _⟩).kind = _
                    rw [MAIDCompileState.addNode_descAt_old st und hund_deps
                      ⟨i, by have := st.descAt_parent_lt ⟨d'.val, hlt⟩ hi_inner; omega⟩]
                    exact h
                · -- new utility node: not decision
                  exfalso
                  rw [show (⟨d'.val, _⟩ : Fin _) = ⟨st.nextId, by simp [MAIDCompileState.addNode]⟩
                      from Fin.ext heq] at hk_inner
                  rw [MAIDCompileState.addNode_descAt_new st und hund_deps] at hk_inner
                  simp [und, CompiledNode.kind] at hk_inner)
  | letExpr x e k ih =>
      simp only [computeReveals, MAIDCompileState.ofProg]
      exact ih hl hd hfresh.2 _ _ _
        ⟨hcon₀.sync, hcon₀.chance, hcon₀.decision, hcon₀.nodeOf_lt, hcon₀.unset⟩
        (st₀.VarsSubCtx_addVar hvars x _ _ _ hfresh.1) hprev
        (varVisible_addVar_pub st₀ rs₀ x _ _ hvars hfresh.1 _ _ hvar₀ (Finset.Subset.refl _))
        (by intro z nid hnid
            by_cases hz : z = x
            · subst hz; exact absurd (hnsc z nid hnid) hfresh.1
            · rw [st₀.lookupDeps_addVar_eq_of_ne x _ _ _ hz]; exact hdt z nid hnid)
        (by -- hhn: new pub var x is not hidden; old hidden vars: nodeOf unchanged
            intro z who' b' hv; cases hv with
            | there hv' => exact hhn z who' b' hv')
        (by -- hnsc: nodeOf only in context; addVar extends context
            intro z nid hnid
            simp only [List.map_cons, List.mem_cons]
            right; exact hnsc z nid hnid)
  | sample x τ m D' k ih =>
      rename_i Γ'
      simp only [computeReveals, MAIDCompileState.ofProg]
      let cnd : CompiledNode Player L B :=
        .chance τ.base (st₀.ctxDeps Γ') (fun raw => L.evalDist D' (VEnv.eraseDistEnv τ m (ρ raw)))
          (fun raw => hd.1 (ρ raw))
      have hcnd_deps : ∀ d ∈ cnd.parents ∪ cnd.obsParents, d < st₀.nextId := by
        intro d hd'; simp [cnd, CompiledNode.parents, CompiledNode.obsParents] at hd'
        exact st₀.depsOfVars_lt _ d hd'
      have hdeps : ∀ d ∈ ({st₀.nextId} : Finset Nat), d < st₀.nextId + 1 := by
        intro d hd'; simp at hd'; omega
      exact ih hl hd.2 hfresh.2 _ _ _
        (revealConsistent_addChance' hcon₀ cnd
          (by intro ⟨_, h⟩; simp [cnd, CompiledNode.kind] at h) hcnd_deps x τ hdeps)
        ((st₀.addNode cnd hcnd_deps).2.VarsSubCtx_addVar (st₀.VarsSubCtx_addNode hvars cnd hcnd_deps)
          x _ _ _ hfresh.1)
        (hprev_transfer_addNode hcon₀ cnd
          (by intro ⟨_, h⟩; simp [cnd, CompiledNode.kind] at h) hcnd_deps hprev)
        (varVisible_addNode_chance_addVar st₀ rs₀ hcon₀ cnd
          (by simp [cnd, CompiledNode.kind]) hcnd_deps x τ _ hvars hfresh.1 hdeps hvar₀)
        (by -- hdt: x→{nextId}⊆{nextId}, y≠x → from hdt
            intro z nid hnid
            simp only [RevealState.addPublicNode, RevealState.bindVar] at hnid
            by_cases hz : z = x
            · subst hz; simp at hnid; subst hnid
              rw [(st₀.addNode cnd hcnd_deps).2.lookupDeps_addVar_eq_self_of_fresh z _ _ _
                (fun hm => hfresh.1 ((st₀.VarsSubCtx_addNode hvars cnd hcnd_deps) z hm))]
              rw [hcon₀.sync]
            · simp [hz] at hnid
              rw [(st₀.addNode cnd hcnd_deps).2.lookupDeps_addVar_eq_of_ne x _ _ _ hz]
              exact hdt z nid hnid)
        (by -- hhn: hidden vars have nodeOf; new var x: bindVar sets it
            intro z who' b' hv
            simp only [RevealState.addPublicNode, RevealState.bindVar]
            cases hv with
            | here => simp -- z = x: nodeOf x = some nextId ≠ none
            | there hv' =>
                by_cases hz : z = x
                · subst hz; simp
                · simp [hz]; exact hhn z who' b' hv')
        (by -- hnsc: x in new context; old vars via hnsc
            intro z nid hnid
            simp only [RevealState.addPublicNode, RevealState.bindVar] at hnid
            simp only [List.map_cons, List.mem_cons]
            by_cases hz : z = x
            · left; exact hz
            · right; simp [hz] at hnid; exact hnsc z nid hnid)
  | commit x who R k ih =>
      -- THE key case: new decision node + IH for continuation.
      -- New node's parents = viewDeps who Γ'. By hvar₀, each dep has
      -- revealTime ≤ nextId = d.val or is who's decision. ✓
      -- Old nodes: preserved by addNode, revealTime only decreases. ✓
      rename_i Γ' b
      simp only [computeReveals, MAIDCompileState.ofProg]
      let dnd : CompiledNode Player L B :=
        .decision b who (allValues B b) (allValues_ne_nil B b) (allValues_nodup B b) (st₀.viewDeps who Γ')
      have hdnd_deps : ∀ d ∈ dnd.parents ∪ dnd.obsParents, d < st₀.nextId := by
        intro d hd'; simp [dnd, CompiledNode.parents, CompiledNode.obsParents] at hd'
        exact st₀.depsOfVars_lt _ d hd'
      have hdeps : ∀ d ∈ ({st₀.nextId} : Finset Nat), d < st₀.nextId + 1 := by
        intro d hd'; simp at hd'; omega
      exact ih hl.2 hd hfresh.2 _ _ _
        (revealConsistent_addDecision' hcon₀ dnd rfl hdnd_deps x (.hidden who b) hdeps)
        ((st₀.addNode dnd hdnd_deps).2.VarsSubCtx_addVar (st₀.VarsSubCtx_addNode hvars dnd hdnd_deps)
          x _ _ _ hfresh.1)
        (by -- hprev: old decisions + NEW decision
            intro d' pw' hk' i hi'
            have hbound : d'.val ≤ st₀.nextId := by
              have := d'.isLt; simp [MAIDCompileState.addNode, MAIDCompileState.addVar] at this; omega
            rcases Nat.lt_or_eq_of_le hbound with hlt | heq
            · -- OLD decision node
              have hk_old : (st₀.descAt ⟨d'.val, hlt⟩).kind = .decision pw' := by
                rw [← MAIDCompileState.addNode_descAt_old st₀ dnd hdnd_deps ⟨d'.val, hlt⟩]; exact hk'
              have hi_old : i ∈ (st₀.descAt ⟨d'.val, hlt⟩).parents := by
                rw [← MAIDCompileState.addNode_descAt_old st₀ dnd hdnd_deps ⟨d'.val, hlt⟩]; exact hi'
              have hilt : i < st₀.nextId := Nat.lt_trans (st₀.descAt_parent_lt ⟨d'.val, hlt⟩ hi_old) (by omega)
              rcases hprev ⟨d'.val, hlt⟩ pw' hk_old i hi_old with h | h
              · left; simp only [RevealState.addPrivateNode, RevealState.bindVar]; exact h
              · right
                have : ((st₀.addNode dnd hdnd_deps).2.addVar x (.hidden who b) {st₀.nextId} hdeps).descAt
                    ⟨i, by simp [MAIDCompileState.addNode, MAIDCompileState.addVar]; omega⟩ =
                    st₀.descAt ⟨i, hilt⟩ := by
                  show (st₀.addNode dnd hdnd_deps).2.descAt ⟨i, _⟩ = _
                  exact MAIDCompileState.addNode_descAt_old st₀ dnd hdnd_deps ⟨i, hilt⟩
                rw [this]; exact h
            · -- NEW decision: convert d' → st₀.nextId, extract pw'=who and parents=viewDeps
              have hdesc_new : (st₀.addNode dnd hdnd_deps).2.descAt
                  ⟨st₀.nextId, by simp [MAIDCompileState.addNode]⟩ = dnd :=
                MAIDCompileState.addNode_descAt_new st₀ dnd hdnd_deps
              -- Convert via show + hdesc_new
              have hpw : pw' = who := by
                have : dnd.kind = .decision pw' := by
                  have h1 := hk'; rw [show d' = (⟨st₀.nextId, by
                    simp [MAIDCompileState.addNode, MAIDCompileState.addVar]⟩ : Fin _) from Fin.ext heq] at h1
                  change ((st₀.addNode dnd hdnd_deps).2.descAt ⟨st₀.nextId, _⟩).kind = _ at h1
                  rw [hdesc_new] at h1; exact h1
                simp only [dnd, CompiledNode.kind, NodeKind.decision.injEq] at this; exact this.symm
              subst hpw
              have hi_dnd : i ∈ dnd.parents := by
                have h1 := hi'; rw [show d' = (⟨st₀.nextId, by
                  simp [MAIDCompileState.addNode, MAIDCompileState.addVar]⟩ : Fin _) from Fin.ext heq] at h1
                change i ∈ ((st₀.addNode dnd hdnd_deps).2.descAt ⟨st₀.nextId, _⟩).parents at h1
                rw [hdesc_new] at h1; exact h1
              have hi_vd : i ∈ st₀.viewDeps pw' Γ' := by
                simp [dnd, CompiledNode.parents] at hi_dnd; exact hi_dnd
              rw [MAIDCompileState.viewDeps] at hi_vd
              obtain ⟨y, hy_mem, hy_dep⟩ := (mem_depsOfVars_iff st₀ _ i).mp hi_vd
              obtain ⟨⟨y', σ⟩, hys_mem, hys_fst⟩ := List.mem_map.mp hy_mem
              simp at hys_fst; subst hys_fst
              rcases hvar₀ pw' y' σ hys_mem i hy_dep with h | h
              · left; simp only [RevealState.addPrivateNode, RevealState.bindVar]
                exact le_trans h (by rw [heq])
              · right
                have hilt : i < st₀.nextId := st₀.depsOfVars_lt _ i hi_vd
                have : ((st₀.addNode dnd hdnd_deps).2.addVar x (.hidden pw' b) {st₀.nextId} hdeps).descAt
                    ⟨i, by simp [MAIDCompileState.addNode, MAIDCompileState.addVar]; omega⟩ =
                    st₀.descAt ⟨i, hilt⟩ := by
                  show (st₀.addNode dnd hdnd_deps).2.descAt ⟨i, _⟩ = _
                  exact MAIDCompileState.addNode_descAt_old st₀ dnd hdnd_deps ⟨i, hilt⟩
                rw [this]; exact h)
        (varVisible_addNode_decision_addVar st₀ rs₀ hcon₀ dnd who
          rfl hdnd_deps x b _ hvars hfresh.1 hdeps hvar₀)
        (by intro z nid hnid
            simp only [RevealState.addPrivateNode, RevealState.bindVar] at hnid
            by_cases hz : z = x
            · subst hz; simp at hnid; subst hnid
              rw [(st₀.addNode dnd hdnd_deps).2.lookupDeps_addVar_eq_self_of_fresh z _ _ _
                (fun hm => hfresh.1 ((st₀.VarsSubCtx_addNode hvars dnd hdnd_deps) z hm))]
              rw [hcon₀.sync]
            · simp [hz] at hnid
              rw [(st₀.addNode dnd hdnd_deps).2.lookupDeps_addVar_eq_of_ne x _ _ _ hz]
              exact hdt z nid hnid)
        (by intro z who' b' hv
            simp only [RevealState.addPrivateNode, RevealState.bindVar]
            cases hv with
            | here => simp
            | there hv' =>
                by_cases hz : z = x
                · subst hz; simp
                · simp [hz]; exact hhn z who' b' hv')
        (by intro z nid hnid
            simp only [RevealState.addPrivateNode, RevealState.bindVar] at hnid
            simp only [List.map_cons, List.mem_cons]
            by_cases hz : z = x
            · left; exact hz
            · right; simp [hz] at hnid; exact hnsc z nid hnid)
  | reveal y who x hx k ih =>
      simp only [computeReveals, MAIDCompileState.ofProg]
      exact ih hl hd hfresh.2 _ _ _
        (revealConsistent_reveal' hcon₀ y x _ _ _)
        (st₀.VarsSubCtx_addVar hvars y _ _ _ hfresh.1)
        (by -- hprev: addVar doesn't change descAt, reveal only decreases revealTime
            intro d pw hk i hi
            rcases hprev d pw hk i hi with h | h
            · left; exact le_trans (by
                simp only [RevealState.aliasVar]
                split
                · rename_i nid hx_eq; simp only
                  by_cases heq : i = nid
                  · rw [if_pos heq]; exact min_le_right _ _
                  · rw [if_neg heq]
                · exact le_refl _) h
            · right; exact h)
        (by sorry) -- VarVisible for extended context
        (by sorry) (by sorry) (by sorry) -- hdt + hhn + hnsc for reveal continuation

/-- The main experimental compilation function: Vegas program → VegasMAID. -/
noncomputable def compileVegasMAID
    (B : MAIDBackend Player L)
    {Γ : VCtx Player L}
    (p : VegasCore Player L Γ)
    (hl : Legal p) (hd : NormalizedDists p)
    (hfresh : FreshBindings p)
    (hpub : ∀ y who b, VHasVar (L := L) Γ y (.hidden who b) → False)
    (env : VEnv (Player := Player) L Γ) :
    let st := MAIDCompileState.ofProg B p hl hd (fun _ => env) .empty
    @VegasMAID Player _ B.fintypePlayer st.nextId :=
  let st := MAIDCompileState.ofProg B p hl hd (fun _ => env) .empty
  let rs := computeReveals B p .empty
  let hcon : RevealConsistent .empty .empty :=
    ⟨rfl, fun nd => nd.elim0, fun nd => nd.elim0,
     fun _ _ h => by simp [RevealState.empty] at h,
     fun _ _ => rfl⟩
  toVegasMAID B st rs
    (computeReveals_consistent B p hl hd _ _ _ hcon)
    (computeReveals_parents_visible B p hl hd hfresh _ _ _ hcon
      (by intro x hx; simp [MAIDCompileState.empty] at hx)
      (fun d => d.elim0)
      (by intro who y σ hy i hi; exfalso;
          simp [MAIDCompileState.empty, MAIDCompileState.lookupDeps,
                MAIDCompileState.lookupDepsAux] at hi)
      (by intro y nid h; simp [RevealState.empty] at h)
      (by intro y who b hv; exact (hpub y who b hv).elim)
      (by intro y nid h; simp [RevealState.empty] at h))

end Vegas

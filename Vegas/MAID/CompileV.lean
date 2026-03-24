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
      -- Utility nodes: sorry for now (needs auxiliary induction on player list)
      sorry
  | letExpr x e k ih =>
      simp only [computeReveals, MAIDCompileState.ofProg]
      exact ih hl hd _ _ _ ⟨hcon₀.sync, hcon₀.chance, hcon₀.decision, hcon₀.nodeOf_lt⟩
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
      -- The goal should be definitionally equal to:
      show RevealConsistent
        ((st₀.addNode cnd hcnd_deps).2.addVar x τ {st₀.nextId} hdeps)
        (rs₀.addPublicNode.bindVar x rs₀.nextId)
      sorry
  | commit x who R k ih =>
      simp only [computeReveals, MAIDCompileState.ofProg]
      apply ih (hd := hd)
      sorry
  | reveal y who x hx k ih =>
      simp only [computeReveals, MAIDCompileState.ofProg]
      apply ih (hd := hd)
      refine ⟨?_, ?_, ?_, ?_⟩
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

/-- Decision parents in the compiled MAID are all visible to the player
    (the factored-observation property). -/
theorem computeReveals_parents_visible (B : MAIDBackend Player L)
    {Γ : VCtx Player L}
    (p : VegasCore Player L Γ) (hl : Legal p) (hd : NormalizedDists p)
    (ρ : RawNodeEnv L → VEnv (Player := Player) L Γ)
    (st₀ : MAIDCompileState Player L B) (rs₀ : RevealState)
    (hcon₀ : RevealConsistent st₀ rs₀) :
    let st := MAIDCompileState.ofProg B p hl hd ρ st₀
    let rs := computeReveals B p rs₀
    ∀ (d : Fin st.nextId) (p : Player),
      (st.descAt d).kind = .decision p →
      ∀ (i : Nat) (hi : i ∈ (st.descAt d).parents),
        rs.revealTime i ≤ ↑d.val ∨
          (∃ q, (st.descAt ⟨i, Nat.lt_trans (st.descAt_parent_lt d hi) d.2⟩).kind =
            .decision q ∧ q = p) := by
  sorry

/-- The main experimental compilation function: Vegas program → VegasMAID. -/
noncomputable def compileVegasMAID
    (B : MAIDBackend Player L)
    {Γ : VCtx Player L}
    (p : VegasCore Player L Γ)
    (hl : Legal p) (hd : NormalizedDists p)
    (env : VEnv (Player := Player) L Γ) :
    let st := MAIDCompileState.ofProg B p hl hd (fun _ => env) .empty
    @VegasMAID Player _ B.fintypePlayer st.nextId :=
  let st := MAIDCompileState.ofProg B p hl hd (fun _ => env) .empty
  let rs := computeReveals B p .empty
  let hcon : RevealConsistent .empty .empty :=
    ⟨rfl, fun nd => nd.elim0, fun nd => nd.elim0, fun _ _ h => by simp [RevealState.empty] at h⟩
  toVegasMAID B st rs
    (computeReveals_consistent B p hl hd _ _ _ hcon)
    (computeReveals_parents_visible B p hl hd _ _ _ hcon)

end Vegas

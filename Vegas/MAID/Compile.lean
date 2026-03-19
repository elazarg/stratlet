import GameTheory.Languages.MAID.Syntax
import Vegas.MAID.Backend
import Vegas.Core
import Vegas.Strategic

/-!
# Vegas to MAID compiler

Direct compilation of a Vegas `VegasSimple` to `GameTheory`'s `MAID.Struct` and
`MAID.Sem`.

The compiler keeps one unified typed descriptor for every emitted MAID node, so
the structural and semantic layers are derived from the same source of truth.
Only true choice/utility sites become MAID nodes:

- `sample`  -> chance node
- `commit`  -> decision node
- `ret`     -> one utility node per player

Administrative bindings (`letExpr`, `reveal`) are compiled through dependency
tracking and environment reconstruction; they do not become nodes themselves.
-/

namespace Vegas

open MAID

variable {Player : Type} [DecidableEq Player] {L : ExprLanguage}
variable [E : ExprKit Player L] [D : DistKit Player L]

/-- Untyped payload used to reconstruct Vegas environments from MAID parent
configurations. -/
abbrev RawTaggedVal (L : ExprLanguage) : Type := Sigma L.Val

/-- Partial assignment of already-known MAID node values. -/
abbrev RawNodeEnv (L : ExprLanguage) : Type := Nat → Option (RawTaggedVal L)

/-- A fully-typed emitted MAID node. This is the compiler's single source of
truth for both `MAID.Struct` and `MAID.Sem`. -/
inductive CompiledNode (Player : Type) [DecidableEq Player] (L : ExprLanguage)
    (B : MAIDBackend Player L) [ExprKit Player L] [DistKit Player L]
    where
  | chance (τ : L.Ty) (parents : Finset Nat)
      (cpdFDist : RawNodeEnv L → FDist (L.Val τ))
      (cpdNorm : ∀ raw, FDist.totalWeight (cpdFDist raw) = 1)
  | decision (τ : L.Ty) (who : Player) (acts : List (L.Val τ))
      (hacts : acts ≠ []) (hnodup : acts.Nodup) (obsParents : Finset Nat)
      (kernel : Vegas.Profile Player L → RawNodeEnv L → FDist (L.Val τ))
  | utility (who : Player) (parents : Finset Nat)
      (ufn : RawNodeEnv L → ℝ)

namespace CompiledNode

noncomputable def valType : CompiledNode Player L B → Type
  | .chance τ _ _ _ => L.Val τ
  | .decision τ _ _ _ _ _ _ => L.Val τ
  | .utility _ _ _ => Unit

variable {B : MAIDBackend Player L}

def kind : CompiledNode Player L B → NodeKind Player
  | .chance _ _ _ _ => .chance
  | .decision _ who _ _ _ _ _ => .decision who
  | .utility who _ _ => .utility who

def parents : CompiledNode Player L B → Finset Nat
  | .chance _ ps _ _ => ps
  | .decision _ _ _ _ _ ps _ => ps
  | .utility _ ps _ => ps

def obsParents : CompiledNode Player L B → Finset Nat
  | .chance _ ps _ _ => ps
  | .decision _ _ _ _ _ ps _ => ps
  | .utility _ ps _ => ps

noncomputable def domainSize : CompiledNode Player L B → Nat
  | .chance τ _ _ _ => B.domainSize τ
  | .decision _ _ acts _ _ _ _ => acts.length
  | .utility _ _ _ => 1

theorem obs_sub (nd : CompiledNode Player L B) :
    nd.obsParents ⊆ nd.parents := by
  intro x hx
  cases nd <;> simpa [obsParents, parents] using hx

theorem obs_eq_nondec (nd : CompiledNode Player L B)
    (h : ¬ ∃ a, nd.kind = .decision a) :
    nd.obsParents = nd.parents := by
  cases nd with
  | chance τ ps cpd hn => rfl
  | utility who ps ufn => rfl
  | decision τ who acts hacts hnodup ps kernel =>
      exfalso
      exact h ⟨who, rfl⟩

theorem utility_domain (nd : CompiledNode Player L B) (a : Player)
    (h : nd.kind = .utility a) :
    nd.domainSize = 1 := by
  cases nd with
  | utility who ps ufn =>
      cases h
      rfl
  | chance τ ps cpd hn =>
      cases h
  | decision τ who acts hacts hnodup ps kernel =>
      cases h

theorem nonutility_pos (nd : CompiledNode Player L B)
    (h : ¬ ∃ a, nd.kind = .utility a) :
    0 < nd.domainSize := by
  cases nd with
  | chance τ ps cpd hn =>
      simpa [domainSize] using B.domainSize_pos τ
  | decision τ who acts hacts hnodup ps kernel =>
      exact List.length_pos_iff.mpr hacts
  | utility who ps ufn =>
      exfalso
      exact h ⟨who, rfl⟩

end CompiledNode

/-- Variable-to-dependency entries accumulated during compilation. -/
abbrev MAIDVarEntry (Player : Type) (L : ExprLanguage) :=
  VarId × BindTy Player L × Finset Nat

/-- Internal state for direct Vegas-to-MAID compilation. -/
structure MAIDCompileState (Player : Type) [DecidableEq Player] (L : ExprLanguage)
    (B : MAIDBackend Player L) [ExprKit Player L] [DistKit Player L]
    where
  nextId : Nat
  nodes : List (Nat × CompiledNode Player L B)
  vars : List (MAIDVarEntry Player L)
  ids_range : nodes.map Prod.fst = List.range nextId
  nodeDeps_lt :
    ∀ e ∈ nodes, ∀ d ∈ e.2.parents ∪ e.2.obsParents, d < e.1
  varDeps_lt :
    ∀ e ∈ vars, ∀ d ∈ e.2.2, d < nextId

namespace MAIDCompileState

variable {B : MAIDBackend Player L}

local instance : Fintype Player := B.fintypePlayer

def empty : MAIDCompileState Player L B where
  nextId := 0
  nodes := []
  vars := []
  ids_range := rfl
  nodeDeps_lt := by
    intro e he
    cases he
  varDeps_lt := by
    intro e he
    cases he

def lookupDepsAux : List (MAIDVarEntry Player L) → VarId → Finset Nat
  | [], _ => ∅
  | (y, _, deps) :: rest, x =>
      if x = y then deps else lookupDepsAux rest x

def lookupDeps (st : MAIDCompileState Player L B) (x : VarId) : Finset Nat :=
  lookupDepsAux st.vars x

omit [DecidableEq Player] E D in
theorem lookupDepsAux_lt {vars : List (MAIDVarEntry Player L)} {n : Nat}
    (hvars : ∀ e ∈ vars, ∀ d ∈ e.2.2, d < n) (x : VarId) :
    ∀ d ∈ lookupDepsAux vars x, d < n := by
  induction vars with
  | nil =>
      intro d hd
      simp [lookupDepsAux] at hd
  | cons e rest ih =>
      rcases e with ⟨y, τ, deps⟩
      by_cases hxy : x = y
      · subst hxy
        intro d hd
        have hmem : d ∈ deps := by
          simpa [lookupDepsAux] using hd
        exact hvars (x, τ, deps) (by simp) d hmem
      · intro d hd
        have hd' : d ∈ lookupDepsAux rest x := by
          simpa [lookupDepsAux, hxy] using hd
        exact ih (fun e he d hd => hvars e (by simp [he]) d hd) d hd'

theorem lookupDeps_lt (st : MAIDCompileState Player L B) (x : VarId) :
    ∀ d ∈ st.lookupDeps x, d < st.nextId := by
  unfold lookupDeps
  exact lookupDepsAux_lt st.varDeps_lt x

def depsOfVars (st : MAIDCompileState Player L B) : List VarId → Finset Nat
  | [] => ∅
  | x :: xs => st.lookupDeps x ∪ st.depsOfVars xs

theorem depsOfVars_lt (st : MAIDCompileState Player L B) (xs : List VarId) :
    ∀ d ∈ st.depsOfVars xs, d < st.nextId := by
  induction xs with
  | nil =>
      intro d hd
      simp [depsOfVars] at hd
  | cons x xs ih =>
      intro d hd
      have hd' : d ∈ st.lookupDeps x ∨ d ∈ st.depsOfVars xs := by
        simpa [depsOfVars, Finset.mem_union] using hd
      rcases hd' with hd | hd
      · exact st.lookupDeps_lt x d hd
      · exact ih d hd

def ctxDeps (st : MAIDCompileState Player L B) (Γ : Ctx Player L) :
    Finset Nat :=
  st.depsOfVars (Γ.map Prod.fst)

def viewDeps (st : MAIDCompileState Player L B) (who : Player) (Γ : Ctx Player L) :
    Finset Nat :=
  st.depsOfVars ((viewCtx who Γ).map Prod.fst)

def sampleDeps (st : MAIDCompileState Player L B)
    {Γ : Ctx Player L} (τ : BindTy Player L) (m : SampleMode τ) :
    Finset Nat :=
  st.depsOfVars ((distCtx τ m Γ).map Prod.fst)

def addVar (st : MAIDCompileState Player L B) (x : VarId) (τ : BindTy Player L)
    (deps : Finset Nat) (hdeps : ∀ d ∈ deps, d < st.nextId) :
    MAIDCompileState Player L B where
  nextId := st.nextId
  nodes := st.nodes
  vars := st.vars ++ [(x, τ, deps)]
  ids_range := st.ids_range
  nodeDeps_lt := st.nodeDeps_lt
  varDeps_lt := by
    intro e he d hd
    simp only [List.mem_append, List.mem_singleton] at he
    rcases he with he | rfl
    · exact st.varDeps_lt e he d hd
    · exact hdeps d hd

def addNode (st : MAIDCompileState Player L B) (nd : CompiledNode Player L B)
    (hdeps : ∀ d ∈ nd.parents ∪ nd.obsParents, d < st.nextId) :
    Nat × MAIDCompileState Player L B :=
  let id := st.nextId
  (id,
    { nextId := st.nextId + 1
      nodes := st.nodes ++ [(id, nd)]
      vars := st.vars
      ids_range := by
        simp [id, st.ids_range, List.range_succ]
      nodeDeps_lt := by
        intro e he d hd
        simp only [List.mem_append, List.mem_singleton] at he
        rcases he with he | rfl
        · exact st.nodeDeps_lt e he d hd
        · simpa [id] using hdeps d hd
      varDeps_lt := by
        intro e he d hd
        exact Nat.lt_trans (st.varDeps_lt e he d hd) (Nat.lt_succ_self _) })

noncomputable def defaultView (B : MAIDBackend Player L) :
    (Γ : Ctx Player L) → Env (Player := Player) L Γ
  | [] => Env.empty L
  | (_, τ) :: Γ =>
      Env.cons (Player := Player) (L := L)
        (MAIDValuation.defaultVal L B.toMAIDValuation τ.base)
        (defaultView B Γ)

def addUtilityNodes (st : MAIDCompileState Player L B)
    (deps : Finset Nat) (hdeps : ∀ d ∈ deps, d < st.nextId)
    (ufn : Player → RawNodeEnv L → ℝ) :
    List Player → MAIDCompileState Player L B
  | [] => st
  | who :: rest =>
      let res := st.addNode (.utility who deps (ufn who)) (by
        intro d hd
        have hd' : d ∈ deps := by
          simpa [CompiledNode.parents, CompiledNode.obsParents] using hd
        exact hdeps d hd')
      addUtilityNodes res.2
        deps
        (fun d hd => Nat.lt_trans (hdeps d hd) (Nat.lt_succ_self _))
        ufn
        rest

theorem nodes_length_eq_nextId (st : MAIDCompileState Player L B) :
    st.nodes.length = st.nextId := by
  simpa using congrArg List.length st.ids_range

theorem index_lt_nodes (st : MAIDCompileState Player L B) (i : Fin st.nextId) :
    i.1 < st.nodes.length := by
  exact Nat.lt_of_lt_of_eq i.2 (st.nodes_length_eq_nextId.symm)

theorem get_id_eq (st : MAIDCompileState Player L B) (i : Fin st.nextId) :
    (st.nodes[i.1]'(st.index_lt_nodes i)).1 = i.1 := by
  calc
    (st.nodes[i.1]'(st.index_lt_nodes i)).1
        = (st.nodes.map Prod.fst)[i.1]'(by
            simpa [List.length_map] using st.index_lt_nodes i) := by
            simp
    _ = (List.range st.nextId)[i.1]'(by
          exact Nat.lt_of_lt_of_eq i.2 (List.length_range (n := st.nextId)).symm) := by
          simp [st.ids_range]
    _ = i.1 := by
          simp

noncomputable def descAt (st : MAIDCompileState Player L B) (i : Fin st.nextId) :
    CompiledNode Player L B :=
  (st.nodes[i.1]'(st.index_lt_nodes i)).2

theorem descAt_parent_lt (st : MAIDCompileState Player L B) (i : Fin st.nextId)
    {d : Nat} (hd : d ∈ (st.descAt i).parents) :
    d < i.1 := by
  let e := st.nodes[i.1]'(st.index_lt_nodes i)
  have he : e ∈ st.nodes := List.mem_iff_getElem.mpr
    ⟨i.1, st.index_lt_nodes i, rfl⟩
  have hid : e.1 = i.1 := st.get_id_eq i
  have hdep := st.nodeDeps_lt e he d (Finset.mem_union.mpr (.inl hd))
  simpa [descAt, e, hid] using hdep

theorem descAt_obs_lt (st : MAIDCompileState Player L B) (i : Fin st.nextId)
    {d : Nat} (hd : d ∈ (st.descAt i).obsParents) :
    d < i.1 := by
  let e := st.nodes[i.1]'(st.index_lt_nodes i)
  have he : e ∈ st.nodes := List.mem_iff_getElem.mpr
    ⟨i.1, st.index_lt_nodes i, rfl⟩
  have hid : e.1 = i.1 := st.get_id_eq i
  have hdep := st.nodeDeps_lt e he d (Finset.mem_union.mpr (.inr hd))
  simpa [descAt, e, hid] using hdep

noncomputable def readVal (raw : RawNodeEnv L) (τ : L.Ty) (id : Nat) : L.Val τ :=
  match raw id with
  | some ⟨τ', v⟩ =>
      if h : τ' = τ then h ▸ v else MAIDValuation.defaultVal L B.toMAIDValuation τ
  | none =>
      MAIDValuation.defaultVal L B.toMAIDValuation τ

noncomputable def ofProg
    (B : MAIDBackend Player L) :
    {Γ : Ctx Player L} →
      (p : VegasCore Player L Γ) →
      Legal p →
      DistinctActs p →
      NormalizedDists p →
      (RawNodeEnv L → Env (Player := Player) L Γ) →
      MAIDCompileState Player L B →
      MAIDCompileState Player L B
  | Γ, .ret payoffs, _hl, _ha, _hd, ρ, st =>
      let _ : Fintype Player := B.fintypePlayer
      st.addUtilityNodes
        (st.ctxDeps Γ)
        (st.depsOfVars_lt _)
        (fun who raw => ((evalPayoffs payoffs (ρ raw)) who : ℝ))
        Finset.univ.toList
  | Γ, .letExpr (b := b) x e k, hl, ha, hd, ρ, st =>
      let deps := st.ctxDeps Γ
      ofProg B k hl ha hd
        (fun raw =>
          let env := ρ raw
          Env.cons (τ := .pub b) (E.eval e env) env)
        (st.addVar x (.pub b) deps (st.depsOfVars_lt _))
  | Γ, .sample x τ m D' k, hl, ha, hd, ρ, st =>
      let deps := st.ctxDeps Γ
      let id := st.nextId
      let cpdFDist : RawNodeEnv L → FDist (L.Val τ.base) := fun raw =>
        let env := ρ raw
        D.eval D' (Env.projectDist τ m env)
      let cpdNorm : ∀ raw, FDist.totalWeight (cpdFDist raw) = 1 :=
        fun raw => hd.1 _
      let res := st.addNode (.chance τ.base deps cpdFDist cpdNorm) (by
        intro d hd'
        have hd'' : d ∈ deps := by
          simpa [CompiledNode.parents, CompiledNode.obsParents] using hd'
        exact st.depsOfVars_lt _ d hd'')
      let st' := res.2
      ofProg B k hl ha hd.2
        (fun raw =>
          let env := ρ raw
          let v := MAIDCompileState.readVal (B := B) raw τ.base id
          Env.cons v env)
        (st'.addVar x τ ({id}) (by
          intro d hd'
          have hdid : d = id := by
            simpa using hd'
          subst d
          exact Nat.lt_succ_self _))
  | Γ, .commit (b := b) x who acts R k, hl, ha, hd, ρ, st =>
      let obs := st.ctxDeps Γ
      have hacts : acts ≠ [] := by
        rcases hl.1 (defaultView B (viewCtx who Γ)) with ⟨a, ha, _⟩
        exact List.ne_nil_of_mem ha
      let id := st.nextId
      let res := st.addNode
        (.decision b who acts hacts ha.1 obs
          (fun σ raw => σ.commit who x acts R (Env.toView who (ρ raw)))) (by
        intro d hd'
        have hd'' : d ∈ obs := by
          simpa [CompiledNode.parents, CompiledNode.obsParents] using hd'
        exact st.depsOfVars_lt _ d hd'')
      let st' := res.2
      ofProg B k hl.2 ha.2 hd
        (fun raw =>
          let env := ρ raw
          let v := MAIDCompileState.readVal (B := B) raw b id
          Env.cons (τ := .hidden who b) v env)
        (st'.addVar x (.hidden who b) ({id}) (by
          intro d hd'
          have hdid : d = id := by
            simpa using hd'
          subst d
          exact Nat.lt_succ_self _))
  | _, .reveal (b := b) y who x hx k, hl, ha, hd, ρ, st =>
      let deps := st.lookupDeps x
      ofProg B k hl ha hd
        (fun raw =>
          let env := ρ raw
          let v : L.Val b := Env.get env hx
          Env.cons (τ := .pub b) v env)
        (st.addVar y (.pub b) deps (st.lookupDeps_lt x))

/-- The native value type for a compiled node. -/
def CompiledNode.valType : CompiledNode Player L B → Type
  | .chance τ _ _ _ => L.Val τ
  | .decision τ _ _ _ _ _ _ => L.Val τ
  | .utility _ _ _ => Unit

noncomputable instance (nd : CompiledNode Player L B) :
    Fintype (CompiledNode.valType (B := B) nd) := by
  cases nd with
  | chance τ _ _ _ => exact MAIDValuation.instFintypeVal L B.toMAIDValuation τ
  | decision τ _ _ _ _ _ _ => exact MAIDValuation.instFintypeVal L B.toMAIDValuation τ
  | utility _ _ _ => exact Unit.fintype

noncomputable instance (nd : CompiledNode Player L B) :
    DecidableEq (CompiledNode.valType (B := B) nd) := by
  cases nd with
  | chance τ _ _ _ => exact L.decEqVal
  | decision τ _ _ _ _ _ _ => exact L.decEqVal
  | utility _ _ _ => exact instDecidableEqPUnit

noncomputable instance (nd : CompiledNode Player L B) :
    Inhabited (CompiledNode.valType (B := B) nd) := by
  cases nd with
  | chance τ _ _ _ => exact ⟨MAIDValuation.defaultVal L B.toMAIDValuation τ⟩
  | decision τ _ _ _ _ _ _ => exact ⟨MAIDValuation.defaultVal L B.toMAIDValuation τ⟩
  | utility _ _ _ => exact ⟨()⟩

noncomputable def toStruct (st : MAIDCompileState Player L B) :
    @MAID.Struct Player _ B.fintypePlayer st.nextId := by
  let _ : Fintype Player := B.fintypePlayer
  exact {
    kind := fun nd => (st.descAt nd).kind
    parents := fun nd =>
      (st.descAt nd).parents.attach.image
        (fun d => ⟨d.1, Nat.lt_trans (st.descAt_parent_lt nd d.2) nd.2⟩)
    obsParents := fun nd =>
      (st.descAt nd).obsParents.attach.image
        (fun d => ⟨d.1, Nat.lt_trans (st.descAt_obs_lt nd d.2) nd.2⟩)
    Val := fun nd => CompiledNode.valType (st.descAt nd)
    instFintype := inferInstance
    instDecidableEq := inferInstance
    instInhabited := inferInstance
    obs_sub := by
      intro nd x hx
      rcases Finset.mem_image.mp hx with ⟨d, hd, rfl⟩
      exact Finset.mem_image.mpr ⟨⟨d.1, (st.descAt nd).obs_sub d.2⟩, by simp, by simp⟩
    obs_eq_nondec := by
      intro nd h
      ext x
      simp [(st.descAt nd).obs_eq_nondec h]
    utility_unique := by
      intro nd a h
      cases hdesc : st.descAt nd with
      | utility _ _ _ =>
          exact PUnit.instUnique
      | chance τ ps cpd hn =>
          exfalso; simp [CompiledNode.kind, hdesc] at h
      | decision τ who acts hacts hnodup obs kernel =>
          exfalso; simp [CompiledNode.kind, hdesc] at h
    acyclic := DAG.acyclic_of_topologicalOrder {
        order := List.finRange st.nextId
        nodup := List.nodup_finRange st.nextId
        length := by simp
        respects := by
          intro i p hp
          have hp' : p.1 < ((List.finRange st.nextId)[i]).1 := by
            rcases Finset.mem_image.mp hp with ⟨d, hd, rfl⟩
            exact st.descAt_parent_lt ((List.finRange st.nextId)[i]) d.2
          simp only [Fin.getElem_fin, List.getElem_finRange, Fin.eta, Fin.val_cast] at hp'
          exact ⟨⟨p.1, by omega⟩, hp', by simp⟩
      }
  }

/-- Convert a node value (in the native valType) to a tagged value for RawNodeEnv. -/
noncomputable def taggedOfVal :
    (nd : CompiledNode Player L B) → CompiledNode.valType nd → Option (RawTaggedVal L)
  | .chance τ _ _ _, v => some ⟨τ, v⟩
  | .decision τ _ _ _ _ _ _, v => some ⟨τ, v⟩
  | .utility _ _ _, _ => none

noncomputable def rawEnvOfCfg (st : MAIDCompileState Player L B)
    {ps : Finset (Fin st.nextId)}
    (cfg : @Cfg Player _ B.fintypePlayer st.nextId st.toStruct ps) :
    RawNodeEnv L :=
  let _ : Fintype Player := B.fintypePlayer
  fun i =>
  if hi : i < st.nextId then
    let nd : Fin st.nextId := ⟨i, hi⟩
    if hmem : nd ∈ ps then
      taggedOfVal (st.descAt nd) (cfg ⟨nd, hmem⟩)
    else
      none
  else
    none

noncomputable def toSem (st : MAIDCompileState Player L B) :
    @MAID.Sem Player _ B.fintypePlayer st.nextId st.toStruct := by
  let _ : Fintype Player := B.fintypePlayer
  exact show MAID.Sem st.toStruct from
    { chanceCPD := by
        intro c cfg
        match hdesc : st.descAt c.1 with
        | .chance τ _parents cpdFDist cpdNorm =>
            change PMF (CompiledNode.valType (st.descAt c.1))
            rw [hdesc]
            exact FDist.toPMF (cpdFDist (st.rawEnvOfCfg cfg)) (cpdNorm _)
        | .decision τ who acts hacts hnodup obs kernel =>
            have hk := c.2; simp [MAIDCompileState.toStruct, CompiledNode.kind, hdesc] at hk
        | .utility who parents ufn =>
            have hk := c.2; simp [MAIDCompileState.toStruct, CompiledNode.kind, hdesc] at hk
      utilityFn := fun p u cfg =>
        match hdesc : st.descAt u.1 with
        | .utility _who _parents ufn => ufn (st.rawEnvOfCfg cfg)
        | .chance τ _parents _ _ =>
            absurd u.2 (by simp [MAIDCompileState.toStruct, CompiledNode.kind, hdesc])
        | .decision τ _who _ _ _ _ _ =>
            absurd u.2 (by simp [MAIDCompileState.toStruct, CompiledNode.kind, hdesc]) }

end MAIDCompileState

namespace VegasCore

noncomputable def toMAID
    (B : MAIDBackend Player L) {Γ : Ctx Player L}
    (p : VegasCore Player L Γ) (env : Env (Player := Player) L Γ)
    (_hΓ : WFCtx Γ) (_hwf : WF p)
    (hl : Legal p) (ha : DistinctActs p)
    (hd : NormalizedDists (P := Player) (L := L) p) :
    Σ n, Σ S : @MAID.Struct Player _ B.fintypePlayer n, @MAID.Sem Player _ B.fintypePlayer n S := by
  let _ : Fintype Player := B.fintypePlayer
  let st := MAIDCompileState.ofProg B p hl ha hd (fun _ => env) .empty
  exact ⟨st.nextId, st.toStruct, MAIDCompileState.toSem st⟩

end VegasCore

end Vegas

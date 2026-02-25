import Mathlib.Probability.ProbabilityMassFunction.Constructions
import Mathlib.Algebra.BigOperators.Fin

import distilled.Vegas
import GameTheory.EFG
import GameTheory.MAID
/-!
# Game Semantics for Vegas Programs

Compiles Vegas programs to standard game-theoretic representations:
- `RGameTree` / `EFG.GameTree` (extensive-form game trees)
- `MAID.Node` list (multi-agent influence diagram)
-/

-- ============================================================================
-- § 1. Rat-weighted game tree (computable)
-- ============================================================================

/-- Computable game tree using `Rat` weights and `Int` payoffs. -/
inductive RGameTree where
  | terminal (payoff : Player → Int)
  | chance (branches : List (RGameTree × Rat))
  | decision (pid : Nat) (player : Player)
      (actions : List RGameTree)

open scoped BigOperators

-- If Player is not Nat, replace with your actual default player.
def defaultPlayer : Player := 0
mutual
  /-- Collect decision-node metadata: (pid, player, numActions). -/
  def RGameTree.collectInfo : RGameTree → List (Nat × Player × Nat)
    | .terminal _ => []
    | .chance branches => collectInfoChance branches
    | .decision pid player actions =>
        (pid, player, actions.length) :: collectInfoDec actions

  /-- Helper for mapping over chance branches. -/
  def RGameTree.collectInfoChance : List (RGameTree × Rat) → List (Nat × Player × Nat)
    | [] => []
    | (t, _) :: bs => RGameTree.collectInfo t ++ collectInfoChance bs

  /-- Helper for mapping over decision actions. -/
  def RGameTree.collectInfoDec : List RGameTree → List (Nat × Player × Nat)
    | [] => []
    | t :: ts =>  RGameTree.collectInfo t ++ collectInfoDec ts
end

def arityOf (pid : Nat) (info : List (Nat × Player × Nat)) : Nat :=
  let ns := info.filterMap (fun ⟨i,_,n⟩ => if i = pid then some n else none)
  Nat.max 1 (ns.foldl Nat.max 0)

def playerOf (pid : Nat) (info : List (Nat × Player × Nat)) : Player :=
  match info.find? (fun ⟨i,_,_⟩ => i = pid) with
  | some ⟨_,p,_⟩ => p
  | none         => defaultPlayer

def toInfoStructure (info : List (Nat × Player × Nat)) : EFG.InfoStructure Player where
  player := fun pid => playerOf pid info
  arity  := fun pid => arityOf pid info
  arity_pos := by
    intro pid
    -- arityOf pid info = max 1 (...) so it's always ≥ 1
    dsimp [arityOf]
    exact Nat.lt_of_lt_of_le (by decide : 0 < 1) (Nat.le_max_left _ _)

def RGameTree.toInfoS (t : RGameTree) : EFG.InfoStructure Player :=
  toInfoStructure (collectInfo t)

-- ============================================================================
-- § 2. Compilation from Vegas to RGameTree
-- ============================================================================

/-- Compile a Vegas program to a computable game tree.
    Commit sites become decision nodes with actions filtered by `R`.
    Sample sites evaluate the syntactic `DistExpr` and enumerate support.
    Requires `Legal p` and `WF p`. -/
def toRGameTree : (p : Prog Γ) → Legal p → WF p → Env Γ → RGameTree
  | .ret u, _, _, env => .terminal (fun who => sorry) -- evalPayoffMap returns Outcome now
  | .letExpr x e k, hl, hw, env =>
    toRGameTree k hl hw.2 (Env.cons (x := x) (evalExpr e env) env)
  | .sample x τ m D k, hl, hw, env =>
    -- Evaluate the DistExpr to get support + weights
    -- For compilation we need to enumerate the support, which requires
    -- evaluating the noncomputable FDist. Use sorry for now.
    sorry
  | .commit x who acts R k, hl, hw, env =>
    let view := env.toView who
    let allowed := acts.filter (evalR R · view)
    .decision x who (allowed.map
      (fun a => toRGameTree k hl.2 hw.2 (Env.cons (x := x) a env)))
  | .reveal y _who _x (b := b) hx k, hl, hw, env =>
    let v : Val b := env.get hx
    toRGameTree k hl hw.2 (Env.cons (x := y) (τ := .pub b) v env)

-- ============================================================================
-- § 3. Bridge to classic EFG (noncomputable)
-- ============================================================================

/-- Construct a `PMF (Fin n)` from `NNReal` weights by normalizing.
    Falls back to uniform distribution if all weights are zero. -/
noncomputable def normalizedFinPMF {n : Nat} (weights : Fin n → NNReal)
    (hn : 0 < n) : PMF (Fin n) :=
  let f : Fin n → ENNReal := fun i => ↑(weights i)
  have htop : ∑' i, f i ≠ ⊤ := by
    rw [tsum_fintype, ← ENNReal.coe_finset_sum]
    exact ENNReal.coe_ne_top
  if h0 : ∑' i, f i = 0 then
    PMF.ofFintype (fun _ => (n : ENNReal)⁻¹) (by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      exact ENNReal.mul_inv_cancel (by exact_mod_cast hn.ne') (ENNReal.natCast_ne_top n))
  else
    PMF.normalize f h0 htop

/-- Build an `EFG.InfoStructure` from collected decision-node metadata.
    Uses first occurrence per pid. Defaults: player 0, arity 1. -/
def rInfoStructure (info : List (Nat × Player × Nat)) : EFG.InfoStructure Player where
  player I := match info.find? (fun e => e.1 == I) with
    | some (_, p, _) => p | none => 0
  arity I := match info.find? (fun e => e.1 == I) with
    | some (_, _, 0) => 1
    | some (_, _, n + 1) => n + 1
    | none => 1
  arity_pos I := by split <;> omega

theorem List.sizeOf_get_lt {α : Type _} [SizeOf α] (xs : List α) (i : Fin xs.length) :
    sizeOf (xs.get i) < sizeOf xs := by
  induction xs with
  | nil => exact i.elim0
  | cons x xs ih =>
    cases i with | mk val isLt =>
    cases val with
    | zero => simp; omega
    | succ n =>
      have := ih ⟨n, Nat.succ_lt_succ_iff.mp isLt⟩
      exact Nat.lt_add_left (1 + sizeOf x) (ih ⟨n, Nat.lt_of_succ_lt_succ (Nat.lt_of_succ_le isLt)⟩)

noncomputable def RGameTree.toEFGWith (S : EFG.InfoStructure Player) :
    RGameTree → EFG.GameTree Player S
  | .terminal payoff => .terminal (fun p => (payoff p : ℝ))
  | .chance [] => .terminal (fun _ => 0)
  | .chance (b :: bs) =>
      let n := bs.length
      let w (i : Fin (n + 1)) : NNReal :=
        ⟨max (↑((b :: bs).get i).2 : ℝ) 0, le_max_right _ _⟩
      .chance n (normalizedFinPMF w (Nat.zero_lt_succ n))
        (fun i => ((b :: bs).get i).1.toEFGWith S)
  | .decision pid _player actions =>
      .decision pid (fun i =>
        if h : i.val < actions.length then
          (actions.get ⟨i.val, h⟩).toEFGWith S
        else .terminal (fun _ => 0))
termination_by t => sizeOf t
decreasing_by
  · simp_wf
    have h_get := List.sizeOf_get_lt (b :: bs) i
    have h_fst : sizeOf ((b :: bs).get i).1 < sizeOf ((b :: bs).get i) := by
      rcases (b :: bs).get i with ⟨t, r⟩
      simp_all
      omega
    calc sizeOf ((b :: bs).get i).1
      _ < sizeOf ((b :: bs).get i) := h_fst
      _ < sizeOf (b :: bs) := h_get
      _ ≤ _ := by simp
  · simp_wf
    have h_get := List.sizeOf_get_lt actions ⟨i.val, h⟩
    calc sizeOf (actions.get ⟨i.val, h⟩)
      _ < sizeOf actions := h_get
      _ ≤ _ := by omega

/-- Convert `RGameTree` to `EFG.GameTree` using its own induced `InfoStructure`. -/
noncomputable def RGameTree.toEFG (t : RGameTree) :
    EFG.GameTree Player t.toInfoS :=
  t.toEFGWith t.toInfoS

-- ============================================================================
-- § 4. Direct Prog → EFG.GameTree
-- ============================================================================

/-! ### Design rationale

The two-step `Prog → RGameTree → EFG.GameTree` route is unsound because
`toRGameTree` **filters** actions by the restriction `R`, making the arity
runtime-dependent. In EFG, all actions must be available at every info set.

The direct approach:
- **Info sets**: each `commit x` site becomes info set `x : VarId = Nat`.
  Since the program is SSA (`WF`), each `x` appears exactly once.
- **Arity**: `acts.length` (the **unfiltered** action list).
  `Legal p` guarantees `acts ≠ []`, so `arity_pos` holds.
- **Restriction `R`**: NOT encoded in the tree. It becomes a constraint on
  strategy profiles (a strategy is legal iff it never picks filtered-out
  actions). This is the standard game-theoretic formulation.
- **Sample nodes**: `DistExpr.ite c t f` is resolved at tree-build time
  (since `env` is available). `DistExpr.weighted entries` enumerates to
  chance branches directly.
-/

/-- Collect (commitSite, player, acts.length) from a program.
    Linear scan — each continuation `k` is visited exactly once (SSA). -/
def Prog.infoEntries : Prog Γ → List (VarId × Player × Nat)
  | .ret _ => []
  | .letExpr _ _ k => k.infoEntries
  | .sample _ _ _ _ k => k.infoEntries
  | .commit x who acts _ k => (x, who, acts.length) :: k.infoEntries
  | .reveal _ _ _ _ k => k.infoEntries

/-- InfoStructure extracted from a Vegas program.
    Each `commit x who acts R k` yields info set `x` with
    `player = who` and `arity = acts.length`. -/
def Prog.mkInfoS (p : Prog Γ) : EFG.InfoStructure Player :=
  rInfoStructure p.infoEntries

/-- Resolve a `DistExpr` to its weighted entries given an environment.
    `.ite` is evaluated eagerly; the result is always a `.weighted` list. -/
def DistExpr.resolveEntries : DistExpr Γ b → Env Γ → List (Val b × ℚ≥0)
  | .weighted entries, _ => entries
  | .ite c t f, env =>
    if evalExpr c env then t.resolveEntries env else f.resolveEntries env

/-- Build the EFG tree directly from a Vegas program.

    - `commit x` → `decision x` with `Fin (S.arity x)` children
      (one per action in `acts`, unfiltered by `R`)
    - `sample x` → `chance` node over the resolved `DistExpr` support
    - `letExpr`, `reveal` → pass-through (extend env, recurse)
    - `ret u` → terminal node with real-valued payoffs

    Requires `Legal p` (non-empty actions) and `WF p` (SSA). -/
noncomputable def Prog.toEFG {Γ : Ctx} (S : EFG.InfoStructure Player) :
    (p : Prog Γ) → Legal p → WF p → Env Γ → EFG.GameTree Player S
  | .ret u, _, _, env =>
      .terminal (fun who => ((evalPayoffMap u env) who : ℝ))
  | .letExpr x e k, hl, hw, env =>
      k.toEFG S hl hw.2 (Env.cons (x := x) (evalExpr e env) env)
  | .sample x τ m D k, hl, hw, env =>
      let entries := D.resolveEntries (env.projectDist τ m)
      match entries with
      | [] => .terminal (fun _ => 0)
      | e :: es =>
          .chance es.length
            (normalizedFinPMF (fun i =>
              let w := ((e :: es).get i).2
              ⟨(w : ℝ), by exact_mod_cast w.coe_nonneg⟩) (by omega))
            (fun i =>
              let v := ((e :: es).get i).1
              k.toEFG S hl hw.2 (Env.cons (x := x) (τ := τ) v env))
  | .commit x who acts R k, hl, hw, env =>
      .decision x (fun (i : Fin (S.arity x)) =>
        if h : i.val < acts.length then
          let a := acts.get ⟨i.val, h⟩
          k.toEFG S hl.2 hw.2 (Env.cons (x := x) (τ := .hidden who _) a env)
        else .terminal (fun _ => 0))
  | .reveal y _who _x (b := b) hx k, hl, hw, env =>
      let v : Val b := env.get hx
      k.toEFG S hl hw.2 (Env.cons (x := y) (τ := .pub b) v env)

-- ============================================================================
-- § 4a. Pure strategy correspondence
-- ============================================================================

/-! ### Outcome conversion

Vegas uses `Outcome = Player →₀ Int` while EFG uses `Player → ℝ`.
We define a cast and show that `evalPayoffMap` lands in the cast's image. -/

/-- Cast an `Outcome` (Player →₀ Int) to a payoff function (Player → ℝ). -/
noncomputable def Outcome.toReal (o : Outcome) : Player → ℝ :=
  fun p => (o p : ℝ)

/-- `evalPayoffMap` cast to ℝ agrees with the terminal payoff in `Prog.toEFG`. -/
theorem evalPayoffMap_toReal_eq {Γ : Ctx} (u : PayoffMap Γ) (env : Env Γ) :
    (evalPayoffMap u env).toReal = fun who => ((evalPayoffMap u env) who : ℝ) := rfl

/-! ### Pure Vegas profiles

A "pure" Vegas profile assigns a point distribution `FDist.pure aᵢ` at each
commit site, where `aᵢ` is one of the available actions. -/

/-- A profile is pure on program `p` if every commit returns a point mass
    on some action in the action list. -/
def Profile.IsPure (σ : Profile) : (p : Prog Γ) → Prop
  | .ret _ => True
  | .letExpr _ _ k => σ.IsPure k
  | .sample _ _ _ _ k => σ.IsPure k
  | .commit x who acts R k =>
    (∀ view : Env (viewCtx who Γ),
      ∃ i : Fin acts.length,
        σ.commit who x acts R view = FDist.pure (acts.get i)) ∧
    σ.IsPure k
  | .reveal _ _ _ _ k => σ.IsPure k

/-! ### Translation of pure profiles to EFG pure strategies -/

/-- Extract the action index from a pure profile at a commit site.
    Returns a `Fin` into the action list. -/
noncomputable def Profile.pureIdx {Γ : Ctx} {b : BaseTy}
    (σ : Profile) (who : Player) (x : VarId)
    (acts : List (Val b))
    (R : Expr ((x, .pub b) :: flattenCtx (viewCtx who Γ)) .bool)
    (view : Env (viewCtx who Γ))
    (hpure : ∃ i : Fin acts.length,
      σ.commit who x acts R view = FDist.pure (acts.get i)) :
    Fin acts.length :=
  hpure.choose

theorem Profile.pureIdx_spec {Γ : Ctx} {b : BaseTy}
    (σ : Profile) (who : Player) (x : VarId)
    (acts : List (Val b))
    (R : Expr ((x, .pub b) :: flattenCtx (viewCtx who Γ)) .bool)
    (view : Env (viewCtx who Γ))
    (hpure : ∃ i : Fin acts.length,
      σ.commit who x acts R view = FDist.pure (acts.get i)) :
    σ.commit who x acts R view = FDist.pure (acts.get (σ.pureIdx who x acts R view hpure)) :=
  hpure.choose_spec

/-! ### Expected payoff from FDist Outcome

Vegas `outcomeDist` returns `FDist Outcome` while EFG `evalTotal` returns
`Player → ℝ`. We define expected payoff to bridge these. -/

/-- Expected payoff for a player under a finitely-supported outcome distribution.
    `E[payoff(p)] = Σ_{o in support} weight(o) * o(p)` -/
noncomputable def FDist.expectedPayoff (d : FDist Outcome) (p : Player) : ℝ :=
  d.sum (fun o w => (w : ℝ) * (o p : ℝ))

/-- Expected payoff of a point mass is just the payoff. -/
theorem FDist.expectedPayoff_pure (o : Outcome) (p : Player) :
    (FDist.pure o).expectedPayoff p = (o p : ℝ) := by
  simp only [expectedPayoff, FDist.pure]
  rw [Finsupp.sum_single_index (by simp)]
  simp [one_mul]

/-- Linearity of expected payoff under bind:
    `E[bind d f](p) = Σ_{a in d.support} d(a) * E[f(a)](p)` -/
theorem FDist.expectedPayoff_bind {α : Type} [DecidableEq α]
    (d : FDist α) (f : α → FDist Outcome) (p : Player) :
    (d.bind f).expectedPayoff p =
    d.sum (fun a w => (w : ℝ) * (f a).expectedPayoff p) := by
  simp only [expectedPayoff, bind]
  rw [Finsupp.sum_sum_index
    (fun o => by simp [zero_mul])
    (fun o m₁ m₂ => by push_cast; ring)]
  congr 1; funext a w
  rw [Finsupp.sum_mapRange_index (fun o => by simp [zero_mul])]
  simp only [Finsupp.sum, NNRat.cast_mul, Finset.mul_sum]
  congr 1; funext o; ring

/-! ### InfoStructure matches program structure

The `InfoStructure S` must have the correct arity at each commit site
for the correspondence to hold. -/

/-- The info structure has matching arity at every commit site in `p`. -/
def InfoMatch (S : EFG.InfoStructure Player) : Prog Γ → Prop
  | .ret _ => True
  | .letExpr _ _ k => InfoMatch S k
  | .sample _ _ _ _ k => InfoMatch S k
  | .commit x _who acts _R k => S.arity x = acts.length ∧ InfoMatch S k
  | .reveal _ _ _ _ k => InfoMatch S k

/-! ### Compatibility of Vegas profiles and EFG pure strategies

A Vegas pure profile and an EFG pure strategy are "compatible" if at every
commit site, they select the same action (by index). -/

/-- A Vegas pure profile and EFG pure strategy agree at every commit site:
    at commit site `x` with actions `acts`, the profile picks `acts[i]`
    and the strategy picks index `i` (both the same `i`). -/
def PureCompatible (σ : Profile) (σ' : EFG.PureStrategy S) :
    (p : Prog Γ) → Prop
  | .ret _ => True
  | .letExpr _ _ k => PureCompatible σ σ' k
  | .sample _ _ _ _ k => PureCompatible σ σ' k
  | .commit x who acts R k =>
    (∀ view : Env (viewCtx who Γ),
      ∃ i : Fin acts.length,
        σ.commit who x acts R view = FDist.pure (acts.get i) ∧
        ∀ (h : i.val < S.arity x), σ' x = ⟨i.val, h⟩) ∧
    PureCompatible σ σ' k
  | .reveal _ _ _ _ k => PureCompatible σ σ' k

/-! ### Bridge lemmas for sample case -/

/-- `evalDistExpr` agrees with `FDist.ofList ∘ resolveEntries`. -/
theorem evalDistExpr_eq_ofList_resolveEntries {Γ : Ctx} {b : BaseTy}
    (D : DistExpr Γ b) (env : Env Γ) :
    evalDistExpr D env = FDist.ofList (D.resolveEntries env) := by
  induction D with
  | weighted => rfl
  | ite c t f iht ihf =>
    simp only [evalDistExpr, DistExpr.resolveEntries]
    split <;> assumption

/-- `Finsupp.sum` of `ofList` with an additive function equals list sum. -/
theorem FDist.ofList_sum_eq {α : Type} [DecidableEq α] {M : Type} [AddCommMonoid M]
    (entries : List (α × ℚ≥0))
    (g : α → ℚ≥0 → M)
    (h0 : ∀ a, g a 0 = 0)
    (hadd : ∀ a w₁ w₂, g a (w₁ + w₂) = g a w₁ + g a w₂) :
    (FDist.ofList entries).sum g =
    (entries.map (fun ⟨a, w⟩ => g a w)).sum := by
  induction entries with
  | nil => simp [FDist.ofList, Finsupp.sum_zero_index]
  | cons e es ih =>
    obtain ⟨a, w⟩ := e
    rw [FDist.ofList_cons, Finsupp.sum_add_index (fun a _ => h0 a) (fun a _ b₁ b₂ => hadd a b₁ b₂),
        Finsupp.sum_single_index (h0 _), ih, List.map_cons, List.sum_cons]

/-- List.sum of a map equals Finset.sum over Fin indices. -/
private theorem list_map_sum_eq_fin_sum {M : Type} [AddCommMonoid M]
    {β : Type} (l : List β) (f : β → M) :
    (l.map f).sum = ∑ i : Fin l.length, f (l.get i) := by
  induction l with
  | nil => simp
  | cons x xs ih =>
    simp only [List.map_cons, List.sum_cons, List.length_cons]
    rw [Fin.sum_univ_succ]
    congr 1
    rw [ih]
    congr 1; ext ⟨i, hi⟩; rfl

/-- When ENNReal weights sum to 1, `normalizedFinPMF` returns the raw weight. -/
private theorem normalizedFinPMF_toReal_eq_of_sum_one {n : Nat}
    (weights : Fin n → NNReal) (hn : 0 < n)
    (hsum : ∑ i : Fin n, (weights i : ENNReal) = 1) (i : Fin n) :
    (normalizedFinPMF weights hn i).toReal = (weights i : ℝ) := by
  simp only [normalizedFinPMF]
  have htsum : ∑' j : Fin n, (↑(weights j) : ENNReal) = 1 := by rwa [tsum_fintype]
  rw [dif_neg (by rw [htsum]; exact one_ne_zero)]
  simp only [PMF.normalize_apply, htsum]
  -- Goal: (↑(weights i) * 1⁻¹).toReal = ↑(weights i)
  rw [inv_one, mul_one]
  simp

/-- Bridge between `Finsupp.sum` of `ofList` and `normalizedFinPMF`-weighted `Fin` sum.
    When the entry list has total weight 1, the weighted Finsupp.sum
    equals the normalized Fin-indexed sum used in EFG chance nodes. -/
theorem FDist.ofList_sum_eq_normalizedFinPMF_sum {α : Type} [DecidableEq α]
    (entries : List (α × ℚ≥0)) (hn : 0 < entries.length)
    (hnorm : (FDist.ofList entries).totalWeight = 1)
    (g : α → ℝ) :
    (FDist.ofList entries).sum (fun a w => (↑w : ℝ) * g a) =
    ∑ i : Fin entries.length,
      (normalizedFinPMF
        (fun i => ⟨(↑(entries.get i).2 : ℝ),
          by exact_mod_cast (entries.get i).2.coe_nonneg⟩) hn i).toReal *
      g (entries.get i).1 := by
  -- Step 1: Convert LHS from Finsupp.sum to List.sum
  rw [FDist.ofList_sum_eq entries (fun a w => (↑w : ℝ) * g a)
    (fun a => by simp) (fun a w₁ w₂ => by push_cast; ring)]
  -- Step 2: Convert List.sum to Finset.sum over Fin
  rw [list_map_sum_eq_fin_sum]
  -- Step 3: Show normalizedFinPMF gives raw weights (since total weight = 1)
  -- Extract totalWeight = list sum of weights
  have htw : ∑ i : Fin entries.length, (entries.get i).2 = (1 : ℚ≥0) := by
    have h := hnorm; unfold FDist.totalWeight at h
    rw [FDist.ofList_sum_eq entries (fun _ w => w) (fun _ => rfl) (fun _ _ _ => rfl)] at h
    rwa [← list_map_sum_eq_fin_sum] at h
  -- Convert to ENNReal sum = 1
  have hsum1' : ∑ i : Fin entries.length,
      ((⟨(↑(entries.get i).2 : ℝ), by exact_mod_cast (entries.get i).2.coe_nonneg⟩ : NNReal) :
        ENNReal) = 1 := by
    have h1 : ∀ i : Fin entries.length,
        ((⟨(↑(entries.get i).2 : ℝ), by exact_mod_cast (entries.get i).2.coe_nonneg⟩ : NNReal) :
          ENNReal) = ((entries.get i).2 : ENNReal) := by
      intro i; simp [NNReal.coe_mk]
    simp_rw [h1]
    rw [show ∑ i : Fin entries.length, ((entries.get i).2 : ENNReal) =
        ((∑ i : Fin entries.length, (entries.get i).2 : ℚ≥0) : ENNReal) from by push_cast; rfl]
    rw [htw]; simp
  -- Apply normalizedFinPMF simplification
  congr 1; ext i; congr 1
  exact normalizedFinPMF_toReal_eq_of_sum_one _ hn hsum1' i

/-- Main theorem: Vegas `outcomeDist` with a pure-compatible profile agrees with
    EFG `evalTotal` under the corresponding pure strategy.

    The expected payoff from the Vegas outcome distribution equals the
    EFG evaluation (which computes expected payoffs through chance nodes). -/
theorem outcomeDist_expectedPayoff_eq_evalTotal
    {Γ : Ctx} (S : EFG.InfoStructure Player)
    (σ : Profile) (σ' : EFG.PureStrategy S)
    (p : Prog Γ) (hl : Legal p) (hw : WF p) (env : Env Γ)
    (hinfo : InfoMatch S p)
    (hcompat : PureCompatible σ σ' p)
    (hnd : NormalizedDists p)
    (who : Player) :
      (outcomeDist σ p env).expectedPayoff who =
      (p.toEFG S hl hw env).evalTotal σ' who := by
  induction p with
  | ret u =>
    -- Both sides reduce to (evalPayoffMap u env who : ℝ)
    simp only [outcomeDist, Prog.toEFG, EFG.evalTotal_terminal]
    simp only [FDist.expectedPayoff, FDist.pure]
    rw [Finsupp.sum_single_index (by simp)]
    simp [one_mul]
  | letExpr x e k ih =>
    exact ih hl hw.2 _ hinfo hcompat hnd
  | sample x τ m D k ih =>
    obtain ⟨hD_norm, hnd_k⟩ := hnd
    -- Vegas side: bind (evalDistExpr D envD) (fun v => outcomeDist σ k (cons v env))
    change (FDist.bind (evalDistExpr D (env.projectDist τ m))
      (fun v => outcomeDist σ k (Env.cons v env))).expectedPayoff who = _
    rw [FDist.expectedPayoff_bind, evalDistExpr_eq_ofList_resolveEntries]
    -- Apply IH to rewrite outcomeDist to evalTotal in each summand
    simp_rw [show ∀ v, (outcomeDist σ k (Env.cons (x := x) v env)).expectedPayoff who =
        (k.toEFG S hl hw.2 (Env.cons (x := x) v env)).evalTotal σ' who from
      fun v => ih hl hw.2 _ hinfo hcompat hnd_k]
    -- Unfold Prog.toEFG for the sample case on the RHS
    conv_rhs => rw [show Prog.toEFG S (.sample x τ m D k) hl hw env =
      match D.resolveEntries (Env.projectDist τ m env) with
      | [] => .terminal (fun _ => (0 : ℝ))
      | e :: es => .chance es.length
        (normalizedFinPMF (fun i =>
          ⟨(((e :: es).get i).2 : ℝ), by exact_mod_cast ((e :: es).get i).2.coe_nonneg⟩) (by omega))
        (fun i => k.toEFG S hl hw.2 (Env.cons (x := x) (τ := τ) ((e :: es).get i).1 env))
    from rfl]
    -- Case split on entries
    split
    · -- entries = []: both sides are 0
      rename_i _ heq; rw [heq]
      simp [FDist.ofList, Finsupp.sum_zero_index]
    · -- entries = e :: es: bridge Finsupp.sum with Fin sum
      rename_i _ e es heq
      rw [heq]
      -- Manually unfold evalTotal for chance node
      -- Bridge: Finsupp.sum of ofList = Finset.sum with normalizedFinPMF
      have hnorm : (FDist.ofList (e :: es)).totalWeight = 1 := by
        have := hD_norm (Env.projectDist τ m env)
        rwa [evalDistExpr_eq_ofList_resolveEntries, heq] at this
      exact FDist.ofList_sum_eq_normalizedFinPMF_sum (e :: es) (by simp) hnorm
        (fun a => EFG.GameTree.evalTotal σ' (Prog.toEFG S k hl hw.2 (Env.cons a env)) who)
  | commit x who' acts R k ih =>
    obtain ⟨harity, hinfo_k⟩ := hinfo
    obtain ⟨hsite, hk⟩ := hcompat
    obtain ⟨i, hi_eq, hi_strat⟩ := hsite (env.toView who')
    have hi_lt : i.val < S.arity x := by omega
    have hσ' : σ' x = ⟨i.val, hi_lt⟩ := hi_strat hi_lt
    -- Vegas side: bind (FDist.pure (acts.get i)) ... = outcomeDist σ k (env.cons (acts.get i))
    change (FDist.bind (σ.commit who' x acts R (env.toView who'))
      (fun v => outcomeDist σ k (Env.cons v env))).expectedPayoff who =
      (Prog.toEFG S (.commit x who' acts R k) hl hw env).evalTotal σ' who
    rw [hi_eq, FDist.pure_bind]
    -- EFG side: evalTotal (.decision x next) σ' = (next (σ' x)).evalTotal σ'
    conv_rhs => rw [show Prog.toEFG S (.commit x who' acts R k) hl hw env =
      EFG.GameTree.decision x (fun j => if h : j.val < acts.length then
        Prog.toEFG S k hl.2 hw.2 (Env.cons (x := x) (τ := .hidden who' _) (acts.get ⟨j.val, h⟩) env)
      else EFG.GameTree.terminal fun _ => 0) from rfl]
    rw [EFG.evalTotal_decision, hσ', dif_pos i.isLt]
    exact ih hl.2 hw.2 _ hinfo_k hk hnd
  | reveal y who' x hx k ih =>
    exact ih hl hw.2 _ hinfo hcompat hnd

-- ============================================================================
-- § 4b. Mixed/behavioral strategy correspondence (statements)
-- ============================================================================

/-! ### Behavioral strategy translation

A general Vegas `Profile` maps each commit site to a distribution over actions
(via `CommitKernel`). The corresponding EFG `BehavioralStrategy` maps each
info set to a `PMF` over `Fin (S.arity I)`.

**Key difficulty**: Vegas strategies are view-dependent (`Env (viewCtx who Γ)`),
but EFG behavioral strategies are fixed per info set. For the translation to
be well-defined, all game-tree nodes reaching info set `x` must have the same
view — which follows from SSA (`WF p`) and the structure of `Prog`. -/

/-- Convert a normalized `FDist (Val b)` whose support is a subset of `acts`
    into a `PMF (Fin acts.length)` by mapping each value to its index. -/
noncomputable def FDist.toFinPMF {b : BaseTy} (d : FDist (Val b))
    (acts : List (Val b))
    (hsupp : ∀ v ∈ d.support, v ∈ acts)
    (hnorm : d.totalWeight = 1) : PMF (Fin acts.length) :=
  sorry -- Requires: for each Fin i, weight = d (acts.get i), and ∑ = 1

/-- Translate a Vegas profile to an EFG behavioral strategy.
    At each info set `x` (commit site), converts the `FDist` from the profile
    to a `PMF (Fin (S.arity x))`.

    Requires: the profile is admissible and normalized, and info structure
    matches the program. -/
noncomputable def Profile.toBehavioral
    {Γ : Ctx} (S : EFG.InfoStructure Player) (σ : Profile)
    (p : Prog Γ) (env : Env Γ)
    (hinfo : InfoMatch S p)
    (hadm : AdmissibleProfile σ p) (hnorm : σ.NormalizedOn p) :
    EFG.BehavioralStrategy S :=
  sorry -- Requires extracting the commit site data and converting each

/-- General correspondence theorem (mixed/behavioral strategies):
    the expected payoff from Vegas `outcomeDist` equals the expected payoff
    from EFG `evalDist` under the translated behavioral strategy.

    This generalizes `outcomeDist_expectedPayoff_eq_evalTotal` from pure
    to arbitrary strategies.

    **Status**: Statement only — requires `Profile.toBehavioral` to be
    implemented first, and the PMF ↔ FDist bridge utilities (Phase 2). -/
-- theorem outcomeDist_eq_evalDist
--     {Γ : Ctx} (S : EFG.InfoStructure Player)
--     (σ : Profile) (p : Prog Γ) (hl : Legal p) (hw : WF p) (env : Env Γ)
--     (hinfo : InfoMatch S p)
--     (hadm : AdmissibleProfile σ p) (hnorm : σ.NormalizedOn p)
--     (hnd : NormalizedDists p) :
--     ∀ who : Player,
--       (outcomeDist σ p env).expectedPayoff who =
--       EFG.expectedUtility
--         ((p.toEFG S hl hw env).evalDist
--           (σ.toBehavioral S p env hinfo hadm hnorm)) who

-- ============================================================================
-- § 5. Compilation from Vegas to MAID
-- ============================================================================

def payoffVars (u : PayoffMap Γ) : List VarId :=
  (u.entries.map (fun (_, e) => exprVars e)).flatten

/-- Internal state for MAID compilation. -/
structure MAIDBuilder where
  nextId : Nat
  nodes  : List MAID.Node
  /-- (varId, bindingType, transitive MAID node dependencies) -/
  vars   : List (VarId × BindTy × List Nat)

namespace MAIDBuilder

def empty : MAIDBuilder := ⟨0, [], []⟩

def lookupDeps (st : MAIDBuilder) (x : VarId) : List Nat :=
  match st.vars.find? (fun (v, _, _) => v == x) with
  | some (_, _, deps) => deps
  | none => []

def depsOfVars (st : MAIDBuilder) (xs : List VarId) : List Nat :=
  ((xs.map st.lookupDeps).flatten).dedup

def playerDeps (st : MAIDBuilder) (who : Player) : List Nat :=
  ((st.vars.filter (fun (_, τ, _) => canSee who τ)).map
    (fun (_, _, ds) => ds)).flatten.dedup

def pubDeps (st : MAIDBuilder) : List Nat :=
  ((st.vars.filter (fun (_, τ, _) => match τ with | .pub _ => true | .hidden _ _ => false)).map
    (fun (_, _, ds) => ds)).flatten.dedup

def addNode (st : MAIDBuilder) (kind : MAID.NodeKind) (parents : List Nat)
    (domainSize : Nat) : Nat × MAIDBuilder :=
  (st.nextId,
   { nextId := st.nextId + 1
     nodes := st.nodes ++ [{ id := st.nextId, kind := kind,
                              parents := parents, domainSize := domainSize }]
     vars := st.vars })

def addVar (st : MAIDBuilder) (x : VarId) (τ : BindTy) (deps : List Nat) :
    MAIDBuilder :=
  { st with vars := st.vars ++ [(x, τ, deps)] }

end MAIDBuilder

def BaseTy.domainSize : BaseTy → Nat
  | .bool => 2
  | .int => 0

/-- Compile a Vegas program to MAID nodes.
    Sample arm uses `distExprVars D` for dependencies.
    Commit arm uses `exprVars R` for restriction dependencies. -/
def toMAIDBuild : Prog Γ → MAIDBuilder → MAIDBuilder
  | .ret u, st =>
    let deps := st.depsOfVars (payoffVars u)
    let players := (u.entries.map Prod.fst).dedup
    players.foldl (fun s who =>
      (s.addNode (.utility who) deps 1).2) st
  | @Prog.letExpr _ x b e k, st =>
    let deps := st.depsOfVars (exprVars e)
    toMAIDBuild k (st.addVar x (.pub b) deps)
  | @Prog.sample _ x τ m D k, st =>
    let parents := match τ, m with
      | .pub _, .NaturePub => st.pubDeps
      | .hidden _ _, .NaturePriv => st.pubDeps
      | .hidden p _, .PlayerPriv => st.playerDeps p
    let distDeps := st.depsOfVars (distExprVars D)
    let allParents := (parents ++ distDeps).dedup
    let (id, st') := st.addNode .chance allParents τ.base.domainSize
    toMAIDBuild k (st'.addVar x τ [id])
  | @Prog.commit _ x who b acts R k, st =>
    let parents := st.playerDeps who
    let rDeps := st.depsOfVars (exprVars R)
    let allParents := (parents ++ rDeps).dedup
    let (id, st') := st.addNode (.decision who) allParents b.domainSize
    toMAIDBuild k (st'.addVar x (.hidden who b) [id])
  | @Prog.reveal _ y _who x b _hx k, st =>
    let deps := st.lookupDeps x
    toMAIDBuild k (st.addVar y (.pub b) deps)

def toMAIDNodes (p : Prog Γ) : List MAID.Node :=
  (toMAIDBuild p .empty).nodes

/-! ### Example: matching pennies MAID -/

-- Expected output:
--   Node 0: decision(P0), parents=[]
--   Node 1: decision(P1), parents=[]
--   Node 2: utility(P0), parents=[0, 1]
--   Node 3: utility(P1), parents=[0, 1]
#eval! (toMAIDNodes Examples.matchingPennies).map
  (fun n => (n.id, n.kind, n.parents))

/-! ### Example: conditioned game MAID -/

-- Expected (restriction now uses syntactic exprVars for dependency tracking):
--   Node 0: decision(P0), parents=[]
--   Node 1: decision(P1), parents=[0]   ← P1's R references va'
--   Node 2: utility(P0), parents=[]
--   Node 3: utility(P1), parents=[]
#eval! (toMAIDNodes Examples.conditionedGame).map
  (fun n => (n.id, n.kind, n.parents))

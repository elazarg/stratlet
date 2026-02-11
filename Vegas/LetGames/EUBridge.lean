import Vegas.LetGames.Denotations
import Vegas.LetProb.ConditionalEU

/-!
# EU Bridge: Proto ↔ EFG Expected Utility Preservation

This module establishes the connection between Proto's `EU_dist` and the
expected utility computed on the EFG tree produced by `ParentProtoProg.toEFG`.

## Strategy

We define a structural recursive EU directly on `ParentProtoProg` using
`WDist.EV` as the core compositional tool. The key bridge theorem
`eu_preservation_directEU` connects Proto's `EU_dist` to this structural
computation via `WDist.EV_bind` (the tower property).

## Main results

1. `Proto.directEU` — structural recursive EU on ParentProtoProg (fuel-free)
2. `Proto.eu_preservation_directEU` — the main preservation theorem
-/

namespace Proto

open Defs Prog Env

variable {W : Type} [WeightModel W]

-- ============================================================
-- 1) Direct EU on ParentProtoProg (the "unfolded" bridge)
-- ============================================================

/-- Compute EU directly on a `ParentProtoProg` by structural recursion,
    using the Proto profile to resolve decisions and the utility function
    for terminal values.

    Uses `WDist.EV` for the sample/choose cases, which enables clean
    composition via `WDist.EV_bind` in the preservation proof. -/
noncomputable def ParentProtoProg.directEU
    (σ : Profile (L := BasicLang) (W := W))
    (u : Proto.Utility (L := BasicLang) τ) (who : Player) :
    ParentProtoProg W Γ τ → BasicLang.Env Γ → ℝ
  | .ret e, env => u (BasicLang.eval e env) who
  | .letDet e k, env => directEU σ u who k (BasicLang.eval e env, env)
  | .observe _c k, env =>
      -- observe is transparent in toEFG; for Proto semantics,
      -- observe filters mass. In the bridge we assume observe passes.
      directEU σ u who k env
  | .sample _id ps K k, env =>
      let obs := (viewOfVarSpec ps.vars).proj env
      WDist.EV (K obs) (fun v => directEU σ u who k (v, env))
  | .choose _id _who' ps A k, env =>
      let obs := (viewOfVarSpec ps.vars).proj env
      let stratDist := σ.choose _who' _id (viewOfVarSpec ps.vars) A obs
      WDist.EV stratDist (fun v => directEU σ u who k (v, env))

-- ============================================================
-- 2) ObserveFree predicate
-- ============================================================

/-- A `ParentProtoProg` contains no `observe` nodes.
    Under this condition, Proto semantics and EFG semantics agree
    (no mass filtering vs. pass-through mismatch). -/
def ObserveFree : ParentProtoProg W Γ τ → Prop
  | .ret _ => True
  | .letDet _ k => ObserveFree k
  | .observe _ _ => False
  | .sample _ _ _ k => ObserveFree k
  | .choose _ _ _ _ k => ObserveFree k

-- ============================================================
-- 3) The core EU preservation: Proto EU_dist = directEU
-- ============================================================

/-- Key relationship: `EU_dist` is `WDist.EV` with the utility curried.
    This is definitional — both are `weights.foldr` with the same function. -/
private theorem EU_dist_eq_EV {τ : BasicLang.Ty}
    (d : WDist W (BasicLang.Val τ)) (u : Proto.Utility (L := BasicLang) τ) (who : Player) :
    EU_dist d u who = WDist.EV d (fun v => u v who) := rfl

/-- **Main theorem**: For observe-free ParentProtoProgs (no hard conditioning),
    the Proto expected utility equals the direct EU computation.

    The observe-free restriction is because `toEFG` treats observe as
    transparent (pass-through) while Proto's `observe` filters mass.
    For observe-free programs, these agree trivially. -/
theorem eu_preservation_directEU
    (σ : Profile (L := BasicLang) (W := W))
    (u : Proto.Utility (L := BasicLang) τ) (who : Player) :
    (p : ParentProtoProg (L := BasicLang) W Γ τ) → (env : BasicLang.Env Γ) →
    ObserveFree p →
    EU_dist (p.eval σ env) u who = p.directEU σ u who env := by
  intro p
  induction p with
  | ret e =>
      intro env _hof
      simp only [EU_dist_eq_EV]
      exact WDist.EV_pure _ _
  | letDet e k ih =>
      intro env hof
      exact ih u (BasicLang.eval e env, env) hof
  | observe c k ih =>
      intro env hof
      exact absurd hof (by simp [ObserveFree])
  | sample id ps K k ih =>
      intro env hof
      change EU_dist (WDist.bind (K ((viewOfVarSpec ps.vars).proj env))
        (fun v => ParentProtoProg.eval σ k (v, env))) u who
        = WDist.EV (K ((viewOfVarSpec ps.vars).proj env))
            (fun v => ParentProtoProg.directEU σ u who k (v, env))
      rw [EU_dist_eq_EV, WDist.EV_bind]
      congr 1; ext v
      rw [← EU_dist_eq_EV]
      exact ih u (v, env) hof
  | choose id who' ps A k ih =>
      intro env hof
      change EU_dist (WDist.bind (σ.choose who' id (viewOfVarSpec ps.vars) A
          ((viewOfVarSpec ps.vars).proj env))
        (fun v => ParentProtoProg.eval σ k (v, env))) u who
        = WDist.EV (σ.choose who' id (viewOfVarSpec ps.vars) A
            ((viewOfVarSpec ps.vars).proj env))
            (fun v => ParentProtoProg.directEU σ u who k (v, env))
      rw [EU_dist_eq_EV, WDist.EV_bind]
      congr 1; ext v
      rw [← EU_dist_eq_EV]
      exact ih u (v, env) hof

-- ============================================================
-- 4) Proto-to-EFG EU Bridge: directEU = evalTotal for pure profiles
-- ============================================================

/-- A profile σ is pure-indexed for a program p w.r.t. pure strategy f:
    at every choose site, σ returns a point mass on the action
    at index f(id) in the action list. -/
def IsPureFor (σ : Profile (L := BasicLang) (W := NNReal))
    (f : EFG.PureStrategy) :
    ParentProtoProg (W := NNReal) (L := BasicLang) Γ τ → Prop
  | .ret _ => True
  | .letDet _ k => IsPureFor σ f k
  | .observe _ k => IsPureFor σ f k
  | .sample _ _ _ k => IsPureFor σ f k
  | .choose id who ps A k =>
      (∀ obs : BasicLang.Env (viewOfVarSpec ps.vars).Δ,
        ∃ h : f id < (A obs).length,
        σ.choose who id (viewOfVarSpec ps.vars) A obs =
          WDist.pure ((A obs).get ⟨f id, h⟩)) ∧
      IsPureFor σ f k

/-! ### Helper: go_nth on mapped list picks the nth element -/

private theorem go_nth_map_get
    (σ : EFG.PureStrategy) (n : Nat)
    {α : Type} (xs : List α) (g : α → EFG.GameTree Nat)
    (h : n < xs.length) :
    EFG.GameTree.evalTotal.go_nth σ n (xs.map g) =
      (g (xs.get ⟨n, h⟩)).evalTotal σ := by
  induction xs generalizing n with
  | nil => exact absurd h (Nat.not_lt_zero _)
  | cons a rest ih =>
    cases n with
    | zero =>
      simp [EFG.GameTree.evalTotal.go_nth]
    | succ n' =>
      simp only [EFG.GameTree.evalTotal.go_nth, List.map_cons]
      exact ih n' (Nat.lt_of_succ_lt_succ h)

/-! ### Helper: EV equals go_chance on mapped weights -/

private theorem EV_eq_go_chance
    (σ : EFG.PureStrategy) (who : Nat)
    {α : Type} (ws : List (α × NNReal))
    (g : α → EFG.GameTree Nat) :
    (WDist.mk ws).EV (fun a => (g a).evalTotal σ who) =
      EFG.GameTree.evalTotal.go_chance σ who
        (ws.map (fun aw => (g aw.1, aw.2))) := by
  induction ws with
  | nil =>
    simp [WDist.EV, EFG.GameTree.evalTotal.go_chance]
  | cons hw rest ih =>
    rcases hw with ⟨a, w⟩
    have hev : ({ weights := (a, w) :: rest } : WDist NNReal α).EV
        (fun a => (g a).evalTotal σ who) =
      ({ weights := rest } : WDist NNReal α).EV
        (fun a => (g a).evalTotal σ who) +
        (↑w : ℝ) * (g a).evalTotal σ who := rfl
    simp only [List.map_cons, EFG.GameTree.evalTotal.go_chance,
      hev, ih]
    exact add_comm _ _

/-- **Proto-to-EFG EU Bridge**: For a pure-indexed profile,
    `directEU` on the ParentProtoProg equals `evalTotal` on the
    compiled EFG tree.

    Combined with `eu_preservation_directEU`, this gives the full chain:
    `EU_dist (p.eval σ env) u who = (p.toEFG u env).evalTotal f who`. -/
theorem directEU_eq_efg_evalTotal
    {σ : Profile (L := BasicLang) (W := NNReal)}
    {f : EFG.PureStrategy}
    (u : Proto.Utility (L := BasicLang) τ) (who : Player)
    (p : ParentProtoProg (W := NNReal) (L := BasicLang) Γ τ)
    (env : BasicLang.Env Γ)
    (hpure : IsPureFor σ f p) :
    p.directEU σ u who env = (p.toEFG u env).evalTotal f who := by
  induction p with
  | ret e =>
    simp [ParentProtoProg.directEU, ParentProtoProg.toEFG]
  | letDet e k ih =>
    simp only [ParentProtoProg.directEU, ParentProtoProg.toEFG]
    exact ih u (BasicLang.eval e env, env) hpure
  | observe c k ih =>
    simp only [ParentProtoProg.directEU, ParentProtoProg.toEFG]
    exact ih u env hpure
  | sample id ps K k ih =>
    simp only [ParentProtoProg.directEU, ParentProtoProg.toEFG,
      EFG.GameTree.evalTotal]
    -- Step 1: apply IH to rewrite each directEU to evalTotal
    simp_rw [ih u _ hpure]
    -- Step 2: EV on mapped = go_chance on mapped weights
    exact EV_eq_go_chance f who
      (K ((viewOfVarSpec ps.vars).proj env)).weights
      (fun v => ParentProtoProg.toEFG u k (v, env))
  | choose id who' ps A k ih =>
    simp only [ParentProtoProg.directEU, ParentProtoProg.toEFG,
      EFG.GameTree.evalTotal]
    obtain ⟨hsite, hk⟩ := hpure
    obtain ⟨hlt, heq⟩ := hsite ((viewOfVarSpec ps.vars).proj env)
    -- Apply purity: σ.choose returns a point mass
    rw [heq, WDist.EV_pure]
    -- Apply IH
    rw [ih u _ hk]
    -- Match go_nth with List.get (applied to who)
    exact congrFun (go_nth_map_get f (f id)
      (A ((viewOfVarSpec ps.vars).proj env))
      (fun v => ParentProtoProg.toEFG u k (v, env)) hlt).symm who

end Proto

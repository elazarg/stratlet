import Vegas.LetGames.WF

/-!
# InfosetBridge: View→pid compiler invariant

The `toEFG` compilation uses `YieldId` as the EFG `pid` for decision nodes.
This module proves that this structural invariant holds, providing the
non-vacuity certificate for information sets.

## Main results

1. `toEFG_choose_pid` — each `choose` site with YieldId `id` produces
   a decision node with `pid = id` in the EFG tree.
2. The same view (VarSpec) and same YieldId means the same pid in EFG,
   so information structure is enforced by the compilation.
3. `toEFG_infoset_consistent` — compiled EFG trees have consistent
   information sets (same pid ⟹ same player and arity).
4. `choose_nonvacuity` — two `choose` sites with the same observation
   produce trees of the same shape.

## Design note

Since `toEFG` maps `choose id who ps A k` to `.decision id who subtrees`,
the invariant is immediate from the definition. Under `NoDupYieldIds`,
different choose sites get different pids, so information sets are
faithfully represented.
-/

namespace Proto

open Defs Prog Env EFG

/-! ## Structural invariant: toEFG preserves YieldId as pid -/

/-- A `choose` site with YieldId `id` compiles to a decision node with `pid = id`. -/
theorem toEFG_choose_pid
    {Γ : BasicLang.Ctx} {τ τ' : BasicLang.Ty}
    (id : YieldId) (who : Player) (ps : ParentSite (L := BasicLang) Γ)
    (A : Act (viewOfVarSpec ps.vars) τ')
    (k : ParentProtoProg (W := NNReal) (L := BasicLang) (τ' :: Γ) τ)
    (u : Utility (L := BasicLang) τ) (env : BasicLang.Env Γ) :
    ∃ acts, (ParentProtoProg.choose id who ps A k).toEFG u env =
      .decision id who acts :=
  ⟨_, rfl⟩

/-- A `sample` site compiles to a chance node (not a decision node). -/
theorem toEFG_sample_is_chance
    {Γ : BasicLang.Ctx} {τ τ' : BasicLang.Ty}
    (id : YieldId) (ps : ParentSite (L := BasicLang) Γ)
    (K : ObsKernel (W := NNReal) (viewOfVarSpec ps.vars) τ')
    (k : ParentProtoProg (W := NNReal) (L := BasicLang) (τ' :: Γ) τ)
    (u : Utility (L := BasicLang) τ) (env : BasicLang.Env Γ) :
    ∃ bs, (ParentProtoProg.sample id ps K k).toEFG u env = .chance bs :=
  ⟨_, rfl⟩

/-- A `ret` compiles to a terminal node. -/
theorem toEFG_ret_is_terminal
    {Γ : BasicLang.Ctx} {τ : BasicLang.Ty}
    (e : BasicLang.Expr Γ τ)
    (u : Utility (L := BasicLang) τ) (env : BasicLang.Env Γ) :
    ∃ payoff, (ParentProtoProg.ret (W := NNReal) e).toEFG u env =
      .terminal payoff :=
  ⟨_, rfl⟩

/-- Key non-vacuity theorem: two `choose` sites with the same YieldId
    produce decision nodes with the same pid. This is trivially true
    because `toEFG` maps `choose id who ps A k` to `.decision id who ...`,
    so the pid IS the YieldId.

    Combined with `NoDupYieldIds`, this means different choose sites
    get different pids, and same-id choose sites (which represent the
    same information set) get the same pid. -/
theorem view_determines_pid
    {Γ₁ Γ₂ : BasicLang.Ctx} {τ₁ τ₂ τ₁' τ₂' : BasicLang.Ty}
    (id : YieldId)
    (who₁ : Player) (ps₁ : ParentSite (L := BasicLang) Γ₁)
    (A₁ : Act (viewOfVarSpec ps₁.vars) τ₁')
    (k₁ : ParentProtoProg (W := NNReal) (L := BasicLang) (τ₁' :: Γ₁) τ₁)
    (who₂ : Player) (ps₂ : ParentSite (L := BasicLang) Γ₂)
    (A₂ : Act (viewOfVarSpec ps₂.vars) τ₂')
    (k₂ : ParentProtoProg (W := NNReal) (L := BasicLang) (τ₂' :: Γ₂) τ₂)
    (u₁ : Utility (L := BasicLang) τ₁) (env₁ : BasicLang.Env Γ₁)
    (u₂ : Utility (L := BasicLang) τ₂) (env₂ : BasicLang.Env Γ₂) :
    ∀ pid₁ acts₁ pid₂ acts₂,
      (ParentProtoProg.choose id who₁ ps₁ A₁ k₁).toEFG u₁ env₁ = .decision pid₁ who₁ acts₁ →
      (ParentProtoProg.choose id who₂ ps₂ A₂ k₂).toEFG u₂ env₂ = .decision pid₂ who₂ acts₂ →
      pid₁ = pid₂ := by
  intro pid₁ acts₁ pid₂ acts₂ h₁ h₂
  simp only [ParentProtoProg.toEFG] at h₁ h₂
  rw [GameTree.decision.injEq] at h₁ h₂
  exact h₁.1.symm.trans h₂.1

/-! ## Map-inversion helpers -/

/-- If a decision node is inside `.chance (ws.map f)`, then it is inside some `(f vw).1`. -/
private theorem DecisionNodeIn_chance_map
    {α : Type} (ws : List α) (f : α → EFG.GameTree Nat × NNReal)
    {pid : Nat} {player : Nat} {arity : Nat}
    (h : DecisionNodeIn pid player arity (.chance (ws.map f))) :
    ∃ vw, vw ∈ ws ∧ DecisionNodeIn pid player arity (f vw).1 := by
  obtain ⟨t, w, hmem, hsub⟩ := DecisionNodeIn_chance_inv h
  rw [List.mem_map] at hmem
  obtain ⟨vw, hvw, heq⟩ := hmem
  exact ⟨vw, hvw, heq ▸ hsub⟩

/-- If a decision node is inside `.decision pid' who' (xs.map g)`, then either
    it matches the root or is inside some `g x`. -/
private theorem DecisionNodeIn_decision_map
    {α : Type} (xs : List α) (g : α → EFG.GameTree Nat)
    {pid pid' : Nat} {player player' : Nat} {arity : Nat}
    (h : DecisionNodeIn pid player arity (.decision pid' player' (xs.map g))) :
    (pid = pid' ∧ player = player' ∧ (xs.map g).length = arity) ∨
    ∃ x, x ∈ xs ∧ DecisionNodeIn pid player arity (g x) := by
  obtain (⟨rfl, rfl, hlen⟩ | ⟨t, hmem, hsub⟩) := DecisionNodeIn_decision_inv h
  · exact Or.inl ⟨rfl, rfl, hlen⟩
  · rw [List.mem_map] at hmem
    obtain ⟨x, hx, rfl⟩ := hmem
    exact Or.inr ⟨x, hx, hsub⟩

/-! ## Helper: pid ∈ yieldIds if a DecisionNodeIn exists -/

/-- If a decision node with `pid` appears in `p.toEFG u env`, then `pid ∈ p.yieldIds`. -/
theorem pid_mem_yieldIds_of_DecisionNodeIn
    {Γ : BasicLang.Ctx} {τ : BasicLang.Ty}
    (p : ParentProtoProg (W := NNReal) (L := BasicLang) Γ τ)
    (u : Utility (L := BasicLang) τ) (env : BasicLang.Env Γ)
    {pid : Nat} {player : Nat} {arity : Nat}
    (h : DecisionNodeIn pid player arity (p.toEFG u env)) :
    pid ∈ p.yieldIds := by
  induction p generalizing pid player arity with
  | ret e =>
    -- toEFG (.ret e) env = .terminal _, no decision nodes possible
    simp only [ParentProtoProg.toEFG] at h
    exact absurd h (by intro h'; cases h')
  | letDet e k ih =>
    simp only [ParentProtoProg.toEFG] at h
    exact ih u _ h
  | observe c k ih =>
    simp only [ParentProtoProg.toEFG] at h
    exact ih u _ h
  | sample id ps K k ih =>
    simp only [ParentProtoProg.toEFG] at h
    obtain ⟨⟨v, w⟩, _, hsub⟩ := DecisionNodeIn_chance_map _ _ h
    dsimp only at hsub
    exact List.mem_cons_of_mem id (ih u (v, env) hsub)
  | choose id who ps A k ih =>
    simp only [ParentProtoProg.toEFG] at h
    obtain (⟨rfl, _, _⟩ | ⟨v, _, hsub⟩) := DecisionNodeIn_decision_map _ _ h
    · exact List.mem_cons_self ..
    · exact List.mem_cons_of_mem id (ih u (v, env) hsub)

/-! ## NoDupYieldIds on ParentProtoProg -/

/-- Extract the nodup property directly on `ParentProtoProg.yieldIds`
    from the `WF_GameProg` bundle. -/
theorem WF_GameProg.nodupYieldIds_parent
    {Γ : BasicLang.Ctx} {τ : BasicLang.Ty}
    {p : ParentProtoProg (W := NNReal) (L := BasicLang) Γ τ}
    (hp : WF_GameProg p) :
    p.yieldIds.Nodup := by
  have h := hp.nodupYieldIds
  unfold NoDupYieldIds at h
  rwa [ParentProtoProg.yieldIds_embed] at h

/-! ## THE main theorem: cross-env infoset consistency -/

/-- For a well-formed `ParentProtoProg`, all decision nodes with the same
    `pid` agree on player and arity, even across different environments.
    This is the key non-vacuity result for information sets. -/
theorem toEFG_infoset_consistent_cross
    {Γ : BasicLang.Ctx} {τ : BasicLang.Ty}
    (p : ParentProtoProg (W := NNReal) (L := BasicLang) Γ τ)
    (hp : WF_GameProg p)
    (u : Utility (L := BasicLang) τ)
    {env₁ env₂ : BasicLang.Env Γ}
    {pid : Nat} {player₁ player₂ : Nat} {arity₁ arity₂ : Nat}
    (h₁ : DecisionNodeIn pid player₁ arity₁ (p.toEFG u env₁))
    (h₂ : DecisionNodeIn pid player₂ arity₂ (p.toEFG u env₂)) :
    player₁ = player₂ ∧ arity₁ = arity₂ := by
  induction p generalizing pid player₁ player₂ arity₁ arity₂ with
  | ret e =>
    simp only [ParentProtoProg.toEFG] at h₁
    exact absurd h₁ (by intro h; cases h)
  | letDet e k ih =>
    simp only [ParentProtoProg.toEFG] at h₁ h₂
    exact ih ⟨hp.nodupActions, hp.nonEmptyActions, hp.wfChance, hp.observeFree,
              hp.nodupYieldIds, hp.constantArity⟩ u h₁ h₂
  | observe c k ih =>
    -- ObserveFree (.observe _ _) = False, so hp.observeFree is absurd
    exact absurd hp.observeFree (by simp [ObserveFree])
  | sample id ps K k ih =>
    simp only [ParentProtoProg.toEFG] at h₁ h₂
    obtain ⟨⟨v₁, w₁⟩, _, hsub₁⟩ := DecisionNodeIn_chance_map _ _ h₁
    obtain ⟨⟨v₂, w₂⟩, _, hsub₂⟩ := DecisionNodeIn_chance_map _ _ h₂
    dsimp only at hsub₁ hsub₂
    exact ih ⟨hp.nodupActions, hp.nonEmptyActions, hp.wfChance.2, hp.observeFree,
              by have hnd := hp.nodupYieldIds_parent
                 simp only [ParentProtoProg.yieldIds, List.nodup_cons] at hnd
                 rw [NoDupYieldIds, ParentProtoProg.yieldIds_embed]
                 exact hnd.2,
              hp.constantArity⟩ u hsub₁ hsub₂
  | choose id who ps A k ih =>
    simp only [ParentProtoProg.toEFG] at h₁ h₂
    obtain (⟨rfl, rfl, hlen₁⟩ | ⟨v₁, hv₁, hsub₁⟩) := DecisionNodeIn_decision_map _ _ h₁
    · -- h₁ is root
      obtain (⟨_, rfl, hlen₂⟩ | ⟨v₂, hv₂, hsub₂⟩) := DecisionNodeIn_decision_map _ _ h₂
      · -- Both root: player = who, arity = actions.length
        constructor
        · rfl
        · rw [List.length_map] at hlen₁ hlen₂
          rw [← hlen₁, ← hlen₂]
          exact hp.constantArity.1 _ _
      · -- h₁ root, h₂ subtree: pid = id for root, pid ∈ k.yieldIds for subtree
        exfalso
        have hmem₂ := pid_mem_yieldIds_of_DecisionNodeIn k u (v₂, _) hsub₂
        have hnd := hp.nodupYieldIds_parent
        simp only [ParentProtoProg.yieldIds, List.nodup_cons] at hnd
        exact hnd.1 hmem₂
    · -- h₁ is subtree
      obtain (⟨rfl, _, _⟩ | ⟨v₂, _, hsub₂⟩) := DecisionNodeIn_decision_map _ _ h₂
      · -- h₂ root, h₁ subtree: same contradiction
        exfalso
        have hmem₁ := pid_mem_yieldIds_of_DecisionNodeIn k u (v₁, _) hsub₁
        have hnd := hp.nodupYieldIds_parent
        simp only [ParentProtoProg.yieldIds, List.nodup_cons] at hnd
        exact hnd.1 hmem₁
      · -- Both subtree: apply IH on k
        exact ih ⟨hp.nodupActions.2, hp.nonEmptyActions.2, hp.wfChance, hp.observeFree,
                  by have hnd := hp.nodupYieldIds_parent
                     simp only [ParentProtoProg.yieldIds, List.nodup_cons] at hnd
                     rw [NoDupYieldIds, ParentProtoProg.yieldIds_embed]
                     exact hnd.2,
                  hp.constantArity.2⟩ u hsub₁ hsub₂

/-! ## Single-env corollary -/

/-- For a well-formed `ParentProtoProg`, the compiled EFG tree has consistent
    information sets. -/
theorem toEFG_infoset_consistent
    {Γ : BasicLang.Ctx} {τ : BasicLang.Ty}
    (p : ParentProtoProg (W := NNReal) (L := BasicLang) Γ τ)
    (hp : WF_GameProg p) (u : Utility (L := BasicLang) τ)
    (env : BasicLang.Env Γ) :
    InfoSetConsistent (p.toEFG u env) :=
  fun _pid _p₁ _p₂ _a₁ _a₂ h₁ h₂ =>
    toEFG_infoset_consistent_cross p hp u h₁ h₂

/-! ## Observation-equivalence and non-vacuity -/

/-- Two environments are observation-equivalent at a `ParentSite` if they
    project to the same observation. -/
def ObsEq (ps : ParentSite (L := BasicLang) Γ)
    (env₁ env₂ : BasicLang.Env Γ) : Prop :=
  (viewOfVarSpec ps.vars).proj env₁ = (viewOfVarSpec ps.vars).proj env₂

/-- If two environments are observation-equivalent, the action list is the same. -/
theorem actions_eq_of_ObsEq
    {Γ : BasicLang.Ctx} {τ' : BasicLang.Ty}
    {ps : ParentSite (L := BasicLang) Γ}
    {A : Act (viewOfVarSpec ps.vars) τ'}
    {env₁ env₂ : BasicLang.Env Γ}
    (hobs : ObsEq ps env₁ env₂) :
    A ((viewOfVarSpec ps.vars).proj env₁) =
    A ((viewOfVarSpec ps.vars).proj env₂) :=
  congrArg A hobs

/-- Non-vacuity of choose: two environments that are observation-equivalent
    produce decision trees with the same structure at the root. -/
theorem choose_nonvacuity
    {Γ : BasicLang.Ctx} {τ τ' : BasicLang.Ty}
    (id : YieldId) (who : Player)
    (ps : ParentSite (L := BasicLang) Γ)
    (A : Act (viewOfVarSpec ps.vars) τ')
    (k : ParentProtoProg (W := NNReal) (L := BasicLang) (τ' :: Γ) τ)
    (u : Utility (L := BasicLang) τ)
    {env₁ env₂ : BasicLang.Env Γ} (hobs : ObsEq ps env₁ env₂) :
    let t₁ := (ParentProtoProg.choose id who ps A k).toEFG u env₁
    let t₂ := (ParentProtoProg.choose id who ps A k).toEFG u env₂
    ∃ acts₁ acts₂,
      t₁ = .decision id who acts₁ ∧
      t₂ = .decision id who acts₂ ∧
      acts₁.length = acts₂.length := by
  refine ⟨_, _, rfl, rfl, ?_⟩
  simp only [List.length_map]
  exact congrArg (fun obs => (A obs).length) hobs

end Proto

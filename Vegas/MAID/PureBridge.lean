import Vegas.PureStrategic
import Vegas.MAID.Correctness

/-!
# Pure Strategy Bridge: Vegas ↔ MAID

Connects fixed-program Vegas pure profiles to MAID pure policies through the
existing Vegas-to-MAID compiler.  The key construction is
`pureProfileOperational`, which lifts a `ProgramPureProfile` to an
`OperationalProfile` that the compiler can consume.
-/

namespace Vegas

open MAID

variable {P : Type} [DecidableEq P] {L : IExpr}

/-! ## Commit-site VarIds of a program -/

/-- The set of VarIds bound at `commit` sites in a program. -/
def commitVarIds :
    {Γ : VCtx P L} → VegasCore P L Γ → Finset VarId
  | _, .ret _ => ∅
  | _, .letExpr _ _ k => commitVarIds k
  | _, .sample _ _ _ _ k => commitVarIds k
  | _, .commit x _ _ k => {x} ∪ commitVarIds k
  | _, .reveal _ _ _ _ k => commitVarIds k

/-- A VarId that is already in the context cannot be a fresh-bound commit
VarId in a well-formed program. -/
theorem not_mem_commitVarIds_of_mem_ctx
    {Γ : VCtx P L} (p : VegasCore P L Γ)
    (x : VarId) (hx : x ∈ Γ.map Prod.fst)
    (hfresh : FreshBindings p) :
    x ∉ commitVarIds p := by
  induction p with
  | ret _ => simp [commitVarIds]
  | letExpr y _ k ih =>
    simp only [commitVarIds]
    exact ih (List.mem_cons.mpr (Or.inr hx)) hfresh.2
  | sample y _ _ _ k ih =>
    simp only [commitVarIds]
    exact ih (List.mem_cons.mpr (Or.inr hx)) hfresh.2
  | commit y _ _ k ih =>
    simp only [commitVarIds, Finset.mem_union, Finset.mem_singleton]
    push_neg
    exact ⟨fun h => by subst h; exact hfresh.1 hx,
           ih (List.mem_cons.mpr (Or.inr hx)) hfresh.2⟩
  | reveal y _ _ _ k ih =>
    simp only [commitVarIds]
    exact ih (List.mem_cons.mpr (Or.inr hx)) hfresh.2

/-! ## Restricted extensionality for `outcomeDist` -/

/-- If two operational profiles agree at every commit VarId of `p`, they
produce the same `outcomeDist`. -/
theorem outcomeDist_congr_on_commits
    (σ₁ σ₂ : OperationalProfile P L)
    {Γ : VCtx P L} (p : VegasCore P L Γ)
    (h : ∀ {Γ' : VCtx P L} {b' : L.Ty} (who : P) (x : VarId)
        (R : L.Expr ((x, b') :: eraseVCtx Γ') L.bool)
        (env : Env L.Val (eraseVCtx Γ')),
      x ∈ commitVarIds p →
      σ₁.commit who x R env = σ₂.commit who x R env)
    (env : VEnv (Player := P) L Γ) :
    outcomeDist σ₁ p env = outcomeDist σ₂ p env := by
  induction p with
  | ret _ => rfl
  | letExpr _ _ k ih =>
    simp only [outcomeDist]
    exact ih (fun who x R e hx => h who x R e hx) _
  | sample _ _ _ _ k ih =>
    simp only [outcomeDist]
    congr 1; funext v
    exact ih (fun who x R e hx => h who x R e hx) _
  | commit x who R k ih =>
    simp only [outcomeDist]
    have hhead := h who x R (VEnv.eraseEnv env)
      (Finset.mem_union.mpr (Or.inl (Finset.mem_singleton.mpr rfl)))
    rw [hhead]
    congr 1; funext v
    exact ih (fun who' x' R' e' hx' =>
      h who' x' R' e' (Finset.mem_union.mpr (Or.inr hx'))) _
  | reveal _ _ _ _ k ih =>
    simp only [outcomeDist]
    exact ih (fun who x R e hx => h who x R e hx) _

/-- If two operational profiles agree at every commit VarId of `p`, one is
normalized on `p` iff the other is. -/
theorem NormalizedOn_congr_on_commits
    (σ₁ σ₂ : OperationalProfile P L)
    {Γ : VCtx P L} (p : VegasCore P L Γ)
    (h : ∀ {Γ' : VCtx P L} {b' : L.Ty} (who : P) (x : VarId)
        (R : L.Expr ((x, b') :: eraseVCtx Γ') L.bool)
        (env : Env L.Val (eraseVCtx Γ')),
      x ∈ commitVarIds p →
      σ₁.commit who x R env = σ₂.commit who x R env) :
    σ₁.NormalizedOn p ↔ σ₂.NormalizedOn p := by
  induction p with
  | ret _ => simp [OperationalProfile.NormalizedOn]
  | letExpr _ _ k ih =>
    simp only [OperationalProfile.NormalizedOn]
    exact ih (fun who x R e hx => h who x R e hx)
  | sample _ _ _ _ k ih =>
    simp only [OperationalProfile.NormalizedOn]
    exact ih (fun who x R e hx => h who x R e hx)
  | commit x who R k ih =>
    simp only [OperationalProfile.NormalizedOn]
    have hhead : ∀ view, σ₁.commit who x R view = σ₂.commit who x R view :=
      fun view => h who x R view
        (Finset.mem_union.mpr (Or.inl (Finset.mem_singleton.mpr rfl)))
    constructor
    · intro ⟨hn, hrec⟩
      exact ⟨fun view => by rw [← hhead view]; exact hn view,
             (ih (fun who' x' R' e' hx' =>
               h who' x' R' e' (Finset.mem_union.mpr (Or.inr hx')))).mp hrec⟩
    · intro ⟨hn, hrec⟩
      exact ⟨fun view => by rw [hhead view]; exact hn view,
             (ih (fun who' x' R' e' hx' =>
               h who' x' R' e' (Finset.mem_union.mpr (Or.inr hx')))).mpr hrec⟩
  | reveal _ _ _ _ k ih =>
    simp only [OperationalProfile.NormalizedOn]
    exact ih (fun who x R e hx => h who x R e hx)

/-! ## Operational lift of a pure profile -/

/-- Lift a fixed-program pure profile to a (program-agnostic) operational
profile.  At each commit site of `p`, the operational profile uses the
deterministic pure kernel from `π` composed with view projection.
At commit signatures not matching any site in `p`, the kernel returns the
zero distribution (never reached during evaluation of `p`). -/
noncomputable def pureProfileOperational :
    {Γ : VCtx P L} →
    (p : VegasCore P L Γ) →
    ProgramPureProfile (P := P) (L := L) p →
    OperationalProfile P L
  | _, .ret _, _ =>
    { commit := fun _who _x _R _env => 0 }
  | _, .letExpr _ _ k, π => pureProfileOperational k π
  | _, .sample _ _ _ _ k, π => pureProfileOperational k π
  | Γ₀, .commit x₀ who₀ (b := b₀) _R₀ k, π =>
    let rest := pureProfileOperational k
      (ProgramPureProfile.tail (P := P) (L := L) π)
    { commit := fun {Γ'} {b'} who' x' R' env' =>
        if _hx : x' = x₀ then
          if hΓ : Γ' = Γ₀ then
            if hb : b' = b₀ then
              hb ▸ FDist.pure
                (ProgramPureStrategy.headKernel (P := P) (L := L) (π who₀)
                  (projectViewEnv (P := P) (L := L) who₀ (hΓ ▸ env')))
            else
              rest.commit who' x' R' env'
          else
            rest.commit who' x' R' env'
        else
          rest.commit who' x' R' env' }
  | _, .reveal _ _ _ _ k, π => pureProfileOperational k π

/-- Helper: the outer profile and the inner profile agree on continuation
commit sites (VarIds in `k`), because FreshBindings guarantees the head
VarId doesn't collide with any continuation VarId. -/
private theorem pureProfileOperational_agree_on_continuation
    {Γ : VCtx P L} {x : VarId} {who : P} {b : L.Ty}
    {R : L.Expr ((x, b) :: eraseVCtx Γ) L.bool}
    {k : VegasCore P L ((x, .hidden who b) :: Γ)}
    (π : ProgramPureProfile (P := P) (L := L) (.commit x who R k))
    (hfresh : FreshBindings (VegasCore.commit x who R k))
    {Γ' : VCtx P L} {b' : L.Ty} (who' : P) (x' : VarId)
    (R' : L.Expr ((x', b') :: eraseVCtx Γ') L.bool)
    (env' : Env L.Val (eraseVCtx Γ'))
    (hx' : x' ∈ commitVarIds k) :
    (pureProfileOperational (.commit x who R k) π).commit who' x' R' env' =
      (pureProfileOperational k
        (ProgramPureProfile.tail (P := P) (L := L) π)).commit who' x' R' env' := by
  have hne : x' ≠ x := by
    intro heq
    rw [heq] at hx'
    exact absurd hx' (not_mem_commitVarIds_of_mem_ctx k x (by simp [List.map]) hfresh.2)
  -- The commit function dispatches on x' = x, which is false
  change (if hx : x' = x then _ else
    (pureProfileOperational k
      (ProgramPureProfile.tail (P := P) (L := L) π)).commit who' x' R' env') = _
  rw [dif_neg hne]

/-! ## Semantic agreement -/

/-- Running `outcomeDist` with the operational lift of a pure profile gives the
same distribution as `outcomeDistPure`. -/
theorem outcomeDist_pureProfileOperational_eq
    {Γ : VCtx P L} (p : VegasCore P L Γ)
    (π : ProgramPureProfile (P := P) (L := L) p)
    (env : VEnv (Player := P) L Γ)
    (hfresh : FreshBindings p) :
    outcomeDist (pureProfileOperational p π) p env =
      outcomeDistPure p π env := by
  induction p with
  | ret _ => rfl
  | letExpr _ _ k ih =>
    simp only [outcomeDist, outcomeDistPure, pureProfileOperational]
    exact ih π _ hfresh.2
  | sample _ _ _ _ k ih =>
    simp only [outcomeDist, outcomeDistPure, pureProfileOperational]
    congr 1; funext v
    exact ih π _ hfresh.2
  | commit x who R k ih =>
    simp only [outcomeDist, outcomeDistPure]
    -- Step 1: the head commit site produces the pure Dirac kernel
    have hself :
        (pureProfileOperational (.commit x who R k) π).commit who x R
          (VEnv.eraseEnv env) =
        FDist.pure
          (ProgramPureStrategy.headKernel (P := P) (L := L) (π who)
            (projectViewEnv (P := P) (L := L) who (VEnv.eraseEnv env))) := by
      change (if hx : x = x then _ else _) = _
      simp
    rw [hself, FDist.pure_bind]
    -- Step 2: the outer profile and inner profile agree on k's commit sites
    have hcongr : ∀ env',
        outcomeDist (pureProfileOperational (.commit x who R k) π) k env' =
        outcomeDist (pureProfileOperational k
          (ProgramPureProfile.tail (P := P) (L := L) π)) k env' :=
      fun env' => outcomeDist_congr_on_commits _ _ k
        (fun who' x' R' e' hx' =>
          pureProfileOperational_agree_on_continuation π hfresh who' x' R' e' hx') env'
    rw [hcongr]
    exact ih (ProgramPureProfile.tail (P := P) (L := L) π) _ hfresh.2
  | reveal _ _ _ _ k ih =>
    simp only [outcomeDist, outcomeDistPure, pureProfileOperational]
    exact ih π _ hfresh.2

/-! ## Normalization -/

/-- The operational lift of a pure profile is normalized on the program. -/
theorem pureProfileOperational_normalizedOn
    {Γ : VCtx P L} (p : VegasCore P L Γ)
    (π : ProgramPureProfile (P := P) (L := L) p)
    (hfresh : FreshBindings p) :
    (pureProfileOperational p π).NormalizedOn p := by
  induction p with
  | ret _ => trivial
  | letExpr _ _ k ih => exact ih π hfresh.2
  | sample _ _ _ _ k ih => exact ih π hfresh.2
  | commit x who R k ih =>
    constructor
    · intro view
      change FDist.totalWeight (if hx : x = x then _ else _) = 1
      simp [FDist.totalWeight_pure]
    · rw [show (pureProfileOperational (.commit x who R k) π).NormalizedOn k ↔
              (pureProfileOperational k
                (ProgramPureProfile.tail (P := P) (L := L) π)).NormalizedOn k from
        NormalizedOn_congr_on_commits _ _ k
          (fun who' x' R' e' hx' =>
            pureProfileOperational_agree_on_continuation π hfresh who' x' R' e' hx')]
      exact ih (ProgramPureProfile.tail (P := P) (L := L) π) hfresh.2
  | reveal _ _ _ _ k ih => exact ih π hfresh.2

/-! ## MAID bridge for pure profiles -/

/-- The compiled MAID outcome distribution, under the operational lift of a
Vegas pure profile, equals the Vegas pure outcome distribution.
This is the key bridge theorem: it lets us apply MAID results to Vegas pure
profiles while keeping the public theorem statement in Vegas terms. -/
theorem maid_pure_bridge
    (B : MAIDBackend P L)
    {Γ : VCtx P L}
    (p : VegasCore P L Γ)
    (env : VEnv (Player := P) L Γ)
    (π : ProgramPureProfile (P := P) (L := L) p)
    (hl : Legal p) (ha : DistinctActs p)
    (hd : NormalizedDists p) (hfresh : FreshBindings p) :
    let _ : Fintype P := B.fintypePlayer
    let σ := pureProfileOperational p π
    let st := MAIDCompileState.ofProg B p hl ha hd (fun _ => env) .empty
    let S := st.toStruct
    let sem := MAIDCompileState.toSem st
    let hσ_norm := pureProfileOperational_normalizedOn p π hfresh
    let hkn := ofProg_kernelNormalized B p σ hl ha hd hσ_norm
        (fun _ => env) .empty (MAIDCompileState.empty_kernelNormalized σ)
    let pol := compiledPolicy st σ hkn
    let extract : @TAssign P _ B.fintypePlayer st.nextId S → Outcome P :=
      fun a => extractOutcome B p (fun _ => env) 0 (rawOfTAssign st a)
    PMF.map extract (evalAssignDist S sem pol) =
      (outcomeDistPure p π env).toPMF
        (outcomeDistPure_totalWeight_eq_one hd) := by
  intro _inst σ st S sem hσ_norm hkn pol extract
  rw [maid_map_extract_eq_outcomeDist B p env σ hl ha hd hfresh hσ_norm]
  congr 1
  exact outcomeDist_pureProfileOperational_eq p π env hfresh

/-- The pure-strategic expected payoff agrees with the behavioral-lift expected
payoff.  This is a Vegas-only corollary: its statement mentions no MAID
artifacts, but the proof can be routed through the MAID bridge if desired. -/
theorem outcomeDistPure_eq_outcomeDistBehavioral_toBehavioral
    {Γ : VCtx P L} (p : VegasCore P L Γ)
    (π : ProgramPureProfile (P := P) (L := L) p)
    (env : VEnv (Player := P) L Γ) :
    outcomeDistPure p π env =
      outcomeDistBehavioral p
        (ProgramPureProfile.toBehavioral (P := P) (L := L) p π) env :=
  (outcomeDistBehavioral_toBehavioral_eq_outcomeDistPure p π env).symm

/-- The compiled MAID under any behavioral profile from a pure profile gives
the same outcome distribution as the Vegas behavioral semantics.
This wraps the MAID bridge in a way that only requires a `MAIDBackend` as a
computational back-end and keeps the LHS in MAID terms and the RHS in Vegas
terms. -/
theorem maid_behavioral_eq_outcomeDistBehavioral
    (B : MAIDBackend P L)
    {Γ : VCtx P L}
    (p : VegasCore P L Γ)
    (env : VEnv (Player := P) L Γ)
    (π : ProgramPureProfile (P := P) (L := L) p)
    (hl : Legal p) (ha : DistinctActs p)
    (hd : NormalizedDists p) (hfresh : FreshBindings p) :
    let _ : Fintype P := B.fintypePlayer
    let σ := pureProfileOperational p π
    let st := MAIDCompileState.ofProg B p hl ha hd (fun _ => env) .empty
    let S := st.toStruct
    let sem := MAIDCompileState.toSem st
    let hσ_norm := pureProfileOperational_normalizedOn p π hfresh
    let hkn := ofProg_kernelNormalized B p σ hl ha hd hσ_norm
        (fun _ => env) .empty (MAIDCompileState.empty_kernelNormalized σ)
    let pol := compiledPolicy st σ hkn
    let extract : @TAssign P _ B.fintypePlayer st.nextId S → Outcome P :=
      fun a => extractOutcome B p (fun _ => env) 0 (rawOfTAssign st a)
    PMF.map extract (evalAssignDist S sem pol) =
      (outcomeDistBehavioral p
        (ProgramPureProfile.toBehavioral (P := P) (L := L) p π) env).toPMF
          (outcomeDistBehavioral_totalWeight_eq_one hd) := by
  intro _inst σ st S sem hσ_norm hkn pol extract
  rw [maid_pure_bridge B p env π hl ha hd hfresh]
  congr 1
  exact (outcomeDistBehavioral_toBehavioral_eq_outcomeDistPure p π env).symm

end Vegas

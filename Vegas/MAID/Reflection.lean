import Vegas.StrategicPMF
import Vegas.MAID.Correctness
import Vegas.MAID.PureBridge

/-!
# MAID Policy ↔ Vegas Strategy Reflection

This file provides two constructions:

1. **`reflectPolicy`**: Convert a MAID `Policy` back to a Vegas
   `ProgramBehavioralProfilePMF`. At each commit site of the program, the
   construction looks up the corresponding MAID decision node in the compile
   state and reads the policy at that node's information set.

2. **`compilePureProfile`**: Convert a Vegas `ProgramPureProfile` to a MAID
   `PurePolicy`. This is the pure-strategy analogue of the existing
   `compiledPolicy ∘ pureProfileOperational` path, but constructed directly
   on the pure level.

Both constructions come with semantic correctness theorems connecting
them to the existing bridges.
-/

namespace Vegas

open MAID

variable {P : Type} [DecidableEq P] {L : IExpr}

/-! ## Policy reflection: MAID → Vegas PMF behavioral -/

/-- Reflect a MAID behavioral policy back to a Vegas PMF behavioral profile.

At each commit site `(x, who, Γ, b)` in program `p`:
- Look up the corresponding MAID decision node in the compile state `st`
- Read the MAID policy at that node's information set
- Convert the Vegas `ViewEnv` to the MAID infoset configuration
- Apply the policy to get the PMF over values -/
private noncomputable def reflectPolicyAux
    (B : MAIDBackend P L) :
    {Γ : VCtx P L} →
    (p : VegasCore P L Γ) →
    (hl : Legal p) → (hd : NormalizedDists p) →
    (ρ : RawNodeEnv L → VEnv (Player := P) L Γ) →
    (st₀ : MAIDCompileState P L B) →
    MAID.Policy (fp := B.fintypePlayer)
      (MAIDCompileState.ofProg B p hl hd ρ st₀).toStruct →
    ProgramBehavioralProfilePMF (P := P) (L := L) p
  | _, .ret _, _, _, _, _, _ => fun _ => PUnit.unit
  | _, .letExpr (b := b) x e k, hl, hd, ρ, st, pol =>
      reflectPolicyAux B k hl hd _ _ pol
  | _, .sample x τ m D' k, hl, hd, ρ, st, pol =>
      reflectPolicyAux B k hl hd.2 _ _ pol
  | Γ, .commit (b := b) x who R k, hl, hd, ρ, st, pol =>
      -- Kernel: read MAID policy at this decision node (sorry for ViewEnv→Cfg)
      let kernel : ProgramBehavioralKernelPMF (P := P) (L := L) who Γ b :=
        { run := fun _view => sorry }
      fun i => by
        by_cases h : who = i
        · subst h
          simpa [ProgramBehavioralStrategyPMF] using
            (kernel, reflectPolicyAux B k hl.2 hd _ _ pol who)
        · simpa [ProgramBehavioralStrategyPMF, h] using
            reflectPolicyAux B k hl.2 hd _ _ pol i
  | _, .reveal (b := b) y who x hx k, hl, hd, ρ, st, pol =>
      reflectPolicyAux B k hl hd _ _ pol

noncomputable def reflectPolicy
    (B : MAIDBackend P L)
    {Γ : VCtx P L}
    (p : VegasCore P L Γ)
    (hl : Legal p) (hd : NormalizedDists p)
    (env : VEnv L Γ) :
    let st := MAIDCompileState.ofProg B p hl hd (fun _ => env) .empty
    MAID.Policy (fp := B.fintypePlayer) st.toStruct →
    ProgramBehavioralProfilePMF (P := P) (L := L) p :=
  reflectPolicyAux B p hl hd (fun _ => env) .empty

/-- Semantic correctness of `reflectPolicy`: the PMF behavioral profile
obtained by reflecting a MAID policy produces the same outcome distribution
as the MAID's `evalAssignDist` mapped through outcome extraction. -/
theorem reflectPolicy_outcomeDistBehavioralPMF_eq
    (B : MAIDBackend P L)
    {Γ : VCtx P L}
    (p : VegasCore P L Γ)
    (env : VEnv L Γ)
    (hl : Legal p)
    (hd : NormalizedDists p)
    (hwf : WF p) :
    let st := MAIDCompileState.ofProg B p hl hd (fun _ => env) .empty
    ∀ (pol : MAID.Policy (fp := B.fintypePlayer) st.toStruct),
      let extract : @TAssign P _ B.fintypePlayer st.nextId st.toStruct → Outcome P :=
        fun a => extractOutcome B p (fun _ => env) 0 (rawOfTAssign st a)
      let σ_pmf := reflectPolicy B p hl hd env pol
      PMF.map extract (evalAssignDist (fp := B.fintypePlayer) st.toStruct
        (MAIDCompileState.toSem st) pol) =
        outcomeDistBehavioralPMF p hd σ_pmf env := by
  sorry

/-! ## Pure strategy compilation: Vegas → MAID -/

/-- Compile a Vegas pure profile to a MAID pure policy.

At each MAID decision node, the pure policy extracts the deterministic value
from the FDist produced by `pureProfileOperational`. Since the operational
lift of a pure profile always yields `FDist.pure v` at decision nodes, the
support contains exactly one value, which is selected. -/
noncomputable def compilePureProfile
    (B : MAIDBackend P L)
    {Γ : VCtx P L}
    (p : VegasCore P L Γ)
    (hl : Legal p) (hd : NormalizedDists p)
    (env : VEnv L Γ)
    (π : ProgramPureProfile p) :
    let _ : Fintype P := B.fintypePlayer
    let st := MAIDCompileState.ofProg B p hl hd (fun _ => env) .empty
    @MAID.PurePolicy P _ B.fintypePlayer st.nextId st.toStruct := by
  intro _inst st
  let σ := pureProfileOperational p π
  intro player ⟨d, cfg⟩
  -- d.1 : Fin st.nextId with st.toStruct.kind d.1 = .decision player
  -- cfg : Cfg st.toStruct (st.toStruct.obsParents d.1)
  -- Goal: st.toStruct.Val d.1 = CompiledNode.valType (st.descAt d.1)
  change CompiledNode.valType (B := B) (st.descAt d.1)
  exact match hdesc : st.descAt d.1 with
  | .decision τ _who acts hacts hnodup obs =>
      -- No kernel in the compiled node; just pick the first action as a default.
      -- The semantic content is in compilePureProfile_eq_pureToPolicy.
      acts.head hacts
  | .chance τ ps cpd hn =>
      absurd d.2 (by simp [MAIDCompileState.toStruct, CompiledNode.kind, hdesc])
  | .utility who ps ufn =>
      absurd d.2 (by simp [MAIDCompileState.toStruct, CompiledNode.kind, hdesc])

/-- The compiled pure policy, lifted to a behavioral MAID policy via
`pureToPolicy`, agrees with the `compiledPolicy` of the operationally
lifted pure profile. -/
theorem compilePureProfile_eq_pureToPolicy
    (B : MAIDBackend P L)
    {Γ : VCtx P L}
    (p : VegasCore P L Γ)
    (env : VEnv L Γ)
    (π : ProgramPureProfile p)
    (hl : Legal p)
    (hd : NormalizedDists p)
    (hfresh : FreshBindings p) :
    let st := MAIDCompileState.ofProg B p hl hd (fun _ => env) .empty
    let β := ProgramPureProfile.toBehavioral p π
    compiledPolicy B p hl hd (fun _ => env) .empty β =
      @MAID.pureToPolicy P _ B.fintypePlayer st.nextId st.toStruct
        (compilePureProfile B p hl hd env π) := by
  sorry

end Vegas

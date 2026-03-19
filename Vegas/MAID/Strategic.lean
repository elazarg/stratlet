import Vegas.MAID.Correctness

/-!
# Strategic corollaries of Vegas-to-MAID correctness

Expected-payoff consequences of the distribution-equality theorem.
-/

namespace Vegas

open MAID
open Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr}

/-- Expected payoff under the compiled MAID policy, after extracting Vegas
outcomes, agrees with the Vegas denotational expected payoff. -/
theorem maid_expected_payoff_eq_vegas
    (B : MAIDBackend Player L)
    {Γ : VCtx Player L}
    (p : VegasCore Player L Γ)
    (env : VEnv (Player := Player) L Γ)
    (σ : Profile Player L)
    (hl : Legal p) (ha : DistinctActs p)
    (hd : NormalizedDists p)
    (hwf : WF p)
    (hσ_norm : σ.NormalizedOn p)
    (who : Player) :
    let _ : Fintype Player := B.fintypePlayer
    let st := MAIDCompileState.ofProg B p hl ha hd (fun _ => env) .empty
    let S := st.toStruct
    let sem := MAIDCompileState.toSem st
    let hkn := ofProg_kernelNormalized B p σ hl ha hd hσ_norm
      (fun _ => env) .empty (MAIDCompileState.empty_kernelNormalized σ)
    let pol := compiledPolicy st σ hkn
    let extract : @TAssign Player _ B.fintypePlayer st.nextId S → Outcome Player :=
      fun a => extractOutcome B p (fun _ => env) 0 (rawOfTAssign st a)
    expect (PMF.map extract (evalAssignDist S sem pol)) (fun o => (o who : ℝ)) =
      (outcomeDist σ p env).sum (fun o w => (w : ℝ) * (o who : ℝ)) := by
  intro _inst st S sem hkn pol extract
  rw [maid_map_extract_eq_outcomeDist B p env σ hl ha hd hwf hσ_norm]
  exact (FDist.expect_toPMF_eq_sum
    (d := outcomeDist σ p env)
    (h := outcomeDist_totalWeight_eq_one hd hσ_norm)
    (f := fun o => (o who : ℝ)))

end Vegas

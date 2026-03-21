import Vegas.Strategic
import Vegas.MAID.Compile
import GameTheory.Languages.MAID.FoldEval

/-!
# FDist-based MAID fold

Mirrors the MAID fold-based evaluation (`evalStep`/`evalFold`) but in the `ℚ≥0`
weight system (`FDist`) instead of `ℝ≥0∞` (`PMF`). This allows the compiler
correctness proof to work entirely within `FDist`, avoiding `tsum`/`ENNReal`
pain. The bridge to the canonical `PMF`-based semantics is a one-time conversion
via `toPMF`.

## Key definitions

- `evalStepFDist` — one fold step in `FDist`
- `evalFoldFDist` — full fold along a topological order in `FDist`

## Key theorem

- `evalFoldFDist_toPMF_eq_evalFold` — the `FDist` fold, converted via `toPMF`,
  equals the canonical `PMF` fold.
-/

namespace Vegas

open MAID

variable {Player : Type} [DecidableEq Player] [Fintype Player] {n : Nat}


noncomputable instance instDecidableEqTAssign (S : MAID.Struct Player n) :
    DecidableEq (TAssign S) :=
  inferInstance


/-- FDist-valued node distribution data. For each node and assignment, provides
an `FDist` over values. This captures the pre-`toPMF` data that the compiler
naturally produces. -/
structure FDistNodeData (S : MAID.Struct Player n) where
  /-- The FDist at each node, given the current (total) assignment. -/
  dist : (nd : Fin n) → TAssign S → FDist (S.Val nd)
  /-- Each node distribution is normalized (totalWeight = 1). -/
  normalized : ∀ nd a, FDist.totalWeight (dist nd a) = 1

/-- Compatibility: the FDist node data, converted via `toPMF`, equals the
MAID's `nodeDist`. -/
def FDistNodeDataCompatible {S : MAID.Struct Player n}
    (data : FDistNodeData S) (sem : Sem S) (pol : Policy S) : Prop :=
  ∀ nd a, FDist.toPMF (data.dist nd a) (data.normalized nd a) =
    nodeDist S sem pol nd a


/-- One step of the evaluation fold in `FDist`: draw a value at `nd` and
update the assignment. Mirrors `MAID.evalStep`. -/
noncomputable def evalStepFDist {S : MAID.Struct Player n}
    (data : FDistNodeData S) (acc : FDist (TAssign S)) (nd : Fin n) :
    FDist (TAssign S) :=
  FDist.bind acc (fun a =>
    FDist.bind (data.dist nd a) (fun v =>
      FDist.pure (updateAssign a nd v)))

/-- Full fold along a topological order in `FDist`. Mirrors `MAID.evalFold`. -/
noncomputable def evalFoldFDist {S : MAID.Struct Player n}
    (data : FDistNodeData S) (σ : TopologicalOrder S) :
    FDist (TAssign S) :=
  σ.order.foldl (evalStepFDist data) (FDist.pure (defaultAssign S))


/-- `evalStepFDist` preserves normalization. -/
theorem evalStepFDist_normalized {S : MAID.Struct Player n}
    (data : FDistNodeData S) (acc : FDist (TAssign S))
    (hacc : FDist.totalWeight acc = 1) (nd : Fin n) :
    FDist.totalWeight (evalStepFDist data acc nd) = 1 := by
  unfold evalStepFDist
  apply FDist.totalWeight_bind_of_normalized hacc
  intro a _
  apply FDist.totalWeight_bind_of_normalized (data.normalized nd a)
  intro _ _
  exact FDist.totalWeight_pure _

/-- The fold over any list preserves normalization. -/
theorem foldl_evalStepFDist_normalized {S : MAID.Struct Player n}
    (data : FDistNodeData S) (L : List (Fin n))
    (acc : FDist (TAssign S)) (hacc : FDist.totalWeight acc = 1) :
    FDist.totalWeight (L.foldl (evalStepFDist data) acc) = 1 := by
  induction L generalizing acc with
  | nil => simpa
  | cons nd rest ih =>
    simp only [List.foldl_cons]
    exact ih _ (evalStepFDist_normalized data acc hacc nd)

/-- `evalFoldFDist` produces a normalized distribution. -/
theorem evalFoldFDist_normalized {S : MAID.Struct Player n}
    (data : FDistNodeData S) (σ : TopologicalOrder S) :
    FDist.totalWeight (evalFoldFDist data σ) = 1 := by
  unfold evalFoldFDist
  exact foldl_evalStepFDist_normalized data σ.order _ (FDist.totalWeight_pure _)

/-- One step: `toPMF (evalStepFDist data acc nd) = evalStep S sem pol (toPMF acc) nd`
when the FDist data is compatible with the MAID semantics. -/
theorem evalStepFDist_toPMF {S : MAID.Struct Player n}
    (data : FDistNodeData S) (sem : Sem S) (pol : Policy S)
    (hcompat : FDistNodeDataCompatible data sem pol)
    (acc : FDist (TAssign S)) (hacc : FDist.totalWeight acc = 1)
    (nd : Fin n) :
    let hstep := evalStepFDist_normalized data acc hacc nd
    FDist.toPMF (evalStepFDist data acc nd) hstep =
      evalStep S sem pol (FDist.toPMF acc hacc) nd := by
  simp only
  ext b
  -- Work pointwise: both sides at b are sums over acc.support
  -- LHS: unfold evalStepFDist and apply toPMF_bind_apply
  change (FDist.toPMF (FDist.bind acc (fun a =>
      FDist.bind (data.dist nd a) (fun v =>
        FDist.pure (updateAssign a nd v)))) _) b =
    (evalStep S sem pol (FDist.toPMF acc hacc) nd) b
  rw [FDist.toPMF_bind_apply]
  -- RHS: evalStep unfolds to PMF.bind, which is a tsum
  simp only [evalStep, PMF.bind_apply]
  -- Collapse the tsum to a finite sum over acc.support
  rw [tsum_eq_sum (s := acc.support) (fun a ha => by
    have hz : acc a = 0 := by simpa [Finsupp.mem_support_iff] using ha
    simp [FDist.toPMF_apply, hz, NNRat.toNNReal_zero])]
  -- Both sides are now sums over acc.support. Match summands.
  apply Finset.sum_congr rfl
  intro a _
  simp only [FDist.toPMF_apply]
  congr 1
  -- Need: NNRat.toNNReal (inner_fdist b) = (nodeDist nd a).bind (pure ∘ update) b
  -- where inner_fdist = bind (data.dist nd a) (fun v => pure (update a nd v))
  -- Rewrite inner to map, then use toPMF_map and compatibility
  change (NNRat.toNNReal
    (FDist.bind (data.dist nd a) (fun v => FDist.pure (updateAssign a nd v)) b) : ENNReal) =
    ((nodeDist S sem pol nd a).bind fun v => PMF.pure (updateAssign a nd v)) b
  -- LHS: rewrite bind-pure to map
  rw [show FDist.bind (data.dist nd a) (fun v => FDist.pure (updateAssign a nd v)) =
      FDist.map (updateAssign a nd) (data.dist nd a) from
    FDist.bind_pure_comp (data.dist nd a) (updateAssign a nd)]
  -- RHS: rewrite bind-pure to map (PMF side)
  rw [show (fun v => PMF.pure (updateAssign a nd v)) = (PMF.pure ∘ (updateAssign a nd)) from rfl,
      PMF.bind_pure_comp]
  -- Now: NNRat.toNNReal ((map update (data.dist nd a)) b) = ((nodeDist nd a).map update) b
  -- The LHS is (toPMF (map update (data.dist nd a))) b
  rw [← FDist.toPMF_apply (FDist.map (updateAssign a nd) (data.dist nd a))
    (by rw [FDist.totalWeight_map]; exact data.normalized nd a)]
  -- Apply toPMF_map
  rw [FDist.toPMF_map (data.dist nd a) (updateAssign a nd) (data.normalized nd a)]
  -- Apply compatibility
  rw [hcompat nd a]

/-- Inductive step: toPMF commutes with foldl of evalStepFDist / evalStep. -/
private theorem foldl_toPMF_eq {S : MAID.Struct Player n}
    (data : FDistNodeData S) (sem : Sem S) (pol : Policy S)
    (hcompat : FDistNodeDataCompatible data sem pol)
    (L : List (Fin n))
    (acc : FDist (TAssign S)) (hacc : FDist.totalWeight acc = 1) :
    FDist.toPMF (L.foldl (evalStepFDist data) acc)
        (foldl_evalStepFDist_normalized data L acc hacc) =
      L.foldl (evalStep S sem pol) (FDist.toPMF acc hacc) := by
  induction L generalizing acc with
  | nil => rfl
  | cons nd rest ih =>
    simp only [List.foldl_cons]
    have hstep := evalStepFDist_normalized data acc hacc nd
    have heq := evalStepFDist_toPMF data sem pol hcompat acc hacc nd
    simp only at heq
    conv_rhs => rw [← heq]
    exact ih (evalStepFDist data acc nd) hstep

/-- The full fold bridge: `toPMF (evalFoldFDist data σ) = evalFold S sem pol σ`. -/
theorem evalFoldFDist_toPMF_eq_evalFold {S : MAID.Struct Player n}
    (data : FDistNodeData S) (sem : Sem S) (pol : Policy S)
    (hcompat : FDistNodeDataCompatible data sem pol)
    (σ : TopologicalOrder S) :
    FDist.toPMF (evalFoldFDist data σ) (evalFoldFDist_normalized data σ) =
      evalFold S sem pol σ := by
  unfold evalFoldFDist evalFold
  have h := foldl_toPMF_eq data sem pol hcompat σ.order
    (FDist.pure (defaultAssign S)) (FDist.totalWeight_pure _)
  rw [FDist.toPMF_pure] at h
  exact h

end Vegas

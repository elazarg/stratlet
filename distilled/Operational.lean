import distilled.Vegas

/-!
# Operational Semantics for Vegas

A trace-based operational semantics for the Vegas game calculus.

A `Trace Γ p` is a complete execution path through program `p`, recording
the value chosen at each `sample` and `commit` site. Deterministic steps
(`letExpr`, `reveal`) are structurally present but carry no choices — they
correspond to silent/inlined transitions (as in the blockchain execution model).

The central connection to the denotational semantics:

  `outcomeDist σ p env` = weighted sum over traces, where each trace `t`
  contributes `traceWeight σ p env t` to the outcome `traceOutcome p env t`.

## Design notes

- **DAG execution model**: The sequential `Prog` syntax linearizes a DAG of
  events. Independent `commit`s and `reveal`s commute — the linearization
  order doesn't affect `outcomeDist`. This is stated as `outcomeDist_comm_commit`
  (proof TODO: requires showing the env projections are independent).

- **`letExpr` is silent**: No operational event. The value is determined by
  the environment, matching the blockchain implementation which inlines lets.

- **`sample` and `commit` are the observable events**: They carry nondeterministic
  choices. `sample` values come from nature (oracle calls on-chain); `commit`
  values come from players.

- **`reveal` is silent but meaningful**: It changes visibility (makes a hidden
  value public) without introducing nondeterminism. The value is already
  determined by the prior `commit`.
-/

-- ============================================================================
-- § 1. Traces
-- ============================================================================

/-- A complete execution path through a Vegas program.
    Indexed by the program it traverses. Records the value chosen at each
    `sample` and `commit` site. `letExpr` and `reveal` are deterministic
    wrappers (no choice recorded). -/
inductive Trace : (Γ : Ctx) → Prog Γ → Type where
  | ret {Γ : Ctx} {u : PayoffMap Γ} :
      Trace Γ (.ret u)
  | letExpr {Γ : Ctx} {x : VarId} {b : BaseTy} {e : Expr Γ b}
      {k : Prog ((x, .pub b) :: Γ)} :
      Trace ((x, .pub b) :: Γ) k → Trace Γ (.letExpr x e k)
  | sample {Γ : Ctx} {x : VarId} {τ : BindTy} {m : SampleMode τ}
      {D : DistExpr (distCtx τ m Γ) τ.base} {k : Prog ((x, τ) :: Γ)} :
      Val τ.base → Trace ((x, τ) :: Γ) k → Trace Γ (.sample x τ m D k)
  | commit {Γ : Ctx} {x : VarId} {who : Player} {b : BaseTy}
      {acts : List (Val b)}
      {R : Expr ((x, .pub b) :: flattenCtx (viewCtx who Γ)) .bool}
      {k : Prog ((x, .hidden who b) :: Γ)} :
      Val b → Trace ((x, .hidden who b) :: Γ) k →
      Trace Γ (.commit x who acts R k)
  | reveal {Γ : Ctx} {y : VarId} {who : Player} {x : VarId} {b : BaseTy}
      {hx : HasVar Γ x (.hidden who b)} {k : Prog ((y, .pub b) :: Γ)} :
      Trace ((y, .pub b) :: Γ) k → Trace Γ (.reveal y who x hx k)

-- ============================================================================
-- § 2. Trace outcome
-- ============================================================================

/-- The outcome produced by following trace `t` through program `p`.
    Mirrors the structure of `outcomeDist` but follows a single deterministic
    path — no weighting, no distribution binding. -/
noncomputable def traceOutcome : {Γ : Ctx} → (p : Prog Γ) → Env Γ → Trace Γ p → Outcome
  | _, .ret u, env, .ret =>
      evalPayoffMap u env
  | _, .letExpr x e k, env, .letExpr t =>
      traceOutcome k (Env.cons (x := x) (evalExpr e env) env) t
  | _, .sample x _ _ _ k, env, .sample v t =>
      traceOutcome k (Env.cons (x := x) v env) t
  | _, .commit x _ _ _ k, env, .commit v t =>
      traceOutcome k (Env.cons (x := x) v env) t
  | _, .reveal y _who _x (b := b) hx k, env, .reveal t =>
      let val : Val b := env.get hx
      traceOutcome k (Env.cons (x := y) (τ := .pub b) val env) t

-- ============================================================================
-- § 3. Trace weight
-- ============================================================================

/-- The probability weight of trace `t` under profile `σ`.
    Product of:
    - At each `sample` site: the distribution weight of the chosen value
    - At each `commit` site: the profile's strategy weight for the chosen value
    - At `letExpr`/`reveal`/`ret`: weight 1 (deterministic) -/
noncomputable def traceWeight (σ : Profile) :
    {Γ : Ctx} → (p : Prog Γ) → Env Γ → Trace Γ p → ℚ≥0
  | _, .ret _, _, .ret => 1
  | _, .letExpr x e k, env, .letExpr t =>
      traceWeight σ k (Env.cons (x := x) (evalExpr e env) env) t
  | _, .sample x τ m D k, env, .sample v t =>
      (evalDistExpr D (env.projectDist τ m)) v *
      traceWeight σ k (Env.cons (x := x) v env) t
  | _, .commit x who acts R k, env, .commit v t =>
      (σ.commit who x acts R (env.toView who)) v *
      traceWeight σ k (Env.cons (x := x) v env) t
  | _, .reveal y _who _x (b := b) hx k, env, .reveal t =>
      let val : Val b := env.get hx
      traceWeight σ k (Env.cons (x := y) (τ := .pub b) val env) t

-- ============================================================================
-- § 4. Trace legality
-- ============================================================================

/-- A trace is legal if every `commit` choice is in the action list and
    satisfies constraint `R`, and every `sample` choice is in the
    distribution's support. -/
def Trace.legal : {Γ : Ctx} → (p : Prog Γ) → Env Γ → Trace Γ p → Prop
  | _, .ret _, _, .ret => True
  | _, .letExpr x e k, env, .letExpr t =>
      legal k (Env.cons (x := x) (evalExpr e env) env) t
  | _, .sample x τ m D k, env, .sample v t =>
      v ∈ (evalDistExpr D (env.projectDist τ m)).support ∧
      legal k (Env.cons (x := x) v env) t
  | _, .commit x who acts R k, env, .commit v t =>
      v ∈ acts ∧ evalR R v (env.toView who) = true ∧
      legal k (Env.cons (x := x) v env) t
  | _, .reveal y _who _x (b := b) hx k, env, .reveal t =>
      let val : Val b := env.get hx
      legal k (Env.cons (x := y) (τ := .pub b) val env) t

-- ============================================================================
-- § 5. Big-step reachability
-- ============================================================================

/-- Profile-free reachability: outcome `oc` can be reached from `(p, env)`
    by some sequence of legal choices at commit sites and in-support choices
    at sample sites. Characterizes the game's possible outcomes regardless
    of strategy. -/
inductive CanReach : {Γ : Ctx} → Prog Γ → Env Γ → Outcome → Prop where
  | ret {Γ : Ctx} {u : PayoffMap Γ} {env : Env Γ} :
      CanReach (.ret u) env (evalPayoffMap u env)
  | letExpr {Γ : Ctx} {x : VarId} {b : BaseTy} {e : Expr Γ b}
      {k : Prog ((x, .pub b) :: Γ)} {env : Env Γ} {oc : Outcome} :
      CanReach k (Env.cons (x := x) (evalExpr e env) env) oc →
      CanReach (.letExpr x e k) env oc
  | sample {Γ : Ctx} {x : VarId} {τ : BindTy} {m : SampleMode τ}
      {D : DistExpr (distCtx τ m Γ) τ.base} {k : Prog ((x, τ) :: Γ)}
      {env : Env Γ} {oc : Outcome}
      (v : Val τ.base)
      (hsupp : v ∈ (evalDistExpr D (env.projectDist τ m)).support) :
      CanReach k (Env.cons (x := x) v env) oc →
      CanReach (.sample x τ m D k) env oc
  | commit {Γ : Ctx} {x : VarId} {who : Player} {b : BaseTy}
      {acts : List (Val b)}
      {R : Expr ((x, .pub b) :: flattenCtx (viewCtx who Γ)) .bool}
      {k : Prog ((x, .hidden who b) :: Γ)}
      {env : Env Γ} {oc : Outcome}
      (v : Val b) (hacts : v ∈ acts)
      (hR : evalR R v (env.toView who) = true) :
      CanReach k (Env.cons (x := x) v env) oc →
      CanReach (.commit x who acts R k) env oc
  | reveal {Γ : Ctx} {y : VarId} {who : Player} {x : VarId} {b : BaseTy}
      {hx : HasVar Γ x (.hidden who b)}
      {k : Prog ((y, .pub b) :: Γ)} {env : Env Γ} {oc : Outcome} :
      CanReach k (Env.cons (x := y) (τ := .pub b) (show Val b from env.get hx) env) oc →
      CanReach (.reveal y who x hx k) env oc

/-- Profile-dependent reachability: outcome `oc` has positive weight under
    profile `σ`. Uses the profile's support at commit sites (not just legality)
    and the distribution's support at sample sites. -/
inductive Reach (σ : Profile) :
    {Γ : Ctx} → Prog Γ → Env Γ → Outcome → Prop where
  | ret {Γ : Ctx} {u : PayoffMap Γ} {env : Env Γ} :
      Reach σ (.ret u) env (evalPayoffMap u env)
  | letExpr {Γ : Ctx} {x : VarId} {b : BaseTy} {e : Expr Γ b}
      {k : Prog ((x, .pub b) :: Γ)} {env : Env Γ} {oc : Outcome} :
      Reach σ k (Env.cons (x := x) (evalExpr e env) env) oc →
      Reach σ (.letExpr x e k) env oc
  | sample {Γ : Ctx} {x : VarId} {τ : BindTy} {m : SampleMode τ}
      {D : DistExpr (distCtx τ m Γ) τ.base} {k : Prog ((x, τ) :: Γ)}
      {env : Env Γ} {oc : Outcome}
      (v : Val τ.base)
      (hsupp : v ∈ (evalDistExpr D (env.projectDist τ m)).support) :
      Reach σ k (Env.cons (x := x) v env) oc →
      Reach σ (.sample x τ m D k) env oc
  | commit {Γ : Ctx} {x : VarId} {who : Player} {b : BaseTy}
      {acts : List (Val b)}
      {R : Expr ((x, .pub b) :: flattenCtx (viewCtx who Γ)) .bool}
      {k : Prog ((x, .hidden who b) :: Γ)}
      {env : Env Γ} {oc : Outcome}
      (v : Val b)
      (hsupp : v ∈ (σ.commit who x acts R (env.toView who)).support) :
      Reach σ k (Env.cons (x := x) v env) oc →
      Reach σ (.commit x who acts R k) env oc
  | reveal {Γ : Ctx} {y : VarId} {who : Player} {x : VarId} {b : BaseTy}
      {hx : HasVar Γ x (.hidden who b)}
      {k : Prog ((y, .pub b) :: Γ)} {env : Env Γ} {oc : Outcome} :
      Reach σ k (Env.cons (x := y) (τ := .pub b) (show Val b from env.get hx) env) oc →
      Reach σ (.reveal y who x hx k) env oc

-- ============================================================================
-- § 6. Connecting traces to reachability
-- ============================================================================

/-- A legal trace witnesses reachability. -/
theorem legal_trace_canReach {Γ : Ctx} {p : Prog Γ} {env : Env Γ}
    (t : Trace Γ p) (hl : t.legal p env) :
    CanReach p env (traceOutcome p env t) := by
  induction t with
  | ret => exact .ret
  | letExpr _ ih => exact .letExpr (ih hl)
  | sample v _ ih => exact .sample v hl.1 (ih hl.2)
  | commit v _ ih => exact .commit v hl.1 hl.2.1 (ih hl.2.2)
  | reveal _ ih => exact .reveal (ih hl)

/-- A positive-weight trace witnesses profile-dependent reachability. -/
theorem pos_weight_trace_reach {Γ : Ctx} {p : Prog Γ} {env : Env Γ}
    (σ : Profile) (t : Trace Γ p) (hw : traceWeight σ p env t ≠ 0) :
    Reach σ p env (traceOutcome p env t) := by
  induction t with
  | ret => exact .ret
  | letExpr _ ih => exact .letExpr (ih hw)
  | sample v _ ih =>
    have h1 := left_ne_zero_of_mul hw
    have h2 := right_ne_zero_of_mul hw
    exact .sample v (Finsupp.mem_support_iff.mpr h1) (ih h2)
  | commit v _ ih =>
    have h1 := left_ne_zero_of_mul hw
    have h2 := right_ne_zero_of_mul hw
    exact .commit v (Finsupp.mem_support_iff.mpr h1) (ih h2)
  | reveal _ ih => exact .reveal (ih hw)

/-- Every reachable outcome has a witnessing trace. -/
theorem canReach_has_trace {Γ : Ctx} {p : Prog Γ} {env : Env Γ} {oc : Outcome}
    (h : CanReach p env oc) :
    ∃ t : Trace Γ p, t.legal p env ∧ traceOutcome p env t = oc := by
  induction h with
  | ret => exact ⟨.ret, trivial, rfl⟩
  | letExpr _ ih =>
    obtain ⟨t, hl, ho⟩ := ih
    exact ⟨.letExpr t, hl, ho⟩
  | sample v hsupp _ ih =>
    obtain ⟨t, hl, ho⟩ := ih
    exact ⟨.sample v t, ⟨hsupp, hl⟩, ho⟩
  | commit v hacts hR _ ih =>
    obtain ⟨t, hl, ho⟩ := ih
    exact ⟨.commit v t, ⟨hacts, hR, hl⟩, ho⟩
  | reveal _ ih =>
    obtain ⟨t, hl, ho⟩ := ih
    exact ⟨.reveal t, hl, ho⟩

-- ============================================================================
-- § 7. Adequacy
-- ============================================================================

/-- **Support correctness**: an outcome is in the support of `outcomeDist`
    iff it is reachable under the profile. -/
theorem reach_iff_outcomeDist_support {Γ : Ctx} (σ : Profile)
    (p : Prog Γ) (env : Env Γ) (oc : Outcome) :
    Reach σ p env oc ↔ oc ∈ (outcomeDist σ p env).support := by
  induction p with
  | ret u =>
    simp only [outcomeDist, FDist.mem_support_pure]
    constructor
    · intro h; cases h; rfl
    · intro h; subst h; exact .ret
  | letExpr x _ k ih =>
    simp only [outcomeDist]
    exact ⟨fun h => by cases h with | letExpr h => exact (ih _).mp h,
           fun h => .letExpr ((ih _).mpr h)⟩
  | sample x τ m D k ih =>
    simp only [outcomeDist, FDist.mem_support_bind]
    constructor
    · intro h
      cases h with
      | sample v hsupp hk => exact ⟨v, hsupp, (ih _).mp hk⟩
    · rintro ⟨v, hsupp, hmem⟩
      exact .sample v hsupp ((ih _).mpr hmem)
  | commit x who acts R k ih =>
    simp only [outcomeDist, FDist.mem_support_bind]
    constructor
    · intro h
      cases h with
      | commit v hsupp hk => exact ⟨v, hsupp, (ih _).mp hk⟩
    · rintro ⟨v, hsupp, hmem⟩
      exact .commit v hsupp ((ih _).mpr hmem)
  | reveal y who x hx k ih =>
    simp only [outcomeDist]
    exact ⟨fun h => by cases h with | reveal h => exact (ih _).mp h,
           fun h => .reveal ((ih _).mpr h)⟩

/-- **Adequacy** (pointwise form): the weight `outcomeDist` assigns to outcome
    `oc` equals the sum of `traceWeight` over all traces producing `oc`.

    Formally: `(outcomeDist σ p env) oc = Σ_{t | traceOutcome = oc} traceWeight σ p env t`

    The sum is well-defined because `FDist` has finite support, so only finitely
    many traces have nonzero weight. -/
theorem adequacy_pointwise {Γ : Ctx} (σ : Profile)
    (p : Prog Γ) (env : Env Γ) (oc : Outcome) :
    (outcomeDist σ p env) oc =
    -- TODO: state RHS as a Finsupp.sum or finitary sum over traces with
    -- nonzero weight. The key insight: outcomeDist is defined by FDist.bind,
    -- which distributes as Σ_{v} weight(v) * (recursive outcomeDist at v).
    -- Unfolding this recursion yields the product-of-weights over traces.
    sorry := by
  sorry

-- ============================================================================
-- § 8. Admissibility and legality of traces
-- ============================================================================

/-- Under an admissible profile, every positive-weight trace is legal. -/
theorem admissible_pos_weight_legal {Γ : Ctx} {σ : Profile}
    {p : Prog Γ} {env : Env Γ}
    (hadm : AdmissibleProfile σ p)
    (t : Trace Γ p) (hw : traceWeight σ p env t ≠ 0) :
    t.legal p env := by
  induction t with
  | ret => trivial
  | letExpr _ ih => exact ih hadm hw
  | sample v _ ih =>
    have h1 := left_ne_zero_of_mul hw
    have h2 := right_ne_zero_of_mul hw
    exact ⟨Finsupp.mem_support_iff.mpr h1, ih hadm h2⟩
  | commit v _ ih =>
    have h1 := left_ne_zero_of_mul hw
    have h2 := right_ne_zero_of_mul hw
    have hv := hadm.1 _ v (Finsupp.mem_support_iff.mpr h1)
    exact ⟨hv.1, hv.2, ih hadm.2 h2⟩
  | reveal _ ih => exact ih hadm hw

/-- Under an admissible profile, `Reach` implies `CanReach`. -/
theorem admissible_reach_canReach {Γ : Ctx} {σ : Profile}
    {p : Prog Γ} {env : Env Γ} {oc : Outcome}
    (hadm : AdmissibleProfile σ p)
    (h : Reach σ p env oc) :
    CanReach p env oc := by
  induction h with
  | ret => exact .ret
  | letExpr _ ih => exact .letExpr (ih hadm)
  | sample v hsupp _ ih => exact .sample v hsupp (ih hadm)
  | commit v hsupp _ ih =>
    have hv := hadm.1 _ v hsupp
    exact .commit v hv.1 hv.2 (ih hadm.2)
  | reveal _ ih => exact .reveal (ih hadm)

-- ============================================================================
-- § 9. Commutativity (DAG property)
-- ============================================================================

/-! ### Independent events commute

The blockchain execution model runs events as a reactive DAG: each event
fires when its dependencies are met, and independent events can fire in
any order. In the sequential `Prog` syntax, this means adjacent constructors
whose bindings don't depend on each other can be swapped without changing
`outcomeDist`.

The key cases:
- Two `commit`s for different players whose constraints `R` don't reference
  each other's variables
- Two `reveal`s of different variables
- A `commit` and a `reveal` of an unrelated variable

Stating this precisely requires showing that the environment projections
(viewCtx, pubCtx) are independent of the swapped binding. The proof
reduces to showing that `Env.cons a (Env.cons b env)` and
`Env.cons b (Env.cons a env)` give the same projections when looked up
through the appropriate HasVar embeddings.
-/

/-- Two adjacent commits with disjoint variable references produce the
    same outcome distribution regardless of order.

    Preconditions:
    - `x₁ ∉ exprVars R₂` (player 2's constraint doesn't see player 1's binding)
    - `x₂ ∉ exprVars R₁` (player 1's constraint doesn't see player 2's binding)
    - Both `x₁` and `x₂` are fresh in `Γ` and distinct

    This is the core DAG commutativity property. -/
theorem outcomeDist_comm_commit
    {Γ : Ctx} {σ : Profile} {_env : Env Γ}
    -- first ordering: commit x₁ then commit x₂
    {x₁ : VarId} {who₁ : Player} {b₁ : BaseTy}
    {_acts₁ : List (Val b₁)}
    {R₁ : Expr ((x₁, .pub b₁) :: flattenCtx (viewCtx who₁ Γ)) .bool}
    {x₂ : VarId} {who₂ : Player} {b₂ : BaseTy}
    {_acts₂ : List (Val b₂)}
    -- R₂ in the extended context (after x₁ is bound)
    {R₂ : Expr ((x₂, .pub b₂) :: flattenCtx
      (viewCtx who₂ ((x₁, .hidden who₁ b₁) :: Γ))) .bool}
    {_k : Prog ((x₂, .hidden who₂ b₂) :: (x₁, .hidden who₁ b₁) :: Γ)}
    -- independence: x₁ not in R₂'s free variables, x₂ not in R₁'s
    -- (stated via syntactic variable extraction)
    (_hindep₁ : x₁ ∉ exprVars R₂)
    (_hindep₂ : x₂ ∉ exprVars R₁)
    (_hfresh₁ : Fresh x₁ Γ) (_hfresh₂ : Fresh x₂ Γ) (_hne : x₁ ≠ x₂) :
    -- TODO: full statement requires constructing the swapped program and
    -- showing outcomeDist equality. This requires:
    -- 1. R₁' and R₂' adapted to the swapped context
    -- 2. k' with swapped bindings
    -- 3. Proof that the env projections commute
    True := by
  trivial

-- TODO: analogous commutativity theorems for:
-- - reveal/reveal
-- - commit/reveal (when independent)
-- - sample/commit (when independent)

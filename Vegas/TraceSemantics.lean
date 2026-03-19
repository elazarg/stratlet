import Vegas.BigStep

/-!
# Trace Semantics for Vegas

A trace-based semantics for the Vegas game calculus.

A `Trace Γ p` is a complete execution path through program `p`, recording
the value chosen at each `sample` and `commit` site. Deterministic steps
(`letExpr`, `reveal`) are structurally present but carry no choices — they
correspond to silent/inlined transitions (as in the blockchain execution model).

The central connection to the denotational semantics:

  `outcomeDist σ p env` agrees pointwise with `traceWeightSum σ p env`, a nested
  sum over distribution supports that corresponds to summing `traceWeight σ p env t`
  over the finitely many positive-weight traces `t`.

## Design notes

- **Action-graph execution model**: The sequential `VegasCore` syntax linearizes an
  action graph of
  events. Independent `commit`s and `reveal`s commute — the linearization
  order doesn't affect `outcomeDist`. This is proved as `outcomeDist_comm_commit`
  and `outcomeDist_comm_reveal`.

- **`letExpr` is silent**: No operational event. The value is determined by
  the environment, matching the blockchain implementation which inlines lets.

- **`sample` and `commit` are the observable events**: They carry nondeterministic
  choices. `sample` values come from nature (oracle calls on-chain); `commit`
  values come from players.

- **`reveal` is silent but meaningful**: It changes visibility (makes a hidden
  value public) without introducing nondeterminism. The value is already
determined by the prior `commit`.
-/

namespace Vegas

variable {P : Type} [DecidableEq P] {L : IExpr}

/-- A complete execution path through a Vegas program.
    Indexed by the program it traverses. Records the value chosen at each
    `sample` and `commit` site. `letExpr` and `reveal` are deterministic
    wrappers (no choice recorded). -/
inductive Trace : (Γ : VCtx P L) → VegasCore P L Γ → Type where
  | ret {Γ : VCtx P L}
      {payoffs : List (P × L.Expr (erasePubVCtx Γ) L.int)} :
      Trace Γ (.ret payoffs)
  | letExpr {Γ : VCtx P L} {x : VarId} {b : L.Ty}
      {e : L.Expr (erasePubVCtx Γ) b}
      {k : VegasCore P L ((x, .pub b) :: Γ)} :
      Trace ((x, .pub b) :: Γ) k → Trace Γ (.letExpr x e k)
  | sample {Γ : VCtx P L} {x : VarId} {τ : BindTy P L} {m : SampleMode τ}
      {D' : L.DistExpr (eraseVCtx (distVCtx τ m Γ)) τ.base}
      {k : VegasCore P L ((x, τ) :: Γ)} :
      L.Val τ.base → Trace ((x, τ) :: Γ) k → Trace Γ (.sample x τ m D' k)
  | commit {Γ : VCtx P L} {x : VarId} {who : P} {b : L.Ty}
      {acts : List (L.Val b)}
      {R : L.Expr ((x, b) :: eraseVCtx (viewVCtx who Γ)) L.bool}
      {k : VegasCore P L ((x, .hidden who b) :: Γ)} :
      L.Val b → Trace ((x, .hidden who b) :: Γ) k →
      Trace Γ (.commit x who acts R k)
  | reveal {Γ : VCtx P L} {y : VarId} {who : P} {x : VarId} {b : L.Ty}
      {hx : VHasVar (L := L) Γ x (.hidden who b)}
      {k : VegasCore P L ((y, .pub b) :: Γ)} :
      Trace ((y, .pub b) :: Γ) k → Trace Γ (.reveal y who x hx k)

noncomputable instance instDecidableEqTrace
    {Γ : VCtx P L} {p : VegasCore P L Γ} :
    DecidableEq (@Trace P _ L Γ p) :=
  fun a b => Classical.propDecidable (a = b)


/-- The outcome produced by following trace `t` through program `p`.
    Mirrors the structure of `outcomeDist` but follows a single deterministic
    path — no weighting, no distribution binding. -/
noncomputable def traceOutcome :
    {Γ : VCtx P L} → (p : VegasCore P L Γ) → VEnv (Player := P) L Γ →
      Trace Γ p → Outcome P
  | _, .ret payoffs, env, .ret =>
      evalPayoffs payoffs env
  | _, .letExpr _ e k, env, .letExpr t =>
      traceOutcome k (VEnv.cons (L.eval e (VEnv.erasePubEnv env)) env) t
  | _, .sample _ _ _ _ k, env, .sample v t =>
      traceOutcome k (VEnv.cons v env) t
  | _, .commit _ _ _ _ k, env, .commit v t =>
      traceOutcome k (VEnv.cons v env) t
  | _, .reveal y _who _x (b := b) hx k, env, .reveal t =>
      let val : L.Val b := VEnv.get env hx
      traceOutcome k (VEnv.cons (x := y) (τ := .pub b) val env) t


/-- The probability weight of trace `t` under profile `σ`.
    Product of:
    - At each `sample` site: the distribution weight of the chosen value
    - At each `commit` site: the profile's strategy weight for the chosen value
    - At `letExpr`/`reveal`/`ret`: weight 1 (deterministic) -/
noncomputable def traceWeight (σ : Profile P L) :
    {Γ : VCtx P L} → (p : VegasCore P L Γ) → VEnv (Player := P) L Γ →
      Trace Γ p → ℚ≥0
  | _, .ret _, _, .ret => 1
  | _, .letExpr _ e k, env, .letExpr t =>
      traceWeight σ k (VEnv.cons (L.eval e (VEnv.erasePubEnv env)) env) t
  | _, .sample _ τ m D' k, env, .sample v t =>
      (L.evalDist D' (VEnv.eraseDistEnv τ m env)) v *
      traceWeight σ k (VEnv.cons v env) t
  | _, .commit x who acts R k, env, .commit v t =>
      (σ.commit who x acts R (VEnv.toView who env)) v *
      traceWeight σ k (VEnv.cons v env) t
  | _, .reveal y _who _x (b := b) hx k, env, .reveal t =>
      let val : L.Val b := VEnv.get env hx
      traceWeight σ k (VEnv.cons (x := y) (τ := .pub b) val env) t


/-- A trace is legal if every `commit` choice is in the action list and
    satisfies constraint `R`, and every `sample` choice is in the
    distribution's support. -/
def Trace.legal : {Γ : VCtx P L} → (p : VegasCore P L Γ) →
    VEnv (Player := P) L Γ → Trace Γ p → Prop
  | _, .ret _, _, .ret => True
  | _, .letExpr _ e k, env, .letExpr t =>
      legal k (VEnv.cons (L.eval e (VEnv.erasePubEnv env)) env) t
  | _, .sample _ τ m D' k, env, .sample v t =>
      v ∈ (L.evalDist D' (VEnv.eraseDistEnv τ m env)).support ∧
      legal k (VEnv.cons v env) t
  | _, .commit _ who acts R k, env, .commit v t =>
      v ∈ acts ∧ evalGuard R v (VEnv.toView who env) = true ∧
      legal k (VEnv.cons v env) t
  | _, .reveal y _who _x (b := b) hx k, env, .reveal t =>
      let val : L.Val b := VEnv.get env hx
      legal k (VEnv.cons (x := y) (τ := .pub b) val env) t


/-- Profile-free reachability: outcome `oc` can be reached from `(p, env)`
    by some sequence of legal choices at commit sites and in-support choices
    at sample sites. Characterizes the game's possible outcomes regardless
    of strategy. -/
inductive CanReach : {Γ : VCtx P L} → VegasCore P L Γ →
    VEnv (Player := P) L Γ → Outcome P → Prop where
  | ret {Γ : VCtx P L}
      {payoffs : List (P × L.Expr (erasePubVCtx Γ) L.int)}
      {env : VEnv (Player := P) L Γ} :
      CanReach (.ret payoffs) env (evalPayoffs payoffs env)
  | letExpr {Γ : VCtx P L} {x : VarId} {b : L.Ty}
      {e : L.Expr (erasePubVCtx Γ) b}
      {k : VegasCore P L ((x, .pub b) :: Γ)}
      {env : VEnv (Player := P) L Γ}
      {oc : Outcome P} :
      CanReach k (VEnv.cons (L.eval e (VEnv.erasePubEnv env)) env) oc →
      CanReach (.letExpr x e k) env oc
  | sample {Γ : VCtx P L} {x : VarId} {τ : BindTy P L} {m : SampleMode τ}
      {D' : L.DistExpr (eraseVCtx (distVCtx τ m Γ)) τ.base}
      {k : VegasCore P L ((x, τ) :: Γ)}
      {env : VEnv (Player := P) L Γ} {oc : Outcome P}
      (v : L.Val τ.base)
      (hsupp : v ∈ (L.evalDist D' (VEnv.eraseDistEnv τ m env)).support) :
      CanReach k (VEnv.cons v env) oc →
      CanReach (.sample x τ m D' k) env oc
  | commit {Γ : VCtx P L} {x : VarId} {who : P} {b : L.Ty}
      {acts : List (L.Val b)}
      {R : L.Expr ((x, b) :: eraseVCtx (viewVCtx who Γ)) L.bool}
      {k : VegasCore P L ((x, .hidden who b) :: Γ)}
      {env : VEnv (Player := P) L Γ} {oc : Outcome P}
      (v : L.Val b) (hacts : v ∈ acts)
      (hR : evalGuard R v (VEnv.toView who env) = true) :
      CanReach k (VEnv.cons v env) oc →
      CanReach (.commit x who acts R k) env oc
  | reveal {Γ : VCtx P L} {y : VarId} {who : P} {x : VarId} {b : L.Ty}
      {hx : VHasVar (L := L) Γ x (.hidden who b)}
      {k : VegasCore P L ((y, .pub b) :: Γ)}
      {env : VEnv (Player := P) L Γ} {oc : Outcome P} :
      CanReach k (VEnv.cons (x := y) (τ := .pub b)
        (show L.Val b from VEnv.get env hx) env) oc →
      CanReach (.reveal y who x hx k) env oc

/-- Profile-dependent reachability: outcome `oc` has positive weight under
    profile `σ`. Uses the profile's support at commit sites (not just legality)
    and the distribution's support at sample sites. -/
inductive Reach (σ : Profile P L) :
    {Γ : VCtx P L} → VegasCore P L Γ → VEnv (Player := P) L Γ →
    Outcome P → Prop where
  | ret {Γ : VCtx P L}
      {payoffs : List (P × L.Expr (erasePubVCtx Γ) L.int)}
      {env : VEnv (Player := P) L Γ} :
      Reach σ (.ret payoffs) env (evalPayoffs payoffs env)
  | letExpr {Γ : VCtx P L} {x : VarId} {b : L.Ty}
      {e : L.Expr (erasePubVCtx Γ) b}
      {k : VegasCore P L ((x, .pub b) :: Γ)}
      {env : VEnv (Player := P) L Γ} {oc : Outcome P} :
      Reach σ k (VEnv.cons (L.eval e (VEnv.erasePubEnv env)) env) oc →
      Reach σ (.letExpr x e k) env oc
  | sample {Γ : VCtx P L} {x : VarId} {τ : BindTy P L} {m : SampleMode τ}
      {D' : L.DistExpr (eraseVCtx (distVCtx τ m Γ)) τ.base}
      {k : VegasCore P L ((x, τ) :: Γ)}
      {env : VEnv (Player := P) L Γ} {oc : Outcome P}
      (v : L.Val τ.base)
      (hsupp : v ∈ (L.evalDist D' (VEnv.eraseDistEnv τ m env)).support) :
      Reach σ k (VEnv.cons v env) oc →
      Reach σ (.sample x τ m D' k) env oc
  | commit {Γ : VCtx P L} {x : VarId} {who : P} {b : L.Ty}
      {acts : List (L.Val b)}
      {R : L.Expr ((x, b) :: eraseVCtx (viewVCtx who Γ)) L.bool}
      {k : VegasCore P L ((x, .hidden who b) :: Γ)}
      {env : VEnv (Player := P) L Γ} {oc : Outcome P}
      (v : L.Val b)
      (hsupp : v ∈ (σ.commit who x acts R (VEnv.toView who env)).support) :
      Reach σ k (VEnv.cons v env) oc →
      Reach σ (.commit x who acts R k) env oc
  | reveal {Γ : VCtx P L} {y : VarId} {who : P} {x : VarId} {b : L.Ty}
      {hx : VHasVar (L := L) Γ x (.hidden who b)}
      {k : VegasCore P L ((y, .pub b) :: Γ)}
      {env : VEnv (Player := P) L Γ} {oc : Outcome P} :
      Reach σ k (VEnv.cons (x := y) (τ := .pub b)
        (show L.Val b from VEnv.get env hx) env) oc →
      Reach σ (.reveal y who x hx k) env oc


/-- A legal trace witnesses reachability. -/
theorem legal_trace_canReach {Γ : VCtx P L} {p : VegasCore P L Γ}
    {env : VEnv (Player := P) L Γ}
    (t : Trace Γ p) (hl : t.legal p env) :
    CanReach p env (traceOutcome p env t) := by
  induction t with
  | ret => exact .ret
  | letExpr _ ih => exact .letExpr (ih hl)
  | sample v _ ih => exact .sample v hl.1 (ih hl.2)
  | commit v _ ih => exact .commit v hl.1 hl.2.1 (ih hl.2.2)
  | reveal _ ih => exact .reveal (ih hl)

/-- A positive-weight trace witnesses profile-dependent reachability. -/
theorem pos_weight_trace_reach {Γ : VCtx P L} {p : VegasCore P L Γ}
    {env : VEnv (Player := P) L Γ}
    (σ : Profile P L) (t : Trace Γ p) (hw : traceWeight σ p env t ≠ 0) :
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
theorem canReach_has_trace {Γ : VCtx P L} {p : VegasCore P L Γ}
    {env : VEnv (Player := P) L Γ} {oc : Outcome P}
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


/-- **Support correctness**: an outcome is in the support of `outcomeDist`
    iff it is reachable under the profile. -/
theorem reach_iff_outcomeDist_support {Γ : VCtx P L} (σ : Profile P L)
    (p : VegasCore P L Γ) (env : VEnv (Player := P) L Γ) (oc : Outcome P) :
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
  | sample x τ m D' k ih =>
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

/-- The weighted count of traces producing outcome `oc`, computed as a nested
    sum over distribution supports by structural induction on `p`. -/
noncomputable def traceWeightSum (σ : Profile P L) :
    {Γ : VCtx P L} → (p : VegasCore P L Γ) → VEnv (Player := P) L Γ →
      Outcome P → ℚ≥0
  | _, .ret u, env, oc =>
      if oc = evalPayoffs u env then 1 else 0
  | _, .letExpr _ e k, env, oc =>
      traceWeightSum σ k (VEnv.cons (L.eval e (VEnv.erasePubEnv env)) env) oc
  | _, .sample _ τ m D' k, env, oc =>
      (L.evalDist D' (VEnv.eraseDistEnv τ m env)).support.sum fun v =>
        (L.evalDist D' (VEnv.eraseDistEnv τ m env)) v *
        traceWeightSum σ k (VEnv.cons v env) oc
  | _, .commit x who acts R k, env, oc =>
      (σ.commit who x acts R (VEnv.toView who env)).support.sum fun v =>
        (σ.commit who x acts R (VEnv.toView who env)) v *
        traceWeightSum σ k (VEnv.cons v env) oc
  | _, .reveal y _who _x (b := b) hx k, env, oc =>
      let val : L.Val b := VEnv.get env hx
      traceWeightSum σ k (VEnv.cons (x := y) (τ := .pub b) val env) oc

/-- **Adequacy** (pointwise form): `outcomeDist σ p env` and `traceWeightSum σ p env`
    agree pointwise. -/
theorem adequacy_pointwise {Γ : VCtx P L} (σ : Profile P L)
    (p : VegasCore P L Γ) (env : VEnv (Player := P) L Γ) (oc : Outcome P) :
    (outcomeDist σ p env) oc = traceWeightSum σ p env oc := by
  induction p with
  | ret u =>
    simp [outcomeDist, traceWeightSum, FDist.pure, Finsupp.single_apply, eq_comm]
  | letExpr x _ k ih =>
    simp only [outcomeDist, traceWeightSum]
    exact ih _
  | sample x τ m D' k ih =>
    simp only [outcomeDist, traceWeightSum, FDist.bind_apply]
    exact Finset.sum_congr rfl fun v _ => by rw [ih]
  | commit x who acts R k ih =>
    simp only [outcomeDist, traceWeightSum, FDist.bind_apply]
    exact Finset.sum_congr rfl fun v _ => by rw [ih]
  | reveal y who x hx k ih =>
    simp only [outcomeDist, traceWeightSum]
    exact ih _

/-- The distribution on traces induced by profile `σ`. -/
noncomputable def traceDist (σ : Profile P L) :
    {Γ : VCtx P L} → (p : VegasCore P L Γ) → VEnv (Player := P) L Γ →
      FDist (Trace Γ p)
  | _, .ret _, _ => FDist.pure .ret
  | _, .letExpr _ e k, env =>
      (traceDist σ k (VEnv.cons (L.eval e (VEnv.erasePubEnv env)) env)).map
        (.letExpr ·)
  | _, .sample _ τ m D' k, env =>
      (L.evalDist D' (VEnv.eraseDistEnv τ m env)).bind fun v =>
        (traceDist σ k (VEnv.cons v env)).map (.sample v ·)
  | _, .commit x who acts R k, env =>
      FDist.bind (σ.commit who x acts R (VEnv.toView who env)) fun v =>
        (traceDist σ k (VEnv.cons v env)).map (.commit v ·)
  | _, .reveal y _who _x (b := b) hx k, env =>
      let val : L.Val b := VEnv.get env hx
      (traceDist σ k (VEnv.cons (x := y) (τ := .pub b) val env)).map (.reveal ·)

private theorem Trace.letExpr_injective {Γ : VCtx P L} {x : VarId} {b : L.Ty}
    {e : L.Expr (erasePubVCtx Γ) b} {k : VegasCore P L ((x, .pub b) :: Γ)} :
    Function.Injective fun (t : Trace ((x, .pub b) :: Γ) k) =>
      Trace.letExpr (e := e) t :=
  fun _ _ h => Trace.letExpr.inj h

private theorem Trace.sample_injective {Γ : VCtx P L} {x : VarId}
    {τ : BindTy P L} {m : SampleMode τ}
    {D' : L.DistExpr (eraseVCtx (distVCtx τ m Γ)) τ.base}
    {k : VegasCore P L ((x, τ) :: Γ)} (v : L.Val τ.base) :
    Function.Injective fun (t : Trace ((x, τ) :: Γ) k) =>
      Trace.sample (D' := D') v t :=
  fun _ _ h => (Trace.sample.inj h).2

private theorem Trace.commit_injective {Γ : VCtx P L} {x : VarId} {who : P}
    {b : L.Ty} {acts : List (L.Val b)}
    {R : L.Expr ((x, b) :: eraseVCtx (viewVCtx who Γ)) L.bool}
    {k : VegasCore P L ((x, .hidden who b) :: Γ)} (v : L.Val b) :
    Function.Injective fun (t : Trace ((x, .hidden who b) :: Γ) k) =>
      Trace.commit (acts := acts) (R := R) v t :=
  fun _ _ h => (Trace.commit.inj h).2

private theorem Trace.reveal_injective {Γ : VCtx P L} {y : VarId} {who : P}
    {x : VarId} {b : L.Ty} {hx : VHasVar (L := L) Γ x (.hidden who b)}
    {k : VegasCore P L ((y, .pub b) :: Γ)} :
    Function.Injective fun (t : Trace ((y, .pub b) :: Γ) k) =>
      Trace.reveal (hx := hx) (k := k) t :=
  fun _ _ h => Trace.reveal.inj h

/-- Each trace gets exactly its `traceWeight` as mass in `traceDist`. -/
theorem traceDist_apply (σ : Profile P L) {Γ : VCtx P L}
    (p : VegasCore P L Γ) (env : VEnv (Player := P) L Γ)
    (t : Trace Γ p) :
    (traceDist σ p env) t = traceWeight σ p env t := by
  induction p with
  | ret u =>
    cases t
    simp [traceDist, traceWeight, FDist.pure, Finsupp.single_eq_same]
  | letExpr x e k ih =>
    cases t with
    | letExpr t =>
      simp only [traceDist, traceWeight]
      rw [FDist.map_apply_injective _ _ _ Trace.letExpr_injective]
      exact ih _ t
  | sample x τ m D' k ih =>
    cases t with
    | sample v t =>
      simp only [traceDist, traceWeight]
      rw [FDist.bind_apply]
      conv_rhs => rw [← ih _ t]
      rw [← FDist.map_apply_injective _ _ _ (Trace.sample_injective v)]
      apply Finset.sum_eq_single v
      · intro v' _ hne
        rw [FDist.map_apply_of_forall_ne _ _ _
          (fun t' _ h => hne ((Trace.sample.inj h).1)), mul_zero]
      · intro hv
        rw [Finsupp.mem_support_iff, not_not] at hv; simp [hv]
  | commit x who acts R k ih =>
    cases t with
    | commit v t =>
      simp only [traceDist, traceWeight]
      rw [FDist.bind_apply]
      conv_rhs => rw [← ih _ t]
      rw [← FDist.map_apply_injective _ _ _ (Trace.commit_injective v)]
      apply Finset.sum_eq_single v
      · intro v' _ hne
        rw [FDist.map_apply_of_forall_ne _ _ _
          (fun t' _ h => hne ((Trace.commit.inj h).1)), mul_zero]
      · intro hv
        rw [Finsupp.mem_support_iff, not_not] at hv
        rw [mul_eq_zero]
        exact Or.inl hv
  | reveal y who x hx k ih =>
    cases t with
    | reveal t =>
      simp only [traceDist, traceWeight]
      rw [FDist.map_apply_injective _ _ _ Trace.reveal_injective]
      exact ih _ t

/-- The outcome distribution is the pushforward of the trace distribution. -/
theorem outcomeDist_eq_map_traceDist (σ : Profile P L) {Γ : VCtx P L}
    (p : VegasCore P L Γ) (env : VEnv (Player := P) L Γ) :
    outcomeDist σ p env = (traceDist σ p env).map (traceOutcome p env) := by
  induction p with
  | ret u =>
    simp only [outcomeDist, traceDist]
    rw [FDist.map_pure]; rfl
  | letExpr x e k ih =>
    simp only [outcomeDist, traceDist]; rw [ih, FDist.map_map]; congr 1
  | sample x τ m D' k ih =>
    simp only [outcomeDist, traceDist]; rw [FDist.bind_map]
    congr 1; ext v; rw [ih, FDist.map_map]; congr 1
  | commit x who acts R k ih =>
    simp only [outcomeDist, traceDist]; rw [FDist.bind_map]
    congr 1; ext v; rw [ih, FDist.map_map]; congr 1
  | reveal y who x hx k ih =>
    simp only [outcomeDist, traceDist]; rw [ih, FDist.map_map]; congr 1


/-- Under an admissible profile, every positive-weight trace is legal. -/
theorem admissible_pos_weight_legal {Γ : VCtx P L} {σ : Profile P L}
    {p : VegasCore P L Γ} {env : VEnv (Player := P) L Γ}
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
theorem admissible_reach_canReach {Γ : VCtx P L} {σ : Profile P L}
    {p : VegasCore P L Γ} {env : VEnv (Player := P) L Γ} {oc : Outcome P}
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


/-! ### Independent events commute -/

/-- Helper: invisible bindings don't affect viewVCtx. -/
theorem viewVCtx_skip_invisible {p : P} {x : VarId} {τ : BindTy P L}
    {Γ : VCtx P L} (h : canSee p τ = false) :
    viewVCtx p ((x, τ) :: Γ) = viewVCtx p Γ := by
  simp [viewVCtx, Vegas.viewVCtx, h]

/-- Two adjacent commits have the same profile-free reachable outcomes when
    their guards and continuations commute pointwise under the swapped
    environments. This is the operational form of commit-commit commutativity:
    anything legally reachable in one order is legally reachable in the other. -/
theorem canReach_comm_commit
    {Γ : VCtx P L} {env : VEnv (Player := P) L Γ} {oc : Outcome P}
    {x₁ : VarId} {who₁ : P} {b₁ : L.Ty}
    {acts₁ : List (L.Val b₁)}
    {R₁ : L.Expr ((x₁, b₁) :: eraseVCtx (viewVCtx who₁ Γ)) L.bool}
    {x₂ : VarId} {who₂ : P} {b₂ : L.Ty}
    {acts₂ : List (L.Val b₂)}
    {R₂ : L.Expr ((x₂, b₂) :: eraseVCtx
      (viewVCtx who₂ ((x₁, .hidden who₁ b₁) :: Γ))) L.bool}
    {k : VegasCore P L
      ((x₂, .hidden who₂ b₂) :: (x₁, .hidden who₁ b₁) :: Γ)}
    {R₂' : L.Expr ((x₂, b₂) :: eraseVCtx (viewVCtx who₂ Γ)) L.bool}
    {R₁' : L.Expr ((x₁, b₁) :: eraseVCtx
      (viewVCtx who₁ ((x₂, .hidden who₂ b₂) :: Γ))) L.bool}
    {k' : VegasCore P L
      ((x₁, .hidden who₁ b₁) :: (x₂, .hidden who₂ b₂) :: Γ)}
    (hk_eq : ∀ (v₁ : L.Val b₁) (v₂ : L.Val b₂)
        (e : VEnv (Player := P) L Γ) (oc' : Outcome P),
      CanReach k (VEnv.cons v₂ (VEnv.cons v₁ e)) oc' ↔
      CanReach k' (VEnv.cons v₁ (VEnv.cons v₂ e)) oc')
    (hR₁ : ∀ (v₁ : L.Val b₁) (v₂ : L.Val b₂)
        (e : VEnv (Player := P) L Γ),
      evalGuard R₁ v₁ (VEnv.toView who₁ e) =
      evalGuard R₁' v₁
        (VEnv.toView who₁ (VEnv.cons (τ := .hidden who₂ b₂) v₂ e)))
    (hR₂ : ∀ (v₁ : L.Val b₁) (v₂ : L.Val b₂)
        (e : VEnv (Player := P) L Γ),
      evalGuard R₂ v₂
        (VEnv.toView who₂ (VEnv.cons (τ := .hidden who₁ b₁) v₁ e)) =
      evalGuard R₂' v₂ (VEnv.toView who₂ e)) :
    CanReach
      (.commit x₁ who₁ acts₁ R₁
        (.commit x₂ who₂ acts₂ R₂ k)) env oc ↔
    CanReach
      (.commit x₂ who₂ acts₂ R₂'
        (.commit x₁ who₁ acts₁ R₁' k')) env oc := by
  constructor
  · intro h
    cases h with
    | commit v₁ hacts₁ hguard₁ h =>
      cases h with
      | commit v₂ hacts₂ hguard₂ h =>
        apply CanReach.commit v₂ hacts₂
        · rw [← hR₂ v₁ v₂ env]
          exact hguard₂
        · apply CanReach.commit v₁ hacts₁
          · rw [← hR₁ v₁ v₂ env]
            exact hguard₁
          · exact (hk_eq v₁ v₂ env oc).1 h
  · intro h
    cases h with
    | commit v₂ hacts₂ hguard₂ h =>
      cases h with
      | commit v₁ hacts₁ hguard₁ h =>
        apply CanReach.commit v₁ hacts₁
        · rw [hR₁ v₁ v₂ env]
          exact hguard₁
        · apply CanReach.commit v₂ hacts₂
          · rw [hR₂ v₁ v₂ env]
            exact hguard₂
          · exact (hk_eq v₁ v₂ env oc).2 h

/-- The algebraic core of commit–commit commutativity. -/
theorem outcomeDist_comm_commit_algebraic
    {b₁ b₂ : L.Ty}
    (d₁ : FDist (L.Val b₁)) (d₂ : FDist (L.Val b₂))
    (f : L.Val b₁ → L.Val b₂ → FDist (Outcome P)) :
    d₁.bind (fun v₁ => d₂.bind (fun v₂ => f v₁ v₂)) =
    d₂.bind (fun v₂ => d₁.bind (fun v₁ => f v₁ v₂)) :=
  FDist.bind_comm d₁ d₂ f

/-- Two adjacent commits with disjoint variable references produce the
    same outcome distribution regardless of order. -/
theorem outcomeDist_comm_commit
    {Γ : VCtx P L} {σ : Profile P L} {env : VEnv (Player := P) L Γ}
    {x₁ : VarId} {who₁ : P} {b₁ : L.Ty}
    {acts₁ : List (L.Val b₁)}
    {R₁ : L.Expr ((x₁, b₁) :: eraseVCtx (viewVCtx who₁ Γ)) L.bool}
    {x₂ : VarId} {who₂ : P} {b₂ : L.Ty}
    {acts₂ : List (L.Val b₂)}
    {R₂ : L.Expr ((x₂, b₂) :: eraseVCtx
      (viewVCtx who₂ ((x₁, .hidden who₁ b₁) :: Γ))) L.bool}
    {k : VegasCore P L
      ((x₂, .hidden who₂ b₂) :: (x₁, .hidden who₁ b₁) :: Γ)}
    {R₂' : L.Expr ((x₂, b₂) :: eraseVCtx (viewVCtx who₂ Γ)) L.bool}
    {R₁' : L.Expr ((x₁, b₁) :: eraseVCtx
      (viewVCtx who₁ ((x₂, .hidden who₂ b₂) :: Γ))) L.bool}
    {k' : VegasCore P L
      ((x₁, .hidden who₁ b₁) :: (x₂, .hidden who₂ b₂) :: Γ)}
    (hk_eq : ∀ (v₁ : L.Val b₁) (v₂ : L.Val b₂)
        (e : VEnv (Player := P) L Γ),
      outcomeDist σ k (VEnv.cons v₂ (VEnv.cons v₁ e)) =
      outcomeDist σ k' (VEnv.cons v₁ (VEnv.cons v₂ e)))
    (hσ₁ : ∀ (v₂ : L.Val b₂) (e : VEnv (Player := P) L Γ),
      σ.commit who₁ x₁ acts₁ R₁ (VEnv.toView who₁ e) =
      σ.commit who₁ x₁ acts₁ R₁'
        (VEnv.toView who₁ (VEnv.cons (τ := .hidden who₂ b₂) v₂ e)))
    (hσ₂ : ∀ (v₁ : L.Val b₁) (e : VEnv (Player := P) L Γ),
      σ.commit who₂ x₂ acts₂ R₂
        (VEnv.toView who₂ (VEnv.cons (τ := .hidden who₁ b₁) v₁ e)) =
      σ.commit who₂ x₂ acts₂ R₂' (VEnv.toView who₂ e)) :
    outcomeDist σ
      (.commit x₁ who₁ acts₁ R₁
        (.commit x₂ who₂ acts₂ R₂ k)) env =
    outcomeDist σ
      (.commit x₂ who₂ acts₂ R₂'
        (.commit x₁ who₁ acts₁ R₁' k')) env := by
  simp only [outcomeDist]
  simp_rw [hσ₂ _ env]
  rw [FDist.bind_comm]
  congr 1; funext v₂
  rw [hσ₁ v₂ env]
  congr 1; funext v₁
  exact hk_eq v₁ v₂ env

/-- Two adjacent reveals of distinct hidden variables produce the same
    outcome distribution regardless of order. -/
theorem outcomeDist_comm_reveal
    {Γ : VCtx P L} {σ : Profile P L} {env : VEnv (Player := P) L Γ}
    {y₁ : VarId} {who₁ : P} {x₁ : VarId} {b₁ : L.Ty}
    {hx₁ : VHasVar (L := L) Γ x₁ (.hidden who₁ b₁)}
    {y₂ : VarId} {who₂ : P} {x₂ : VarId} {b₂ : L.Ty}
    {hx₂ : VHasVar (L := L) Γ x₂ (.hidden who₂ b₂)}
    {k : VegasCore P L ((y₂, .pub b₂) :: (y₁, .pub b₁) :: Γ)}
    {k' : VegasCore P L ((y₁, .pub b₁) :: (y₂, .pub b₂) :: Γ)}
    (hk_eq : ∀ (v₁ : L.Val b₁) (v₂ : L.Val b₂)
        (e : VEnv (Player := P) L Γ),
      outcomeDist σ k (VEnv.cons v₂ (VEnv.cons v₁ e)) =
      outcomeDist σ k' (VEnv.cons v₁ (VEnv.cons v₂ e))) :
    outcomeDist σ
      (.reveal y₁ who₁ x₁ hx₁
        (.reveal y₂ who₂ x₂ hx₂.there k)) env =
    outcomeDist σ
      (.reveal y₂ who₂ x₂ hx₂
        (.reveal y₁ who₁ x₁ hx₁.there k')) env := by
  simp only [outcomeDist]
  exact hk_eq (VEnv.get env hx₁) (VEnv.get env hx₂) env

end Vegas

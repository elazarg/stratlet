import Vegas.WF

/-!
# Big-step semantics for Vegas

The canonical denotational semantics of Vegas programs, together with the
normalization theorem used by the strategic and backend bridges.
-/

namespace Vegas

noncomputable def outcomeDist {P : Type} [DecidableEq P]
    {L : Vegas.IExpr}
    (σ : Vegas.OmniscientOperationalProfile P L) :
    {Γ : Vegas.VCtx P L} →
      Vegas.VegasCore P L Γ →
      Vegas.VEnv (Player := P) L Γ →
      FDist (Outcome P)
  | _, .ret payoffs, env =>
      FDist.pure (evalPayoffs payoffs env)
  | _, .letExpr x e k, env =>
      outcomeDist σ k <|
        Vegas.VEnv.cons (Player := P) (L := L) (x := x) (τ := .pub _)
          (L.eval e (VEnv.erasePubEnv env)) env
  | _, .sample x D' k, env =>
      FDist.bind
        (L.evalDist D' (VEnv.eraseSampleEnv env))
        (fun v =>
          outcomeDist σ k
            (Vegas.VEnv.cons (Player := P) (L := L) (x := x) (τ := .pub _) v env))
  | _, .commit x who R k, env =>
      FDist.bind
        (σ.commit who x R (Vegas.VEnv.eraseEnv env))
        (fun v =>
          outcomeDist σ k
            (Vegas.VEnv.cons (Player := P) (L := L) (x := x)
              (τ := .hidden who _) v env))
  | _, .reveal y _who _x (b := b) hx k, env =>
      let v : L.Val b := Vegas.VEnv.get (Player := P) (L := L) env hx
      outcomeDist σ k
        (Vegas.VEnv.cons (Player := P) (L := L) (x := y) (τ := .pub b) v env)

theorem outcomeDist_totalWeight_eq_one {P : Type} [DecidableEq P]
    {L : Vegas.IExpr}
    {Γ : Vegas.VCtx P L} {σ : Vegas.OmniscientOperationalProfile P L}
    {p : Vegas.VegasCore P L Γ} {env : Vegas.VEnv (Player := P) L Γ}
    (hd : NormalizedDists p) (hσ : σ.NormalizedOn p) :
    (outcomeDist σ p env).totalWeight = 1 := by
  induction p with
  | ret u =>
      simp [outcomeDist, FDist.totalWeight_pure]
  | letExpr x e k ih =>
      exact ih hd hσ
  | sample x D' k ih =>
      simp only [outcomeDist]
      exact FDist.totalWeight_bind_of_normalized (hd.1 _) (fun _ _ => ih hd.2 hσ)
  | commit x who R k ih =>
      simp only [outcomeDist]
      exact FDist.totalWeight_bind_of_normalized (hσ.1 _) (fun _ _ => ih hd hσ.2)
  | reveal y who x hx k ih =>
      exact ih hd hσ

end Vegas

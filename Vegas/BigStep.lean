import Vegas.WF

/-!
# Big-step semantics for Vegas

The canonical denotational semantics of Vegas programs, together with the
normalization theorem used by the strategic and backend bridges.
-/

namespace Vegas

noncomputable def outcomeDist {P : Type} [DecidableEq P]
    {L : Vegas.ExprLanguage}
    [E : Vegas.ExprKit P L]
    [D : Vegas.DistKit P L]
    (σ : Vegas.Profile P L) :
    {Γ : Vegas.Ctx P L} →
      Vegas.VegasCore P L Γ →
      Vegas.Env (Player := P) L Γ →
      FDist (Outcome P)
  | _, .ret payoffs, env =>
      FDist.pure (evalPayoffs payoffs env)
  | _, .letExpr x e k, env =>
      outcomeDist σ k <|
        Vegas.Env.cons (Player := P) (L := L) (x := x) (τ := .pub _)
          (E.eval e env) env
  | _, .sample x τ m D' k, env =>
      FDist.bind
        (D.eval D' (Vegas.Env.projectDist (Player := P) (L := L) τ m env))
        (fun v =>
          outcomeDist σ k
            (Vegas.Env.cons (Player := P) (L := L) (x := x) (τ := τ) v env))
  | _, .commit x who acts R k, env =>
      FDist.bind
        (σ.commit who x acts R (Vegas.Env.toView (Player := P) (L := L) who env))
        (fun v =>
          outcomeDist σ k
            (Vegas.Env.cons (Player := P) (L := L) (x := x) (τ := .hidden who _) v env))
  | _, .reveal y _who _x (b := b) hx k, env =>
      let v : L.Val b := Vegas.Env.get (Player := P) (L := L) env hx
      outcomeDist σ k (Vegas.Env.cons (Player := P) (L := L) (x := y) (τ := .pub b) v env)

theorem outcomeDist_totalWeight_eq_one {P : Type} [DecidableEq P]
    {L : Vegas.ExprLanguage}
    [E : Vegas.ExprKit P L]
    [D : Vegas.DistKit P L]
    {Γ : Vegas.Ctx P L} {σ : Vegas.Profile P L}
    {p : Vegas.VegasCore P L Γ} {env : Vegas.Env (Player := P) L Γ}
    (hd : NormalizedDists p) (hσ : σ.NormalizedOn p) :
    (outcomeDist σ p env).totalWeight = 1 := by
  induction p with
  | ret u =>
      simp [outcomeDist, FDist.totalWeight_pure]
  | letExpr x e k ih =>
      exact ih hd hσ
  | sample x τ m D' k ih =>
      simp only [outcomeDist]
      exact FDist.totalWeight_bind_of_normalized (hd.1 _) (fun _ _ => ih hd.2 hσ)
  | commit x who acts R k ih =>
      simp only [outcomeDist]
      exact FDist.totalWeight_bind_of_normalized (hσ.1 _) (fun _ _ => ih hd hσ.2)
  | reveal y who x hx k ih =>
      exact ih hd hσ

end Vegas

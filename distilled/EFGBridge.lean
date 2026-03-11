import distilled.Vegas
import GameTheory.Languages.EFG
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Probability.ProbabilityMassFunction.Constructions

open scoped BigOperators
open _root_.EFG

/-!
# Vegas to EFG bridge

This file defines a current-API compilation target for Vegas programs into the
`GameTheory` extensive-form representation.

The bridge is intentionally scoped to executable infrastructure:
- extract an EFG information structure from commit sites
- compile a Vegas program to an `EFG.GameTree`
- package the result as an `EFGGame`

Correctness theorems live separately.
-/

/-- Normalize finitely many nonnegative weights into a `PMF`. If every weight is
zero, fall back to the uniform distribution. -/
noncomputable def normalizedFinPMF {n : Nat} (weights : Fin n → NNReal)
    (hn : 0 < n) : PMF (Fin n) :=
  let f : Fin n → ENNReal := fun i => ↑(weights i)
  have htop : ∑' i, f i ≠ ⊤ := by
    rw [tsum_fintype, ← ENNReal.coe_finset_sum]
    exact ENNReal.coe_ne_top
  if h0 : ∑' i, f i = 0 then
    PMF.ofFintype (fun _ => (n : ENNReal)⁻¹) (by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      exact ENNReal.mul_inv_cancel (by exact_mod_cast hn.ne') (ENNReal.natCast_ne_top n))
  else
    PMF.normalize f h0 htop

/-- A default value for Vegas base types, used only to witness legal views. -/
def defaultVal : (b : BaseTy) → Val b
  | .int => 0
  | .bool => false

/-- A canonical environment for any context, used only in proof obligations. -/
def defaultEnv : (Γ : Ctx) → Env Γ
  | [] => Env.empty
  | (_, τ) :: Γ => Env.cons (defaultVal τ.base) (defaultEnv Γ)

/-- Commit-site metadata: variable id, acting player, and arity. -/
def Prog.infoEntries : Prog Γ → List (VarId × Player × Nat)
  | .ret _ => []
  | .letExpr _ _ k => Prog.infoEntries k
  | .sample _ _ _ _ k => Prog.infoEntries k
  | .commit x who acts _ k => (x, who, acts.length) :: Prog.infoEntries k
  | .reveal _ _ _ _ k => Prog.infoEntries k

/-- Maximum player index mentioned by any commit site, plus one. -/
def Prog.playerCount (p : Prog Γ) : Nat :=
  p.infoEntries.foldl (fun n e => max n e.2.1.succ) 1

/-- The player label stored at a global commit-site index. -/
def Prog.entryPlayer (p : Prog Γ) (i : Fin p.infoEntries.length) : Player :=
  (p.infoEntries.get i).2.1

/-- The action arity stored at a global commit-site index. -/
def Prog.entryArity (p : Prog Γ) (i : Fin p.infoEntries.length) : Nat :=
  (p.infoEntries.get i).2.2

/-- Every legal commit site has strictly positive arity. -/
theorem Prog.infoEntries_arity_pos (p : Prog Γ) (hl : Legal p) :
    ∀ e ∈ p.infoEntries, 0 < e.2.2 := by
  induction p with
  | ret u =>
      intro e he
      simp [Prog.infoEntries] at he
  | letExpr x e k ih =>
      intro e he
      exact ih hl e (by simpa [Prog.infoEntries] using he)
  | sample x τ m D k ih =>
      intro e he
      exact ih hl e (by simpa [Prog.infoEntries] using he)
  | commit x who acts R k ih =>
      rcases hl with ⟨hlegal, hk⟩
      intro e he
      simp only [Prog.infoEntries, List.mem_cons] at he
      rcases he with rfl | he
      · rcases hlegal (defaultEnv _) with ⟨a, ha, _⟩
        exact List.length_pos_of_mem ha
      · exact ih hk e he
  | reveal y who x hx k ih =>
      intro e he
      exact ih hl e (by simpa [Prog.infoEntries] using he)

/-- Every player mentioned by a commit site lies below `playerCount`. -/
theorem Prog.entryPlayer_lt_playerCount (p : Prog Γ) (i : Fin p.infoEntries.length) :
    p.entryPlayer i < p.playerCount := by
  unfold Prog.entryPlayer Prog.playerCount
  have hacc :
      ∀ (acc : Nat) (es : List (VarId × Player × Nat)),
        acc ≤ es.foldl (fun n e => max n e.2.1.succ) acc := by
    intro acc es
    induction es generalizing acc with
    | nil =>
        simp
    | cons a es ih =>
        rw [List.foldl_cons]
        exact Nat.le_trans (Nat.le_max_left _ _) (ih _)
  have hmax :
      (p.infoEntries.get i).2.1.succ ≤
        p.infoEntries.foldl (fun n e => max n e.2.1.succ) 1 := by
    let rec go (acc : Nat) {es : List (VarId × Player × Nat)} {e : VarId × Player × Nat}
        (hmem : e ∈ es) :
        e.2.1.succ ≤ es.foldl (fun n e => max n e.2.1.succ) acc := by
      induction es generalizing acc with
      | nil =>
          cases hmem
      | cons a es ih =>
          simp only [List.mem_cons] at hmem
          rw [List.foldl_cons]
          rcases hmem with rfl | hmem
          · exact Nat.le_trans (Nat.le_max_right _ _) (hacc _ _)
          · exact ih (acc := max acc a.2.1.succ) hmem
    exact go 1 (List.get_mem _ _)
  exact lt_of_lt_of_le (Nat.lt_succ_self _) hmax

/-- The EFG infosets for a player are the global commit indices belonging to them. -/
def Prog.mkInfoS (p : Prog Γ) (hl : Legal p) : InfoStructure where
  n := p.playerCount
  Infoset := fun who => {i : Fin p.infoEntries.length // p.entryPlayer i = who.val}
  arity := fun _ I => p.entryArity I.1
  arity_pos := by
    intro who I
    exact p.infoEntries_arity_pos hl _ (List.get_mem _ _)

/-- Resolve a syntactic distribution expression to its weighted support. -/
def DistExpr.resolveEntries : DistExpr Γ b → Env Γ → List (Val b × ℚ≥0)
  | .weighted entries, _ => entries
  | .ite c t f, env =>
      if evalExpr c env then t.resolveEntries env else f.resolveEntries env

/-- Compile a Vegas program to an EFG tree over the root program's infosets. -/
noncomputable def Prog.toEFGTreeAux (root : Prog Δ) (hlRoot : Legal root) :
    (p : Prog Γ) → Legal p → Env Γ → (base : Nat) →
    root.infoEntries.drop base = p.infoEntries →
    GameTree (root.mkInfoS hlRoot) Outcome
  | .ret u, _, env, _, _ =>
      .terminal (evalPayoffMap u env)
  | .letExpr x e k, hl, env, base, hentries =>
      Prog.toEFGTreeAux root hlRoot k hl
        (Env.cons (x := x) (evalExpr e env) env) base
        (by simpa [Prog.infoEntries] using hentries)
  | .sample x τ m D k, hl, env, base, hentries =>
      let entries := D.resolveEntries (env.projectDist τ m)
      match entries with
      | [] => .terminal 0
      | e :: es =>
          .chance (List.length (e :: es))
            (normalizedFinPMF
              (fun i =>
                let w := ((e :: es).get i).2
                ⟨(w : ℝ), by exact_mod_cast w.coe_nonneg⟩)
              (by simp))
            (by simp)
            (fun i =>
              let v := ((e :: es).get i).1
              Prog.toEFGTreeAux root hlRoot k hl
                (Env.cons (x := x) (τ := τ) v env) base
                (by simpa [Prog.infoEntries] using hentries))
  | .commit x who acts R k, hl, env, base, hentries =>
      have hbase : base < root.infoEntries.length := by
        have hlen : 0 < (root.infoEntries.drop base).length := by
          simpa [hentries, Prog.infoEntries]
        simpa [List.length_drop] using hlen
      have hdrop :
          root.infoEntries.get ⟨base, hbase⟩ :: root.infoEntries.drop (base + 1) =
            (x, who, acts.length) :: Prog.infoEntries k := by
        simpa [hentries, Prog.infoEntries] using (List.drop_eq_getElem_cons hbase)
      have hget : root.infoEntries.get ⟨base, hbase⟩ = (x, who, acts.length) :=
        (List.cons.inj hdrop).1
      have htail : root.infoEntries.drop (base + 1) = Prog.infoEntries k :=
        (List.cons.inj hdrop).2
      have hplayer : root.entryPlayer ⟨base, hbase⟩ = who := by
        simpa [Prog.entryPlayer] using congrArg (fun e => e.2.1) hget
      let pWho : Fin root.playerCount :=
        ⟨who, by
          simpa [hplayer] using root.entryPlayer_lt_playerCount ⟨base, hbase⟩⟩
      let I : (root.mkInfoS hlRoot).Infoset pWho :=
        ⟨⟨base, hbase⟩, by
          simpa [Prog.mkInfoS, pWho, hplayer]⟩
      have hentryArity : root.entryArity ⟨base, hbase⟩ = acts.length := by
        simpa [Prog.entryArity] using congrArg (fun e => e.2.2) hget
      have hArity : (root.mkInfoS hlRoot).arity pWho I = acts.length := by
        simpa [Prog.mkInfoS, I] using hentryArity
      .decision (p := pWho) I (fun a =>
        let idx : Fin acts.length := by
          simpa [InfoStructure.Act, hArity] using a
        Prog.toEFGTreeAux root hlRoot k hl.2
          (Env.cons (x := x) (τ := .hidden who _) (acts.get idx) env)
          (base + 1) htail)
  | .reveal y who x hx k, hl, env, base, hentries =>
      let v := env.get hx
      Prog.toEFGTreeAux root hlRoot k hl
        (Env.cons (x := y) (τ := .pub _) v env) base
        (by simpa [Prog.infoEntries] using hentries)

/-- Compile a Vegas program into an `EFGGame` using the current `GameTheory` API. -/
noncomputable def Prog.toEFGGame (p : Prog Γ) (hl : Legal p) (env : Env Γ) :
    EFGGame where
  inf := p.mkInfoS hl
  Outcome := Outcome
  tree := Prog.toEFGTreeAux p hl p hl env 0 rfl
  utility := fun o who => (o who.val : ℝ)


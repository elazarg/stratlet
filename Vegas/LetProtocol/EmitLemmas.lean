/-
Vegas/LetProtocol/EmitLemmas.lean

Simp lemmas, Extension Lemma, and projection lemma for the emit layer.
-/

import Vegas.LetProtocol.Emit
import Vegas.LetProtocol.ProtoLemmas
import Vegas.LetProb.WDistLemmas

namespace Emit

open Defs Prog Proto

variable {L : Language}
variable {W : Type} [WeightModel W]

-- ============================================================
-- Helper lemmas for WDist
-- ============================================================

/-- WDist.map with identity is the identity. -/
private theorem WDist_map_id {α : Type*} (d : WDist W α) :
    WDist.map (fun x => x) d = d := by
  cases d with
  | mk ws =>
    apply WDist.ext_weights
    simp only [WDist.map, WDist.mk_weights]
    rw [show (fun x : α × W => ((fun x => x) x.1, x.2)) = id from
      funext fun x => by simp]
    simp

/-- `WDist.map` composition law. -/
private theorem WDist_map_map {α β γ : Type*} (f : β → γ) (g : α → β) (d : WDist W α) :
    WDist.map f (WDist.map g d) = WDist.map (f ∘ g) d := by
  cases d with
  | mk ws => apply WDist.ext_weights; simp [WDist.map, List.map_map]

/-- `WDist.bind` after `WDist.map`. -/
private theorem WDist_bind_map {α β γ : Type*} (f : α → β) (d : WDist W α) (g : β → WDist W γ) :
    WDist.bind (WDist.map f d) g = WDist.bind d (g ∘ f) := by
  cases d with
  | mk ws => apply WDist.ext_weights; simp [WDist.map, WDist.bind, List.flatMap_map]

/-- `WDist.map` distributes into `WDist.bind`. -/
private theorem WDist_map_bind {α β γ : Type*} (f : β → γ) (d : WDist W α) (g : α → WDist W β) :
    WDist.map f (WDist.bind d g) = WDist.bind d (fun x => WDist.map f (g x)) := by
  cases d with
  | mk ws =>
    apply WDist.ext_weights
    simp only [WDist.map, WDist.bind, WDist.mk_weights]
    induction ws with
    | nil => simp
    | cons hd tl ih =>
      rcases hd with ⟨a, w⟩
      simp only [List.flatMap_cons, List.map_append, List.map_map]
      congr 1
      convert ih using 2
      ext ⟨b, w'⟩
      simp

-- ============================================================
-- 0) Simp lemmas for evalEProto
-- ============================================================

@[simp] lemma evalEProto_ret {Ev : Type} {Γ τ} (σ : Profile (L := L) (W := W))
    (e : L.Expr Γ τ) (env : L.Env Γ) :
    evalEProto (Ev := Ev) σ (.ret e) env = WDist.pure (L.eval e env, []) := rfl

@[simp] lemma evalEProto_letDet {Ev : Type} {Γ τ τ'} (σ : Profile (L := L) (W := W))
    (e : L.Expr Γ τ') (k : EProtoProg Ev (τ' :: Γ) τ) (env : L.Env Γ) :
    evalEProto σ (.letDet e k) env =
      evalEProto σ k (L.eval e env, env) := rfl

@[simp] lemma evalEProto_sample_bind {Ev : Type} {Γ τ τ'} (σ : Profile (L := L) (W := W))
    (id : YieldId) (v : View Γ) (K : ObsKernel v τ')
    (k : EProtoProg Ev (τ' :: Γ) τ) (env : L.Env Γ) :
    evalEProto σ (.doBind (.sample id v K) k) env =
      WDist.bind (WDist.map (fun x => (x, ([] : Trace Ev))) (K (v.proj env)))
        (fun (x, tr1) => WDist.map (fun (v', tr2) => (v', tr1 ++ tr2))
          (evalEProto σ k (x, env))) := rfl

@[simp] lemma evalEProto_choose_bind {Ev : Type} {Γ τ τ'} (σ : Profile (L := L) (W := W))
    (id : YieldId) (who : Player) (v : View Γ) (A : Act v τ')
    (k : EProtoProg Ev (τ' :: Γ) τ) (env : L.Env Γ) :
    evalEProto σ (.doBind (.choose id who v A) k) env =
      WDist.bind (WDist.map (fun x => (x, ([] : Trace Ev))) (σ.choose who id v A (v.proj env)))
        (fun (x, tr1) => WDist.map (fun (v', tr2) => (v', tr1 ++ tr2))
          (evalEProto σ k (x, env))) := rfl

@[simp] lemma evalEProto_observe {Ev : Type} {Γ τ} (σ : Profile (L := L) (W := W))
    (cond : L.Expr Γ L.bool) (k : EProtoProg Ev Γ τ) (env : L.Env Γ) :
    evalEProto σ (EProtoProg.observe cond k) env =
      if L.toBool (L.eval cond env)
      then evalEProto σ k env
      else WDist.zero := by
  by_cases h : L.toBool (L.eval cond env)
  · simp only [EProtoProg.observe, evalEProto, Prog.evalWith, Prog.evalProg_gen, EProtoSem,
      TracedEff, h, ite_true, WDist.bind_pure]
    exact WDist_map_id _
  · simp only [EProtoProg.observe, evalEProto, Prog.evalWith, Prog.evalProg_gen, EProtoSem,
      TracedEff, h]
    rfl

@[simp] lemma evalEProto_emit {Ev : Type} {Γ τ} (σ : Profile (L := L) (W := W))
    (f : L.Env Γ → Ev) (k : EProtoProg Ev Γ τ) (env : L.Env Γ) :
    evalEProto σ (EProtoProg.emit f k) env =
      WDist.map (fun (v, tr) => (v, f env :: tr)) (evalEProto σ k env) := by
  simp only [EProtoProg.emit, evalEProto, Prog.evalWith, Prog.evalProg_gen, EProtoSem,
    TracedEff, WDist.bind_pure]
  rfl

-- ============================================================
-- 1) applyProfileE preserves doStmt (emit transparency)
-- ============================================================

/-- `applyProfileE` does not touch `doStmt` nodes (both observe and emit pass through). -/
theorem applyProfileE_preserves_doStmt {Ev : Type} (π : PProfile (L := L) (W := W))
    {Γ : L.Ctx} {τ : L.Ty} (s : CmdStmtEv Ev Γ) (k : EProtoProg Ev Γ τ) :
    applyProfileE π (.doStmt s k) = .doStmt s (applyProfileE π k) := rfl

-- ============================================================
-- 2) Lifted Extension Lemma
-- ============================================================

/--
If a total profile `σ` extends a partial profile `π`, then evaluating
an `EProtoProg` under `σ` is the same whether or not we first apply `π`.

This mirrors `evalProto_applyProfile_of_extends` from ProtoLemmas.
-/
theorem evalEProto_applyProfileE_of_extends {Ev : Type}
    (σ : Profile (L := L) (W := W)) (π : PProfile (L := L) (W := W))
    (hExt : ProtoProg.Extends (W := W) σ π) :
    ∀ {Γ τ} (p : EProtoProg (L := L) Ev Γ τ) (env : L.Env Γ),
      evalEProto σ (applyProfileE π p) env
        =
      evalEProto σ p env := by
  intro Γ τ p
  induction p with
  | ret e =>
      intro env; rfl
  | letDet e k ih =>
      intro env; exact ih _
  | doStmt s k ih =>
      intro env
      cases s with
      | observe cond =>
          -- Fold back to smart constructor for simp lemma matching
          change evalEProto σ (EProtoProg.observe cond (applyProfileE π k)) env =
               evalEProto σ (EProtoProg.observe cond k) env
          simp only [evalEProto_observe]
          split
          · exact ih _
          · rfl
      | emit f =>
          change evalEProto σ (EProtoProg.emit f (applyProfileE π k)) env =
               evalEProto σ (EProtoProg.emit f k) env
          simp only [evalEProto_emit]
          congr 1
          exact ih _
  | doBind c k ih =>
      intro env
      cases c with
      | sample id v K =>
          simp only [applyProfileE, evalEProto_sample_bind]
          congr 1; funext ⟨x, tr1⟩; congr 1; exact ih (x, env)
      | choose id who v A =>
          cases hπ : π.choose? who id v A with
          | none =>
              simp only [applyProfileE, hπ, evalEProto_choose_bind]
              congr 1; funext ⟨x, tr1⟩; congr 1; exact ih (x, env)
          | some Kdec =>
              simp only [applyProfileE, hπ, evalEProto_sample_bind, evalEProto_choose_bind]
              have hσ := hExt who id v A Kdec hπ
              subst hσ
              congr 1; funext ⟨x, tr1⟩; congr 1; exact ih (x, env)

-- ============================================================
-- 3) Projection lemma: liftProto preserves semantics
-- ============================================================

/--
Evaluating a lifted protocol program produces the same distribution
as evaluating the original, but with an empty trace appended.

`evalEProto σ (liftProto p) env = WDist.map (fun v => (v, [])) (evalProto σ p env)`
-/
theorem evalEProto_liftProto {Ev : Type}
    (σ : Profile (L := L) (W := W)) :
    ∀ {Γ τ} (p : ProtoProg (L := L) (W := W) Γ τ) (env : L.Env Γ),
      evalEProto (Ev := Ev) σ (liftProto p) env =
        WDist.map (fun v => (v, ([] : Trace Ev))) (evalProto σ p env) := by
  intro Γ τ p
  induction p with
  | ret e =>
      intro env
      simp only [liftProto, evalEProto_ret, evalProto, Prog.evalWith, Prog.evalProg_gen,
        ProtoSem, EffWDist, Prob.EffWDist, WDist.map, WDist.pure]
      rfl
  | letDet e k ih =>
      intro env
      simp only [liftProto, evalEProto_letDet, evalProto, Prog.evalWith, Prog.evalProg_gen]
      exact ih _
  | doStmt s k ih =>
      intro env
      cases s with
      | observe cond =>
          simp only [liftProto]
          -- LHS: evalEProto σ (.doStmt (.observe cond) (liftProto k)) env
          -- Fold to smart constructor
          change evalEProto σ (EProtoProg.observe cond (liftProto k)) env =
            WDist.map (fun v => (v, ([] : Trace Ev)))
              (evalProto σ (ProtoProg.observe cond k) env)
          simp only [evalEProto_observe, ProtoProg.evalProto_observe]
          split
          · rw [ih _]
          · simp [WDist.map, WDist.zero]
  | doBind c k ih =>
      intro env
      cases c with
      | sample id v K =>
          -- Unfold liftProto (definitional)
          change evalEProto σ (.doBind (.sample id v K) (liftProto k)) env =
               WDist.map (fun v => (v, ([] : Trace Ev)))
                (evalProto σ (.doBind (.sample id v K) k) env)
          rw [evalEProto_sample_bind]
          -- Unfold evalProto on sample (definitional, bypasses smart constructor mismatch)
          conv_rhs =>
            rw [show evalProto σ (Prog.doBind (CmdBindProto.sample id v K) k) env =
                WDist.bind (K (v.proj env)) (fun x => evalProto σ k (x, env)) from rfl]
            rw [WDist_map_bind]
          conv_lhs =>
            rw [WDist_bind_map (fun x => (x, ([] : Trace Ev))) (K (v.proj env))]
          congr 1; ext x
          -- Beta-reduce the composition on LHS
          change WDist.map (fun x_1 => (x_1.1, ([] : Trace Ev) ++ x_1.2))
              (evalEProto σ (liftProto k) (x, env)) =
            WDist.map (fun v => (v, ([] : Trace Ev))) (evalProto σ k (x, env))
          rw [ih (x, env), WDist_map_map]; congr 1
      | choose id who v A =>
          -- Unfold liftProto (definitional)
          change evalEProto σ (.doBind (.choose id who v A) (liftProto k)) env =
               WDist.map (fun v => (v, ([] : Trace Ev)))
                (evalProto σ (.doBind (.choose id who v A) k) env)
          rw [evalEProto_choose_bind]
          -- Unfold evalProto on choose (definitional, bypasses smart constructor mismatch)
          conv_rhs =>
            rw [show evalProto σ (Prog.doBind (CmdBindProto.choose id who v A) k) env =
                WDist.bind (σ.choose who id v A (v.proj env))
                  (fun x => evalProto σ k (x, env)) from rfl]
            rw [WDist_map_bind]
          conv_lhs =>
            rw [WDist_bind_map (fun x => (x, ([] : Trace Ev)))
              (σ.choose who id v A (v.proj env))]
          congr 1; ext x
          -- Beta-reduce the composition on LHS
          change WDist.map (fun x_1 => (x_1.1, ([] : Trace Ev) ++ x_1.2))
              (evalEProto σ (liftProto k) (x, env)) =
            WDist.map (fun v => (v, ([] : Trace Ev))) (evalProto σ k (x, env))
          rw [ih (x, env), WDist_map_map]; congr 1

end Emit

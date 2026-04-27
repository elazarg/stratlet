import GameTheory.Languages.FOSG.Information
import GameTheory.Languages.FOSG.Strategy
import Vegas.Strategic
import Vegas.ViewKernel
import Vegas.WFProgram

/-!
# Vegas to FOSG bridge, first layer

This file records the part of the Vegas/FOSG correspondence that is already
structural: commit guards are state-dependent action-availability constraints.
The full `GameTheory.FOSG` compiler still needs a careful world choice. In
particular, the FOSG transition field is total over all worlds, while Vegas'
normalization proof is attached to the original program and its syntactic
subprograms. A compiler should therefore use a reachable-world type carrying
the inherited obligations, rather than quantify over arbitrary
`Σ Γ, VegasCore P L Γ × VEnv L Γ` states.
-/

namespace Vegas
namespace FOSGBridge

open GameTheory

variable {P : Type} [DecidableEq P] {L : IExpr}

/-- A static FOSG action alphabet for Vegas: a player action is a typed value.

The player argument is intentionally unused. FOSG requires a per-player static
action type, while a Vegas commit node chooses the active player and the type
of value expected at that node. Node-local availability below filters this
static alphabet down to the values of the demanded type satisfying the guard.
-/
abbrev Action (L : IExpr) (_who : P) : Type :=
  Sigma L.Val

/-- A Vegas runtime configuration, before restricting to reachable states. -/
structure World (P : Type) [DecidableEq P] (L : IExpr) where
  Γ : VCtx P L
  prog : VegasCore P L Γ
  env : VEnv L Γ

namespace World

/-- The initial world associated with a checked Vegas program. -/
def initial (g : WFProgram P L) : World P L where
  Γ := g.Γ
  prog := g.prog
  env := g.env

end World

/-- Vegas terminal states are exactly `ret` configurations. -/
def terminal (w : World P L) : Prop :=
  match w.prog with
  | .ret _ => True
  | _ => False

/-- The only strategic FOSG states are Vegas `commit` nodes. -/
def active (w : World P L) : Finset P :=
  match w.prog with
  | .commit _ who _ _ => {who}
  | _ => ∅

/-- Node-local action availability.

At a commit node, the owner may choose exactly values of the committed type
that satisfy the guard in the current erased environment. Every other player,
and every non-commit node, has no available concrete action.
-/
def availableActions (w : World P L) (who : P) : Set (Action (P := P) L who) :=
  match w.prog with
  | .commit _ owner (b := b) R _ =>
      if owner = who then
        {a | ∃ v : L.Val b,
          a = Sigma.mk b v ∧
            evalGuard (Player := P) (L := L) R v (VEnv.eraseEnv w.env) = true}
      else
        ∅
  | _ => ∅

abbrev JointAction (P : Type) [DecidableEq P] (L : IExpr) : Type :=
  GameTheory.JointAction (fun who : P => Action (P := P) L who)

/-- FOSG joint-action legality for the structural Vegas/FOSG layer. -/
abbrev JointActionLegal (w : World P L) (a : JointAction P L) : Prop :=
  GameTheory.JointActionLegal
    (fun who : P => Action (P := P) L who)
    active
    terminal
    availableActions
    w
    a

/-- A joint action where exactly `who` commits to `v`. -/
def commitJointAction (who : P) {b : L.Ty} (v : L.Val b) : JointAction P L :=
  fun i => if i = who then some (Sigma.mk b v) else none

@[simp] theorem terminal_ret
    {Γ : VCtx P L} {env : VEnv L Γ}
    (payoffs : List (P × L.Expr (erasePubVCtx Γ) L.int)) :
    terminal ({ Γ := Γ, prog := VegasCore.ret payoffs, env := env } : World P L) := by
  simp [terminal]

@[simp] theorem active_ret
    {Γ : VCtx P L} {env : VEnv L Γ}
    (payoffs : List (P × L.Expr (erasePubVCtx Γ) L.int)) :
    active ({ Γ := Γ, prog := VegasCore.ret payoffs, env := env } : World P L) = ∅ := by
  simp [active]

theorem terminal_active_eq_empty {w : World P L} :
    terminal w → active w = ∅ := by
  cases w with
  | mk Γ prog env =>
      cases prog <;> simp [terminal, active]

theorem terminal_no_legal {w : World P L} {a : JointAction P L} :
    terminal w → ¬ JointActionLegal w a := by
  intro hterm hlegal
  exact hlegal.1 hterm

/-- Internal Vegas states have a legal FOSG no-op joint action. -/
theorem noop_legal_of_active_empty {w : World P L}
    (hterm : ¬ terminal w) (hactive : active w = ∅) :
    JointActionLegal w
      (GameTheory.FOSG.noopAction (fun who : P => Action (P := P) L who)) := by
  refine ⟨hterm, ?_⟩
  intro i
  simp [GameTheory.FOSG.noopAction, hactive]

/-- Program-level `Legal` is exactly what is needed to avoid FOSG deadlock:
every nonterminal Vegas configuration admits at least one legal joint action.

For commit states this witness is the guard-satisfying value promised by
`Legal`; for administrative and nature/reveal states it is the all-`none`
joint action.
-/
theorem exists_jointActionLegal_of_legal
    (w : World P L) (hlegal : Legal w.prog) (hterm : ¬ terminal w) :
    ∃ a : JointAction P L, JointActionLegal w a := by
  cases w with
  | mk Γ prog env =>
      cases prog with
      | ret payoffs =>
          simp [terminal] at hterm
      | letExpr x e k =>
          refine ⟨GameTheory.FOSG.noopAction (fun who : P => Action (P := P) L who), ?_⟩
          refine ⟨by simp [terminal], ?_⟩
          intro i
          simp [GameTheory.FOSG.noopAction, active]
      | sample x D k =>
          refine ⟨GameTheory.FOSG.noopAction (fun who : P => Action (P := P) L who), ?_⟩
          refine ⟨by simp [terminal], ?_⟩
          intro i
          simp [GameTheory.FOSG.noopAction, active]
      | commit x who R k =>
          rcases hlegal.1 (VEnv.eraseEnv env) with ⟨v, hv⟩
          refine ⟨commitJointAction (L := L) who v, ?_⟩
          refine ⟨by simp [terminal], ?_⟩
          intro i
          by_cases hi : i = who
          · subst i
            simp [commitJointAction, active, availableActions, hv]
          · simp [commitJointAction, active, hi]
      | reveal y who x hx k =>
          refine ⟨GameTheory.FOSG.noopAction (fun who : P => Action (P := P) L who), ?_⟩
          refine ⟨by simp [terminal], ?_⟩
          intro i
          simp [GameTheory.FOSG.noopAction, active]

/-- The initial checked program has a legal FOSG joint action whenever it is
not already terminal. -/
theorem initial_exists_jointActionLegal
    (g : WFProgram P L) (hterm : ¬ terminal (World.initial g)) :
    ∃ a : JointAction P L, JointActionLegal (World.initial g) a :=
  exists_jointActionLegal_of_legal (World.initial g) g.legal hterm

namespace ProgramBehavioralProfile

/-- Dropping the head commit site preserves behavioral guard-legality. -/
theorem tail_isLegal
    {Γ : VCtx P L} {x : VarId} {who : P} {b : L.Ty}
    {R : L.Expr ((x, b) :: eraseVCtx Γ) L.bool}
    {k : VegasCore P L ((x, .hidden who b) :: Γ)}
    {σ : ProgramBehavioralProfile (P := P) (L := L) (.commit x who R k)}
    (hσ : σ.IsLegal) :
    (ProgramBehavioralProfile.tail (P := P) (L := L) σ).IsLegal := by
  intro j
  by_cases hj : who = j
  · subst hj
    have hσ_who : (σ who).IsLegal (.commit x who R k) := hσ who
    dsimp [ProgramBehavioralStrategy.IsLegal] at hσ_who
    dsimp [ProgramBehavioralProfile.tail]
    split at hσ_who
    · split
      · exact hσ_who.2
      · exact absurd rfl ‹_›
    · exact absurd rfl ‹_›
  · have hσ_j : (σ j).IsLegal (.commit x who R k) := hσ j
    dsimp [ProgramBehavioralStrategy.IsLegal] at hσ_j
    dsimp [ProgramBehavioralProfile.tail]
    split at hσ_j
    · rename_i h
      exact absurd h hj
    · split
      · rename_i h
        exact absurd h hj
      · exact hσ_j

end ProgramBehavioralProfile

/-! ## Program cursors

The FOSG state must remember not only the current subprogram but also where
that subprogram sits inside the original Vegas program. This is what lets a
fixed Vegas strategy profile be projected to the current continuation without
putting strategy data into the game state.
-/

/-- `ProgramSuffix root p` means `p` is the current continuation reached by
stepping forward from `root`. It is a typed cursor into the original program. -/
inductive ProgramSuffix {Γ₀ : VCtx P L} (root : VegasCore P L Γ₀) :
    {Γ : VCtx P L} → VegasCore P L Γ → Type where
  | here : ProgramSuffix root root
  | letExpr
      {Γ : VCtx P L} {x : VarId} {b : L.Ty}
      {e : L.Expr (erasePubVCtx Γ) b}
      {k : VegasCore P L ((x, .pub b) :: Γ)}
      (s : ProgramSuffix root (.letExpr x e k)) :
      ProgramSuffix root k
  | sample
      {Γ : VCtx P L} {x : VarId} {b : L.Ty}
      {D : L.DistExpr (erasePubVCtx Γ) b}
      {k : VegasCore P L ((x, .pub b) :: Γ)}
      (s : ProgramSuffix root (.sample x D k)) :
      ProgramSuffix root k
  | commit
      {Γ : VCtx P L} {x : VarId} {who : P} {b : L.Ty}
      {R : L.Expr ((x, b) :: eraseVCtx Γ) L.bool}
      {k : VegasCore P L ((x, .hidden who b) :: Γ)}
      (s : ProgramSuffix root (.commit x who R k)) :
      ProgramSuffix root k
  | reveal
      {Γ : VCtx P L} {y : VarId} {who : P} {x : VarId} {b : L.Ty}
      {hx : VHasVar Γ x (.hidden who b)}
      {k : VegasCore P L ((y, .pub b) :: Γ)}
      (s : ProgramSuffix root (.reveal y who x hx k)) :
      ProgramSuffix root k

namespace ProgramSuffix

def fresh
    {Γ₀ Γ : VCtx P L} {root : VegasCore P L Γ₀} {p : VegasCore P L Γ}
    (s : ProgramSuffix root p) :
    FreshBindings root → FreshBindings p := by
  induction s with
  | here => intro h; exact h
  | letExpr s ih => intro h; exact ih h |>.2
  | sample s ih => intro h; exact ih h |>.2
  | commit s ih => intro h; exact ih h |>.2
  | reveal s ih => intro h; exact ih h |>.2

def viewScoped
    {Γ₀ Γ : VCtx P L} {root : VegasCore P L Γ₀} {p : VegasCore P L Γ}
    (s : ProgramSuffix root p) :
    ViewScoped root → ViewScoped p := by
  induction s with
  | here => intro h; exact h
  | letExpr s ih => intro h; exact ih h
  | sample s ih => intro h; exact ih h
  | commit s ih => intro h; exact (ih h).2
  | reveal s ih => intro h; exact ih h

def normalized
    {Γ₀ Γ : VCtx P L} {root : VegasCore P L Γ₀} {p : VegasCore P L Γ}
    (s : ProgramSuffix root p) :
    NormalizedDists root → NormalizedDists p := by
  induction s with
  | here => intro h; exact h
  | letExpr s ih => intro h; exact ih h
  | sample s ih => intro h; exact (ih h).2
  | commit s ih => intro h; exact ih h
  | reveal s ih => intro h; exact ih h

def legal
    {Γ₀ Γ : VCtx P L} {root : VegasCore P L Γ₀} {p : VegasCore P L Γ}
    (s : ProgramSuffix root p) :
    Legal root → Legal p := by
  induction s with
  | here => intro h; exact h
  | letExpr s ih => intro h; exact ih h
  | sample s ih => intro h; exact ih h
  | commit s ih => intro h; exact (ih h).2
  | reveal s ih => intro h; exact ih h

noncomputable def behavioralProfile
    {Γ₀ Γ : VCtx P L} {root : VegasCore P L Γ₀} {p : VegasCore P L Γ}
    (s : ProgramSuffix root p) :
    ProgramBehavioralProfile (P := P) (L := L) root →
      ProgramBehavioralProfile (P := P) (L := L) p := by
  induction s with
  | here => intro σ; exact σ
  | letExpr s ih => intro σ; exact ih σ
  | sample s ih => intro σ; exact ih σ
  | commit s ih =>
      intro σ
      exact ProgramBehavioralProfile.tail (P := P) (L := L) (ih σ)
  | reveal s ih => intro σ; exact ih σ

theorem behavioralProfile_isLegal
    {Γ₀ Γ : VCtx P L} {root : VegasCore P L Γ₀} {p : VegasCore P L Γ}
    (s : ProgramSuffix root p)
    {σ : ProgramBehavioralProfile (P := P) (L := L) root}
    (hσ : σ.IsLegal) :
    (s.behavioralProfile σ).IsLegal := by
  induction s generalizing σ with
  | here => exact hσ
  | letExpr s ih => exact ih hσ
  | sample s ih => exact ih hσ
  | commit s ih =>
      exact ProgramBehavioralProfile.tail_isLegal (P := P) (L := L) (ih hσ)
  | reveal s ih => exact ih hσ

end ProgramSuffix

/-! ## A checked-world FOSG skeleton

The next layer uses worlds that carry the local obligations needed by the FOSG
structure itself. This avoids totalizing the game over malformed, deadlocking
Vegas configurations. We carry `FreshBindings` and `ViewScoped` separately
rather than `WF`: after a `commit`, the continuation is reveal-complete only
relative to a nonempty pending stack, so the raw continuation need not satisfy
`WF` with an empty pending stack.
-/

/-- A Vegas runtime configuration carrying the local obligations needed by
FOSG's total transition, non-deadlock, and observation-soundness fields.

This is intentionally not named `WFWorld`: `WF` includes
`RevealComplete []`, which is not stable under stepping through a `commit`.
-/
structure CheckedWorld (g : WFProgram P L) (hctx : WFCtx g.Γ) where
  Γ : VCtx P L
  prog : VegasCore P L Γ
  env : VEnv L Γ
  suffix : ProgramSuffix g.prog prog
  wctx : WFCtx Γ
  fresh : FreshBindings prog
  viewScoped : ViewScoped prog
  normalized : NormalizedDists prog
  legal : Legal prog

namespace CheckedWorld

def toWorld {g : WFProgram P L} {hctx : WFCtx g.Γ}
    (w : CheckedWorld g hctx) : World P L where
  Γ := w.Γ
  prog := w.prog
  env := w.env

def initial (g : WFProgram P L) (hctx : WFCtx g.Γ) : CheckedWorld g hctx where
  Γ := g.Γ
  prog := g.prog
  env := g.env
  suffix := .here
  wctx := hctx
  fresh := g.wf.1
  viewScoped := g.wf.2.2
  normalized := g.normalized
  legal := g.legal

end CheckedWorld

def checkedTerminal {g : WFProgram P L} {hctx : WFCtx g.Γ}
    (w : CheckedWorld g hctx) : Prop :=
  terminal w.toWorld

def checkedActive {g : WFProgram P L} {hctx : WFCtx g.Γ}
    (w : CheckedWorld g hctx) : Finset P :=
  active w.toWorld

def checkedAvailableActions
    {g : WFProgram P L} {hctx : WFCtx g.Γ}
    (w : CheckedWorld g hctx) (who : P) : Set (Action (P := P) L who) :=
  availableActions w.toWorld who

abbrev CheckedJointActionLegal
    {g : WFProgram P L} {hctx : WFCtx g.Γ}
    (w : CheckedWorld g hctx) (a : JointAction P L) : Prop :=
  GameTheory.JointActionLegal
    (fun who : P => Action (P := P) L who)
    checkedActive
    checkedTerminal
    checkedAvailableActions
    w
    a

private theorem commit_value_of_legal
    {Γ : VCtx P L} {x : VarId} {who : P} {b : L.Ty}
    {R : L.Expr ((x, b) :: eraseVCtx Γ) L.bool}
    {k : VegasCore P L ((x, .hidden who b) :: Γ)}
    {env : VEnv L Γ} {a : JointAction P L}
    (ha : JointActionLegal
      ({ Γ := Γ, prog := VegasCore.commit x who R k, env := env } : World P L) a) :
    ∃ v : L.Val b,
      a who = some (Sigma.mk b v) ∧
        evalGuard (Player := P) (L := L) R v (VEnv.eraseEnv env) = true := by
  have hlocal := ha.2 who
  cases hact : a who with
  | none =>
      have hnot : who ∉ ({who} : Finset P) := by
        simp [active, hact] at hlocal
      exact False.elim (hnot (by simp))
  | some ai =>
      have havail : ai ∈
          availableActions
            ({ Γ := Γ, prog := VegasCore.commit x who R k, env := env } : World P L)
            who := by
        have hpair : who ∈ ({who} : Finset P) ∧
            ai ∈ availableActions
              ({ Γ := Γ, prog := VegasCore.commit x who R k, env := env } : World P L)
              who := by
          simpa [JointActionLegal, GameTheory.JointActionLegal, active, hact] using hlocal
        exact hpair.2
      rcases (by
        simpa [availableActions] using havail) with ⟨v, hai, hv⟩
      exact ⟨v, by simp [hai], hv⟩

theorem checked_terminal_active_eq_empty
    {g : WFProgram P L} {hctx : WFCtx g.Γ} {w : CheckedWorld g hctx} :
    checkedTerminal w → checkedActive w = ∅ :=
  terminal_active_eq_empty

theorem checked_terminal_no_legal
    {g : WFProgram P L} {hctx : WFCtx g.Γ}
    {w : CheckedWorld g hctx} {a : JointAction P L} :
    checkedTerminal w → ¬ CheckedJointActionLegal w a := by
  intro hterm hlegal
  exact hlegal.1 hterm

theorem checked_nonterminal_exists_legal
    {g : WFProgram P L} {hctx : WFCtx g.Γ} {w : CheckedWorld g hctx} :
    ¬ checkedTerminal w →
      ∃ a : JointAction P L, CheckedJointActionLegal w a := by
  intro hterm
  exact exists_jointActionLegal_of_legal w.toWorld w.legal hterm

/-- The one-step transition kernel of the checked-world FOSG skeleton. -/
noncomputable def checkedTransition
    {g : WFProgram P L} {hctx : WFCtx g.Γ}
    (w : CheckedWorld g hctx)
    (a : {a : JointAction P L // CheckedJointActionLegal w a}) :
    PMF (CheckedWorld g hctx) := by
  cases w with
  | mk Γ prog env suffix wctx fresh viewScoped normalized legal =>
      cases prog with
      | ret payoffs =>
          exact False.elim (a.2.1 (by simp [checkedTerminal, CheckedWorld.toWorld, terminal]))
      | letExpr x e k =>
          exact PMF.pure
            { Γ := _
              prog := k
              env := VEnv.cons (Player := P) (L := L) (x := x) (τ := .pub _)
                (L.eval e (VEnv.erasePubEnv env)) env
              suffix := .letExpr suffix
              wctx := WFCtx.cons fresh.1 wctx
              fresh := fresh.2
              viewScoped := viewScoped
              normalized := normalized
              legal := legal }
      | sample x D k =>
          exact PMF.map
            (fun v =>
              { Γ := _
                prog := k
                env := VEnv.cons (Player := P) (L := L) (x := x) (τ := .pub _)
                  v env
                suffix := .sample suffix
                wctx := WFCtx.cons fresh.1 wctx
                fresh := fresh.2
                viewScoped := viewScoped
                normalized := normalized.2
                legal := legal })
            ((L.evalDist D (VEnv.eraseSampleEnv env)).toPMF (normalized.1 env))
      | commit x who R k =>
          have ha : JointActionLegal
              ({ Γ := Γ, prog := VegasCore.commit x who R k, env := env } : World P L)
              a.1 := by
            simpa [CheckedJointActionLegal, checkedActive, checkedTerminal,
              checkedAvailableActions, CheckedWorld.toWorld] using a.2
          let v := Classical.choose (commit_value_of_legal (L := L) ha)
          exact PMF.pure
            { Γ := _
              prog := k
              env := VEnv.cons (Player := P) (L := L) (x := x) (τ := .hidden who _)
                v env
              suffix := .commit suffix
              wctx := WFCtx.cons fresh.1 wctx
              fresh := fresh.2
              viewScoped := viewScoped.2
              normalized := normalized
              legal := legal.2 }
      | reveal y who x hx k =>
          exact PMF.pure
            { Γ := _
              prog := k
              env := VEnv.cons (Player := P) (L := L) (x := y) (τ := .pub _)
                (env x (.hidden who _) hx) env
              suffix := .reveal suffix
              wctx := WFCtx.cons fresh.1 wctx
              fresh := fresh.2
              viewScoped := viewScoped
              normalized := normalized
              legal := legal }

def rewardOnEnteringRet
    {g : WFProgram P L} {hctx : WFCtx g.Γ}
    (_w : CheckedWorld g hctx)
    (_a : {a : JointAction P L // CheckedJointActionLegal _w a})
    (w' : CheckedWorld g hctx) (who : P) : ℝ :=
  match w'.prog with
  | .ret payoffs => (evalPayoffs payoffs w'.env who : ℝ)
  | _ => 0

/-- A first executable FOSG control-flow object for a checked Vegas program.

This captures the operational control flow and guard-as-availability
structure. The observation types are intentionally coarse, and rewards are paid
on transitions that enter `ret`; consequently this is not the final
utility-preserving compiler used for solution-concept transport.
-/
noncomputable def controlFlowFOSG (g : WFProgram P L) (hctx : WFCtx g.Γ) :
    GameTheory.FOSG P (CheckedWorld g hctx)
      (fun who : P => Action (P := P) L who)
      (fun _who : P => Unit)
      Unit where
  init := CheckedWorld.initial g hctx
  active := checkedActive
  availableActions := checkedAvailableActions
  terminal := checkedTerminal
  transition := checkedTransition
  reward := rewardOnEnteringRet
  privObs := fun _ _ _ _ => ()
  pubObs := fun _ _ _ => ()
  terminal_active_eq_empty := by
    intro w hterm
    exact checked_terminal_active_eq_empty hterm
  terminal_no_legal := by
    intro w a hterm
    exact checked_terminal_no_legal hterm
  nonterminal_exists_legal := by
    intro w hterm
    exact checked_nonterminal_exists_legal hterm

/-! ## Observation-preserving target

`controlFlowFOSG` is useful for the transition/availability core, but its
`Unit` observations intentionally discard information. The definitions below
are the bridge target for strategy transport: every transition emits the next
public protocol state and the next player-local view. This remains a
control-flow bridge, not a completed utility-preserving semantic compiler.
-/

/-- Public observation after a Vegas/FOSG transition: the current public
program cursor together with the public environment. The cursor is public
control-flow metadata and is needed to project a fixed Vegas strategy profile
to the current continuation. -/
structure PublicObs (g : WFProgram P L) (hctx : WFCtx g.Γ) where
  Γ : VCtx P L
  prog : VegasCore P L Γ
  suffix : ProgramSuffix g.prog prog
  env : VEnv L (pubVCtx Γ)

/-- Private observation after a Vegas/FOSG transition: the observing player's
current view environment. -/
structure PrivateObs (P : Type) [DecidableEq P] (L : IExpr) (who : P) where
  Γ : VCtx P L
  env : VEnv L (viewVCtx who Γ)

def publicObsOfWorld {g : WFProgram P L} {hctx : WFCtx g.Γ}
    (w : CheckedWorld g hctx) : PublicObs g hctx where
  Γ := w.Γ
  prog := w.prog
  suffix := w.suffix
  env := VEnv.toPub w.env

def privateObsOfWorld {g : WFProgram P L} {hctx : WFCtx g.Γ}
    (who : P) (w : CheckedWorld g hctx) : PrivateObs P L who where
  Γ := w.Γ
  env := VEnv.toView who w.env

/-- The private observation's stored structured view is exactly the
strategy-facing erased view after erasure. -/
theorem privateObsOfWorld_eraseEnv
    {g : WFProgram P L} {hctx : WFCtx g.Γ}
    (who : P) (w : CheckedWorld g hctx) :
    VEnv.eraseEnv (privateObsOfWorld who w).env =
      projectViewEnv who (VEnv.eraseEnv w.env) := by
  exact (projectViewEnv_eraseEnv_eq_toView (who := who) w.wctx w.env).symm

/-- A FOSG compiler target that preserves the public protocol location and
each player's local Vegas view at every step.

This is the object that should be used for the future strategy/equilibrium
transport work. The remaining work is not to invent a game model, but to prove
that these observation histories determine exactly the same view environments
that Vegas strategies consume.
-/
noncomputable def observedControlFlowFOSG (g : WFProgram P L) (hctx : WFCtx g.Γ) :
    GameTheory.FOSG P (CheckedWorld g hctx)
      (fun who : P => Action (P := P) L who)
      (fun who : P => PrivateObs P L who)
      (PublicObs g hctx) where
  init := CheckedWorld.initial g hctx
  active := checkedActive
  availableActions := checkedAvailableActions
  terminal := checkedTerminal
  transition := checkedTransition
  reward := rewardOnEnteringRet
  privObs := fun who _ _ w' => privateObsOfWorld who w'
  pubObs := fun _ _ w' => publicObsOfWorld w'
  terminal_active_eq_empty := by
    intro w hterm
    exact checked_terminal_active_eq_empty hterm
  terminal_no_legal := by
    intro w a hterm
    exact checked_terminal_no_legal hterm
  nonterminal_exists_legal := by
    intro w hterm
    exact checked_nonterminal_exists_legal hterm

namespace Observed

/-- Last element of a list, as an `Option`. Kept local to avoid depending on
which `List.getLast?` lemmas are imported. -/
def last? {α : Type} : List α → Option α
  | [] => none
  | [x] => some x
  | _ :: xs => last? xs

@[simp] theorem last?_append_singleton {α : Type} (xs : List α) (x : α) :
    last? (xs ++ [x]) = some x := by
  induction xs with
  | nil => rfl
  | cons y ys ih =>
      cases ys with
      | nil => rfl
      | cons z zs =>
          simpa [last?] using ih

/-- Observation events extracted from an observed FOSG information state. -/
noncomputable def observationEvents
    (g : WFProgram P L) (hctx : WFCtx g.Γ) (who : P)
    (s : (observedControlFlowFOSG g hctx).InfoState who) :
    List (PrivateObs P L who × PublicObs g hctx) :=
  s.filterMap
    (GameTheory.FOSG.PlayerEvent.observationPart
      (G := observedControlFlowFOSG g hctx) (i := who))

/-- Latest private/public observation in an observed FOSG information state. -/
noncomputable def latestObservation?
    (g : WFProgram P L) (hctx : WFCtx g.Γ) (who : P)
    (s : (observedControlFlowFOSG g hctx).InfoState who) :
    Option (PrivateObs P L who × PublicObs g hctx) :=
  last? (observationEvents g hctx who s)

noncomputable def latestPrivateObs?
    (g : WFProgram P L) (hctx : WFCtx g.Γ) (who : P)
    (s : (observedControlFlowFOSG g hctx).InfoState who) :
    Option (PrivateObs P L who) :=
  (latestObservation? g hctx who s).map Prod.fst

noncomputable def latestPublicObs?
    (g : WFProgram P L) (hctx : WFCtx g.Γ) (who : P)
    (s : (observedControlFlowFOSG g hctx).InfoState who) :
    Option (PublicObs g hctx) :=
  (latestObservation? g hctx who s).map Prod.snd

@[simp] theorem observationEvents_nil (g : WFProgram P L) (hctx : WFCtx g.Γ) (who : P) :
    observationEvents g hctx who [] = [] := rfl

@[simp] theorem latestObservation?_nil (g : WFProgram P L) (hctx : WFCtx g.Γ) (who : P) :
    latestObservation? g hctx who [] = none := rfl

theorem latestObservation?_append_obs
    (g : WFProgram P L) (hctx : WFCtx g.Γ) (who : P)
    (s : (observedControlFlowFOSG g hctx).InfoState who)
    (priv : PrivateObs P L who) (pub : PublicObs g hctx) :
    latestObservation? g hctx who
      (s ++ [GameTheory.FOSG.PlayerEvent.obs priv pub]) = some (priv, pub) := by
  simp [latestObservation?, observationEvents]

theorem latestObservation?_append_act_obs
    (g : WFProgram P L) (hctx : WFCtx g.Γ) (who : P)
    (s : (observedControlFlowFOSG g hctx).InfoState who)
    (a : Action (P := P) L who)
    (priv : PrivateObs P L who) (pub : PublicObs g hctx) :
    latestObservation? g hctx who
      (s ++ [GameTheory.FOSG.PlayerEvent.act a,
        GameTheory.FOSG.PlayerEvent.obs priv pub]) = some (priv, pub) := by
  simp [latestObservation?, observationEvents]

/-- Extending an observed FOSG history records the destination world's Vegas
view/public state as the latest information-state observation. -/
theorem latestObservation?_history_snoc
    (g : WFProgram P L) (hctx : WFCtx g.Γ) (who : P)
    (h : (observedControlFlowFOSG g hctx).History)
    (a : (observedControlFlowFOSG g hctx).LegalAction h.lastState)
    (dst : CheckedWorld g hctx)
    (support : (observedControlFlowFOSG g hctx).transition h.lastState a dst ≠ 0) :
    latestObservation? g hctx who ((h.snoc a dst support).playerView who) =
      some (privateObsOfWorld who dst, publicObsOfWorld dst) := by
  rw [GameTheory.FOSG.History.playerView_snoc]
  let e : (observedControlFlowFOSG g hctx).Step :=
    { src := h.lastState, act := a, dst := dst, support := support }
  change latestObservation? g hctx who (h.playerView who ++ e.playerView who) =
    some (privateObsOfWorld who dst, publicObsOfWorld dst)
  cases hact : e.ownAction? who with
  | none =>
      rw [GameTheory.FOSG.Step.playerView_of_none e who hact]
      simpa [e, observedControlFlowFOSG] using
        latestObservation?_append_obs g hctx who (h.playerView who)
          (privateObsOfWorld who dst) (publicObsOfWorld dst)
  | some ai =>
      rw [GameTheory.FOSG.Step.playerView_of_some e who hact]
      simpa [e, observedControlFlowFOSG] using
        latestObservation?_append_act_obs g hctx who (h.playerView who) ai
          (privateObsOfWorld who dst) (publicObsOfWorld dst)

/-! ## Behavioral profile candidate

The following definitions build a raw FOSG behavioral profile from a legal Vegas
behavioral profile. They are deliberately named `candidate`: the legal-support
proof is the next obligation, and only after that proof should this be exposed
as a strategy transport.
-/

noncomputable def moveAtCursor
    (g : WFProgram P L) (_hctx : WFCtx g.Γ)
    (σ : LegalProgramBehavioralProfile g)
    (who : P)
    {Γ : VCtx P L} {p : VegasCore P L Γ}
    (suffix : ProgramSuffix g.prog p)
    (view : ViewEnv (P := P) (L := L) who Γ) :
    PMF (Option (Action (P := P) L who)) :=
  match p with
  | .commit x owner (b := b) R k =>
      if howner : owner = who then
        by
          cases howner
          let σp : ProgramBehavioralProfile (P := P) (L := L) (.commit x who R k) :=
            suffix.behavioralProfile (fun i => (σ i).val)
          let d := ProgramBehavioralStrategy.headKernel (P := P) (L := L) (σp who) view
          have hd :
              FDist.totalWeight d = 1 :=
            ProgramBehavioralStrategy.headKernel_normalized
              (P := P) (L := L) (σp who) view
          exact PMF.map (fun v => some (Sigma.mk b v)) (d.toPMF hd)
      else
        PMF.pure none
  | _ => PMF.pure none

private theorem mem_fdist_support_of_mem_toPMF_support
    {α : Type} [DecidableEq α] {d : FDist α} {h : d.totalWeight = 1} {a : α}
    (ha : a ∈ (d.toPMF h).support) :
    a ∈ d.support := by
  rw [PMF.mem_support_iff, FDist.toPMF_apply] at ha
  rw [Finsupp.mem_support_iff]
  intro hzero
  exact ha (by rw [hzero, NNRat.toNNReal_zero]; rfl)

theorem headKernel_supported_atCursor
    (g : WFProgram P L) (_hctx : WFCtx g.Γ)
    (σ : LegalProgramBehavioralProfile g)
    {Γ : VCtx P L} {x : VarId} {who : P} {b : L.Ty}
    {R : L.Expr ((x, b) :: eraseVCtx Γ) L.bool}
    {k : VegasCore P L ((x, .hidden who b) :: Γ)}
    (suffix : ProgramSuffix g.prog (.commit x who R k))
    (ρ : Env L.Val (eraseVCtx Γ)) :
    FDist.Supported
      (ProgramBehavioralStrategy.headKernel (P := P) (L := L)
        ((suffix.behavioralProfile (fun i => (σ i).val)) who)
        (projectViewEnv (P := P) (L := L) who ρ))
      (fun v => evalGuard (Player := P) (L := L) R v ρ = true) := by
  let raw : ProgramBehavioralProfile (P := P) (L := L) g.prog :=
    fun i => (σ i).val
  have hraw : raw.IsLegal := fun i => (σ i).2
  have hcursor : (suffix.behavioralProfile raw).IsLegal :=
    suffix.behavioralProfile_isLegal hraw
  have hsite := hcursor who
  simp [ProgramBehavioralStrategy.IsLegal] at hsite
  simpa [raw] using hsite.1 ρ

noncomputable def moveAtWorld
    (g : WFProgram P L) (hctx : WFCtx g.Γ)
    (σ : LegalProgramBehavioralProfile g)
    (who : P) (w : CheckedWorld g hctx) :
    PMF (Option (Action (P := P) L who)) :=
  moveAtCursor g hctx σ who w.suffix
    (projectViewEnv who (VEnv.eraseEnv w.env))

theorem moveAtWorld_support_available
    (g : WFProgram P L) (hctx : WFCtx g.Γ)
    (σ : LegalProgramBehavioralProfile g)
    (who : P) (w : CheckedWorld g hctx)
    {oi : Option (Action (P := P) L who)}
    (hoi : oi ∈ (moveAtWorld g hctx σ who w).support) :
    oi ∈ (observedControlFlowFOSG g hctx).availableMovesAtState w who := by
  cases w with
  | mk Γ prog env suffix wctx fresh viewScoped normalized legal =>
      cases prog with
      | ret payoffs =>
          have hoiNone : oi = none := by
            simpa [moveAtWorld, moveAtCursor] using hoi
          subst oi
          simp [GameTheory.FOSG.availableMovesAtState,
            GameTheory.FOSG.locallyLegalAtState, observedControlFlowFOSG,
            checkedActive, CheckedWorld.toWorld, active]
      | letExpr x e k =>
          have hoiNone : oi = none := by
            simpa [moveAtWorld, moveAtCursor] using hoi
          subst oi
          simp [GameTheory.FOSG.availableMovesAtState,
            GameTheory.FOSG.locallyLegalAtState, observedControlFlowFOSG,
            checkedActive, CheckedWorld.toWorld, active]
      | sample x D k =>
          have hoiNone : oi = none := by
            simpa [moveAtWorld, moveAtCursor] using hoi
          subst oi
          simp [GameTheory.FOSG.availableMovesAtState,
            GameTheory.FOSG.locallyLegalAtState, observedControlFlowFOSG,
            checkedActive, CheckedWorld.toWorld, active]
      | reveal y owner x hx k =>
          have hoiNone : oi = none := by
            simpa [moveAtWorld, moveAtCursor] using hoi
          subst oi
          simp [GameTheory.FOSG.availableMovesAtState,
            GameTheory.FOSG.locallyLegalAtState, observedControlFlowFOSG,
            checkedActive, CheckedWorld.toWorld, active]
      | commit x owner R k =>
          by_cases howner : owner = who
          · cases howner
            let d :=
              ProgramBehavioralStrategy.headKernel (P := P) (L := L)
                ((suffix.behavioralProfile (fun i => (σ i).val)) who)
                (projectViewEnv (P := P) (L := L) who (VEnv.eraseEnv env))
            have hd :
                FDist.totalWeight d = 1 :=
              ProgramBehavioralStrategy.headKernel_normalized
                (P := P) (L := L)
                ((suffix.behavioralProfile (fun i => (σ i).val)) who)
                (projectViewEnv (P := P) (L := L) who (VEnv.eraseEnv env))
            have hoi' :
                ∃ v, ¬(d.toPMF hd) v = 0 ∧ some (Sigma.mk _ v) = oi := by
              simpa [moveAtWorld, moveAtCursor, d, hd] using hoi
            rcases hoi' with ⟨v, hvprob, hvo⟩
            rw [← hvo]
            have hv : v ∈ (d.toPMF hd).support := by
              rw [PMF.mem_support_iff]
              simpa [d] using hvprob
            have hvFD : v ∈ d.support :=
              mem_fdist_support_of_mem_toPMF_support (d := d) (h := hd) hv
            have hguard :
                evalGuard (Player := P) (L := L) R v (VEnv.eraseEnv env) = true := by
              exact headKernel_supported_atCursor (P := P) (L := L)
                g hctx σ suffix (VEnv.eraseEnv env) v hvFD
            simp [GameTheory.FOSG.availableMovesAtState,
              GameTheory.FOSG.locallyLegalAtState, observedControlFlowFOSG,
              checkedActive, checkedAvailableActions, CheckedWorld.toWorld,
              active, availableActions, hguard]
          · have hoiNone : oi = none := by
              simpa [moveAtWorld, moveAtCursor, howner] using hoi
            subst oi
            have hnot : who ≠ owner := fun h => howner h.symm
            simp [GameTheory.FOSG.availableMovesAtState,
              GameTheory.FOSG.locallyLegalAtState, observedControlFlowFOSG,
              checkedActive, CheckedWorld.toWorld, active, hnot]

noncomputable def moveAtObservation?
    (g : WFProgram P L) (hctx : WFCtx g.Γ)
    (σ : LegalProgramBehavioralProfile g)
    (who : P)
    (obs : PrivateObs P L who × PublicObs g hctx) :
    PMF (Option (Action (P := P) L who)) := by
  let priv := obs.1
  let pub := obs.2
  by_cases hΓ : priv.Γ = pub.Γ
  · exact moveAtCursor g hctx σ who pub.suffix (hΓ ▸ VEnv.eraseEnv priv.env)
  · exact PMF.pure none

theorem moveAtObservation?_of_world
    (g : WFProgram P L) (hctx : WFCtx g.Γ)
    (σ : LegalProgramBehavioralProfile g)
    (who : P) (w : CheckedWorld g hctx) :
    moveAtObservation? g hctx σ who
      (privateObsOfWorld who w, publicObsOfWorld w) =
      moveAtWorld g hctx σ who w := by
  unfold moveAtObservation? moveAtWorld
  simp only [dite_eq_ite]
  rw [privateObsOfWorld_eraseEnv]
  simp only [publicObsOfWorld]
  simp [privateObsOfWorld]

/-- Raw FOSG behavioral profile induced by a Vegas legal behavioral profile.

This is not yet bundled as a legal FOSG profile; legality is the next theorem.
-/
noncomputable def behavioralProfileCandidate
    (g : WFProgram P L) (hctx : WFCtx g.Γ)
    (σ : LegalProgramBehavioralProfile g) :
    GameTheory.FOSG.BehavioralProfile (observedControlFlowFOSG g hctx) :=
  fun who s =>
    match latestObservation? g hctx who s with
    | none => moveAtWorld g hctx σ who (CheckedWorld.initial g hctx)
    | some obs => moveAtObservation? g hctx σ who obs

theorem behavioralProfileCandidate_support_available_snoc
    (g : WFProgram P L) (hctx : WFCtx g.Γ)
    (σ : LegalProgramBehavioralProfile g)
    (who : P)
    (h : (observedControlFlowFOSG g hctx).History)
    (a : (observedControlFlowFOSG g hctx).LegalAction h.lastState)
    (dst : CheckedWorld g hctx)
    (support : (observedControlFlowFOSG g hctx).transition h.lastState a dst ≠ 0)
    {oi : Option (Action (P := P) L who)}
    (hoi : oi ∈
      (behavioralProfileCandidate g hctx σ who
        ((h.snoc a dst support).playerView who)).support) :
    oi ∈ (observedControlFlowFOSG g hctx).availableMoves
      (h.snoc a dst support) who := by
  rw [behavioralProfileCandidate,
    latestObservation?_history_snoc g hctx who h a dst support] at hoi
  simp only at hoi
  rw [moveAtObservation?_of_world] at hoi
  simpa [GameTheory.FOSG.availableMoves,
    GameTheory.FOSG.availableMovesAtState] using
    moveAtWorld_support_available g hctx σ who dst hoi

theorem behavioralProfileCandidate_support_available_appendStep
    (g : WFProgram P L) (hctx : WFCtx g.Γ)
    (σ : LegalProgramBehavioralProfile g)
    (who : P)
    (h : (observedControlFlowFOSG g hctx).History)
    (e : (observedControlFlowFOSG g hctx).Step)
    (hsrc : e.src = h.lastState)
    {oi : Option (Action (P := P) L who)}
    (hoi : oi ∈
      (behavioralProfileCandidate g hctx σ who
        ((h.appendStep e hsrc).playerView who)).support) :
    oi ∈ (observedControlFlowFOSG g hctx).availableMoves
      (h.appendStep e hsrc) who := by
  cases e with
  | mk src act dst support =>
      cases hsrc
      simpa [GameTheory.FOSG.History.appendStep_eq_snoc] using
        behavioralProfileCandidate_support_available_snoc
          g hctx σ who h act dst support hoi

theorem behavioralProfileCandidate_support_available
    (g : WFProgram P L) (hctx : WFCtx g.Γ)
    (σ : LegalProgramBehavioralProfile g)
    (who : P)
    (h : (observedControlFlowFOSG g hctx).History)
    {oi : Option (Action (P := P) L who)}
    (hoi : oi ∈
      (behavioralProfileCandidate g hctx σ who (h.playerView who)).support) :
    oi ∈ (observedControlFlowFOSG g hctx).availableMoves h who := by
  let G := observedControlFlowFOSG g hctx
  cases h with
  | mk steps chain =>
      induction steps using List.reverseRecOn with
      | nil =>
          have hoi' : oi ∈
              (moveAtWorld g hctx σ who (CheckedWorld.initial g hctx)).support := by
            simpa [G, behavioralProfileCandidate, GameTheory.FOSG.History.playerView,
              GameTheory.FOSG.History.playerViewFrom, latestObservation?,
              observationEvents, last?] using hoi
          simpa [G, GameTheory.FOSG.availableMoves, GameTheory.FOSG.availableMovesAtState,
            GameTheory.FOSG.History.lastState, GameTheory.FOSG.lastStateFrom] using
            moveAtWorld_support_available g hctx σ who (CheckedWorld.initial g hctx) hoi'
      | append_singleton steps e ih =>
          let hprefix : G.History :=
            { steps := steps
              chain := GameTheory.FOSG.StepChainFrom.left
                (G := G) (es₁ := steps) (es₂ := [e]) chain }
          have hright :
              G.StepChainFrom (G.lastStateFrom G.init steps) [e] :=
            GameTheory.FOSG.StepChainFrom.right
              (G := G) (es₁ := steps) (es₂ := [e]) chain
          have hsrc : e.src = hprefix.lastState := by
            simpa [hprefix, GameTheory.FOSG.History.lastState,
              GameTheory.FOSG.StepChainFrom] using hright.1
          let hfull : G.History := hprefix.appendStep e hsrc
          have hEq : ({ steps := steps ++ [e], chain := chain } : G.History) = hfull := by
            ext
            rfl
          rw [hEq] at hoi ⊢
          exact behavioralProfileCandidate_support_available_appendStep
            g hctx σ who hprefix e hsrc hoi

/-- Transport a Vegas guard-legal behavioral profile to a legal behavioral
profile of the observed control-flow FOSG.

The target name is intentionally specific: this is not yet the final
utility-preserving Vegas-to-FOSG compiler, only the observed control-flow FOSG
defined in this file.
-/
noncomputable def toObservedControlFlowLegalBehavioralProfile
    (g : WFProgram P L) (hctx : WFCtx g.Γ)
    (σ : LegalProgramBehavioralProfile g) :
    (observedControlFlowFOSG g hctx).LegalBehavioralProfile :=
  fun who =>
    ⟨behavioralProfileCandidate g hctx σ who, by
      intro h oi hoi
      exact behavioralProfileCandidate_support_available g hctx σ who h hoi⟩

@[simp] theorem toObservedControlFlowLegalBehavioralProfile_apply
    (g : WFProgram P L) (hctx : WFCtx g.Γ)
    (σ : LegalProgramBehavioralProfile g) (who : P) :
    ((toObservedControlFlowLegalBehavioralProfile g hctx σ who).1) =
      behavioralProfileCandidate g hctx σ who := rfl

@[simp] theorem behavioralProfileCandidate_nil
    (g : WFProgram P L) (hctx : WFCtx g.Γ)
    (σ : LegalProgramBehavioralProfile g) (who : P) :
    behavioralProfileCandidate g hctx σ who
      ((GameTheory.FOSG.History.nil (observedControlFlowFOSG g hctx)).playerView who) =
      moveAtWorld g hctx σ who (CheckedWorld.initial g hctx) := by
  simp [behavioralProfileCandidate, latestObservation?, observationEvents, last?]

@[simp] theorem behavioralProfileCandidate_snoc
    (g : WFProgram P L) (hctx : WFCtx g.Γ)
    (σ : LegalProgramBehavioralProfile g)
    (who : P)
    (h : (observedControlFlowFOSG g hctx).History)
    (a : (observedControlFlowFOSG g hctx).LegalAction h.lastState)
    (dst : CheckedWorld g hctx)
    (support : (observedControlFlowFOSG g hctx).transition h.lastState a dst ≠ 0) :
    behavioralProfileCandidate g hctx σ who
      ((h.snoc a dst support).playerView who) =
      moveAtWorld g hctx σ who dst := by
  rw [behavioralProfileCandidate,
    latestObservation?_history_snoc g hctx who h a dst support]
  simp [moveAtObservation?_of_world]

end Observed

end FOSGBridge
end Vegas

import GameTheory.Languages.FOSG.Information
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
structure CheckedWorld (P : Type) [DecidableEq P] (L : IExpr) where
  Γ : VCtx P L
  prog : VegasCore P L Γ
  env : VEnv L Γ
  wctx : WFCtx Γ
  fresh : FreshBindings prog
  viewScoped : ViewScoped prog
  normalized : NormalizedDists prog
  legal : Legal prog

namespace CheckedWorld

def toWorld (w : CheckedWorld P L) : World P L where
  Γ := w.Γ
  prog := w.prog
  env := w.env

def initial (g : WFProgram P L) (hctx : WFCtx g.Γ) : CheckedWorld P L where
  Γ := g.Γ
  prog := g.prog
  env := g.env
  wctx := hctx
  fresh := g.wf.1
  viewScoped := g.wf.2.2
  normalized := g.normalized
  legal := g.legal

end CheckedWorld

def checkedTerminal (w : CheckedWorld P L) : Prop :=
  terminal w.toWorld

def checkedActive (w : CheckedWorld P L) : Finset P :=
  active w.toWorld

def checkedAvailableActions
    (w : CheckedWorld P L) (who : P) : Set (Action (P := P) L who) :=
  availableActions w.toWorld who

abbrev CheckedJointActionLegal
    (w : CheckedWorld P L) (a : JointAction P L) : Prop :=
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

theorem checked_terminal_active_eq_empty {w : CheckedWorld P L} :
    checkedTerminal w → checkedActive w = ∅ :=
  terminal_active_eq_empty

theorem checked_terminal_no_legal {w : CheckedWorld P L} {a : JointAction P L} :
    checkedTerminal w → ¬ CheckedJointActionLegal w a := by
  intro hterm hlegal
  exact hlegal.1 hterm

theorem checked_nonterminal_exists_legal {w : CheckedWorld P L} :
    ¬ checkedTerminal w →
      ∃ a : JointAction P L, CheckedJointActionLegal w a := by
  intro hterm
  exact exists_jointActionLegal_of_legal w.toWorld w.legal hterm

/-- The one-step transition kernel of the checked-world FOSG skeleton. -/
noncomputable def checkedTransition
    (w : CheckedWorld P L)
    (a : {a : JointAction P L // CheckedJointActionLegal w a}) :
    PMF (CheckedWorld P L) := by
  cases w with
  | mk Γ prog env wctx fresh viewScoped normalized legal =>
      cases prog with
      | ret payoffs =>
          exact False.elim (a.2.1 (by simp [checkedTerminal, CheckedWorld.toWorld, terminal]))
      | letExpr x e k =>
          exact PMF.pure
            { Γ := _
              prog := k
              env := VEnv.cons (Player := P) (L := L) (x := x) (τ := .pub _)
                (L.eval e (VEnv.erasePubEnv env)) env
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
              wctx := WFCtx.cons fresh.1 wctx
              fresh := fresh.2
              viewScoped := viewScoped
              normalized := normalized
              legal := legal }

def rewardOnEnteringRet
    (_w : CheckedWorld P L)
    (_a : {a : JointAction P L // CheckedJointActionLegal _w a})
    (w' : CheckedWorld P L) (who : P) : ℝ :=
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
    GameTheory.FOSG P (CheckedWorld P L)
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

/-- Public observation after a Vegas/FOSG transition: the current program
location together with the public environment. -/
structure PublicObs (P : Type) [DecidableEq P] (L : IExpr) where
  Γ : VCtx P L
  prog : VegasCore P L Γ
  env : VEnv L (pubVCtx Γ)

/-- Private observation after a Vegas/FOSG transition: the observing player's
current view environment. -/
structure PrivateObs (P : Type) [DecidableEq P] (L : IExpr) (who : P) where
  Γ : VCtx P L
  env : VEnv L (viewVCtx who Γ)

def publicObsOfWorld (w : CheckedWorld P L) : PublicObs P L where
  Γ := w.Γ
  prog := w.prog
  env := VEnv.toPub w.env

def privateObsOfWorld (who : P) (w : CheckedWorld P L) : PrivateObs P L who where
  Γ := w.Γ
  env := VEnv.toView who w.env

/-- The private observation's stored structured view is exactly the
strategy-facing erased view after erasure. -/
theorem privateObsOfWorld_eraseEnv
    (who : P) (w : CheckedWorld P L) :
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
    GameTheory.FOSG P (CheckedWorld P L)
      (fun who : P => Action (P := P) L who)
      (fun who : P => PrivateObs P L who)
      (PublicObs P L) where
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
    List (PrivateObs P L who × PublicObs P L) :=
  s.filterMap
    (GameTheory.FOSG.PlayerEvent.observationPart
      (G := observedControlFlowFOSG g hctx) (i := who))

/-- Latest private/public observation in an observed FOSG information state. -/
noncomputable def latestObservation?
    (g : WFProgram P L) (hctx : WFCtx g.Γ) (who : P)
    (s : (observedControlFlowFOSG g hctx).InfoState who) :
    Option (PrivateObs P L who × PublicObs P L) :=
  last? (observationEvents g hctx who s)

noncomputable def latestPrivateObs?
    (g : WFProgram P L) (hctx : WFCtx g.Γ) (who : P)
    (s : (observedControlFlowFOSG g hctx).InfoState who) :
    Option (PrivateObs P L who) :=
  (latestObservation? g hctx who s).map Prod.fst

noncomputable def latestPublicObs?
    (g : WFProgram P L) (hctx : WFCtx g.Γ) (who : P)
    (s : (observedControlFlowFOSG g hctx).InfoState who) :
    Option (PublicObs P L) :=
  (latestObservation? g hctx who s).map Prod.snd

@[simp] theorem observationEvents_nil (g : WFProgram P L) (hctx : WFCtx g.Γ) (who : P) :
    observationEvents g hctx who [] = [] := rfl

@[simp] theorem latestObservation?_nil (g : WFProgram P L) (hctx : WFCtx g.Γ) (who : P) :
    latestObservation? g hctx who [] = none := rfl

theorem latestObservation?_append_obs
    (g : WFProgram P L) (hctx : WFCtx g.Γ) (who : P)
    (s : (observedControlFlowFOSG g hctx).InfoState who)
    (priv : PrivateObs P L who) (pub : PublicObs P L) :
    latestObservation? g hctx who
      (s ++ [GameTheory.FOSG.PlayerEvent.obs priv pub]) = some (priv, pub) := by
  simp [latestObservation?, observationEvents]

theorem latestObservation?_append_act_obs
    (g : WFProgram P L) (hctx : WFCtx g.Γ) (who : P)
    (s : (observedControlFlowFOSG g hctx).InfoState who)
    (a : Action (P := P) L who)
    (priv : PrivateObs P L who) (pub : PublicObs P L) :
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
    (dst : CheckedWorld P L)
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

end Observed

end FOSGBridge
end Vegas

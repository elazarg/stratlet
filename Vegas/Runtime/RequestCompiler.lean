/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import Vegas.Runtime.ActionWindow

/-! # Whole-protocol compilation to bounded request windows

Each source decision is implemented by a request window. Timeout resolves to
the source's designated action; accepted requests resolve to source menu
actions. Controllers retain all their own request transcripts across windows.
Perfect recall permits a uniform replay of that private memory from source
information. The compiler neither chooses quit payoffs nor adds quit outcomes.

This finite runtime keeps request attempts private, freezes source observations
during a window, and guarantees delivery and deadline progress. Public request
side channels and transaction costs are not part of this target semantics.
-/

noncomputable section

namespace Vegas.Runtime.RequestCompiler

open GameTheory GameTheory.Protocol GameTheory.Math.Probability

variable {Player : Type}
variable {E : ExecutionProtocol Player} (M : InformationModel E)

/-- A source-level timeout action and a request representation at every menu.
The timeout action must already be legal in the source. Its consequences are
entirely determined by source execution and utility. -/
structure Interface (M : InformationModel E) (Request : Player → Type) where
  gate : (who : Player) → ActionWindow.Gate (M.InfoState who) (M.Choice who) (Request who)
  slots : (who : Player) → M.InfoState who → Nat

variable {Request : Player → Type} (interface : Interface M Request)

abbrev Policy (who : Player) := ActionWindow.Policy (M.InfoState who) (Request who)
abbrev Memory (who : Player) := ActionWindow.Memory (M.InfoState who) (Request who)
abbrev State := E.History × ((who : Player) → Memory M (Request := Request) who)

def enabled (who : Player) (info : M.InfoState who) : Prop :=
  ∃ choice : M.Choice who info, choice.1 ≠ none

include interface in
theorem enabled_iff (who : Player) (history : E.History) :
    enabled M who (M.infoOf who history.trace) ↔ E.active history.state who := by
  constructor
  · rintro ⟨choice, hsome⟩
    have hlegal := (M.menu_adequate who history.trace choice.1).mp choice.2
    cases hchoice : choice.1 with
    | none => exact False.elim (hsome hchoice)
    | some action =>
        rw [hchoice] at hlegal
        exact hlegal.1
  · intro hactive
    let choice := interface.gate who |>.timeoutAction (M.infoOf who history.trace)
    refine ⟨choice, ?_⟩
    intro hnone
    have hlegal := (M.menu_adequate who history.trace choice.1).mp choice.2
    simp only [LegalOption, hnone] at hlegal
    exact hlegal hactive

open Classical in
def past (who : Player) (info : M.InfoState who) : List (M.InfoState who) :=
  if h : ∃ history : E.History, M.infoOf who history.trace = info then
    M.actedAt who (Classical.choose h).trace
  else []

theorem past_eq (hrecall : M.PerfectRecall) (who : Player) (history : E.History) :
    past M who (M.infoOf who history.trace) = M.actedAt who history.trace := by
  unfold past
  rw [dif_pos ⟨history, rfl⟩]
  exact M.actedAt_eq_of_perfectRecall hrecall who _ _
    (Classical.choose_spec (show ∃ h : E.History,
      M.infoOf who h.trace = M.infoOf who history.trace from ⟨history, rfl⟩))

open Classical in
def resolve (who : Player) (policy : Policy M (Request := Request) who)
    (info : M.InfoState who) (memory : Memory M (Request := Request) who) :
    M.Choice who info × ActionWindow.Attempts (Request who) :=
  if enabled M who info then
    ActionWindow.execute (interface.gate who) policy info memory (interface.slots who info + 1) []
  else ((interface.gate who).timeoutAction info, [])

open Classical in
def record (who : Player) (policy : Policy M (Request := Request) who)
    (info : M.InfoState who) (memory : Memory M (Request := Request) who) :
    Memory M (Request := Request) who :=
  if enabled M who info then (info, (resolve M interface who policy info memory).2) :: memory
  else memory

def replay (who : Player) (policy : Policy M (Request := Request) who) :
    List (M.InfoState who) → Memory M (Request := Request) who
  | [] => []
  | info :: previous => record M interface who policy info (replay who policy previous)

def backtranslate (who : Player) (policy : Policy M (Request := Request) who) : M.Policy who :=
  fun info => (resolve M interface who policy info
    (replay M interface who policy (past M who info))).1

def compile (who : Player) (policy : M.Policy who) : Policy M (Request := Request) who :=
  ActionWindow.compile (interface.gate who) policy

@[simp] theorem resolve_compile (who : Player) (policy : M.Policy who)
    (info : M.InfoState who) (memory : Memory M (Request := Request) who) :
    (resolve M interface who (compile M interface who policy) info memory).1 = policy info := by
  unfold resolve compile
  split_ifs with henabled
  · simp only [ActionWindow.execute_compile]
  · apply Subtype.ext
    have hnone (choice : M.Choice who info) : choice.1 = none := by
      by_contra h
      exact henabled ⟨choice, h⟩
    exact (hnone _).trans (hnone _).symm

@[simp] theorem backtranslate_compile (who : Player) (policy : M.Policy who) :
    backtranslate M interface who (compile M interface who policy) = policy := by
  funext info
  exact resolve_compile M interface who policy info _

@[simp] theorem backtranslate_silence (who : Player) :
    backtranslate M interface who (fun _ _ _ => none) = (interface.gate who).timeoutAction := by
  funext info
  unfold backtranslate resolve
  split_ifs
  · exact ActionWindow.silence_timeout _ _ _ _ _
  · rfl

@[simp] theorem backtranslate_compile_map (who : Player) (policy : FinDist (M.Policy who)) :
    (policy.map (compile M interface who)).map (backtranslate M interface who) = policy := by
  rw [FinDist.map_comp,
    show backtranslate M interface who ∘ compile M interface who = id from
      funext (backtranslate_compile M interface who), FinDist.map_id]

def choices (profile : (who : Player) → Policy M (Request := Request) who)
    (state : State M (Request := Request)) (who : Player) :
    M.Choice who (M.infoOf who state.1.trace) :=
  (resolve M interface who (profile who) (M.infoOf who state.1.trace) (state.2 who)).1

def command (profile : (who : Player) → Policy M (Request := Request) who)
    (state : State M (Request := Request)) (hterm : ¬ E.terminal state.1.state) :
    {joint // E.Legal state.1.state joint} :=
  ⟨fun who => (choices M interface profile state who).1,
    E.legal_of_legalOption hterm (fun who =>
      (M.menu_adequate who state.1.trace _).mp (choices M interface profile state who).2)⟩

def nextMemory (profile : (who : Player) → Policy M (Request := Request) who)
    (state : State M (Request := Request)) (who : Player) : Memory M (Request := Request) who :=
  record M interface who (profile who) (M.infoOf who state.1.trace) (state.2 who)

open Classical in
def run (profile : (who : Player) → Policy M (Request := Request) who) :
    Nat → State M (Request := Request) → FinDist (State M (Request := Request))
  | 0, state => FinDist.pure state
  | fuel + 1, state =>
      if hterm : E.terminal state.1.state then FinDist.pure state
      else (E.step state.1.state (command M interface profile state hterm)).bindOnSupport
        fun _ realized => run profile fuel
          (state.1.extend (command M interface profile state hterm).2 realized,
            nextMemory M interface profile state)

def Compatible (profile : (who : Player) → Policy M (Request := Request) who)
    (state : State M (Request := Request)) : Prop :=
  ∀ who, state.2 who = replay M interface who (profile who) (M.actedAt who state.1.trace)

theorem command_eq (hrecall : M.PerfectRecall)
    (profile : (who : Player) → Policy M (Request := Request) who)
    (state : State M (Request := Request)) (hstate : Compatible M interface profile state)
    (hterm : ¬ E.terminal state.1.state) :
    command M interface profile state hterm =
      M.historyChooser (fun who => backtranslate M interface who (profile who)) state.1 hterm := by
  apply Subtype.ext
  funext who
  simp only [command, choices, InformationModel.historyChooser, InformationModel.jointAt,
    InformationModel.Policy.act, backtranslate, past_eq M hrecall, hstate who]

theorem compatible_next
    (profile : (who : Player) → Policy M (Request := Request) who)
    (state : State M (Request := Request)) (hstate : Compatible M interface profile state)
    (hterm : ¬ E.terminal state.1.state)
    {next : E.State}
    (realized : next ∈ (E.step state.1.state (command M interface profile state hterm)).support) :
    Compatible M interface profile
      (state.1.extend (command M interface profile state hterm).2 realized,
        nextMemory M interface profile state) := by
  intro who
  have hlegal := E.legalOption_of_legal (command M interface profile state hterm).2 who
  change nextMemory M interface profile state who = _
  simp only [ExecutionProtocol.History.extend, InfoSignals.actedAt]
  cases hchoice : (command M interface profile state hterm).1 who with
  | none =>
      have hinactive : ¬ E.active state.1.state who := by
        simpa only [LegalOption, hchoice] using hlegal
      have hdisabled := (enabled_iff M interface who state.1).not.mpr hinactive
      simp only [nextMemory, record, if_neg hdisabled, hstate who]
  | some action =>
      simp only [nextMemory, replay, hstate who]

theorem run_law (hrecall : M.PerfectRecall)
    (profile : (who : Player) → Policy M (Request := Request) who)
    (fuel : Nat) (state : State M (Request := Request))
    (hstate : Compatible M interface profile state) :
    (run M interface profile fuel state).map Prod.fst =
      M.runFrom (fun who => backtranslate M interface who (profile who)) fuel state.1 := by
  induction fuel generalizing state with
  | zero => exact FinDist.map_pure _ _
  | succ fuel ih =>
      change _ = E.runHistoryFor _ _ _
      by_cases hterm : E.terminal state.1.state
      · rw [run, dif_pos hterm, FinDist.map_pure,
          ExecutionProtocol.runHistoryFor_of_terminal _ _ hterm]
      · rw [run, dif_neg hterm, FinDist.map_bindOnSupport,
          ExecutionProtocol.runHistoryFor_succ_of_not_terminal _ _ hterm,
          ← command_eq M interface hrecall profile state hstate hterm]
        exact FinDist.bindOnSupport_congr fun _ realized =>
          ih _ (compatible_next M interface profile state hstate hterm realized)

def initial : State M (Request := Request) := (E.initHistory, fun _ => [])

theorem initial_compatible (profile : (who : Player) → Policy M (Request := Request) who) :
    Compatible M interface profile (initial M) := by intro who; rfl

def sourceGame (horizon : Nat) (utility : E.History → Player → ℝ) : UtilityGame Player where
  form := M.toGameForm horizon
  utility := utility

def targetGame (horizon : Nat) (utility : E.History → Player → ℝ) : UtilityGame Player where
  form := ⟨⟨Policy M (Request := Request), State M (Request := Request)⟩,
    fun profile => run M interface profile horizon (initial M)⟩
  utility state := utility state.1

/-- Exact source-history laws for every controller profile, not only for
unilateral deviations at compiled equilibria. -/
theorem play_law (hrecall : M.PerfectRecall) (horizon : Nat)
    (utility : E.History → Player → ℝ)
    (profile : (who : Player) → Policy M (Request := Request) who) :
    ((targetGame M interface horizon utility).form.play profile).map Prod.fst =
      (sourceGame M horizon utility).form.play
        (fun who => backtranslate M interface who (profile who)) :=
  run_law M interface hrecall profile horizon _ (initial_compatible M interface profile)

/-- Persistent silence realizes the source-designated timeout policy at every
decision. This is a source execution, not an extra runtime abort outcome. -/
theorem silence_law (hrecall : M.PerfectRecall) (horizon : Nat)
    (utility : E.History → Player → ℝ) :
    ((targetGame M interface horizon utility).form.play
      (fun _ _ _ _ => none)).map Prod.fst =
    (sourceGame M horizon utility).form.play (fun who => (interface.gate who).timeoutAction) := by
  rw [play_law M interface hrecall]
  simp only [backtranslate_silence]

section Adequacy

variable [DecidableEq Player]

def adequacy (hrecall : M.PerfectRecall) (horizon : Nat)
    (utility : E.History → Player → ℝ) :
    DeviationAdequacy (sourceGame M horizon utility) (targetGame M interface horizon utility) where
  compileStrategy := compile M interface
  backtranslateStrategy := backtranslate M interface
  decodeOutcome := Prod.fst
  utility_eq := rfl
  compiled_considered _ _ := trivial
  honest_law profile := by
    rw [play_law M interface hrecall]
    simp only [backtranslate_compile]
  deviation_law profile who replacement _ := by
    rw [play_law M interface hrecall]
    congr 1
    funext player
    by_cases heq : player = who
    · subst player; simp
    · simp [Profile.update, heq]

end Adequacy

section Mixed

variable [Fintype Player]

/-- Random seeds may correlate a player's choices across all its windows.
Each player's seed is private and sampled independently of the other players. -/
theorem mixed_play_law (hrecall : M.PerfectRecall) (horizon : Nat)
    (utility : E.History → Player → ℝ)
    (profile : (who : Player) → FinDist (Policy M (Request := Request) who)) :
    ((targetGame M interface horizon utility).mixed.form.play profile).map Prod.fst =
      (sourceGame M horizon utility).mixed.form.play
        (fun who => (profile who).map (backtranslate M interface who)) := by
  simp only [FinDist.map_bind,
    FinDist.pi_map, FinDist.bind_map]
  exact FinDist.bind_congr fun profile _ => play_law M interface hrecall horizon utility profile

variable [DecidableEq Player]

/-- Whole-protocol adequacy with finite private randomization over arbitrary
history-dependent controllers. No incentive assumption on quitting is used. -/
def mixedAdequacy (hrecall : M.PerfectRecall) (horizon : Nat)
    (utility : E.History → Player → ℝ) :
    DeviationAdequacy (sourceGame M horizon utility).mixed
      (targetGame M interface horizon utility).mixed where
  compileStrategy who strategy := strategy.map (compile M interface who)
  backtranslateStrategy who strategy := strategy.map (backtranslate M interface who)
  decodeOutcome := Prod.fst
  utility_eq := rfl
  compiled_considered _ _ := trivial
  honest_law profile := by
    rw [mixed_play_law M interface hrecall]
    exact congrArg (sourceGame M horizon utility).mixed.form.play
      (funext fun who => backtranslate_compile_map M interface who (profile who))
  deviation_law profile who replacement _ := by
    rw [mixed_play_law M interface hrecall]
    congr 1
    funext player
    by_cases heq : player = who
    · subst player; simp
    · simp only [Profile.update_of_ne _ _ heq]
      exact backtranslate_compile_map M interface player (profile player)

end Mixed

open Classical in
/-- A canonical request validator. Silence and rejected packets use the
designated source action; valid packets implement exactly the source menu.
`timeoutAction` is supplied by the source, not inferred from payoffs. -/
def menuInterface (timeoutAction : (who : Player) → M.Policy who)
    (slots : (who : Player) → M.InfoState who → Nat) :
    Interface M (fun who => Option (E.Action who)) where
  gate who := {
    timeoutAction := timeoutAction who
    decode := fun info request =>
      if h : request ∈ M.menu who info then some ⟨request, h⟩ else none
    encode := fun _ choice => choice.1
    decode_encode := by intros; simp }
  slots := slots

end Vegas.Runtime.RequestCompiler

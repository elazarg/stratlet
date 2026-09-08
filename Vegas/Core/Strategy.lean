/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import Vegas.Core.SmallStep
import Vegas.Core.Obligations
import GameTheory.Core.Form

/-!
# Written-order source strategies

This module gives `VegasCore` a direct sequential strategic denotation. It is
independent of event graphs, compilation, machines, and runtime scheduling.
Each decision site is identified by its structural occurrence in the source
AST. A player's policy sees exactly that player's current source view.
-/

noncomputable section

namespace Vegas

open GameTheory Math.Probability

variable {P : Type} [DecidableEq P] {L : IExpr}

/-- A structurally identified commitment belonging to `who` in `prog`. -/
inductive SourceDecisionSite (who : P) :
    {Γ : VCtx P L} → VegasCore P L Γ →
      (Δ : VCtx P L) → (x : VarId) → (b : L.Ty) →
      L.Expr ((x, b) :: eraseVCtx (viewVCtx who Δ)) L.bool → Type where
  | here {Γ x b}
      (guard : L.Expr ((x, b) :: eraseVCtx (viewVCtx who Γ)) L.bool)
      (tail : VegasCore P L ((x, .sealed who b) :: Γ)) :
      SourceDecisionSite who (.commit x who guard tail) Γ x b guard
  | sample {Γ : VCtx P L} {sampleName : VarId} {sampleTy : L.Ty}
      {dist : L.DistExpr (erasePubVCtx Γ) sampleTy}
      {tail : VegasCore P L ((sampleName, .pub sampleTy) :: Γ)} {Δ x b guard}
      (site : SourceDecisionSite who tail Δ x b guard) :
      SourceDecisionSite who (.sample sampleName (b := sampleTy) dist tail) Δ x b guard
  | commit {Γ : VCtx P L} {commitName : VarId} {actor : P} {commitTy : L.Ty}
      {commitGuard : L.Expr ((commitName, commitTy) :: eraseVCtx (viewVCtx actor Γ)) L.bool}
      {tail : VegasCore P L ((commitName, .sealed actor commitTy) :: Γ)} {Δ x b guard}
      (site : SourceDecisionSite who tail Δ x b guard) :
      SourceDecisionSite who
        (.commit commitName actor (b := commitTy) commitGuard tail) Δ x b guard
  | reveal {Γ : VCtx P L} {publicName : VarId} {actor : P} {sealedName : VarId} {revealTy : L.Ty}
      {source : VHasVar Γ sealedName (.sealed actor revealTy)}
      {tail : VegasCore P L ((publicName, .pub revealTy) :: Γ)} {Δ x b guard}
      (site : SourceDecisionSite who tail Δ x b guard) :
      SourceDecisionSite who
        (.reveal publicName actor sealedName (b := revealTy) source tail) Δ x b guard

namespace SourceDecisionSite

/-- The number of source instructions preceding this decision. -/
def depth {who : P} : {Γ : VCtx P L} → {prog : VegasCore P L Γ} →
    {Δ : VCtx P L} → {x : VarId} → {b : L.Ty} →
    {guard : L.Expr ((x, b) :: eraseVCtx (viewVCtx who Δ)) L.bool} →
    SourceDecisionSite who prog Δ x b guard → Nat
  | _, _, _, _, _, _, .here _ _ => 0
  | _, _, _, _, _, _, .sample site => site.depth + 1
  | _, _, _, _, _, _, .commit site => site.depth + 1
  | _, _, _, _, _, _, .reveal site => site.depth + 1

/-- In a straight-line source term, the instruction position identifies the
entire typed decision occurrence. -/
theorem indices_eq_of_depth_eq {who : P} {Γ : VCtx P L} {prog : VegasCore P L Γ}
    {Δ₁ Δ₂ : VCtx P L} {x₁ x₂ : VarId} {b₁ b₂ : L.Ty}
    {guard₁ : L.Expr ((x₁, b₁) :: eraseVCtx (viewVCtx who Δ₁)) L.bool}
    {guard₂ : L.Expr ((x₂, b₂) :: eraseVCtx (viewVCtx who Δ₂)) L.bool}
    (first : SourceDecisionSite who prog Δ₁ x₁ b₁ guard₁)
    (second : SourceDecisionSite who prog Δ₂ x₂ b₂ guard₂)
    (hdepth : first.depth = second.depth) :
    Δ₁ = Δ₂ ∧ x₁ = x₂ ∧ b₁ = b₂ ∧ HEq guard₁ guard₂ ∧ HEq first second := by
  induction first with
  | here =>
      cases second with
      | here => exact ⟨rfl, rfl, rfl, HEq.rfl, HEq.rfl⟩
      | commit site => simp [depth] at hdepth
  | sample site ih =>
      cases second with
      | sample other =>
          obtain ⟨rfl, rfl, rfl, hg, hs⟩ := ih other (Nat.add_right_cancel hdepth)
          cases eq_of_heq hg
          cases eq_of_heq hs
          refine ⟨rfl, rfl, rfl, HEq.rfl, ?_⟩
          rfl
  | commit site ih =>
      cases second with
      | here => simp [depth] at hdepth
      | commit other =>
          obtain ⟨rfl, rfl, rfl, hg, hs⟩ := ih other (Nat.add_right_cancel hdepth)
          cases eq_of_heq hg
          cases eq_of_heq hs
          refine ⟨rfl, rfl, rfl, HEq.rfl, ?_⟩
          rfl
  | reveal site ih =>
      cases second with
      | reveal other =>
          obtain ⟨rfl, rfl, rfl, hg, hs⟩ := ih other (Nat.add_right_cancel hdepth)
          cases eq_of_heq hg
          cases eq_of_heq hs
          refine ⟨rfl, rfl, rfl, HEq.rfl, ?_⟩
          rfl

end SourceDecisionSite

/-- A behavioral policy supplies a guarded finite law at every source decision
site owned by the player. Its input is only the player's visible environment. -/
def SourceBehavioralPolicy {Γ : VCtx P L} (prog : VegasCore P L Γ) (who : P) :=
  ∀ {Δ x b guard}, SourceDecisionSite who prog Δ x b guard →
    (visible : Env L.Val (eraseVCtx (viewVCtx who Δ))) →
      FinDist {value : L.Val b // evalGuard guard value visible = true}

/-- One source policy per player. -/
def SourceBehavioralProfile {Γ : VCtx P L} (prog : VegasCore P L Γ) :=
  ∀ who, SourceBehavioralPolicy prog who

namespace SourceBehavioralProfile

def afterSample {Γ : VCtx P L} {x : VarId} {b : L.Ty}
    {dist : L.DistExpr (erasePubVCtx Γ) b}
    {tail : VegasCore P L ((x, .pub b) :: Γ)}
    (profile : SourceBehavioralProfile (.sample x dist tail)) :
    SourceBehavioralProfile tail :=
  fun who _ _ _ _ site => profile who (.sample (Γ := Γ) site)

def afterCommit {Γ : VCtx P L} {x : VarId} {actor : P} {b : L.Ty}
    {guard : L.Expr ((x, b) :: eraseVCtx (viewVCtx actor Γ)) L.bool}
    {tail : VegasCore P L ((x, .sealed actor b) :: Γ)}
    (profile : SourceBehavioralProfile (.commit x actor guard tail)) :
    SourceBehavioralProfile tail :=
  fun who _ _ _ _ site => profile who (.commit (Γ := Γ) site)

def afterReveal {Γ : VCtx P L} {y : VarId} {actor : P} {x : VarId} {b : L.Ty}
    {source : VHasVar Γ x (.sealed actor b)}
    {tail : VegasCore P L ((y, .pub b) :: Γ)}
    (profile : SourceBehavioralProfile (.reveal y actor x source tail)) :
    SourceBehavioralProfile tail :=
  fun who _ _ _ _ site => profile who (.reveal (Γ := Γ) site)

end SourceBehavioralProfile

/-- The context at the terminal `ret` reached by following source continuations. -/
def sourceTerminalCtx : {Γ : VCtx P L} → VegasCore P L Γ → VCtx P L
  | Γ, .ret _ => Γ
  | _, .sample _x _ tail => sourceTerminalCtx tail
  | _, .commit _x _ _ tail => sourceTerminalCtx tail
  | _, .reveal _y _ _ _ tail => sourceTerminalCtx tail

/-- The payoff expressions at the terminal `ret` of a source program. -/
def sourceTerminalPayoffs : {Γ : VCtx P L} → (prog : VegasCore P L Γ) →
    List (P × L.Expr (erasePubVCtx (sourceTerminalCtx prog)) L.int)
  | _, .ret payoffs => payoffs
  | _, .sample _ _ tail => sourceTerminalPayoffs tail
  | _, .commit _ _ _ tail => sourceTerminalPayoffs tail
  | _, .reveal _ _ _ _ tail => sourceTerminalPayoffs tail

/-- The canonical strategic signature of a source term. -/
def sourceGameSignature {Γ : VCtx P L} (prog : VegasCore P L Γ) : GameSignature P where
  Strategy := SourceBehavioralPolicy prog
  Outcome := VEnv L (sourceTerminalCtx prog)

/-- Execute a source program in written order under a behavioral profile. -/
def denoteSource : {Γ : VCtx P L} → (prog : VegasCore P L Γ) →
    SourceBehavioralProfile prog → VEnv L Γ →
      FinDist (VEnv L (sourceTerminalCtx prog))
  | _, .ret _, _, env => FinDist.pure env
  | _, .sample _x dist tail, profile, env =>
      (L.evalDist dist env.eraseSampleEnv).bind fun value =>
        denoteSource tail profile.afterSample (env.cons value)
  | _, .commit _x who guard tail, profile, env =>
      (profile who (.here guard tail) ((env.toView who).eraseEnv)).bind fun choice =>
        denoteSource tail profile.afterCommit (env.cons choice.1)
  | _, .reveal _y who x source tail, profile, env =>
      denoteSource tail profile.afterReveal
        (env.cons (@VEnv.get P L _ x (.sealed who _) env source))

/-- The canonical utility-free game form of a source term from an initial
environment. Its profiles are definitionally source behavioral profiles. -/
def sourceGameForm {Γ : VCtx P L} (prog : VegasCore P L Γ) (env : VEnv L Γ) :
    GameForm P where
  sig := sourceGameSignature prog
  play profile := denoteSource prog profile env

@[simp] theorem sourceGameForm_play {Γ : VCtx P L} (prog : VegasCore P L Γ)
    (env : VEnv L Γ) (profile : Profile (sourceGameSignature prog)) :
    (sourceGameForm prog env).play profile = denoteSource prog profile env := rfl

theorem SourceDecisionSite.satisfiable
    {who : P} {Γ Δ : VCtx P L} {prog : VegasCore P L Γ} {x b guard}
    (site : SourceDecisionSite who prog Δ x b guard) (legal : Legal prog)
    (visible : Env L.Val (eraseVCtx (viewVCtx who Δ))) :
    ∃ value : L.Val b, evalGuard guard value visible = true := by
  induction site with
  | here => exact legal.1 visible
  | sample site ih => exact ih legal visible
  | commit site ih => exact ih legal.2 visible
  | reveal site ih => exact ih legal visible

/-- Global guard legality constructs a pure behavioral profile. This is an
inhabitation result, not a distinguished strategic recommendation. -/
def legalSourceProfile {Γ : VCtx P L} (prog : VegasCore P L Γ)
    (legal : Legal prog) : SourceBehavioralProfile prog :=
  fun _ _ _ _ _ site visible =>
    let witness := Classical.choose (site.satisfiable legal visible)
    FinDist.pure ⟨witness, Classical.choose_spec (site.satisfiable legal visible)⟩

theorem sourceBehavioralProfile_nonempty {Γ : VCtx P L}
    (prog : VegasCore P L Γ) (legal : Legal prog) :
    Nonempty (SourceBehavioralProfile prog) :=
  ⟨legalSourceProfile prog legal⟩

@[simp] theorem denoteSource_ret {Γ : VCtx P L} (payoffs) (env : VEnv L Γ)
    (profile : SourceBehavioralProfile (.ret payoffs)) :
    denoteSource (.ret payoffs) profile env = FinDist.pure env := rfl

@[simp] theorem denoteSource_sample {Γ : VCtx P L} (x : VarId) {b : L.Ty}
    (dist : L.DistExpr (erasePubVCtx Γ) b)
    (tail : VegasCore P L ((x, .pub b) :: Γ))
    (profile : SourceBehavioralProfile (.sample x dist tail)) (env : VEnv L Γ) :
    denoteSource (.sample x dist tail) profile env =
      (L.evalDist dist env.eraseSampleEnv).bind fun value =>
        denoteSource tail profile.afterSample (env.cons value) := rfl

@[simp] theorem denoteSource_commit {Γ : VCtx P L} (x : VarId) (who : P) {b : L.Ty}
    (guard : L.Expr ((x, b) :: eraseVCtx (viewVCtx who Γ)) L.bool)
    (tail : VegasCore P L ((x, .sealed who b) :: Γ))
    (profile : SourceBehavioralProfile (.commit x who guard tail)) (env : VEnv L Γ) :
    denoteSource (.commit x who guard tail) profile env =
      (profile who (.here guard tail) ((env.toView who).eraseEnv)).bind fun choice =>
        denoteSource tail profile.afterCommit (env.cons choice.1) := rfl

@[simp] theorem denoteSource_reveal {Γ : VCtx P L} (y : VarId) (who : P)
    (x : VarId) {b : L.Ty} (source : VHasVar Γ x (.sealed who b))
    (tail : VegasCore P L ((y, .pub b) :: Γ))
    (profile : SourceBehavioralProfile (.reveal y who x source tail)) (env : VEnv L Γ) :
    denoteSource (.reveal y who x source tail) profile env =
      denoteSource tail profile.afterReveal
        (env.cons (@VEnv.get P L Γ x (.sealed who b) env source)) := rfl

/-- Every terminal environment in the denotation's support is realized by the
written-order small-step semantics. -/
theorem denoteSource_support_star :
    {Γ : VCtx P L} → (prog : VegasCore P L Γ) →
      (profile : SourceBehavioralProfile prog) → (env : VEnv L Γ) →
      (terminalEnv : VEnv L (sourceTerminalCtx prog)) →
      terminalEnv ∈ (denoteSource prog profile env).support →
      SmallStep.Star
        { ctx := Γ, env := env, cont := prog }
        { ctx := sourceTerminalCtx prog, env := terminalEnv,
          cont := .ret (sourceTerminalPayoffs prog) }
  | _, .ret payoffs, _profile, env, terminalEnv, hsupport => by
      rw [denoteSource_ret, FinDist.mem_support_pure] at hsupport
      subst terminalEnv
      exact .refl _
  | _, .sample x dist tail, profile, env, terminalEnv, hsupport => by
      rw [denoteSource_sample, FinDist.support_bind] at hsupport
      obtain ⟨value, hvalue, htail⟩ := Set.mem_iUnion₂.mp hsupport
      exact (SmallStep.Star.single (SmallStep.sample dist tail value hvalue)).trans
        (denoteSource_support_star tail profile.afterSample (env.cons value)
          terminalEnv htail)
  | _, .commit x who guard tail, profile, env, terminalEnv, hsupport => by
      rw [denoteSource_commit, FinDist.support_bind] at hsupport
      obtain ⟨choice, _hchoice, htail⟩ := Set.mem_iUnion₂.mp hsupport
      exact (SmallStep.Star.single (SmallStep.commit guard tail choice.1 choice.2)).trans
        (denoteSource_support_star tail profile.afterCommit (env.cons choice.1)
          terminalEnv htail)
  | _, .reveal y who x source tail, profile, env, terminalEnv, hsupport => by
      exact (SmallStep.Star.single (SmallStep.reveal source tail)).trans
        (denoteSource_support_star tail profile.afterReveal
          (env.cons (@VEnv.get P L _ x (.sealed who _) env source)) terminalEnv hsupport)

end Vegas

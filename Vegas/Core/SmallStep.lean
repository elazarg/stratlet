/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import Vegas.Core.Basic
import Vegas.Foundation.Payoff

/-!
# Small-step operational semantics for `VegasCore`

This is the simplest faithful answer to "what does a Vegas program do?". A
program is executed **sequentially, in its own written order** — the canonical
source schedule. There is no external/runtime scheduler and no event graph here,
and no observability machinery; only the bare operational reading a programmer
needs to follow a run by hand.

The two intrinsic complications of the language are present, and nothing else:

* **Probability.** `sample` draws a value from a distribution; the step records
  that the drawn value lies in that distribution's support (nature's draw).
* **Information hiding.** `commit` evaluates its guard in the *acting player's
  view* of the environment, and `reveal` discloses a sealed value under a public
  alias.

The semantics is a reduction relation `SmallStep` between configurations. It is
support-level: it says which transitions are *possible*, not with what
probability — the quantitative weights belong to the denotational layers, not to
this operational reading.

Freshness of the introduced names (and well-formedness generally) is **not**
enforced here: it is a side condition supplied later by `GraphProgram` /
`WFProgram`. Raw `VegasCore` may reuse a name; a step simply pushes the new
binding onto the environment.
-/

namespace Vegas

variable {P : Type} [DecidableEq P] {L : IExpr}

/-- A running configuration: the current visibility context, the values bound so
far, and the remaining program to execute. -/
structure SourceConfig (P : Type) [DecidableEq P] (L : IExpr) where
  /-- The variables in scope, with their visibility. -/
  ctx : VCtx P L
  /-- The values bound to those variables. -/
  env : VEnv L ctx
  /-- The remaining program to run. -/
  cont : VegasCore P L ctx

namespace SourceConfig

/-- The initial configuration of a closed program: empty context and
environment, with the whole program still to run. -/
def initial (prog : VegasCore P L []) : SourceConfig P L where
  ctx := []
  env := VEnv.empty L
  cont := prog

/-- A configuration is terminal when the program has reduced to a `ret`. -/
def IsTerminal (cfg : SourceConfig P L) : Prop :=
  ∃ payoffs, cfg.cont = .ret payoffs

/-- The outcome a configuration reports: the evaluated payoffs at a terminal
`ret`, and nothing while the program is still running. -/
def payout? (cfg : SourceConfig P L) : Option (Payout P) :=
  match cfg.cont with
  | .ret payoffs => some (evalPayoffs payoffs cfg.env)
  | _ => none

@[simp] theorem payout?_ret {Γ : VCtx P L} {env : VEnv L Γ}
    (payoffs : List (P × L.Expr (erasePubVCtx Γ) L.int)) :
    payout? { ctx := Γ, env := env, cont := .ret payoffs } =
      some (evalPayoffs payoffs env) := rfl

end SourceConfig

/-- One reduction step of a Vegas program.

Each rule consumes the program's head constructor and produces the successor
configuration with the new binding pushed onto the environment. Written in the
canonical `⟨Γ, env, program⟩ ⟶ ⟨Γ', env', program'⟩` shape (context, then
environment, then the remaining program).

* `sample`: nature draws `v` from `D'` (evaluated in the public-only
  environment, since nature has no private knowledge) and binds it as a *public*
  variable (a fresh name in well-formed programs).
* `commit`: player `who` chooses a value `v` satisfying the guard `R`, which is
  evaluated against `who`'s *own view* of the environment; the value is bound as
  *sealed*, owned by `who`.
* `reveal`: the sealed value at `x` is copied under a *public* name `y`, making
  it observable to everyone. The original sealed binding stays in scope — reveal
  adds a public alias, it does not mutate the secret. -/
inductive SmallStep : SourceConfig P L → SourceConfig P L → Prop where
  /-- Nature draws a value in the support of the sample distribution. -/
  | sample {Γ : VCtx P L} {env : VEnv L Γ} {x : VarId} {b : L.Ty}
      (D' : L.DistExpr (erasePubVCtx Γ) b)
      (k : VegasCore P L ((x, .pub b) :: Γ))
      (v : L.Val b)
      (hv : v ∈ (L.evalDist D' env.eraseSampleEnv).support) :
      SmallStep ⟨Γ, env, .sample x D' k⟩ ⟨(x, .pub b) :: Γ, env.cons v, k⟩
  /-- A player commits a value satisfying its guard, sealed from the others. -/
  | commit {Γ : VCtx P L} {env : VEnv L Γ} {x : VarId} {who : P} {b : L.Ty}
      (R : L.Expr ((x, b) :: eraseVCtx (viewVCtx who Γ)) L.bool)
      (k : VegasCore P L ((x, .sealed who b) :: Γ))
      (v : L.Val b)
      (hguard : evalGuard R v ((env.toView who).eraseEnv) = true) :
      SmallStep ⟨Γ, env, .commit x who R k⟩
        ⟨(x, .sealed who b) :: Γ, env.cons v, k⟩
  /-- A previously sealed value is disclosed under a public alias. -/
  | reveal {Γ : VCtx P L} {env : VEnv L Γ} {y : VarId} {who : P} {x : VarId}
      {b : L.Ty}
      (hx : VHasVar Γ x (.sealed who b))
      (k : VegasCore P L ((y, .pub b) :: Γ)) :
      SmallStep ⟨Γ, env, .reveal y who x hx k⟩
        ⟨(y, .pub b) :: Γ, env.cons (env.get hx : L.Val b), k⟩

namespace SmallStep

/-- Reflexive-transitive closure: a complete run is a chain of small steps. -/
inductive Star : SourceConfig P L → SourceConfig P L → Prop where
  /-- The empty run stays put. -/
  | refl (cfg : SourceConfig P L) : Star cfg cfg
  /-- Extend a run by one more step. -/
  | tail {a b c : SourceConfig P L} : Star a b → SmallStep b c → Star a c

/-- A single step is a run. -/
theorem Star.single {a b : SourceConfig P L} (h : SmallStep a b) : Star a b :=
  .tail (.refl a) h

/-- Runs compose. -/
theorem Star.trans {a b c : SourceConfig P L}
    (hab : Star a b) (hbc : Star b c) : Star a c := by
  induction hbc with
  | refl => exact hab
  | tail _ hstep ih => exact .tail ih hstep

end SmallStep

/-! ## Labels (instrumentation)

The rules above are the explanatory semantics: a program's operational meaning is
the unlabeled `SmallStep` relation, and that is how it should be presented first
(e.g. in the paper). Labels add **no behavior** — `LStep` is `SmallStep`
annotated with the full payload of each step (the kind, the names, and the
drawn/chosen/disclosed value, *including* committed secrets), and forgetting the
label recovers
`SmallStep` exactly (`smallStep_iff_exists_label`). They are instrumentation for
later stages — linearization against the event graph, and per-player/epistemic
views of a run — where naming each transition is convenient. A label records the
*full* action; information-hiding is applied later as a per-player view of
labels, not baked in here. -/

/-- The full payload of one step: which kind of event fired, the names involved,
and the value drawn / chosen / disclosed (including committed secrets — this is
instrumentation, not a player-visible observation). -/
inductive Label (P : Type) (L : IExpr) where
  /-- Nature drew `v` and published it as `x`. -/
  | sample (x : VarId) {b : L.Ty} (v : L.Val b)
  /-- Player `who` committed `v` (sealed) as `x`. -/
  | commit (x : VarId) (who : P) {b : L.Ty} (v : L.Val b)
  /-- The sealed value `v` at `x` was disclosed under the public alias `y`. -/
  | reveal (y : VarId) (who : P) (x : VarId) {b : L.Ty} (v : L.Val b)

/-- `SmallStep` annotated with the label of the step that fired. Definitionally
the same three transitions; the label is an output index. -/
inductive LStep : SourceConfig P L → Label P L → SourceConfig P L → Prop where
  /-- Nature draws a value in the support of the sample distribution. -/
  | sample {Γ : VCtx P L} {env : VEnv L Γ} {x : VarId} {b : L.Ty}
      (D' : L.DistExpr (erasePubVCtx Γ) b)
      (k : VegasCore P L ((x, .pub b) :: Γ))
      (v : L.Val b)
      (hv : v ∈ (L.evalDist D' env.eraseSampleEnv).support) :
      LStep ⟨Γ, env, .sample x D' k⟩ (.sample x v)
        ⟨(x, .pub b) :: Γ, env.cons v, k⟩
  /-- A player commits a value satisfying its guard, sealed from the others. -/
  | commit {Γ : VCtx P L} {env : VEnv L Γ} {x : VarId} {who : P} {b : L.Ty}
      (R : L.Expr ((x, b) :: eraseVCtx (viewVCtx who Γ)) L.bool)
      (k : VegasCore P L ((x, .sealed who b) :: Γ))
      (v : L.Val b)
      (hguard : evalGuard R v ((env.toView who).eraseEnv) = true) :
      LStep ⟨Γ, env, .commit x who R k⟩ (.commit x who v)
        ⟨(x, .sealed who b) :: Γ, env.cons v, k⟩
  /-- A previously sealed value is disclosed under a public alias. -/
  | reveal {Γ : VCtx P L} {env : VEnv L Γ} {y : VarId} {who : P} {x : VarId}
      {b : L.Ty}
      (hx : VHasVar Γ x (.sealed who b))
      (k : VegasCore P L ((y, .pub b) :: Γ)) :
      LStep ⟨Γ, env, .reveal y who x hx k⟩
        (.reveal y who x (env.get hx : L.Val b))
        ⟨(y, .pub b) :: Γ, env.cons (env.get hx : L.Val b), k⟩

/-- Forgetting the label recovers an ordinary step. -/
theorem LStep.toSmallStep {a b : SourceConfig P L} {ℓ : Label P L}
    (h : LStep a ℓ b) : SmallStep a b := by
  cases h with
  | sample D' k v hv => exact .sample D' k v hv
  | commit R k v hg => exact .commit R k v hg
  | reveal hx k => exact .reveal hx k

/-- A step is exactly a labeled step with its label forgotten: labels are pure
instrumentation over `SmallStep`. -/
theorem smallStep_iff_exists_label {a b : SourceConfig P L} :
    SmallStep a b ↔ ∃ ℓ : Label P L, LStep a ℓ b := by
  constructor
  · intro h
    cases h with
    | sample D' k v hv => exact ⟨_, .sample D' k v hv⟩
    | commit R k v hg => exact ⟨_, .commit R k v hg⟩
    | reveal hx k => exact ⟨_, .reveal hx k⟩
  · rintro ⟨_, h⟩
    exact h.toSmallStep

end Vegas

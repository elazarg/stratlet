import Vegas.Equilibrium
import Vegas.PureStrategic

/-!
# Protocol-native semantics for Vegas

This file defines Vegas's solution concepts directly in terms of the
protocol's own `outcomeDistBehavioral` semantics (rather than through
the `toKernelGame` bridge) and proves that the two definitions agree.
The purpose is to make the protocol picture explicit in-tree: what a
Vegas Nash equilibrium *means* at the protocol level is exactly the
statement of `ProtocolNash`, and the existing `Vegas.IsNash` (defined
via `KernelGame`) is shown to be literally the same proposition.

The file has four regions.

* **Region A (protocol-native definitions, proved).**
  `protocolEU`, `ProtocolNash`, `ProtocolBestResponse`,
  `ProtocolDominant`, `ProtocolStrictNash`. These are defined directly
  on `LegalProgramBehavioralProfile` / `...Strategy`, with the guard-
  legality constraint carried by the subtype. Correspondence theorems
  (`isNash_iff_protocolNash`, etc.) prove each equals its
  `KernelGame`-transported counterpart by definitional unfolding.

* **Region B (context-free subclass, proved decidable).**
  `CommitGuardContextFree` / `ContextFreeGuards` carve out the
  sub-class of Vegas programs whose commit guards read only the
  proposed action — never the ambient environment. Matching-pennies
  (trivial `true` guard) qualifies; conditioned-game does not. This
  class is the natural target for a future protocol-preserving MAID
  compilation (see Region D).

* **Region C (named conjectures, not theorems).**
  `ProtocolKuhnProperty g : Prop` — the protocol-level Kuhn claim:
  every mixture over legal pure strategies is outcome-equivalent to
  some legal behavioural profile. Proving this from the existing MAID
  Kuhn would require repairing `reflectPolicyAuxV`'s off-path defaults
  to be guard-respecting, or a direct Vegas Kuhn proof. Left as a
  named target.

  `MaidNashImpliesProtocolNash g : Prop` — the provable direction of
  the MAID bridge (MAID Nash of the compiled MAID plus legality ⇒
  Protocol Nash). This could be a theorem, but its precise statement
  requires lining up against `compiledPolicyV` / `reflectPolicyV` in
  `Vegas.MAID.Bridge`; we name it as a `Prop`-valued target for a
  future dedicated MAID-bridge pass rather than forcing that detour
  mid-plan. The converse is intentionally *not* stated (generally
  false — MAID Nash quantifies over deviations that include
  guard-violating alternatives).

* **Region D (gap documentation, prose only).**
  The general-case MAID compilation is outcome-preserving but not
  protocol-representing: the action graph at each decision node takes
  the full `L.Val τ` rather than a guard-filtered subtype, so MAID
  equilibria can recommend guard-violating moves. Closing this gap
  requires subtype-valued decision-node `Val` in the MAID struct —
  a separate refactor of comparable scope to Vegas Kuhn. For
  `ContextFreeGuards` programs, the restricted-MAID construction is
  conceptually straightforward, but its mechanisation is still
  deferred; see the paper's Mechanisation-Notes discussion.
-/

namespace Vegas

open GameTheory

variable {P : Type} [DecidableEq P] {L : IExpr}

/-! ## Region A — protocol-native solution concepts -/

/-- Protocol-level expected utility: evaluate the Vegas program's
behavioural outcome distribution against the legal profile
(unpacking each strategy via `.val`) and take the expected payoff
for player `i`. -/
noncomputable def protocolEU (g : WFProgram P L)
    (σ : LegalProgramBehavioralProfile g) (i : P) : ℝ :=
  (outcomeDistBehavioral g.prog (fun j => (σ j).val) g.env).sum
    (fun o w => (w : ℝ) * (o i : ℝ))

@[simp] theorem toKernelGame_eu_eq_protocolEU (g : WFProgram P L)
    (σ : LegalProgramBehavioralProfile g) (i : P) :
    (toKernelGame g).eu σ i = protocolEU g σ i := by
  simpa [protocolEU] using
    toKernelGame_eu (g := g) (σ := σ) (who := i)

@[simp] theorem eu_eq_protocolEU (g : WFProgram P L)
    (σ : StrategyProfile g) (i : P) :
    Vegas.eu g σ i = protocolEU g σ i := by
  simp [protocolEU, eu, Game]

/-- Protocol-level Nash equilibrium: no player can improve their
protocol-level expected utility by a unilateral deviation within
the guard-legal strategy space. -/
def ProtocolNash (g : WFProgram P L)
    (σ : LegalProgramBehavioralProfile g) : Prop :=
  ∀ (who : P) (s' : LegalProgramBehavioralStrategy g who),
    protocolEU g σ who ≥ protocolEU g (Function.update σ who s') who

theorem isNash_iff_protocolNash (g : WFProgram P L)
    (σ : StrategyProfile g) :
    Vegas.IsNash g σ ↔ ProtocolNash g σ := by
  unfold Vegas.IsNash ProtocolNash
  simp only [KernelGame.IsNash, ge_iff_le]
  constructor
  · intro h who s'
    have := h who s'
    simpa [eu_eq_protocolEU, Game] using this
  · intro h who s'
    have := h who s'
    simpa [eu_eq_protocolEU, Game] using this

/-- Protocol-level best response: `s` maximises player `who`'s
protocol-level expected utility among all legal deviations, holding
opponents' strategies in `σ` fixed. -/
def ProtocolBestResponse (g : WFProgram P L)
    (who : P) (σ : LegalProgramBehavioralProfile g)
    (s : LegalProgramBehavioralStrategy g who) : Prop :=
  ∀ (s' : LegalProgramBehavioralStrategy g who),
    protocolEU g (Function.update σ who s) who ≥
      protocolEU g (Function.update σ who s') who

theorem isBestResponse_iff_protocolBestResponse (g : WFProgram P L)
    (who : P) (σ : StrategyProfile g) (s : Strategy g who) :
    Vegas.IsBestResponse g who σ s ↔ ProtocolBestResponse g who σ s := by
  unfold Vegas.IsBestResponse ProtocolBestResponse
  simp only [KernelGame.IsBestResponse, ge_iff_le]
  constructor
  · intro h s'
    have := h s'
    simpa [eu_eq_protocolEU, Game, Strategy, StrategyProfile] using this
  · intro h s'
    have := h s'
    simpa [eu_eq_protocolEU, Game, Strategy, StrategyProfile] using this

/-- Protocol-level dominant strategy: `s` is at least as good as any
legal alternative, for player `who`, at every legal profile of
opponents. -/
def ProtocolDominant (g : WFProgram P L)
    (who : P) (s : LegalProgramBehavioralStrategy g who) : Prop :=
  ∀ (σ : LegalProgramBehavioralProfile g)
    (s' : LegalProgramBehavioralStrategy g who),
    protocolEU g (Function.update σ who s) who ≥
      protocolEU g (Function.update σ who s') who

theorem isDominant_iff_protocolDominant (g : WFProgram P L)
    (who : P) (s : Strategy g who) :
    Vegas.IsDominant g who s ↔ ProtocolDominant g who s := by
  unfold Vegas.IsDominant ProtocolDominant
  simp only [KernelGame.IsDominant, ge_iff_le]
  constructor
  · intro h σ s'
    have := h σ s'
    simpa [eu_eq_protocolEU, Game, Strategy, StrategyProfile] using this
  · intro h σ s'
    have := h σ s'
    simpa [eu_eq_protocolEU, Game, Strategy, StrategyProfile] using this

/-- Protocol-level strict Nash equilibrium: every legal unilateral
deviation strictly decreases the deviator's protocol-level expected
utility. -/
def ProtocolStrictNash (g : WFProgram P L)
    (σ : LegalProgramBehavioralProfile g) : Prop :=
  ∀ (who : P) (s' : LegalProgramBehavioralStrategy g who), s' ≠ σ who →
    protocolEU g σ who > protocolEU g (Function.update σ who s') who

theorem isStrictNash_iff_protocolStrictNash (g : WFProgram P L)
    (σ : StrategyProfile g) :
    Vegas.IsStrictNash g σ ↔ ProtocolStrictNash g σ := by
  unfold Vegas.IsStrictNash ProtocolStrictNash
  simp only [KernelGame.IsStrictNash]
  constructor
  · intro h who s' hne
    have := h who s' hne
    simpa [eu_eq_protocolEU, Game, Strategy, StrategyProfile] using this
  · intro h who s' hne
    have := h who s' hne
    simpa [eu_eq_protocolEU, Game, Strategy, StrategyProfile] using this

/-! ## Region B — context-free guards -/

/-- A commit guard is *context-free* when it depends only on the
proposed action variable, not on the ambient environment. Formally,
its expression-dependency set is contained in the singleton `{x}`.
This is the special case in which the legality of an action can be
decided without consulting the current execution environment. -/
def CommitGuardContextFree {Γ : VCtx P L} {x : VarId} {b : L.Ty}
    (R : L.Expr ((x, b) :: eraseVCtx Γ) L.bool) : Prop :=
  L.exprDeps R ⊆ {x}

/-- Every commit site in the program has a context-free guard. -/
def ContextFreeGuards :
    {Γ : VCtx P L} → VegasCore P L Γ → Prop
  | _, .ret _ => True
  | _, .letExpr _ _ k => ContextFreeGuards k
  | _, .sample _ _ k => ContextFreeGuards k
  | _, .commit _ _ R k => CommitGuardContextFree R ∧ ContextFreeGuards k
  | _, .reveal _ _ _ _ k => ContextFreeGuards k

instance CommitGuardContextFree.instDecidable
    {Γ : VCtx P L} {x : VarId} {b : L.Ty}
    [DecidableEq VarId]
    (R : L.Expr ((x, b) :: eraseVCtx Γ) L.bool) :
    Decidable (CommitGuardContextFree R) := by
  unfold CommitGuardContextFree; infer_instance

instance ContextFreeGuards.instDecidable [DecidableEq VarId] :
    {Γ : VCtx P L} → (p : VegasCore P L Γ) →
    Decidable (ContextFreeGuards p)
  | _, .ret _ => instDecidableTrue
  | _, .letExpr _ _ k => ContextFreeGuards.instDecidable k
  | _, .sample _ _ k => ContextFreeGuards.instDecidable k
  | _, .commit _ _ R k =>
      let _ := CommitGuardContextFree.instDecidable R
      let _ := ContextFreeGuards.instDecidable k
      inferInstanceAs (Decidable (_ ∧ _))
  | _, .reveal _ _ _ _ k => ContextFreeGuards.instDecidable k

/-! ## Region C — named conjectures -/

/-- The protocol-level Kuhn property for a Vegas program: every
mixture over guard-legal pure strategies admits a guard-legal
behavioural profile with the same outcome distribution.

Stated here as a `Prop`-valued definition rather than a theorem.
Proving it would require one of:

* Repairing `MAID.Struct.Val` / `reflectPolicyAuxV`'s off-path
  defaults (`MAIDValuation.defaultVal`) to be guard-respecting, then
  routing through the existing MAID Kuhn.
* Constructing a direct Vegas Kuhn argument at the legal-subtype
  level.

Both are substantial, and neither is attempted here. The name is in
place so paper and future proof work have a target. -/
def ProtocolKuhnProperty (g : WFProgram P L) : Prop :=
  ∀ (μ : ∀ who, PMF (LegalProgramPureStrategy g who)),
    ∃ β : LegalProgramBehavioralProfile g,
      (toKernelGame g).outcomeKernel β =
        (((fun who => μ who) : ∀ who, PMF (LegalProgramPureStrategy g who))
          |> fun _ => (toKernelGame g).outcomeKernel β)
  -- The equation's RHS is a placeholder: the intended statement is
  -- "outcome distribution equals the pushforward mixture under μ",
  -- but writing the pushforward requires MAID-style machinery that
  -- is out of scope here. Any consumer of this `Prop` should treat
  -- it as a named conjecture, not a usable lemma.

/-- Provable direction of the MAID ↔ Protocol bridge: MAID Nash of
the compiled MAID, restricted to legal reflected profiles, implies
Protocol Nash of the Vegas program. Stated as a `Prop` to be
specialised against concrete MAID-bridge infrastructure in a future
dedicated pass; the obstruction is not mathematical but mechanical,
matching the `compiledPolicyV` / `reflectPolicyV` boundary.

The converse (Protocol Nash ⇒ MAID Nash) is **intentionally not
named**: it is false in general, because MAID Nash quantifies over
deviations that include guard-violating alternatives the protocol
rejects. -/
def MaidNashImpliesProtocolNash (g : WFProgram P L) : Prop :=
  ∀ (σ : LegalProgramBehavioralProfile g),
    -- Placeholder: a rigorous statement needs to reference
    -- MAID bridge artefacts (`vegasMAID_behavioral_bridge`,
    -- `reflectPolicyV`) that are not imported at this layer. A
    -- future pass that imports `Vegas.MAID.Bridge` can refine this
    -- into a proved theorem by restricting the MAID's universal
    -- deviation quantifier to the legal reflected subset.
    ProtocolNash g σ → ProtocolNash g σ

end Vegas

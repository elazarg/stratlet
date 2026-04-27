import GameTheory.Languages.FOSG.Information
import GameTheory.Languages.FOSG.Strategy
import GameTheory.Languages.FOSG.Compile
import Vegas.Strategic
import Vegas.Finite
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

This broad alphabet is adequate for the structural control-flow bridge. A
finite execution bridge should use a program-local action alphabet instead:
otherwise `Fintype (Action L who)` would require finiteness of `L.Ty`, not just
finiteness of values that actually occur in `g`.
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

/-- Number of operational syntax nodes remaining before a Vegas program reaches
`ret`, ignoring probabilistic branching because branching changes only
environments, not the continuation shape. -/
def syntaxSteps :
    {Γ : VCtx P L} → VegasCore P L Γ → Nat
  | _, .ret _ => 0
  | _, .letExpr _ _ k => syntaxSteps k + 1
  | _, .sample _ _ k => syntaxSteps k + 1
  | _, .commit _ _ _ k => syntaxSteps k + 1
  | _, .reveal _ _ _ _ k => syntaxSteps k + 1

@[simp] theorem syntaxSteps_ret
    {Γ : VCtx P L}
    (payoffs : List (P × L.Expr (erasePubVCtx Γ) L.int)) :
    syntaxSteps (P := P) (L := L) (.ret payoffs) = 0 := rfl

@[simp] theorem syntaxSteps_letExpr
    {Γ : VCtx P L} {x : VarId} {b : L.Ty}
    {e : L.Expr (erasePubVCtx Γ) b}
    {k : VegasCore P L ((x, .pub b) :: Γ)} :
    syntaxSteps (P := P) (L := L) (.letExpr x e k) = syntaxSteps k + 1 := rfl

@[simp] theorem syntaxSteps_sample
    {Γ : VCtx P L} {x : VarId} {b : L.Ty}
    {D : L.DistExpr (erasePubVCtx Γ) b}
    {k : VegasCore P L ((x, .pub b) :: Γ)} :
    syntaxSteps (P := P) (L := L) (.sample x D k) = syntaxSteps k + 1 := rfl

@[simp] theorem syntaxSteps_commit
    {Γ : VCtx P L} {x : VarId} {who : P} {b : L.Ty}
    {R : L.Expr ((x, b) :: eraseVCtx Γ) L.bool}
    {k : VegasCore P L ((x, .hidden who b) :: Γ)} :
    syntaxSteps (P := P) (L := L) (.commit x who R k) = syntaxSteps k + 1 := rfl

@[simp] theorem syntaxSteps_reveal
    {Γ : VCtx P L} {y : VarId} {who : P} {x : VarId} {b : L.Ty}
    {hx : VHasVar Γ x (.hidden who b)}
    {k : VegasCore P L ((y, .pub b) :: Γ)} :
    syntaxSteps (P := P) (L := L) (.reveal y who x hx k) = syntaxSteps k + 1 := rfl

/-- A program has no remaining syntax steps exactly at `ret`. -/
theorem terminal_iff_syntaxSteps_eq_zero {w : World P L} :
    terminal w ↔ syntaxSteps w.prog = 0 := by
  cases w with
  | mk Γ prog env =>
      cases prog <;> simp [terminal, syntaxSteps]

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

/-! ## Program-local action cursors

The broad `Action L who` alphabet above is useful for the first structural
bridge, but finite FOSG execution should not quantify over every type in `L`.
The following cursor describes exactly the commit sites of one program owned by
one player; `ProgramAction` is the corresponding finite-by-construction target
alphabet once value types are finite.
-/

/-- A cursor to a commit site owned by `who` inside a fixed Vegas program. -/
inductive CommitCursor (who : P) :
    {Γ : VCtx P L} → VegasCore P L Γ → Type where
  | here
      {Γ : VCtx P L} {x : VarId} {b : L.Ty}
      {R : L.Expr ((x, b) :: eraseVCtx Γ) L.bool}
      {k : VegasCore P L ((x, .hidden who b) :: Γ)} :
      CommitCursor who (.commit x who R k)
  | letExpr
      {Γ : VCtx P L} {x : VarId} {b : L.Ty}
      {e : L.Expr (erasePubVCtx Γ) b}
      {k : VegasCore P L ((x, .pub b) :: Γ)}
      (c : CommitCursor who k) :
      CommitCursor who (.letExpr x e k)
  | sample
      {Γ : VCtx P L} {x : VarId} {b : L.Ty}
      {D : L.DistExpr (erasePubVCtx Γ) b}
      {k : VegasCore P L ((x, .pub b) :: Γ)}
      (c : CommitCursor who k) :
      CommitCursor who (.sample x D k)
  | commit
      {Γ : VCtx P L} {x : VarId} {owner : P} {b : L.Ty}
      {R : L.Expr ((x, b) :: eraseVCtx Γ) L.bool}
      {k : VegasCore P L ((x, .hidden owner b) :: Γ)}
      (c : CommitCursor who k) :
      CommitCursor who (.commit x owner R k)
  | reveal
      {Γ : VCtx P L} {y : VarId} {owner : P} {x : VarId} {b : L.Ty}
      {hx : VHasVar Γ x (.hidden owner b)}
      {k : VegasCore P L ((y, .pub b) :: Γ)}
      (c : CommitCursor who k) :
      CommitCursor who (.reveal y owner x hx k)

namespace CommitCursor

/-- The value type chosen at the pointed commit site. -/
def ty {who : P} :
    {Γ : VCtx P L} → {p : VegasCore P L Γ} →
      CommitCursor (P := P) (L := L) who p → L.Ty
  | _, .commit _ _ (b := b) _ _, .here => b
  | _, .letExpr _ _ _, .letExpr c => ty c
  | _, .sample _ _ _, .sample c => ty c
  | _, .commit _ _ _ _, .commit c => ty c
  | _, .reveal _ _ _ _ _, .reveal c => ty c

/-- Enumerate the commit sites owned by `who` in a fixed program. -/
def enumerate (who : P) :
    {Γ : VCtx P L} → (p : VegasCore P L Γ) →
      List (CommitCursor (P := P) (L := L) who p)
  | _, .ret _ => []
  | _, .letExpr _ _ k => (enumerate who k).map .letExpr
  | _, .sample _ _ k => (enumerate who k).map .sample
  | Γ, .commit x owner (b := b) R k =>
      if h : owner = who then
        by
          have head :
              CommitCursor (P := P) (L := L) who
                (.commit x owner (b := b) R k) := by
            cases h
            exact .here
          exact head :: (enumerate who k).map .commit
      else
        (enumerate who k).map .commit
  | _, .reveal _ _ _ _ k => (enumerate who k).map .reveal

/-- `enumerate` is complete: every cursor appears in the generated list. -/
theorem mem_enumerate {who : P} :
    {Γ : VCtx P L} → {p : VegasCore P L Γ} →
      (c : CommitCursor (P := P) (L := L) who p) →
        c ∈ enumerate (P := P) (L := L) who p
  | _, _, .here => by
      simp [enumerate]
  | _, _, .letExpr c => by
      simp [enumerate, mem_enumerate c]
  | _, _, .sample c => by
      simp [enumerate, mem_enumerate c]
  | _, _, .commit c => by
      simp only [enumerate]
      split
      · right
        exact List.mem_map.mpr ⟨c, mem_enumerate c, rfl⟩
      · exact List.mem_map.mpr ⟨c, mem_enumerate c, rfl⟩
  | _, _, .reveal c => by
      simp [enumerate, mem_enumerate c]

/-- The set of owned commit cursors is finite without assuming all language
types are finite. -/
@[reducible] noncomputable def instFintype
    (who : P) {Γ : VCtx P L} (p : VegasCore P L Γ) :
    Fintype (CommitCursor (P := P) (L := L) who p) := by
  classical
  exact Fintype.ofList (enumerate (P := P) (L := L) who p)
    (fun c => mem_enumerate (P := P) (L := L) c)

end CommitCursor

/-- Program-local action alphabet: choose one owned commit site and a value of
that site's type. This is the intended replacement alphabet for finite FOSG
execution, avoiding any global finiteness assumption on `L.Ty`. -/
structure ProgramAction {Γ : VCtx P L} (p : VegasCore P L Γ) (who : P) where
  cursor : CommitCursor (P := P) (L := L) who p
  value : L.Val (CommitCursor.ty cursor)

namespace ProgramAction

/-- Erase a program-local action to the broad structural action alphabet. -/
def toAction {Γ : VCtx P L} {p : VegasCore P L Γ} {who : P}
    (a : ProgramAction (P := P) (L := L) p who) : Action (P := P) L who :=
  Sigma.mk (CommitCursor.ty a.cursor) a.value

/-- Local decidable equality helper for program actions. Kept as an explicit
definition rather than a global instance because it is classical over the
dependent cursor proof shape. -/
@[reducible] noncomputable def instDecidableEq
    {Γ : VCtx P L} (p : VegasCore P L Γ) (who : P) :
    DecidableEq (ProgramAction (P := P) (L := L) p who) :=
  Classical.decEq _

/-- Program-local actions are finite when the value types that occur in the
language are finite. This avoids the stronger and usually wrong requirement
that the global sigma alphabet `Action L who` be finite. -/
@[reducible] noncomputable def instFintype
    (LF : FiniteValuation L) {Γ : VCtx P L}
    (p : VegasCore P L Γ) (who : P) :
    Fintype (ProgramAction (P := P) (L := L) p who) := by
  classical
  let _ : Fintype (CommitCursor (P := P) (L := L) who p) :=
    CommitCursor.instFintype (P := P) (L := L) who p
  have hVal : ∀ c : CommitCursor (P := P) (L := L) who p,
      Fintype (L.Val (CommitCursor.ty c)) :=
    fun c => LF.fintypeVal (CommitCursor.ty c)
  let e :
      ProgramAction (P := P) (L := L) p who ≃
        Sigma (fun c : CommitCursor (P := P) (L := L) who p =>
          L.Val (CommitCursor.ty c)) :=
    { toFun := fun a => ⟨a.cursor, a.value⟩
      invFun := fun a => { cursor := a.1, value := a.2 }
      left_inv := by
        intro a
        cases a
        rfl
      right_inv := by
        intro a
        cases a
        rfl }
  let _ : ∀ c : CommitCursor (P := P) (L := L) who p,
      Fintype (L.Val (CommitCursor.ty c)) := hVal
  exact Fintype.ofEquiv
    (Sigma (fun c : CommitCursor (P := P) (L := L) who p =>
      L.Val (CommitCursor.ty c))) e.symm

end ProgramAction

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

/-- Lift a program-local commit cursor at the current suffix back to a cursor
for the original root program. -/
noncomputable def liftCommitCursor
    {Γ₀ Γ : VCtx P L} {root : VegasCore P L Γ₀} {p : VegasCore P L Γ}
    (s : ProgramSuffix root p) {who : P} :
    CommitCursor (P := P) (L := L) who p →
      CommitCursor (P := P) (L := L) who root := by
  induction s with
  | here =>
      intro c
      exact c
  | letExpr s ih =>
      intro c
      exact ih (.letExpr c)
  | sample s ih =>
      intro c
      exact ih (.sample c)
  | commit s ih =>
      intro c
      exact ih (.commit c)
  | reveal s ih =>
      intro c
      exact ih (.reveal c)

/-- Convert a suffix proof whose endpoint is an owned commit node into the
program-local commit cursor for that site. -/
noncomputable def commitCursor
    {Γ₀ Γ : VCtx P L} {root : VegasCore P L Γ₀}
    {x : VarId} {who : P} {b : L.Ty}
    {R : L.Expr ((x, b) :: eraseVCtx Γ) L.bool}
    {k : VegasCore P L ((x, .hidden who b) :: Γ)}
    (s : ProgramSuffix root (.commit x who R k)) :
    CommitCursor (P := P) (L := L) who root :=
  s.liftCommitCursor .here

/-- Lifting a commit cursor through a suffix preserves the commit site's value
type. -/
theorem ty_liftCommitCursor
    {Γ₀ Γ : VCtx P L} {root : VegasCore P L Γ₀} {p : VegasCore P L Γ}
    (s : ProgramSuffix root p) {who : P}
    (c : CommitCursor (P := P) (L := L) who p) :
    CommitCursor.ty (s.liftCommitCursor c) = CommitCursor.ty c := by
  induction s with
  | here =>
      rfl
  | letExpr s ih =>
      simpa [liftCommitCursor, CommitCursor.ty] using ih (.letExpr c)
  | sample s ih =>
      simpa [liftCommitCursor, CommitCursor.ty] using ih (.sample c)
  | commit s ih =>
      simpa [liftCommitCursor, CommitCursor.ty] using ih (.commit c)
  | reveal s ih =>
      simpa [liftCommitCursor, CommitCursor.ty] using ih (.reveal c)

/-- The cursor extracted from a suffix ending at a commit has the type of that
commit. -/
theorem ty_commitCursor
    {Γ₀ Γ : VCtx P L} {root : VegasCore P L Γ₀}
    {x : VarId} {who : P} {b : L.Ty}
    {R : L.Expr ((x, b) :: eraseVCtx Γ) L.bool}
    {k : VegasCore P L ((x, .hidden who b) :: Γ)}
    (s : ProgramSuffix root (.commit x who R k)) :
    CommitCursor.ty (commitCursor (P := P) (L := L) s) = b := by
  simpa [commitCursor, CommitCursor.ty] using
    ty_liftCommitCursor (P := P) (L := L) (s := s)
      (c := (.here :
        CommitCursor (P := P) (L := L) who (.commit x who (b := b) R k)))

end ProgramSuffix

/-! ## Canonical program cursors

`ProgramSuffix` is useful for proof transport, but it is not the right finite
state key: it is a proof-shaped path. `ProgramCursor` is the canonical data
representation of a position in the linear Vegas syntax.
-/

/-- A canonical cursor to one syntactic continuation of a Vegas program. -/
inductive ProgramCursor :
    {Γ : VCtx P L} → VegasCore P L Γ → Type where
  | here {Γ : VCtx P L} {p : VegasCore P L Γ} :
      ProgramCursor p
  | letExpr
      {Γ : VCtx P L} {x : VarId} {b : L.Ty}
      {e : L.Expr (erasePubVCtx Γ) b}
      {k : VegasCore P L ((x, .pub b) :: Γ)}
      (c : ProgramCursor k) :
      ProgramCursor (.letExpr x e k)
  | sample
      {Γ : VCtx P L} {x : VarId} {b : L.Ty}
      {D : L.DistExpr (erasePubVCtx Γ) b}
      {k : VegasCore P L ((x, .pub b) :: Γ)}
      (c : ProgramCursor k) :
      ProgramCursor (.sample x D k)
  | commit
      {Γ : VCtx P L} {x : VarId} {who : P} {b : L.Ty}
      {R : L.Expr ((x, b) :: eraseVCtx Γ) L.bool}
      {k : VegasCore P L ((x, .hidden who b) :: Γ)}
      (c : ProgramCursor k) :
      ProgramCursor (.commit x who R k)
  | reveal
      {Γ : VCtx P L} {y : VarId} {who : P} {x : VarId} {b : L.Ty}
      {hx : VHasVar Γ x (.hidden who b)}
      {k : VegasCore P L ((y, .pub b) :: Γ)}
      (c : ProgramCursor k) :
      ProgramCursor (.reveal y who x hx k)

namespace ProgramCursor

/-- Context at the cursor target. -/
def Γ :
    {Γ₀ : VCtx P L} → {root : VegasCore P L Γ₀} →
      ProgramCursor (P := P) (L := L) root → VCtx P L
  | Γ₀, _, .here => Γ₀
  | _, _, .letExpr c => Γ c
  | _, _, .sample c => Γ c
  | _, _, .commit c => Γ c
  | _, _, .reveal c => Γ c

/-- Program continuation at the cursor target. -/
def prog :
    {Γ₀ : VCtx P L} → {root : VegasCore P L Γ₀} →
      (c : ProgramCursor (P := P) (L := L) root) → VegasCore P L (Γ c)
  | _, root, .here => root
  | _, _, .letExpr c => prog c
  | _, _, .sample c => prog c
  | _, _, .commit c => prog c
  | _, _, .reveal c => prog c

/-- Local proof obligations attached to a program cursor endpoint. -/
def EndpointValid
    {Γ₀ : VCtx P L} {root : VegasCore P L Γ₀}
    (c : ProgramCursor (P := P) (L := L) root) : Prop :=
  WFCtx c.Γ ∧ FreshBindings c.prog ∧ ViewScoped c.prog ∧
    NormalizedDists c.prog ∧ Legal c.prog

/-- Extend an existing suffix by a canonical cursor rooted at its endpoint. -/
def toSuffixFrom
    {Γ₀ Γ : VCtx P L} {root : VegasCore P L Γ₀} {p : VegasCore P L Γ}
    (s : ProgramSuffix root p) :
    (c : ProgramCursor (P := P) (L := L) p) →
      ProgramSuffix root (prog c)
  | .here => s
  | .letExpr c => toSuffixFrom (.letExpr s) c
  | .sample c => toSuffixFrom (.sample s) c
  | .commit c => toSuffixFrom (.commit s) c
  | .reveal c => toSuffixFrom (.reveal s) c

/-- Convert a canonical cursor to the existing proof-shaped suffix. -/
def toSuffix
    {Γ₀ : VCtx P L} {root : VegasCore P L Γ₀}
    (c : ProgramCursor (P := P) (L := L) root) :
    ProgramSuffix root (prog c) :=
  toSuffixFrom .here c

/-- Compose a cursor from `root` to `p` with a cursor from `p` to a deeper
continuation. -/
def extend :
    {Γ₀ : VCtx P L} → {root : VegasCore P L Γ₀} →
      (c : ProgramCursor (P := P) (L := L) root) →
      ProgramCursor (P := P) (L := L) (prog c) →
        ProgramCursor (P := P) (L := L) root
  | _, _, .here, d => d
  | _, _, .letExpr c, d => .letExpr (extend c d)
  | _, _, .sample c, d => .sample (extend c d)
  | _, _, .commit c, d => .commit (extend c d)
  | _, _, .reveal c, d => .reveal (extend c d)

@[simp] theorem extend_here_left
    {Γ : VCtx P L} {root : VegasCore P L Γ}
    (d : ProgramCursor (P := P) (L := L) root) :
    extend (P := P) (L := L) (.here : ProgramCursor (P := P) (L := L) root) d = d := rfl

/-- Canonical cursors are finite because Vegas syntax is linear. -/
@[reducible] noncomputable def instFintype :
    {Γ : VCtx P L} → (p : VegasCore P L Γ) →
      Fintype (ProgramCursor (P := P) (L := L) p)
  | _, .ret _ =>
      let e : ProgramCursor (P := P) (L := L) (.ret _) ≃ Unit :=
        { toFun := fun _ => ()
          invFun := fun _ => .here
          left_inv := by
            intro c
            cases c
            rfl
          right_inv := by
            intro u
            cases u
            rfl }
      Fintype.ofEquiv Unit e.symm
  | Γ, .letExpr x (b := b) e k =>
      let _ : Fintype (ProgramCursor (P := P) (L := L) k) := instFintype k
      let e : ProgramCursor (P := P) (L := L) (.letExpr x (b := b) e k) ≃
          Unit ⊕ ProgramCursor (P := P) (L := L) k :=
        { toFun := fun c =>
            match c with
            | .here => Sum.inl ()
            | .letExpr c => Sum.inr c
          invFun := fun s =>
            match s with
            | Sum.inl _ => .here
            | Sum.inr c => .letExpr c
          left_inv := by
            intro c
            cases c <;> rfl
          right_inv := by
            intro s
            cases s <;> rfl }
      Fintype.ofEquiv (Unit ⊕ ProgramCursor (P := P) (L := L) k) e.symm
  | Γ, .sample x (b := b) D k =>
      let _ : Fintype (ProgramCursor (P := P) (L := L) k) := instFintype k
      let e : ProgramCursor (P := P) (L := L) (.sample x (b := b) D k) ≃
          Unit ⊕ ProgramCursor (P := P) (L := L) k :=
        { toFun := fun c =>
            match c with
            | .here => Sum.inl ()
            | .sample c => Sum.inr c
          invFun := fun s =>
            match s with
            | Sum.inl _ => .here
            | Sum.inr c => .sample c
          left_inv := by
            intro c
            cases c <;> rfl
          right_inv := by
            intro s
            cases s <;> rfl }
      Fintype.ofEquiv (Unit ⊕ ProgramCursor (P := P) (L := L) k) e.symm
  | Γ, .commit x who (b := b) R k =>
      let _ : Fintype (ProgramCursor (P := P) (L := L) k) := instFintype k
      let e : ProgramCursor (P := P) (L := L) (.commit x who (b := b) R k) ≃
          Unit ⊕ ProgramCursor (P := P) (L := L) k :=
        { toFun := fun c =>
            match c with
            | .here => Sum.inl ()
            | .commit c => Sum.inr c
          invFun := fun s =>
            match s with
            | Sum.inl _ => .here
            | Sum.inr c => .commit c
          left_inv := by
            intro c
            cases c <;> rfl
          right_inv := by
            intro s
            cases s <;> rfl }
      Fintype.ofEquiv (Unit ⊕ ProgramCursor (P := P) (L := L) k) e.symm
  | Γ, .reveal y who x (b := b) hx k =>
      let _ : Fintype (ProgramCursor (P := P) (L := L) k) := instFintype k
      let e : ProgramCursor (P := P) (L := L) (.reveal y who x (b := b) hx k) ≃
          Unit ⊕ ProgramCursor (P := P) (L := L) k :=
        { toFun := fun c =>
            match c with
            | .here => Sum.inl ()
            | .reveal c => Sum.inr c
          invFun := fun s =>
            match s with
            | Sum.inl _ => .here
            | Sum.inr c => .reveal c
          left_inv := by
            intro c
            cases c <;> rfl
          right_inv := by
            intro s
            cases s <;> rfl }
      Fintype.ofEquiv (Unit ⊕ ProgramCursor (P := P) (L := L) k) e.symm

end ProgramCursor

/-! ## Cursor-based world data -/

/-- Data-bearing world state keyed by a canonical finite program cursor. This
is the finite-state carrier that should replace the older suffix-based
`CheckedWorldData` once the FOSG target is migrated. -/
structure CursorWorldData (g : WFProgram P L) where
  cursor : ProgramCursor (P := P) (L := L) g.prog
  env : VEnv L cursor.Γ

namespace CursorWorldData

def prog {g : WFProgram P L} (d : CursorWorldData (P := P) (L := L) g) :
    VegasCore P L d.cursor.Γ :=
  d.cursor.prog

def suffix {g : WFProgram P L} (d : CursorWorldData (P := P) (L := L) g) :
    ProgramSuffix g.prog d.prog :=
  d.cursor.toSuffix

/-- Local proof obligations for a cursor-keyed checked world. -/
def Valid {g : WFProgram P L} (d : CursorWorldData (P := P) (L := L) g) : Prop :=
  WFCtx d.cursor.Γ ∧ FreshBindings d.prog ∧ ViewScoped d.prog ∧
    NormalizedDists d.prog ∧ Legal d.prog

/-- Cursor-keyed world data is finite under finite value types. -/
@[reducible] noncomputable def instFintype
    (g : WFProgram P L) (LF : FiniteValuation L) :
    Fintype (CursorWorldData (P := P) (L := L) g) := by
  let _ : Fintype (ProgramCursor (P := P) (L := L) g.prog) :=
    ProgramCursor.instFintype (P := P) (L := L) g.prog
  have hEnv : ∀ c : ProgramCursor (P := P) (L := L) g.prog,
      Fintype (VEnv L c.Γ) := fun c => VEnv.instFintype LF
  let e :
      CursorWorldData (P := P) (L := L) g ≃
        Sigma (fun c : ProgramCursor (P := P) (L := L) g.prog =>
          VEnv L c.Γ) :=
    { toFun := fun d => ⟨d.cursor, d.env⟩
      invFun := fun d => { cursor := d.1, env := d.2 }
      left_inv := by
        intro d
        cases d
        rfl
      right_inv := by
        intro d
        cases d
        rfl }
  let _ : ∀ c : ProgramCursor (P := P) (L := L) g.prog,
      Fintype (VEnv L c.Γ) := hEnv
  exact Fintype.ofEquiv
    (Sigma (fun c : ProgramCursor (P := P) (L := L) g.prog => VEnv L c.Γ))
    e.symm

end CursorWorldData

/-- Checked worlds over the finite cursor-keyed carrier. This is the intended
finite world type for the final executable FOSG target. -/
abbrev CursorCheckedWorld (g : WFProgram P L) : Type :=
  {d : CursorWorldData (P := P) (L := L) g // d.Valid}

namespace CursorCheckedWorld

/-- Forget the cursor-keyed checked obligations to the raw runtime world. -/
def toWorld {g : WFProgram P L}
    (w : CursorCheckedWorld (P := P) (L := L) g) : World P L where
  Γ := w.1.cursor.Γ
  prog := w.1.prog
  env := w.1.env

/-- Terminality for the finite cursor-keyed checked-world carrier. -/
def terminal {g : WFProgram P L}
    (w : CursorCheckedWorld (P := P) (L := L) g) : Prop :=
  Vegas.FOSGBridge.terminal w.toWorld

/-- Active players for the finite cursor-keyed checked-world carrier. -/
def active {g : WFProgram P L}
    (w : CursorCheckedWorld (P := P) (L := L) g) : Finset P :=
  Vegas.FOSGBridge.active w.toWorld

/-- Broad-alphabet action availability for the finite cursor-keyed carrier. -/
def availableActions {g : WFProgram P L}
    (w : CursorCheckedWorld (P := P) (L := L) g) (who : P) :
    Set (Action (P := P) L who) :=
  Vegas.FOSGBridge.availableActions w.toWorld who

/-- Remaining operational syntax nodes at a finite cursor-keyed checked world. -/
def remainingSyntaxSteps {g : WFProgram P L}
    (w : CursorCheckedWorld (P := P) (L := L) g) : Nat :=
  syntaxSteps w.1.prog

theorem terminal_iff_remainingSyntaxSteps_eq_zero
    {g : WFProgram P L} {w : CursorCheckedWorld (P := P) (L := L) g} :
    w.terminal ↔ w.remainingSyntaxSteps = 0 := by
  cases w with
  | mk data valid =>
      cases data
      simp [terminal, remainingSyntaxSteps, toWorld, terminal_iff_syntaxSteps_eq_zero]

/-- The finite cursor-keyed checked-world carrier is finite under finite value
types. `Fintype.ofFinite` avoids requiring decidability of the proof-bearing
`Valid` predicate. -/
@[reducible] noncomputable def instFintype
    (g : WFProgram P L) (LF : FiniteValuation L) :
    Fintype (CursorCheckedWorld (P := P) (L := L) g) := by
  let _ : Fintype (CursorWorldData (P := P) (L := L) g) :=
    CursorWorldData.instFintype (P := P) (L := L) g LF
  exact Fintype.ofFinite (CursorCheckedWorld (P := P) (L := L) g)

/-- Initial state for the finite cursor-keyed checked-world carrier. -/
def initial (g : WFProgram P L) (hctx : WFCtx g.Γ) :
    CursorCheckedWorld (P := P) (L := L) g :=
  ⟨{ cursor := .here
     env := g.env },
    by
      exact ⟨hctx, g.wf.1, g.wf.2.2, g.normalized, g.legal⟩⟩

end CursorCheckedWorld

/-- Result carrier for cursor-recursive execution before reattaching the
`WFProgram` wrapper. -/
structure CursorRuntimeState {Γ₀ : VCtx P L} (root : VegasCore P L Γ₀) where
  cursor : ProgramCursor (P := P) (L := L) root
  env : VEnv L cursor.Γ
  valid : cursor.EndpointValid

namespace CursorRuntimeState

/-- Reattach a cursor runtime state to a fixed checked program. -/
def toChecked {g : WFProgram P L}
    (s : CursorRuntimeState (P := P) (L := L) g.prog) :
    CursorCheckedWorld (P := P) (L := L) g :=
  ⟨{ cursor := s.cursor, env := s.env },
    by
      simpa [CursorWorldData.Valid, CursorWorldData.prog,
        ProgramCursor.EndpointValid] using s.valid⟩

end CursorRuntimeState

/-! ## Program points

`CheckedWorld` carries proof fields needed by the FOSG structure. For
finiteness, the data-bearing part is smaller: a syntactic point in the fixed
program plus an environment for that point's context.
-/

/-- A typed syntactic continuation of a fixed root program. -/
structure ProgramPoint {Γ₀ : VCtx P L} (root : VegasCore P L Γ₀) where
  Γ : VCtx P L
  prog : VegasCore P L Γ
  suffix : ProgramSuffix root prog

/-- The data-bearing part of a checked world, before attaching local proof
obligations. -/
structure CheckedWorldData (g : WFProgram P L) where
  point : ProgramPoint (P := P) (L := L) g.prog
  env : VEnv L point.Γ

namespace CheckedWorldData

def prog {g : WFProgram P L} (d : CheckedWorldData (P := P) (L := L) g) :
    VegasCore P L d.point.Γ :=
  d.point.prog

def suffix {g : WFProgram P L} (d : CheckedWorldData (P := P) (L := L) g) :
    ProgramSuffix g.prog d.prog :=
  d.point.suffix

/-- Local proof obligations attached to a checked world. This predicate is
separated from `CheckedWorldData` so finiteness can be proved on the data
carrier first and then restricted to valid states. -/
def Valid {g : WFProgram P L} (d : CheckedWorldData (P := P) (L := L) g) : Prop :=
  WFCtx d.point.Γ ∧ FreshBindings d.prog ∧ ViewScoped d.prog ∧
    NormalizedDists d.prog ∧ Legal d.prog

end CheckedWorldData

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

/-- Embed the finite cursor-keyed carrier into the current suffix-based
`CheckedWorld` presentation. -/
def ofCursorChecked {g : WFProgram P L} {hctx : WFCtx g.Γ}
    (w : CursorCheckedWorld (P := P) (L := L) g) :
    CheckedWorld g hctx where
  Γ := w.1.cursor.Γ
  prog := w.1.prog
  env := w.1.env
  suffix := w.1.suffix
  wctx := w.2.1
  fresh := w.2.2.1
  viewScoped := w.2.2.2.1
  normalized := w.2.2.2.2.1
  legal := w.2.2.2.2.2

/-- Forget the proof obligations on a checked world. -/
def toData {g : WFProgram P L} {hctx : WFCtx g.Γ}
    (w : CheckedWorld g hctx) : CheckedWorldData (P := P) (L := L) g where
  point :=
    { Γ := w.Γ
      prog := w.prog
      suffix := w.suffix }
  env := w.env

/-- Reattach checked-world proof obligations to data. -/
def ofValid {g : WFProgram P L} {hctx : WFCtx g.Γ}
    (d : CheckedWorldData (P := P) (L := L) g)
    (h : d.Valid) : CheckedWorld g hctx where
  Γ := d.point.Γ
  prog := d.prog
  env := d.env
  suffix := d.suffix
  wctx := h.1
  fresh := h.2.1
  viewScoped := h.2.2.1
  normalized := h.2.2.2.1
  legal := h.2.2.2.2

/-- Checked worlds are exactly valid checked-world data. -/
def equivValidData {g : WFProgram P L} {hctx : WFCtx g.Γ} :
    CheckedWorld g hctx ≃
      {d : CheckedWorldData (P := P) (L := L) g // d.Valid} where
  toFun := fun w =>
    ⟨w.toData, by
      exact ⟨w.wctx, w.fresh, w.viewScoped, w.normalized, w.legal⟩⟩
  invFun := fun d => ofValid d.1 d.2
  left_inv := by
    intro w
    cases w
    rfl
  right_inv := by
    intro d
    cases d with
    | mk data valid =>
        apply Subtype.ext
        cases data
        rfl

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

/-- Remaining operational syntax nodes at a checked world. -/
def CheckedWorld.remainingSyntaxSteps {g : WFProgram P L} {hctx : WFCtx g.Γ}
    (w : CheckedWorld g hctx) : Nat :=
  syntaxSteps w.prog

theorem checkedTerminal_iff_remainingSyntaxSteps_eq_zero
    {g : WFProgram P L} {hctx : WFCtx g.Γ} {w : CheckedWorld g hctx} :
    checkedTerminal w ↔ w.remainingSyntaxSteps = 0 := by
  cases w
  simp [checkedTerminal, CheckedWorld.remainingSyntaxSteps, CheckedWorld.toWorld,
    terminal_iff_syntaxSteps_eq_zero]

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

/-- Joint actions over the program-local action alphabet. -/
abbrev ProgramJointAction (g : WFProgram P L) : Type :=
  GameTheory.JointAction
    (fun who : P => ProgramAction (P := P) (L := L) g.prog who)

/-- Erase a program-local joint action to the broad structural alphabet. -/
def ProgramJointAction.toAction {g : WFProgram P L}
    (a : ProgramJointAction (P := P) (L := L) g) : JointAction P L :=
  fun who => (a who).map ProgramAction.toAction

namespace CursorCheckedWorld

/-- Program-local action availability for the finite cursor-keyed carrier. At
a commit node, only the active owner may choose the current commit cursor paired
with a guard-legal value. -/
def availableProgramActions {g : WFProgram P L}
    (w : CursorCheckedWorld (P := P) (L := L) g) (who : P) :
    Set (ProgramAction (P := P) (L := L) g.prog who) :=
  {a | ProgramAction.toAction a ∈ w.availableActions who ∧
    ∃ (x : VarId) (owner : P) (b : L.Ty)
      (R : L.Expr ((x, b) :: eraseVCtx w.1.cursor.Γ) L.bool)
      (k : VegasCore P L ((x, .hidden owner b) :: w.1.cursor.Γ)),
      ∃ hprog : w.1.prog = VegasCore.commit x owner R k,
      ∃ howner : owner = who,
        by
          cases howner
          exact a.cursor =
            ProgramSuffix.commitCursor (P := P) (L := L)
              (by
                rw [← hprog]
                exact w.1.suffix)}

end CursorCheckedWorld

/-- FOSG joint-action legality for the cursor-keyed program-local alphabet. -/
abbrev CursorProgramJointActionLegal
    {g : WFProgram P L}
    (w : CursorCheckedWorld (P := P) (L := L) g)
    (a : ProgramJointAction (P := P) (L := L) g) : Prop :=
  GameTheory.JointActionLegal
    (fun who : P => ProgramAction (P := P) (L := L) g.prog who)
    CursorCheckedWorld.active
    CursorCheckedWorld.terminal
    CursorCheckedWorld.availableProgramActions
    w
    a

/-- Cursor-world program-local legality implies legality after erasing to the
broad structural action alphabet. -/
theorem CursorProgramJointActionLegal.toAction
    {g : WFProgram P L}
    {w : CursorCheckedWorld (P := P) (L := L) g}
    {a : ProgramJointAction (P := P) (L := L) g}
    (ha : CursorProgramJointActionLegal w a) :
    JointActionLegal w.toWorld (ProgramJointAction.toAction a) := by
  refine ⟨ha.1, ?_⟩
  intro i
  have hlocal := ha.2 i
  cases hai : a i with
  | none =>
      simpa [ProgramJointAction.toAction, hai, CursorProgramJointActionLegal,
        CursorCheckedWorld.active, CursorCheckedWorld.terminal] using hlocal
  | some ai =>
      have hpair : i ∈ w.active ∧ ai ∈ w.availableProgramActions i := by
        simpa [ProgramJointAction.toAction, hai, CursorProgramJointActionLegal] using hlocal
      have hbroad : i ∈ active w.toWorld ∧
          ProgramAction.toAction ai ∈ availableActions w.toWorld i := by
        refine ⟨?_, hpair.2.1⟩
        simpa [CursorCheckedWorld.active] using hpair.1
      simpa [ProgramJointAction.toAction, hai] using hbroad

/-- A program-local joint action where exactly `who` commits to `v` at the
current suffix endpoint. -/
noncomputable def commitProgramJointAction
    {g : WFProgram P L} {Γ : VCtx P L}
    {x : VarId} {who : P} {b : L.Ty}
    {R : L.Expr ((x, b) :: eraseVCtx Γ) L.bool}
    {k : VegasCore P L ((x, .hidden who b) :: Γ)}
    (suffix : ProgramSuffix g.prog (.commit x who R k))
    (v : L.Val b) : ProgramJointAction (P := P) (L := L) g :=
  fun i =>
    if h : i = who then
      by
        cases h
        exact some
          ({ cursor := ProgramSuffix.commitCursor (P := P) (L := L) suffix
             value := by
               rw [ProgramSuffix.ty_commitCursor (P := P) (L := L) suffix]
               exact v } :
            ProgramAction (P := P) (L := L) g.prog who)
    else
      none

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

/-- The committed value carried by a legal joint action at a Vegas commit node. -/
noncomputable def commitValueOfLegal
    {Γ : VCtx P L} {x : VarId} {who : P} {b : L.Ty}
    {R : L.Expr ((x, b) :: eraseVCtx Γ) L.bool}
    {k : VegasCore P L ((x, .hidden who b) :: Γ)}
    {env : VEnv L Γ} {a : JointAction P L}
    (ha : JointActionLegal
      ({ Γ := Γ, prog := VegasCore.commit x who R k, env := env } : World P L) a) :
    L.Val b :=
  Classical.choose (commit_value_of_legal (L := L) ha)

theorem commitValueOfLegal_action
    {Γ : VCtx P L} {x : VarId} {who : P} {b : L.Ty}
    {R : L.Expr ((x, b) :: eraseVCtx Γ) L.bool}
    {k : VegasCore P L ((x, .hidden who b) :: Γ)}
    {env : VEnv L Γ} {a : JointAction P L}
    (ha : JointActionLegal
      ({ Γ := Γ, prog := VegasCore.commit x who R k, env := env } : World P L) a) :
    a who = some (Sigma.mk b (commitValueOfLegal (L := L) ha)) :=
  (Classical.choose_spec (commit_value_of_legal (L := L) ha)).1

theorem commitValueOfLegal_guard
    {Γ : VCtx P L} {x : VarId} {who : P} {b : L.Ty}
    {R : L.Expr ((x, b) :: eraseVCtx Γ) L.bool}
    {k : VegasCore P L ((x, .hidden who b) :: Γ)}
    {env : VEnv L Γ} {a : JointAction P L}
    (ha : JointActionLegal
      ({ Γ := Γ, prog := VegasCore.commit x who R k, env := env } : World P L) a) :
    evalGuard (Player := P) (L := L) R
      (commitValueOfLegal (L := L) ha) (VEnv.eraseEnv env) = true :=
  (Classical.choose_spec (commit_value_of_legal (L := L) ha)).2

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

/-- Terminal cursor worlds have no active players. -/
theorem cursor_terminal_active_eq_empty
    {g : WFProgram P L}
    {w : CursorCheckedWorld (P := P) (L := L) g} :
    w.terminal → w.active = ∅ :=
  terminal_active_eq_empty

/-- Terminal cursor worlds admit no legal program-local joint action. -/
theorem cursor_terminal_no_program_legal
    {g : WFProgram P L}
    {w : CursorCheckedWorld (P := P) (L := L) g}
    {a : ProgramJointAction (P := P) (L := L) g} :
    w.terminal → ¬ CursorProgramJointActionLegal w a := by
  intro hterm hlegal
  exact hlegal.1 hterm

set_option linter.flexible false in
/-- Program-level `Legal` prevents deadlock for the cursor-keyed program-local
action alphabet. -/
theorem cursor_nonterminal_exists_program_legal
    {g : WFProgram P L}
    {w : CursorCheckedWorld (P := P) (L := L) g} :
    ¬ w.terminal →
      ∃ a : ProgramJointAction (P := P) (L := L) g,
        CursorProgramJointActionLegal w a := by
  intro hterm
  cases w with
  | mk data valid =>
      cases data with
      | mk cursor env =>
          rcases valid with ⟨wctx, fresh, viewScoped, normalized, legal⟩
          cases hprog : cursor.prog with
          | ret payoffs =>
              simp [CursorCheckedWorld.terminal, CursorCheckedWorld.toWorld,
                CursorWorldData.prog, terminal, hprog] at hterm
          | letExpr x e k =>
              refine ⟨GameTheory.FOSG.noopAction
                (fun who : P => ProgramAction (P := P) (L := L) g.prog who), ?_⟩
              refine ⟨by simp [CursorCheckedWorld.terminal, CursorCheckedWorld.toWorld,
                CursorWorldData.prog, terminal, hprog], ?_⟩
              intro i
              simp [GameTheory.FOSG.noopAction, CursorCheckedWorld.active,
                CursorCheckedWorld.toWorld, CursorWorldData.prog, active, hprog]
          | sample x D k =>
              refine ⟨GameTheory.FOSG.noopAction
                (fun who : P => ProgramAction (P := P) (L := L) g.prog who), ?_⟩
              refine ⟨by simp [CursorCheckedWorld.terminal, CursorCheckedWorld.toWorld,
                CursorWorldData.prog, terminal, hprog], ?_⟩
              intro i
              simp [GameTheory.FOSG.noopAction, CursorCheckedWorld.active,
                CursorCheckedWorld.toWorld, CursorWorldData.prog, active, hprog]
          | commit x who R k =>
              change Legal cursor.prog at legal
              rw [hprog] at legal
              rcases legal.1 (VEnv.eraseEnv env) with ⟨v, hv⟩
              let suffix : ProgramSuffix (P := P) (L := L) g.prog
                  (VegasCore.commit x who R k) := by
                rw [← hprog]
                exact cursor.toSuffix
              refine ⟨commitProgramJointAction (P := P) (L := L) suffix v, ?_⟩
              refine ⟨by simp [CursorCheckedWorld.terminal, CursorCheckedWorld.toWorld,
                CursorWorldData.prog, terminal, hprog], ?_⟩
              intro i
              by_cases hi : i = who
              · subst i
                simp [commitProgramJointAction, CursorCheckedWorld.active,
                  CursorCheckedWorld.toWorld, CursorWorldData.prog, active,
                  CursorCheckedWorld.availableProgramActions,
                  CursorCheckedWorld.availableActions, availableActions,
                  ProgramAction.toAction, ProgramSuffix.ty_commitCursor, hprog, hv]
                refine ⟨x, who, _, R, k, ?_, rfl, ?_⟩
                · exact ⟨rfl, rfl, rfl, HEq.rfl, HEq.rfl⟩
                · rfl
              · have hnone : commitProgramJointAction (P := P) (L := L) suffix v i = none := by
                    simp [commitProgramJointAction, hi]
                rw [hnone]
                simp [CursorCheckedWorld.active, CursorCheckedWorld.toWorld,
                  CursorWorldData.prog, active, hprog, hi]
          | reveal y who x hx k =>
              refine ⟨GameTheory.FOSG.noopAction
                (fun who : P => ProgramAction (P := P) (L := L) g.prog who), ?_⟩
              refine ⟨by simp [CursorCheckedWorld.terminal, CursorCheckedWorld.toWorld,
                CursorWorldData.prog, terminal, hprog], ?_⟩
              intro i
              simp [GameTheory.FOSG.noopAction, CursorCheckedWorld.active,
                CursorCheckedWorld.toWorld, CursorWorldData.prog, active, hprog]

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
          let v := commitValueOfLegal (L := L) ha
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

/-- Cursor-recursive transition over the erased broad action alphabet.

The recursion follows the cursor frames until the endpoint is definitionally at
the current syntax node. This is the transport-avoiding core used by the
cursor-keyed FOSG target. -/
noncomputable def cursorTransitionState
    {Γ₀ : VCtx P L} :
    {root : VegasCore P L Γ₀} →
    (c : ProgramCursor (P := P) (L := L) root) →
    (env : VEnv L c.Γ) →
    (valid : c.EndpointValid) →
    (a : JointAction P L) →
    (ha : JointActionLegal
      ({ Γ := c.Γ, prog := c.prog, env := env } : World P L) a) →
    PMF (CursorRuntimeState (P := P) (L := L) root)
  | .ret payoffs, .here, env, valid, a, ha =>
      False.elim (ha.1 (by simp [ProgramCursor.prog, terminal]))
  | .letExpr x e k, .here, env, valid, _a, _ha =>
      let wctx := valid.1
      let fresh := valid.2.1
      let viewScoped := valid.2.2.1
      let normalized := valid.2.2.2.1
      let legal := valid.2.2.2.2
      PMF.pure
        { cursor := ProgramCursor.letExpr ProgramCursor.here
          env := VEnv.cons (Player := P) (L := L) (x := x) (τ := .pub _)
            (L.eval e (VEnv.erasePubEnv env)) env
          valid := ⟨WFCtx.cons fresh.1 wctx, fresh.2, viewScoped, normalized, legal⟩ }
  | .sample x D k, .here, env, valid, _a, _ha =>
      let wctx := valid.1
      let fresh := valid.2.1
      let viewScoped := valid.2.2.1
      let normalized := valid.2.2.2.1
      let legal := valid.2.2.2.2
      PMF.map
        (fun v =>
          { cursor := ProgramCursor.sample ProgramCursor.here
            env := VEnv.cons (Player := P) (L := L) (x := x) (τ := .pub _)
              v env
            valid := ⟨WFCtx.cons fresh.1 wctx, fresh.2, viewScoped,
              normalized.2, legal⟩ })
        ((L.evalDist D (VEnv.eraseSampleEnv env)).toPMF (normalized.1 env))
  | .commit x who R k, .here, env, valid, a, ha =>
      let wctx := valid.1
      let fresh := valid.2.1
      let viewScoped := valid.2.2.1
      let normalized := valid.2.2.2.1
      let legal := valid.2.2.2.2
      let v := commitValueOfLegal (L := L) ha
      PMF.pure
        { cursor := ProgramCursor.commit ProgramCursor.here
          env := VEnv.cons (Player := P) (L := L) (x := x)
            (τ := .hidden who _) v env
          valid := ⟨WFCtx.cons fresh.1 wctx, fresh.2, viewScoped.2,
            normalized, legal.2⟩ }
  | .reveal y who x hx k, .here, env, valid, _a, _ha =>
      let wctx := valid.1
      let fresh := valid.2.1
      let viewScoped := valid.2.2.1
      let normalized := valid.2.2.2.1
      let legal := valid.2.2.2.2
      PMF.pure
        { cursor := ProgramCursor.reveal ProgramCursor.here
          env := VEnv.cons (Player := P) (L := L) (x := y) (τ := .pub _)
            (env x (.hidden who _) hx) env
          valid := ⟨WFCtx.cons fresh.1 wctx, fresh.2, viewScoped,
            normalized, legal⟩ }
  | .letExpr x e k, .letExpr c, env, valid, a, ha =>
      PMF.map
        (fun (s : CursorRuntimeState (P := P) (L := L) k) =>
          { cursor := ProgramCursor.letExpr s.cursor
            env := s.env
            valid := by simpa [ProgramCursor.EndpointValid] using s.valid })
        (cursorTransitionState c env
          (by simpa [ProgramCursor.EndpointValid] using valid) a
          (by simpa [ProgramCursor.EndpointValid] using ha))
  | .sample x D k, .sample c, env, valid, a, ha =>
      PMF.map
        (fun (s : CursorRuntimeState (P := P) (L := L) k) =>
          { cursor := ProgramCursor.sample s.cursor
            env := s.env
            valid := by simpa [ProgramCursor.EndpointValid] using s.valid })
        (cursorTransitionState c env
          (by simpa [ProgramCursor.EndpointValid] using valid) a
          (by simpa [ProgramCursor.EndpointValid] using ha))
  | .commit x who R k, .commit c, env, valid, a, ha =>
      PMF.map
        (fun (s : CursorRuntimeState (P := P) (L := L) k) =>
          { cursor := ProgramCursor.commit s.cursor
            env := s.env
            valid := by simpa [ProgramCursor.EndpointValid] using s.valid })
        (cursorTransitionState c env
          (by simpa [ProgramCursor.EndpointValid] using valid) a
          (by simpa [ProgramCursor.EndpointValid] using ha))
  | .reveal y who x hx k, .reveal c, env, valid, a, ha =>
      PMF.map
        (fun (s : CursorRuntimeState (P := P) (L := L) k) =>
          { cursor := ProgramCursor.reveal s.cursor
            env := s.env
            valid := by simpa [ProgramCursor.EndpointValid] using s.valid })
        (cursorTransitionState c env
          (by simpa [ProgramCursor.EndpointValid] using valid) a
          (by simpa [ProgramCursor.EndpointValid] using ha))

/-- Cursor-keyed transition over program-local actions. -/
noncomputable def cursorProgramTransition
    {g : WFProgram P L}
    (w : CursorCheckedWorld (P := P) (L := L) g)
    (a : {a : ProgramJointAction (P := P) (L := L) g //
      CursorProgramJointActionLegal w a}) :
    PMF (CursorCheckedWorld (P := P) (L := L) g) :=
  PMF.map CursorRuntimeState.toChecked
    (cursorTransitionState w.1.cursor w.1.env
      (by
        simpa [CursorWorldData.Valid, CursorWorldData.prog,
          ProgramCursor.EndpointValid] using w.2)
      (ProgramJointAction.toAction a.1)
      (CursorProgramJointActionLegal.toAction a.2))

set_option linter.flexible false in
/-- Every supported cursor-recursive transition consumes exactly one
operational syntax node. -/
theorem cursorTransitionState_remainingSyntaxSteps
    {Γ₀ : VCtx P L} :
    {root : VegasCore P L Γ₀} →
    (c : ProgramCursor (P := P) (L := L) root) →
    (env : VEnv L c.Γ) →
    (valid : c.EndpointValid) →
    (a : JointAction P L) →
    (ha : JointActionLegal
      ({ Γ := c.Γ, prog := c.prog, env := env } : World P L) a) →
    (dst : CursorRuntimeState (P := P) (L := L) root) →
    cursorTransitionState c env valid a ha dst ≠ 0 →
      syntaxSteps dst.cursor.prog + 1 = syntaxSteps c.prog
  | .ret payoffs, .here, env, valid, a, ha, dst, _hsupp =>
      False.elim (ha.1 (by simp [ProgramCursor.prog, terminal]))
  | .letExpr x e k, .here, env, valid, a, ha, dst, hsupp => by
      simp [cursorTransitionState, ProgramCursor.prog, syntaxSteps] at hsupp ⊢
      subst dst
      rfl
  | .sample x D k, .here, env, valid, a, ha, dst, hsupp => by
      simp [cursorTransitionState, ProgramCursor.prog, syntaxSteps] at hsupp ⊢
      rcases hsupp with ⟨v, hdst, _hv⟩
      subst dst
      rfl
  | .commit x who R k, .here, env, valid, a, ha, dst, hsupp => by
      simp [cursorTransitionState, ProgramCursor.prog, syntaxSteps] at hsupp ⊢
      subst dst
      rfl
  | .reveal y who x hx k, .here, env, valid, a, ha, dst, hsupp => by
      simp [cursorTransitionState, ProgramCursor.prog, syntaxSteps] at hsupp ⊢
      subst dst
      rfl
  | .letExpr x e k, .letExpr c, env, valid, a, ha, dst, hsupp => by
      simp [cursorTransitionState, ProgramCursor.prog] at hsupp ⊢
      rcases hsupp with ⟨s, hdst, hsuppS⟩
      have hrec := cursorTransitionState_remainingSyntaxSteps c env
        (by simpa [ProgramCursor.EndpointValid] using valid) a
        (by simpa [ProgramCursor.EndpointValid] using ha) s hsuppS
      subst dst
      exact hrec
  | .sample x D k, .sample c, env, valid, a, ha, dst, hsupp => by
      simp [cursorTransitionState, ProgramCursor.prog] at hsupp ⊢
      rcases hsupp with ⟨s, hdst, hsuppS⟩
      have hrec := cursorTransitionState_remainingSyntaxSteps c env
        (by simpa [ProgramCursor.EndpointValid] using valid) a
        (by simpa [ProgramCursor.EndpointValid] using ha) s hsuppS
      subst dst
      exact hrec
  | .commit x who R k, .commit c, env, valid, a, ha, dst, hsupp => by
      simp [cursorTransitionState, ProgramCursor.prog] at hsupp ⊢
      rcases hsupp with ⟨s, hdst, hsuppS⟩
      have hrec := cursorTransitionState_remainingSyntaxSteps c env
        (by simpa [ProgramCursor.EndpointValid] using valid) a
        (by simpa [ProgramCursor.EndpointValid] using ha) s hsuppS
      subst dst
      exact hrec
  | .reveal y who x hx k, .reveal c, env, valid, a, ha, dst, hsupp => by
      simp [cursorTransitionState, ProgramCursor.prog] at hsupp ⊢
      rcases hsupp with ⟨s, hdst, hsuppS⟩
      have hrec := cursorTransitionState_remainingSyntaxSteps c env
        (by simpa [ProgramCursor.EndpointValid] using valid) a
        (by simpa [ProgramCursor.EndpointValid] using ha) s hsuppS
      subst dst
      exact hrec

set_option linter.flexible false in
/-- The cursor-keyed program transition consumes exactly one operational syntax
node on every supported transition. -/
theorem cursorProgramTransition_remainingSyntaxSteps
    {g : WFProgram P L}
    (w : CursorCheckedWorld (P := P) (L := L) g)
    (a : {a : ProgramJointAction (P := P) (L := L) g //
      CursorProgramJointActionLegal w a})
    (dst : CursorCheckedWorld (P := P) (L := L) g)
    (hsupp : cursorProgramTransition w a dst ≠ 0) :
    dst.remainingSyntaxSteps + 1 = w.remainingSyntaxSteps := by
  rw [cursorProgramTransition] at hsupp
  rcases (PMF.mem_support_map_iff _ _ _).mp (by
      rw [PMF.mem_support_iff]
      exact hsupp) with ⟨s, hsuppS, hdst⟩
  subst dst
  have hstep :=
    cursorTransitionState_remainingSyntaxSteps
      (P := P) (L := L) w.1.cursor w.1.env
      (by
        simpa [CursorWorldData.Valid, CursorWorldData.prog,
          ProgramCursor.EndpointValid] using w.2)
      (ProgramJointAction.toAction a.1)
      (CursorProgramJointActionLegal.toAction a.2) s
      (by
        rw [PMF.mem_support_iff] at hsuppS
        exact hsuppS)
  simpa [CursorCheckedWorld.remainingSyntaxSteps, CursorRuntimeState.toChecked,
    CursorWorldData.prog] using hstep

set_option linter.flexible false in
/-- Every supported checked transition consumes exactly one operational syntax
node. -/
theorem checkedTransition_remainingSyntaxSteps
    {g : WFProgram P L} {hctx : WFCtx g.Γ}
    (w : CheckedWorld g hctx)
    (a : {a : JointAction P L // CheckedJointActionLegal w a})
    (dst : CheckedWorld g hctx)
    (hsupp : checkedTransition w a dst ≠ 0) :
    dst.remainingSyntaxSteps + 1 = w.remainingSyntaxSteps := by
  cases w with
  | mk Γ prog env suffix wctx fresh viewScoped normalized legal =>
      cases prog with
      | ret payoffs =>
          exact False.elim (a.2.1 (by simp [checkedTerminal, CheckedWorld.toWorld, terminal]))
      | letExpr x e k =>
          simp [checkedTransition, CheckedWorld.remainingSyntaxSteps, syntaxSteps] at hsupp ⊢
          subst dst
          rfl
      | sample x D k =>
          simp [checkedTransition, CheckedWorld.remainingSyntaxSteps, syntaxSteps] at hsupp ⊢
          rcases hsupp with ⟨v, hdst, _hv⟩
          subst dst
          rfl
      | commit x who R k =>
          simp [checkedTransition, CheckedWorld.remainingSyntaxSteps, syntaxSteps] at hsupp ⊢
          subst dst
          rfl
      | reveal y who x hx k =>
          simp [checkedTransition, CheckedWorld.remainingSyntaxSteps, syntaxSteps] at hsupp ⊢
          subst dst
          rfl

def rewardOnEnteringRet
    {g : WFProgram P L} {hctx : WFCtx g.Γ}
    (_w : CheckedWorld g hctx)
    (_a : {a : JointAction P L // CheckedJointActionLegal _w a})
    (w' : CheckedWorld g hctx) (who : P) : ℝ :=
  match w'.prog with
  | .ret payoffs => (evalPayoffs payoffs w'.env who : ℝ)
  | _ => 0

/-- Reward over cursor-keyed program-local actions. Rewards are paid when a
transition enters a `ret` continuation. -/
def rewardOnEnteringRetCursor
    {g : WFProgram P L}
    (_w : CursorCheckedWorld (P := P) (L := L) g)
    (_a : {a : ProgramJointAction (P := P) (L := L) g //
      CursorProgramJointActionLegal _w a})
    (w' : CursorCheckedWorld (P := P) (L := L) g) (who : P) : ℝ :=
  match w'.1.prog with
  | .ret payoffs => (evalPayoffs payoffs w'.1.env who : ℝ)
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

def publicObsOfCursorWorld {g : WFProgram P L} {hctx : WFCtx g.Γ}
    (w : CursorCheckedWorld (P := P) (L := L) g) : PublicObs g hctx where
  Γ := w.1.cursor.Γ
  prog := w.1.prog
  suffix := w.1.suffix
  env := VEnv.toPub w.1.env

def privateObsOfCursorWorld {g : WFProgram P L}
    (who : P) (w : CursorCheckedWorld (P := P) (L := L) g) :
    PrivateObs P L who where
  Γ := w.1.cursor.Γ
  env := VEnv.toView who w.1.env

/-- The private observation's stored structured view is exactly the
strategy-facing erased view after erasure. -/
theorem privateObsOfWorld_eraseEnv
    {g : WFProgram P L} {hctx : WFCtx g.Γ}
    (who : P) (w : CheckedWorld g hctx) :
    VEnv.eraseEnv (privateObsOfWorld who w).env =
      projectViewEnv who (VEnv.eraseEnv w.env) := by
  exact (projectViewEnv_eraseEnv_eq_toView (who := who) w.wctx w.env).symm

/-- Cursor-world variant of `privateObsOfWorld_eraseEnv`. -/
theorem privateObsOfCursorWorld_eraseEnv
    {g : WFProgram P L}
    (who : P) (w : CursorCheckedWorld (P := P) (L := L) g) :
    VEnv.eraseEnv (privateObsOfCursorWorld who w).env =
      projectViewEnv who (VEnv.eraseEnv w.1.env) := by
  exact (projectViewEnv_eraseEnv_eq_toView (who := who) w.2.1 w.1.env).symm

/-- Cursor-keyed observation-preserving FOSG over the program-local action
alphabet.

This is the finite executable FOSG target for program-action strategy and
equilibrium transport. -/
noncomputable def observedProgramFOSG (g : WFProgram P L) (hctx : WFCtx g.Γ) :
    GameTheory.FOSG P (CursorCheckedWorld (P := P) (L := L) g)
      (fun who : P => ProgramAction (P := P) (L := L) g.prog who)
      (fun who : P => PrivateObs P L who)
      (PublicObs g hctx) where
  init := CursorCheckedWorld.initial g hctx
  active := CursorCheckedWorld.active
  availableActions := CursorCheckedWorld.availableProgramActions
  terminal := CursorCheckedWorld.terminal
  transition := cursorProgramTransition
  reward := rewardOnEnteringRetCursor
  privObs := fun who _ _ w' => privateObsOfCursorWorld who w'
  pubObs := fun _ _ w' => publicObsOfCursorWorld w'
  terminal_active_eq_empty := by
    intro w hterm
    exact cursor_terminal_active_eq_empty hterm
  terminal_no_legal := by
    intro w a hterm
    exact cursor_terminal_no_program_legal hterm
  nonterminal_exists_legal := by
    intro w hterm
    exact cursor_nonterminal_exists_program_legal hterm

/-- Finite-world helper for `observedProgramFOSG`. -/
@[reducible] noncomputable def observedProgramFOSG.instFintypeWorld
    (g : WFProgram P L) (_hctx : WFCtx g.Γ) (LF : FiniteValuation L) :
    Fintype (CursorCheckedWorld (P := P) (L := L) g) :=
  CursorCheckedWorld.instFintype (P := P) (L := L) g LF

/-- Per-player finite action helper for `observedProgramFOSG`. -/
@[reducible] noncomputable def observedProgramFOSG.instFintypeAction
    (g : WFProgram P L) (_hctx : WFCtx g.Γ) (LF : FiniteValuation L)
    (who : P) :
    Fintype (ProgramAction (P := P) (L := L) g.prog who) :=
  ProgramAction.instFintype (P := P) (L := L) LF g.prog who

/-- Per-player action equality helper for `observedProgramFOSG`. -/
@[reducible] noncomputable def observedProgramFOSG.instDecidableEqAction
    (g : WFProgram P L) (_hctx : WFCtx g.Γ) (who : P) :
    DecidableEq (ProgramAction (P := P) (L := L) g.prog who) :=
  ProgramAction.instDecidableEq (P := P) (L := L) g.prog who

/-- Per-player optional-action finite helper for FOSG execution APIs. -/
@[reducible] noncomputable def observedProgramFOSG.instFintypeOptionAction
    (g : WFProgram P L) (hctx : WFCtx g.Γ) (LF : FiniteValuation L)
    (who : P) :
    Fintype (Option (ProgramAction (P := P) (L := L) g.prog who)) := by
  let _ : Fintype (ProgramAction (P := P) (L := L) g.prog who) :=
    observedProgramFOSG.instFintypeAction (P := P) (L := L) g hctx LF who
  infer_instance

/-- Terminal decidability helper for FOSG execution APIs. -/
@[reducible] noncomputable def observedProgramFOSG.instDecidablePredTerminal
    (g : WFProgram P L) (hctx : WFCtx g.Γ) :
    DecidablePred (observedProgramFOSG g hctx).terminal :=
  Classical.decPred _

/-- Along any chained realized path in `observedProgramFOSG`, elapsed history
length plus remaining syntax steps is constant. -/
theorem observedProgramFOSG_stepChain_remainingSyntaxSteps
    (g : WFProgram P L) (hctx : WFCtx g.Γ)
    (w : CursorCheckedWorld (P := P) (L := L) g)
    {es : List (observedProgramFOSG g hctx).Step}
    (hchain : (observedProgramFOSG g hctx).StepChainFrom w es) :
    ((observedProgramFOSG g hctx).lastStateFrom w es).remainingSyntaxSteps +
        es.length = w.remainingSyntaxSteps := by
  induction es generalizing w with
  | nil =>
      simp [GameTheory.FOSG.lastStateFrom]
  | cons e es ih =>
      rcases hchain with ⟨hsrc, htail⟩
      subst hsrc
      have hdec :
          e.dst.remainingSyntaxSteps + 1 = e.src.remainingSyntaxSteps := by
        simpa [observedProgramFOSG] using
          cursorProgramTransition_remainingSyntaxSteps
            (P := P) (L := L) (g := g)
            e.src e.act e.dst e.support
      have htailInv := ih (w := e.dst) htail
      simp [GameTheory.FOSG.lastStateFrom] at htailInv ⊢
      omega

/-- For every realized history of the cursor-world target, elapsed length plus
remaining syntax steps is the source program's syntax-step bound. -/
theorem observedProgramFOSG_history_remainingSyntaxSteps
    (g : WFProgram P L) (hctx : WFCtx g.Γ)
    (h : (observedProgramFOSG g hctx).History) :
    h.lastState.remainingSyntaxSteps + h.steps.length = syntaxSteps g.prog := by
  simpa [GameTheory.FOSG.History.lastState, observedProgramFOSG,
    CursorCheckedWorld.remainingSyntaxSteps, CursorWorldData.prog] using
    observedProgramFOSG_stepChain_remainingSyntaxSteps
      (P := P) (L := L) g hctx (CursorCheckedWorld.initial g hctx) h.chain

/-- The cursor-world observed program FOSG is bounded by the number of
operational syntax nodes in the source Vegas program. -/
theorem observedProgramFOSG_boundedHorizon
    (g : WFProgram P L) (hctx : WFCtx g.Γ) :
    (observedProgramFOSG g hctx).BoundedHorizon (syntaxSteps g.prog) := by
  intro h hlen
  have hinv := observedProgramFOSG_history_remainingSyntaxSteps
    (P := P) (L := L) g hctx h
  rw [hlen] at hinv
  have hzero : h.lastState.remainingSyntaxSteps = 0 := by
    omega
  exact (CursorCheckedWorld.terminal_iff_remainingSyntaxSteps_eq_zero
    (P := P) (L := L) (g := g) (w := h.lastState)).2 hzero

/-- Finite-history helper for the cursor-world observed FOSG. -/
@[reducible] noncomputable def observedProgramFOSG.instFintypeHistory
    (g : WFProgram P L) (hctx : WFCtx g.Γ) (LF : FiniteValuation L)
    [Fintype P] :
    Fintype (observedProgramFOSG g hctx).History := by
  letI : Fintype (CursorCheckedWorld (P := P) (L := L) g) :=
    observedProgramFOSG.instFintypeWorld (P := P) (L := L) g hctx LF
  letI : ∀ who : P,
      Fintype (Option (ProgramAction (P := P) (L := L) g.prog who)) :=
    fun who =>
      observedProgramFOSG.instFintypeOptionAction
        (P := P) (L := L) g hctx LF who
  exact GameTheory.FOSG.historyFintypeOfBoundedHorizon
    (G := observedProgramFOSG (P := P) (L := L) g hctx)
    (observedProgramFOSG_boundedHorizon (P := P) (L := L) g hctx)

/-- The bounded run distribution used by `observedProgramKernelGame`, with the
finite execution instances fixed by `FiniteValuation`. -/
noncomputable def observedProgramRunDist
    (g : WFProgram P L) (hctx : WFCtx g.Γ) (LF : FiniteValuation L)
    [Fintype P]
    (σ : (observedProgramFOSG g hctx).LegalBehavioralProfile) :
    PMF (observedProgramFOSG g hctx).History := by
  letI : Fintype (CursorCheckedWorld (P := P) (L := L) g) :=
    observedProgramFOSG.instFintypeWorld (P := P) (L := L) g hctx LF
  letI : ∀ who : P,
      Fintype (Option (ProgramAction (P := P) (L := L) g.prog who)) :=
    fun who =>
      observedProgramFOSG.instFintypeOptionAction
        (P := P) (L := L) g hctx LF who
  letI : DecidablePred (observedProgramFOSG g hctx).terminal :=
    observedProgramFOSG.instDecidablePredTerminal (P := P) (L := L) g hctx
  exact (observedProgramFOSG g hctx).runDist (syntaxSteps g.prog) σ

/-- Compile the cursor-world observed FOSG to a finite `KernelGame` through
GameTheory's bounded-horizon route. -/
noncomputable def observedProgramKernelGame
    (g : WFProgram P L) (hctx : WFCtx g.Γ) (LF : FiniteValuation L)
    [Fintype P] :
    KernelGame P := by
  letI : Fintype (CursorCheckedWorld (P := P) (L := L) g) :=
    observedProgramFOSG.instFintypeWorld (P := P) (L := L) g hctx LF
  letI : ∀ who : P,
      Fintype (Option (ProgramAction (P := P) (L := L) g.prog who)) :=
    fun who =>
      observedProgramFOSG.instFintypeOptionAction
        (P := P) (L := L) g hctx LF who
  letI : DecidablePred (observedProgramFOSG g hctx).terminal :=
    observedProgramFOSG.instDecidablePredTerminal (P := P) (L := L) g hctx
  letI : Fintype (observedProgramFOSG g hctx).History :=
    observedProgramFOSG.instFintypeHistory (P := P) (L := L) g hctx LF
  exact (observedProgramFOSG g hctx).toKernelGameOfBoundedHorizon
    (observedProgramFOSG_boundedHorizon (P := P) (L := L) g hctx)

@[simp] theorem observedProgramKernelGame_outcomeKernel
    (g : WFProgram P L) (hctx : WFCtx g.Γ) (LF : FiniteValuation L)
    [Fintype P]
    (σ : (observedProgramFOSG g hctx).LegalBehavioralProfile) :
    (observedProgramKernelGame (P := P) (L := L) g hctx LF).outcomeKernel σ =
      observedProgramRunDist (P := P) (L := L) g hctx LF σ := by
  letI : Fintype (CursorCheckedWorld (P := P) (L := L) g) :=
    observedProgramFOSG.instFintypeWorld (P := P) (L := L) g hctx LF
  letI : ∀ who : P,
      Fintype (Option (ProgramAction (P := P) (L := L) g.prog who)) :=
    fun who =>
      observedProgramFOSG.instFintypeOptionAction
        (P := P) (L := L) g hctx LF who
  letI : DecidablePred (observedProgramFOSG g hctx).terminal :=
    observedProgramFOSG.instDecidablePredTerminal (P := P) (L := L) g hctx
  letI : Fintype (observedProgramFOSG g hctx).History :=
    observedProgramFOSG.instFintypeHistory (P := P) (L := L) g hctx LF
  simpa [observedProgramKernelGame, observedProgramRunDist] using
    (GameTheory.FOSG.toKernelGameOfBoundedHorizon_outcomeKernel
      (G := observedProgramFOSG (P := P) (L := L) g hctx)
      (observedProgramFOSG_boundedHorizon (P := P) (L := L) g hctx) σ)

/-- Broad-action FOSG control-flow object that preserves the public protocol
location and each player's local Vegas view at every step.

This is retained for observation-history lemmas over the structural action
alphabet. The program-action compiler target is `observedProgramFOSG`.
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

/-- Observation events extracted from the final program-action FOSG information
state. -/
noncomputable def programObservationEvents
    (g : WFProgram P L) (hctx : WFCtx g.Γ) (who : P)
    (s : (observedProgramFOSG g hctx).InfoState who) :
    List (PrivateObs P L who × PublicObs g hctx) :=
  s.filterMap
    (GameTheory.FOSG.PlayerEvent.observationPart
      (G := observedProgramFOSG g hctx) (i := who))

noncomputable def programLatestObservation?
    (g : WFProgram P L) (hctx : WFCtx g.Γ) (who : P)
    (s : (observedProgramFOSG g hctx).InfoState who) :
    Option (PrivateObs P L who × PublicObs g hctx) :=
  last? (programObservationEvents g hctx who s)

@[simp] theorem programObservationEvents_nil
    (g : WFProgram P L) (hctx : WFCtx g.Γ) (who : P) :
    programObservationEvents g hctx who [] = [] := rfl

@[simp] theorem programLatestObservation?_nil
    (g : WFProgram P L) (hctx : WFCtx g.Γ) (who : P) :
    programLatestObservation? g hctx who [] = none := rfl

theorem programLatestObservation?_append_obs
    (g : WFProgram P L) (hctx : WFCtx g.Γ) (who : P)
    (s : (observedProgramFOSG g hctx).InfoState who)
    (priv : PrivateObs P L who) (pub : PublicObs g hctx) :
    programLatestObservation? g hctx who
      (s ++ [GameTheory.FOSG.PlayerEvent.obs priv pub]) = some (priv, pub) := by
  simp [programLatestObservation?, programObservationEvents]

theorem programLatestObservation?_append_act_obs
    (g : WFProgram P L) (hctx : WFCtx g.Γ) (who : P)
    (s : (observedProgramFOSG g hctx).InfoState who)
    (a : ProgramAction (P := P) (L := L) g.prog who)
    (priv : PrivateObs P L who) (pub : PublicObs g hctx) :
    programLatestObservation? g hctx who
      (s ++ [GameTheory.FOSG.PlayerEvent.act a,
        GameTheory.FOSG.PlayerEvent.obs priv pub]) = some (priv, pub) := by
  simp [programLatestObservation?, programObservationEvents]

/-- Extending a program-action FOSG history records the destination cursor
world's Vegas view/public state as the latest information-state observation. -/
theorem programLatestObservation?_history_snoc
    (g : WFProgram P L) (hctx : WFCtx g.Γ) (who : P)
    (h : (observedProgramFOSG g hctx).History)
    (a : (observedProgramFOSG g hctx).LegalAction h.lastState)
    (dst : CursorCheckedWorld (P := P) (L := L) g)
    (support : (observedProgramFOSG g hctx).transition h.lastState a dst ≠ 0) :
    programLatestObservation? g hctx who ((h.snoc a dst support).playerView who) =
      some (privateObsOfCursorWorld who dst, publicObsOfCursorWorld dst) := by
  rw [GameTheory.FOSG.History.playerView_snoc]
  let e : (observedProgramFOSG g hctx).Step :=
    { src := h.lastState, act := a, dst := dst, support := support }
  change programLatestObservation? g hctx who (h.playerView who ++ e.playerView who) =
    some (privateObsOfCursorWorld who dst, publicObsOfCursorWorld dst)
  cases hact : e.ownAction? who with
  | none =>
      rw [GameTheory.FOSG.Step.playerView_of_none e who hact]
      simpa [e, observedProgramFOSG] using
        programLatestObservation?_append_obs g hctx who (h.playerView who)
          (privateObsOfCursorWorld who dst) (publicObsOfCursorWorld dst)
  | some ai =>
      rw [GameTheory.FOSG.Step.playerView_of_some e who hact]
      simpa [e, observedProgramFOSG] using
        programLatestObservation?_append_act_obs g hctx who (h.playerView who) ai
          (privateObsOfCursorWorld who dst) (publicObsOfCursorWorld dst)

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

/-- Program-action variant of `moveAtCursor`, targeting the finite
`observedProgramFOSG` action alphabet. -/
noncomputable def moveAtProgramCursor
    (g : WFProgram P L) (_hctx : WFCtx g.Γ)
    (σ : LegalProgramBehavioralProfile g)
    (who : P)
    {Γ : VCtx P L} {p : VegasCore P L Γ}
    (suffix : ProgramSuffix g.prog p)
    (view : ViewEnv (P := P) (L := L) who Γ) :
    PMF (Option (ProgramAction (P := P) (L := L) g.prog who)) :=
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
          exact PMF.map
            (fun v => some
              ({ cursor := ProgramSuffix.commitCursor (P := P) (L := L) suffix
                 value := by
                   rw [ProgramSuffix.ty_commitCursor (P := P) (L := L) suffix]
                   exact v } :
                ProgramAction (P := P) (L := L) g.prog who))
            (d.toPMF hd)
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

noncomputable def moveAtCursorWorld
    (g : WFProgram P L) (hctx : WFCtx g.Γ)
    (σ : LegalProgramBehavioralProfile g)
    (who : P) (w : CursorCheckedWorld (P := P) (L := L) g) :
    PMF (Option (ProgramAction (P := P) (L := L) g.prog who)) :=
  moveAtProgramCursor g hctx σ who w.1.suffix
    (projectViewEnv who (VEnv.eraseEnv w.1.env))

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

/-- Program-action observation lookup for the final `observedProgramFOSG`
target. -/
noncomputable def moveAtProgramObservation?
    (g : WFProgram P L) (hctx : WFCtx g.Γ)
    (σ : LegalProgramBehavioralProfile g)
    (who : P)
    (obs : PrivateObs P L who × PublicObs g hctx) :
    PMF (Option (ProgramAction (P := P) (L := L) g.prog who)) := by
  let priv := obs.1
  let pub := obs.2
  by_cases hΓ : priv.Γ = pub.Γ
  · exact moveAtProgramCursor g hctx σ who pub.suffix (hΓ ▸ VEnv.eraseEnv priv.env)
  · exact PMF.pure none

theorem moveAtProgramObservation?_of_cursorWorld
    (g : WFProgram P L) (hctx : WFCtx g.Γ)
    (σ : LegalProgramBehavioralProfile g)
    (who : P) (w : CursorCheckedWorld (P := P) (L := L) g) :
    moveAtProgramObservation? g hctx σ who
      (privateObsOfCursorWorld who w, publicObsOfCursorWorld w) =
      moveAtCursorWorld g hctx σ who w := by
  unfold moveAtProgramObservation? moveAtCursorWorld
  simp only [dite_eq_ite]
  rw [privateObsOfCursorWorld_eraseEnv]
  simp only [publicObsOfCursorWorld]
  simp [privateObsOfCursorWorld]

/-- Raw behavioral profile induced by a Vegas legal behavioral profile for the
final program-action FOSG. The `Candidate` suffix is intentional until the
support-availability theorem below this layer is completed. -/
noncomputable def programBehavioralProfileCandidate
    (g : WFProgram P L) (hctx : WFCtx g.Γ)
    (σ : LegalProgramBehavioralProfile g) :
    GameTheory.FOSG.BehavioralProfile (observedProgramFOSG g hctx) :=
  fun who s =>
    match programLatestObservation? g hctx who s with
    | none => moveAtCursorWorld g hctx σ who (CursorCheckedWorld.initial g hctx)
    | some obs => moveAtProgramObservation? g hctx σ who obs

@[simp] theorem programBehavioralProfileCandidate_nil
    (g : WFProgram P L) (hctx : WFCtx g.Γ)
    (σ : LegalProgramBehavioralProfile g) (who : P) :
    programBehavioralProfileCandidate g hctx σ who
      ((GameTheory.FOSG.History.nil (observedProgramFOSG g hctx)).playerView who) =
      moveAtCursorWorld g hctx σ who (CursorCheckedWorld.initial g hctx) := by
  simp [programBehavioralProfileCandidate, programLatestObservation?,
    programObservationEvents, last?]

@[simp] theorem programBehavioralProfileCandidate_snoc
    (g : WFProgram P L) (hctx : WFCtx g.Γ)
    (σ : LegalProgramBehavioralProfile g)
    (who : P)
    (h : (observedProgramFOSG g hctx).History)
    (a : (observedProgramFOSG g hctx).LegalAction h.lastState)
    (dst : CursorCheckedWorld (P := P) (L := L) g)
    (support : (observedProgramFOSG g hctx).transition h.lastState a dst ≠ 0) :
    programBehavioralProfileCandidate g hctx σ who
      ((h.snoc a dst support).playerView who) =
      moveAtCursorWorld g hctx σ who dst := by
  rw [programBehavioralProfileCandidate,
    programLatestObservation?_history_snoc g hctx who h a dst support]
  simp [moveAtProgramObservation?_of_cursorWorld]

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

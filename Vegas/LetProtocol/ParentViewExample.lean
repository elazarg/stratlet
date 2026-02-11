import Vegas.LetProtocol.ParentViewLemmas
import Vegas.LetCore.Concrete

/-!
# ParentView Example

A small example showing how `ParentProtoProg` with parent specs replaces
explicit projection functions.

**Sequential game**: Player 0 chooses a boolean (yield 0), then Player 1
observes yield 0 and chooses a boolean (yield 1). The result is the pair.

With raw `ProtoProg`, Player 1's View requires an explicit projection function
that extracts the first binding from the context. With `ParentProtoProg`,
we just declare `parents := [0]` and provide a `VarSpec` that points to
de Bruijn index 0 (the most recently bound variable).
-/

namespace Proto

open Defs Prog Env

-- ============================================================
-- 1) Setup: BasicLang aliases
-- ============================================================

private abbrev L := BasicLang
private abbrev EL := basicExprLaws

variable {W : Type} [WeightModel W]

-- ============================================================
-- 2) The sequential game using ParentProtoProg
-- ============================================================

/-- Empty view: reveals nothing. Player 0's initial choice sees no context. -/
private def psEmpty : ParentSite (L := L) [] where
  parents := []
  Δ := []
  vars := .nil

/-- Parent view: reveals yield 0 (the most recently bound variable).
    After Player 0 chooses, the context is [Ty.bool].
    We point to de Bruijn var 0. -/
private def psSeeYield0 : ParentSite (L := L) [Ty.bool] where
  parents := [0]
  Δ := [Ty.bool]
  vars := .cons .vz .nil

/-- Action set: both booleans. -/
private def boolActions : Act (v := viewOfVarSpec psEmpty.vars) Ty.bool :=
  fun _ => [true, false]

/-- Action set for Player 1 (can depend on observed value, but we offer both). -/
private def boolActions1 : Act (v := viewOfVarSpec psSeeYield0.vars) Ty.bool :=
  fun _ => [true, false]

/--
Sequential game as ParentProtoProg:
- Yield 0: Player 0 chooses a bool (sees nothing)
- Yield 1: Player 1 chooses a bool (sees yield 0)
- Return: the value of yield 1

This replaces manual View construction with declarative parent specs.
-/
private def seqGame : ParentProtoProg (L := L) (W := W) [] Ty.bool :=
  .choose 0 0 psEmpty boolActions
    (.choose 1 1 psSeeYield0 boolActions1
      (.ret (EL.vz)))

/-- The embedding produces a well-formed ProtoProg. -/
private def seqGameProto : ProtoProg (L := L) (W := W) [] Ty.bool :=
  ParentProtoProg.embed seqGame

-- ============================================================
-- 3) Verify: evaluation via embedding
-- ============================================================

/-- Evaluation of the parent-spec game equals evaluation of the embedded proto game. -/
example (σ : Profile (L := L) (W := W)) (env : L.Env []) :
    seqGame.eval σ env = evalProto σ seqGameProto env :=
  rfl

/-- The embedded game is parent-derived. -/
example : IsParentDerived (W := W) seqGameProto :=
  ParentProtoProg.embed_isParentDerived seqGame

/-- The parent specs are [[], [0]]: yield 0 sees nothing, yield 1 sees yield 0. -/
example : ParentProtoProg.parentSpecs (W := W) seqGame = [[], [0]] := rfl

/-- Yield ids are [0, 1]. -/
example : ParentProtoProg.yieldIds (W := W) seqGame = [0, 1] := rfl

-- ============================================================
-- 4) Compare: what the raw ProtoProg version would look like
-- ============================================================

/-- The equivalent raw ProtoProg with manual View construction. -/
private def seqGameRaw : ProtoProg (L := L) (W := W) [] Ty.bool :=
  let vEmpty : View [] := ⟨[], fun _ => ()⟩
  let vSee0 : View (L := L) [Ty.bool] := ⟨[Ty.bool], fun env => env⟩
  ProtoProg.choose 0 0 vEmpty (fun _ => [L.fromBool true, L.fromBool false])
    (ProtoProg.choose 1 1 vSee0 (fun _ => [L.fromBool true, L.fromBool false])
      (ProtoProg.ret EL.vz))

/-- The embedded parent-spec version and the raw version have the same yield ids. -/
example : Proto.yieldIds (seqGameProto (W := W)) = Proto.yieldIds (seqGameRaw (W := W)) := rfl

end Proto

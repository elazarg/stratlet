/-
Simply Typed Probabilistic Let-Calculus (intrinsically typed, De Bruijn)

Design goals:
- Small, standalone core (no lambdas; first-order types Int/Bool)
- Intrinsically typed + well-scoped by construction (typed De Bruijn vars)
- “Probabilistic” layer via `let_sample`
- Conditioning via `observe` (hard evidence / rejection)
- Semantics as finite-support *weighted* distributions (unnormalized), which keeps
  `observe` total and avoids partiality inside the evaluator.

You can later generalize by:
- changing the weight semiring (`Rat`) to something else
- replacing `Dist` with decision/choice kernels
- adding information-restricted contexts, etc.
-/

import Mathlib.Data.Rat.Init
import Mathlib.Data.Int.Basic
import Mathlib.Data.List.Basic

import Vegas.Deterministic

namespace ProbLet

/-! ## 3) Finite-support weighted distributions -/

/-- Weights for finite-support semantics. (Not assumed normalized.) -/
abbrev W := Rat

/-- Finite-support weighted distribution (multiset-style). -/
abbrev WDist (α : Type) := List (α × W)

namespace WDist

def pure (a : α) : WDist α := [(a, (1 : W))]

def map (f : α → β) (xs : WDist α) : WDist β :=
  List.map (fun aw => (f aw.1, aw.2)) xs

def scale (c : W) (xs : WDist α) : WDist α :=
  List.map (fun aw => (aw.1, c * aw.2)) xs

def bind (xs : WDist α) (f : α → WDist β) : WDist β :=
  match xs with
  | [] => []
  | (a, w) :: xs' =>
      scale w (f a) ++ bind xs' f

def mass (xs : WDist α) : W :=
  xs.foldl (fun acc aw => acc + aw.2) 0

def normalize (xs : WDist α) : Option (WDist α) :=
  let m := mass xs
  if m = 0 then none else some (scale (1 / m) xs)

def addMass [DecidableEq α] (a : α) (w : W) : WDist α → WDist α
  | [] => [(a, w)]
  | (b, wb) :: xs =>
      if a = b then
        (b, wb + w) :: xs
      else
        (b, wb) :: addMass a w xs

def combine [DecidableEq α] (xs : WDist α) : WDist α :=
  xs.foldl (fun acc aw => addMass aw.1 aw.2 acc) []

end WDist


/-! ## 4) Primitive distributions and programs -/

/--
Primitive finite-support distributions.
Parameters are deterministic expressions over the current context.
-/
inductive Dist : Ctx → Ty → Type where
  /-- Bernoulli with weight `p` for true and `1-p` for false. -/
  | bernoulli {Γ} (p : Rat) : Dist Γ .bool
  /-- Uniform integer on the closed interval [min, max]; empty if min > max. -/
  | uniform {Γ} (min max : Expr Γ .int) : Dist Γ .int
deriving Repr

/--
Programs: return, deterministic let, probabilistic let-sample, and observe.

`observe cond k` is hard evidence (rejection): if `cond` is false, the path has no mass.
-/
inductive Prog : Ctx → Ty → Type where
  | ret {Γ τ} (e : Expr Γ τ) : Prog Γ τ
  | letDet {Γ τ τ'} (e : Expr Γ τ') (k : Prog (τ' :: Γ) τ) : Prog Γ τ
  | letSample {Γ τ τ'} (d : Dist Γ τ') (k : Prog (τ' :: Γ) τ) : Prog Γ τ
  | observe {Γ τ} (cond : Expr Γ .bool) (k : Prog Γ τ) : Prog Γ τ
deriving Repr

/-! ## 5) Semantics (interpreter) -/

private def uniformSupport (mn mx : Int) : List Int :=
  if mn ≤ mx then
    let n : Nat := Int.toNat (mx - mn + 1)
    (List.range n).map (fun i => mn + Int.ofNat i)
  else
    []

def evalDist : Dist Γ τ → Env Γ → WDist (Val τ)
  | .bernoulli p, _ =>
      -- No constraint enforced here; you can later restrict p ∈ [0,1] if desired.
      [(true, p), (false, (1 - p))]
  | .uniform minE maxE, env =>
      let mn := evalExpr minE env
      let mx := evalExpr maxE env
      let xs := uniformSupport mn mx
      match xs.length with
      | 0 => []
      | n =>
          let prob : W := (1 : W) / ((n : Nat) : W)
          xs.map (fun v => (v, prob))

def evalProg : Prog Γ τ → Env Γ → WDist (Val τ)
  | .ret e, env =>
      WDist.pure (evalExpr e env)
  | .letDet e k, env =>
      let v := evalExpr e env
      evalProg k (v, env)
  | .letSample d k, env =>
      WDist.bind (evalDist d env) (fun v => evalProg k (v, env))
  | .observe cond k, env =>
      if evalExpr cond env then
        evalProg k env
      else
        []

/-! ## Tiny sanity examples -/

namespace Examples

def Γ0 : Ctx := []

-- sample x ~ Bernoulli(1/2); observe x = true; return x
def ex1 : Prog Γ0 .bool :=
  Prog.letSample (Dist.bernoulli (1/2))
    (Prog.observe (Expr.var Var.vz) (Prog.ret (Expr.var Var.vz)))

#eval evalProg ex1 ()   -- expected: [(true, 1/2)]  (unnormalized; false branch rejected)

-- sample n ~ Uniform(2,4); return (n == 3)
def ex2 : Prog Γ0 .bool :=
  Prog.letSample (Dist.uniform (Expr.constInt 2) (Expr.constInt 4))
    (Prog.ret (Expr.eqInt (Expr.var Var.vz) (Expr.constInt 3)))

#eval WDist.combine (evalProg Examples.ex2 ())
-- expected: [(false, 2/3), (true, 1/3)] up to ordering

end Examples

end ProbLet

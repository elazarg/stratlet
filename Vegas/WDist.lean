
/-! ## 3) Finite-support weighted distributions -/

/-- Weights for finite-support semantics. (Not assumed normalized.) -/
abbrev W := Rat

/-- Finite-support weighted distribution (multiset-style). -/
abbrev WDist (α : Type) := List (α × W)

namespace WDist

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

/-- Mass of an event/predicate (sums weights of outcomes satisfying it). -/
def massOf {α} (p : α → Bool) (xs : WDist α) : W :=
  xs.foldl (fun acc aw => if p aw.1 then acc + aw.2 else acc) 0

/-- Hard conditioning / evidence: keep only outcomes satisfying predicate. -/
def cond {α} (p : α → Bool) (xs : WDist α) : WDist α :=
  xs.foldr (fun aw acc => if p aw.1 then aw :: acc else acc) []

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

def zero : WDist α := []

def pure (a : α) : WDist α := [(a, (1 : W))]

def guard (b : Bool) : WDist Unit :=
  if b then pure () else zero

@[simp] theorem bind_pure (a : α) (f : α → WDist β) :
    WDist.bind (WDist.pure a) f = f a := by
  simp [WDist.bind, WDist.pure, WDist.scale]

@[simp] theorem bind_nil (f : α → WDist β) :
    WDist.bind ([] : WDist α) f = [] := by
  simp [WDist.bind]

end WDist

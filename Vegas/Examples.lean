import Vegas.WF

namespace Vegas

namespace Examples

def va : VarId := 0
def vb : VarId := 1
def va' : VarId := 2
def vb' : VarId := 3

def Γ0 : CtxSimple := []
def Γ1 : CtxSimple := [(va, .hidden 0 .bool)]
def Γ2 : CtxSimple := [(vb, .hidden 1 .bool), (va, .hidden 0 .bool)]
def Γ3 : CtxSimple := [(va', .pub .bool), (vb, .hidden 1 .bool), (va, .hidden 0 .bool)]
def Γ4 : CtxSimple :=
  [(vb', .pub .bool), (va', .pub .bool),
   (vb, .hidden 1 .bool), (va, .hidden 0 .bool)]

def hva_in_Γ2 : HasVarSimple Γ2 va (.hidden 0 .bool) := .there .here
def hvb_in_Γ3 : HasVarSimple Γ3 vb (.hidden 1 .bool) := .there .here
def hva'_in_Γ4 : HasVarSimple Γ4 va' (.pub .bool) := .there .here
def hvb'_in_Γ4 : HasVarSimple Γ4 vb' (.pub .bool) := .here

def mpPayoff : PayoffMap Γ4 :=
  ⟨[ (0, .ite
        (.eqBool (.var va' hva'_in_Γ4) (.var vb' hvb'_in_Γ4))
        (.constInt 1) (.constInt (-1))),
     (1, .ite
        (.eqBool (.var va' hva'_in_Γ4) (.var vb' hvb'_in_Γ4))
        (.constInt (-1)) (.constInt 1))
   ], by decide⟩

def matchingPennies : VegasSimple Γ0 :=
  .commit va 0 (b := .bool) [true, false] (.constBool true)
    (.commit vb 1 (b := .bool) [true, false] (.constBool true)
      (.reveal va' 0 va hva_in_Γ2
        (.reveal vb' 1 vb hvb_in_Γ3
          (.ret mpPayoff.entries))))

noncomputable def mpProfile : ProfileSimple where
  commit := fun {_Γ} {b} _who x _acts _R _view =>
    match x with
    | 0 =>
      match b with
      | .bool => FDist.pure true
      | .int => FDist.zero
    | 1 =>
      match b with
      | .bool => FDist.pure false
      | .int => FDist.zero
    | _ => FDist.zero

def conditionedGame : VegasSimple Γ0 :=
  .commit va 0 (b := .bool) [true, false] (.constBool true)
    (.reveal va' 0 va .here
      (.commit vb 1 (b := .bool) [true, false]
        (.var va' (.there .here))
        (.reveal vb' 1 vb .here
          (.ret [(0, .constInt 1), (1, .constInt 0)]))))

example : WF matchingPennies := by
  decide

example : RevealComplete [] matchingPennies := by
  decide

example : WF conditionedGame := by
  decide

example : RevealComplete [] conditionedGame := by
  decide

end Examples

end Vegas

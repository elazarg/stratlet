import Vegas.LetProtocol.Proto

/-!
# Step: Handler-based IO evaluation of ProtoProg

Provides a callback interface (`ProtoHandler`) and an IO evaluator (`stepProto`)
that walks a ProtoProg, delegating sample/choose events to the handler.
-/

namespace Proto

open Defs Prog

variable {L : Language}

/-- Callback interface for handling protocol events during IO evaluation. -/
structure ProtoHandler (L : Language) where
  /-- Handle a sample event: given yield id and the distribution, produce a value. -/
  onSample : {τ : L.Ty} → YieldId → WDist (L.Val τ) → IO (L.Val τ)
  /-- Handle a choose event: given yield id, player, and action list, produce a value. -/
  onChoose : {τ : L.Ty} → YieldId → Player → List (L.Val τ) → IO (L.Val τ)

/-- Evaluate a `ProtoProg` using IO, delegating to a handler for sample/choose events. -/
def stepProto (h : ProtoHandler L) {Γ τ} : ProtoProg (L := L) Γ τ → L.Env Γ → IO (L.Val τ)
  | .ret e, env => pure (L.eval e env)
  | .letDet e k, env => stepProto h k (L.eval e env, env)
  | .doStmt (.observe cond) k, env =>
      if L.toBool (L.eval cond env)
      then stepProto h k env
      else throw (IO.userError "Observation failed")
  | .doBind (.sample id v K) k, env => do
      let dist := K (v.proj env)
      let val ← h.onSample id dist
      stepProto h k (val, env)
  | .doBind (.choose id who v A) k, env => do
      let actions := A (v.proj env)
      let val ← h.onChoose id who actions
      stepProto h k (val, env)

end Proto

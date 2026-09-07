/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import Vegas.Machine.Program

/-!
# Fixed trusted-oracle policy

This module turns one semantic sample step into a deterministic transition
chosen by an explicit oracle response.  The oracle's fixed behavioral policy
is exactly the retained finite law.  Pushing deterministic execution through
that policy recovers the original machine transition.

This is the classical trusted-oracle boundary.  It says nothing about how an
implementation samples, authenticates, transports, or withholds a response.
Those are later protocol and security refinements.
-/

noncomputable section

namespace Vegas.Machine.Contract

open EventGraph
open GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player]
variable {L : IExpr} {program : Program Player L}

namespace OraclePolicy

/-- One concrete oracle choice is an index into the exact table evaluated at
the current public state.  Using indices avoids requiring the ABI to encode a
dependently typed source value directly. -/
abbrev Choice (dist : EventDist L) (env : ReadEnv L dist.reads) :=
  Fin (dist.evalLaw env).entries.length

/-- The known oracle policy on concrete table indices. -/
def choiceLaw (dist : EventDist L) (env : ReadEnv L dist.reads) :
    FinDist (Choice dist env) :=
  (dist.evalLaw env).indexLaw

/-- Deterministically realize one concrete table index. -/
def realizeChoice (cfg : Config program.graph)
    (event : InternalEvent program.graph)
    (dist : EventDist L) (env : ReadEnv L dist.reads)
    (choice : Choice dist env) : Config program.graph :=
  cfg.completeNode event.node
    { ty := dist.ty
      value := (dist.evalLaw env).entryValue choice }

/-- The table-index oracle policy pushes forward to exactly the semantic
sample transition.  This is the emitter-facing form of trusted sampling. -/
theorem map_realizeChoice_choiceLaw
    (state : program.State)
    (event : InternalEvent program.graph)
    (row : EventNode Player L) (dist : EventDist L)
    (rowGet : program.graph.nodes[event.node]? = some row)
    (semEq : row.sem = .sample dist)
    (ready : Ready program.graph state.1 event.node)
    (env : ReadEnv L dist.reads)
    (envOk : ReadEnv.ofStore? state.1.store dist.reads = some env) :
    (choiceLaw dist env).map
        (realizeChoice state.1 event dist env) =
      stepInternal program.graph state.1
        (.sample row dist rowGet semEq ready env envOk) := by
  change
    (dist.evalLaw env).indexLaw.map
        (fun choice =>
          state.1.completeNode event.node
            { ty := dist.ty
              value := (dist.evalLaw env).entryValue choice }) =
      (dist.eval env).map
        (fun value =>
          state.1.completeNode event.node
            { ty := dist.ty, value := value })
  unfold EventDist.eval RationalLaw.denote
  rw [FinDist.map_comp]
  rfl

/-- Machine-level exactness of the fixed table-index oracle policy. -/
theorem map_realizeChoice_choiceLaw_eq_machine
    (state : program.State)
    (event : InternalEvent program.graph)
    (row : EventNode Player L) (dist : EventDist L)
    (rowGet : program.graph.nodes[event.node]? = some row)
    (semEq : row.sem = .sample dist)
    (ready : Ready program.graph state.1 event.node)
    (env : ReadEnv L dist.reads)
    (envOk : ReadEnv.ofStore? state.1.store dist.reads = some env) :
    (choiceLaw dist env).map
        (realizeChoice state.1 event dist env) =
      (program.step state
        (.internal event
          (.sample row dist rowGet semEq ready env envOk))).map Subtype.val := by
  rw [map_realizeChoice_choiceLaw state event row dist rowGet semEq ready env
    envOk]
  exact
    (EventGraph.map_val_stepAvailable program.graph state
      (.internal event
        (.sample row dist rowGet semEq ready env envOk))).symm

/-- One response admitted by the fixed oracle policy for a particular sample
law and public read environment.  Support membership is part of the response
surface, so deterministic execution cannot invent an impossible draw. -/
structure Response (dist : EventDist L) (env : ReadEnv L dist.reads) where
  value : L.Val dist.ty
  supported : value ∈ (dist.eval env).support

/-- The oracle's known behavioral strategy: draw a supported response with
exactly the retained source probability law. -/
def responseLaw (dist : EventDist L) (env : ReadEnv L dist.reads) :
    FinDist (Response dist env) :=
  (dist.eval env).bindOnSupport fun value supported =>
    FinDist.pure ⟨value, supported⟩

/-- Forgetting support evidence from the fixed oracle response recovers the
exact semantic distribution. -/
theorem map_value_responseLaw (dist : EventDist L)
    (env : ReadEnv L dist.reads) :
    (responseLaw dist env).map Response.value = dist.eval env := by
  unfold responseLaw
  rw [FinDist.map_bindOnSupport]
  rw [FinDist.bindOnSupport_eq_bind_of_eq_on_support
    (g := fun value => FinDist.pure value)]
  · exact FinDist.bind_pure _
  · intro value supported
    simp

/-- Execute one supported oracle response deterministically on the raw graph
configuration. -/
def realizeConfig (cfg : Config program.graph)
    (event : InternalEvent program.graph)
    {dist : EventDist L} {env : ReadEnv L dist.reads}
    (response : Response dist env) : Config program.graph :=
  cfg.completeNode event.node
    { ty := dist.ty, value := response.value }

/-- Fixing the oracle policy and executing its response is exactly the
original stochastic sample transition on raw graph configurations. -/
theorem map_realizeConfig_responseLaw
    (state : program.State)
    (event : InternalEvent program.graph)
    (row : EventNode Player L) (dist : EventDist L)
    (rowGet : program.graph.nodes[event.node]? = some row)
    (semEq : row.sem = .sample dist)
    (ready : Ready program.graph state.1 event.node)
    (env : ReadEnv L dist.reads)
    (envOk : ReadEnv.ofStore? state.1.store dist.reads = some env) :
    (responseLaw dist env).map
        (realizeConfig state.1 event) =
      stepInternal program.graph state.1
        (.sample row dist rowGet semEq ready env envOk) := by
  unfold responseLaw realizeConfig stepInternal
  rw [FinDist.map_bindOnSupport]
  rw [FinDist.bindOnSupport_eq_bind_of_eq_on_support
    (g := fun value =>
      FinDist.pure
        (state.1.completeNode event.node
          { ty := dist.ty, value := value }))]
  · rw [← FinDist.map_eq_bind]
  · intro value supported
    simp

/-- Machine-level formulation of `map_realizeConfig_responseLaw`: after
erasing reachability evidence, a deterministic oracle player with the fixed
policy induces exactly `Program.step`. -/
theorem map_realizeConfig_responseLaw_eq_machine
    (state : program.State)
    (event : InternalEvent program.graph)
    (row : EventNode Player L) (dist : EventDist L)
    (rowGet : program.graph.nodes[event.node]? = some row)
    (semEq : row.sem = .sample dist)
    (ready : Ready program.graph state.1 event.node)
    (env : ReadEnv L dist.reads)
    (envOk : ReadEnv.ofStore? state.1.store dist.reads = some env) :
    (responseLaw dist env).map
        (realizeConfig state.1 event) =
      (program.step state
        (.internal event
          (.sample row dist rowGet semEq ready env envOk))).map Subtype.val := by
  rw [map_realizeConfig_responseLaw state event row dist rowGet semEq ready env
    envOk]
  exact
    (EventGraph.map_val_stepAvailable program.graph state
      (.internal event
        (.sample row dist rowGet semEq ready env envOk))).symm

end OraclePolicy

end Vegas.Machine.Contract

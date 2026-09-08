/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import Vegas.Core.ForcedChoice
import Vegas.Game.SourceCorrespondence
import VegasTests.PersistentDisclosurePolicy

/-! # Policy-independent source continuation after public quitting

The public first disposition determines the later guarded source choice after
quitting. This holds for arbitrary source environments and behavioral policies,
not just the finite environments exercised by the graph fixture. The theorem
keeps both source bindings and the reveal event; it does not implement them on
behalf of a silent player in a message runtime.
-/

namespace VegasTests.PersistentDisclosure

open Vegas GameTheory.Math.Probability

/-- After the first public refusal, the later legal value is publicly known,
even though the guard's other branch inspects the owner's secret. -/
def secondForcedChoice : PublicForcedChoice (L := simpleExpr) secondGuard where
  enabled := .isNone (.var 5 (.there .here))
  value := .none
  characterizes := by
    intro env henabled chosen
    change (env.get (VHasVar.there (.there .here)) : Option Bool).isNone = true at henabled
    change (if (env.get (VHasVar.there (.there .here)) : Option Bool).isNone
      then chosen.isNone else _) = true ↔ chosen = none
    rw [henabled]
    cases chosen <;> simp

/-- The actual suffix at the second decision of the compiled graph fixture. -/
def secondCore : VegasCore Player simpleExpr SecondContext :=
  .commit 8 0 secondGuard (.reveal 9 0 8 .here (.ret [(0, payoff)]))

def secondSite : SourceDecisionSite (0 : Player) core SecondContext 8
    (.option .bool) secondGuard :=
  .commit (.commit (.reveal (.sample (.commit (.reveal (.commit (.reveal
    (.here (who := (0 : Player)) (L := simpleExpr) secondGuard
      (.reveal 9 0 8 .here (.ret [(0, payoff)]))))))))))

/-- Restrict an arbitrary whole-program policy profile to its actual suffix;
this neither replaces opponents nor supplies a separately chosen policy. -/
def secondProfile (profile : SourceBehavioralProfile core) :
    SourceBehavioralProfile secondCore :=
  profile.afterCommit.afterCommit.afterReveal.afterSample.afterCommit.afterReveal
    |>.afterCommit.afterReveal

/-- Every policy at the second decision produces the same complete suffix law
after public refusal. In particular, no invocation of its choice callback is
needed to select the source value. -/
theorem source_suffix_after_refusal (profile : SourceBehavioralProfile core)
    (env : VEnv simpleExpr SecondContext)
    (hquit : (env.get (VHasVar.there (.there .here)) : Option Bool) = none) :
    denoteSource secondCore (secondProfile profile) env =
      FinDist.pure ((env.cons (none : Option Bool)).cons (none : Option Bool)) := by
  have henabled : simpleExpr.toBool
      (simpleExpr.eval secondForcedChoice.enabled env.eraseSampleEnv) = true := by
    change (env.get (VHasVar.there (.there .here)) : Option Bool).isNone = true
    rw [hquit]
    rfl
  unfold secondCore
  rw [secondForcedChoice.denoteSource_commit _ _ env henabled]
  rfl

/-- In the canonical source environment, a later opponent response cannot
restore a choice removed by earlier quitting. -/
theorem source_suffix_refusal_independent (left right : SourceBehavioralProfile core)
    (secret signal response : Bool) :
    denoteSource secondCore (secondProfile left) (secondEnv secret signal none response) =
      denoteSource secondCore (secondProfile right) (secondEnv secret signal none response) := by
  rw [source_suffix_after_refusal left _ rfl, source_suffix_after_refusal right _ rfl]

def firstDisposition (env : VEnv simpleExpr (sourceTerminalCtx core)) : Option Bool :=
  env.get (.there (.there (.there (.there .here))))

def lastDisposition (env : VEnv simpleExpr (sourceTerminalCtx core)) : Option Bool :=
  env.get .here

/-- Every supported execution of the whole written-order source retains the
first refusal at the second checkpoint, for arbitrary source profiles. -/
theorem source_refusal_persists (profile : SourceBehavioralProfile core)
    (env : VEnv simpleExpr (sourceTerminalCtx core))
    (hsupport : env ∈ (denoteSource core profile (VEnv.empty simpleExpr)).support)
    (hquit : firstDisposition env = none) : lastDisposition env = none := by
  simp only [core, denoteSource, FinDist.support_bind, Set.mem_iUnion,
    FinDist.mem_support_pure] at hsupport
  obtain ⟨secret, _, marker, _, signal, _, first, _, response, _, later, _, rfl⟩ := hsupport
  change first.1 = none at hquit
  change later.1 = none
  have hlegal := later.2
  change (if first.1.isNone then later.1.isNone else _) = true at hlegal
  have hnone : first.1.isNone = true := congrArg Option.isNone hquit
  simp only [hnone, if_true] at hlegal
  exact Option.isNone_iff_eq_none.mp hlegal

/-- The same persistence property holds under every native behavioral graph
profile. Its decoded outcome is related to the written-order source by the
general compiler theorem; no well-formed-source admission is inferred. -/
theorem graph_refusal_persists
    (profile : ∀ who, program.information.BehavioralPolicy who)
    (history : program.execution.History)
    (hsupport : history ∈ (program.information.runBehavioral profile graph.nodeCount).support)
    (hquit : firstDisposition
      (ToEventGraph.observeSourceOutcome source legal history.state) = none) :
    lastDisposition (ToEventGraph.observeSourceOutcome source legal history.state) = none := by
  have hsource := ToEventGraph.runBehavioral_backtranslate_source source legal profile
  have hdecoded : ToEventGraph.observeSourceOutcome source legal history.state ∈
      ((program.information.runBehavioral profile graph.nodeCount).map
        (fun final => ToEventGraph.observeSourceOutcome source legal final.state)).support := by
    rw [FinDist.support_map]
    exact ⟨history, hsupport, rfl⟩
  have hmem := Eq.mp (congrArg
    (fun law => ToEventGraph.observeSourceOutcome source legal history.state ∈ law.support)
    hsource) hdecoded
  exact source_refusal_persists _ _ hmem hquit

/-- info: 'VegasTests.PersistentDisclosure.source_suffix_after_refusal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms VegasTests.PersistentDisclosure.source_suffix_after_refusal

/-- info: 'Vegas.PublicForcedChoice.denoteSource_commit' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.PublicForcedChoice.denoteSource_commit

/-- info: 'VegasTests.PersistentDisclosure.source_refusal_persists' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms VegasTests.PersistentDisclosure.source_refusal_persists

/-- info: 'VegasTests.PersistentDisclosure.graph_refusal_persists' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms VegasTests.PersistentDisclosure.graph_refusal_persists

/-- info: 'Vegas.ToEventGraph.runBehavioral_backtranslate_source' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.ToEventGraph.runBehavioral_backtranslate_source

end VegasTests.PersistentDisclosure

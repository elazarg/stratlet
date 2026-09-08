/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import VegasTests.Game

/-! # Equilibrium of the compiled hidden matching-pennies game -/

noncomputable section

namespace VegasTests.MatchingPenniesEquilibrium

open Vegas EventGraph GameTheory GameTheory.Protocol GameTheory.Math.Probability

abbrev program := matchingPenniesMachine
abbrev graph := program.graph

theorem nodeTarget_eq (node : Nat) : graph.nodeTarget node = node := by
  change 0 + node = node
  omega

theorem nodeCount_eq : graph.nodeCount = 4 := rfl

theorem node_ty (node : Fin graph.nodeCount) : (graph.nodeRow node).ty = .bool := by
  fin_cases node <;> rfl

def action (who : TestPlayer) (bit : Bool) : FrontierAction graph who where
  value? node := if node.val = who.val then
    some (cast (congrArg simpleExpr.Val (node_ty node).symm) bit) else none

theorem ready_initial_iff (who : TestPlayer) (node : Fin graph.nodeCount) :
    ReadyCommitNode graph (Config.initial graph) who node ↔ node.val = who.val := by
  have hcanonical : ReadyCommitNode graph (Config.initial graph) who node ↔
      ∃ guard, (graph.nodeRow node).sem = .commit who guard ∧
        Ready graph (Config.initial graph) node := by
    constructor
    · rintro ⟨row, guard, hrow, hsem, hready⟩
      have heq : row = graph.nodeRow node :=
        Option.some.inj (hrow.symm.trans (graph.nodes_get?_nodeRow node))
      subst row
      exact ⟨guard, hsem, hready⟩
    · rintro ⟨guard, hsem, hready⟩
      exact ⟨_, guard, graph.nodes_get?_nodeRow node, hsem, hready⟩
  rw [hcanonical]
  fin_cases node
  · obtain ⟨guard, hguard⟩ := matchingPenniesNode0_commit
    change (∃ guard', (graph.nodeRow matchingPenniesNode0).sem = .commit who guard' ∧ _) ↔ _
    rw [hguard]
    constructor
    · rintro ⟨_, hsem, _⟩
      exact congrArg Fin.val (NodeSem.commit.inj hsem).1
    · intro heq
      have hwho : who = 0 := Fin.ext heq.symm
      subst who
      refine ⟨guard, rfl, ?_⟩
      exact ⟨by simp [Config.initial], by
        change matchingPenniesMachine.graph.prereqs matchingPenniesNode0 ⊆ _
        rw [matchingPenniesNode0_prereqs]; exact Finset.empty_subset _⟩
  · obtain ⟨guard, hguard⟩ := matchingPenniesNode1_commit
    change (∃ guard', (graph.nodeRow matchingPenniesNode1).sem = .commit who guard' ∧ _) ↔ _
    rw [hguard]
    constructor
    · rintro ⟨_, hsem, _⟩
      exact congrArg Fin.val (NodeSem.commit.inj hsem).1
    · intro heq
      have hwho : who = 1 := Fin.ext heq.symm
      subst who
      refine ⟨guard, rfl, ?_⟩
      exact ⟨by simp [Config.initial], by
        change matchingPenniesMachine.graph.prereqs matchingPenniesNode1 ⊆ _
        rw [matchingPenniesNode1_prereqs]; exact Finset.empty_subset _⟩
  · change (∃ guard, NodeSem.reveal (Player := TestPlayer) (L := simpleExpr) 0 =
      .commit who guard ∧ _) ↔ 2 = who.val
    constructor
    · rintro ⟨_, heq, _⟩; cases heq
    · intro heq; have := who.isLt; omega
  · change (∃ guard, NodeSem.reveal (Player := TestPlayer) (L := simpleExpr) 1 =
      .commit who guard ∧ _) ↔ 3 = who.val
    constructor
    · rintro ⟨_, heq, _⟩; cases heq
    · intro heq; have := who.isLt; omega

theorem action_available (who : TestPlayer) (bit : Bool) :
    FrontierAction.Available graph (Config.initial graph) who (action who bit) := by
  classical
  intro node
  split
  next hready =>
    have heq := (ready_initial_iff who node).mp hready
    refine ⟨cast (congrArg simpleExpr.Val (node_ty node).symm) bit,
      by simp [action, heq], ?_⟩
    fin_cases who <;> fin_cases node <;> norm_num at heq
    all_goals
      refine ⟨⟨_, _, rfl, rfl, hready.ready, bit, ?_,
        ⟨fun ref href => False.elim ?_⟩, ?_, ?_⟩⟩
      · rfl
      · change ref ∈ (∅ : Finset (FieldRef simpleExpr)) at href
        exact Finset.notMem_empty ref href
      · change ReadEnv.ofStore? _ ∅ = some _
        simp only [ReadEnv.ofStore?, Finset.notMem_empty, false_implies, implies_true,
          dite_true, Option.some.injEq]
        apply ReadEnv.ext
        intro ref href
        simp at href
      · rfl
  next hready =>
    simp [action, (ready_initial_iff who node).not.mp hready]

abbrev initialInfo (who : TestPlayer) :=
  program.information.infoOf who program.execution.initHistory.trace

def choice (who : TestPlayer) (bit : Bool) : program.information.Choice who (initialInfo who) :=
  ⟨some (action who bit), (program.information.menu_adequate who
    program.execution.initHistory.trace _).mpr
      ⟨matchingPenniesInitial_active who, action_available who bit⟩⟩

def ownNode (who : TestPlayer) : Fin graph.nodeCount :=
  ⟨who.val, Nat.lt_trans who.isLt (by decide)⟩

theorem choice_exhaustive (who : TestPlayer)
    (chosen : program.information.Choice who (initialInfo who)) :
    ∃ bit, chosen = choice who bit := by
  classical
  have hlocal := (program.information.menu_adequate who
    program.execution.initHistory.trace chosen.1).mp chosen.2
  obtain ⟨packet, hpacket⟩ := LegalOption.exists_eq_some_of_active chosen.1 hlocal
    (matchingPenniesInitial_active who)
  rw [hpacket] at hlocal
  have havailable : FrontierAction.Available graph (Config.initial graph) who packet := hlocal.2
  have hready : ReadyCommitNode graph (Config.initial graph) who (ownNode who) :=
    (ready_initial_iff who _).mpr rfl
  have hvalue := havailable (ownNode who)
  rw [dif_pos hready] at hvalue
  obtain ⟨value, hvalue, _⟩ := hvalue
  let bit : Bool := cast (congrArg simpleExpr.Val (node_ty (ownNode who))) value
  refine ⟨bit, Subtype.ext (hpacket.trans (congrArg some ?_))⟩
  have hvalues : packet.value? = (action who bit).value? := by
    funext node
    by_cases heq : node.val = who.val
    · have hnode : node = ownNode who := Fin.ext heq
      subst node
      rw [hvalue]
      simp [action, ownNode, bit]
    · have hnot := (ready_initial_iff who node).not.mpr heq
      have hnone := havailable node
      rw [dif_neg hnot] at hnone
      simpa [action, heq] using hnone
  cases packet
  exact congrArg FrontierAction.mk hvalues

theorem choice_injective (who : TestPlayer) : Function.Injective (choice who) := by
  intro left right heq
  have hvalues := congrArg
    (fun chosen => chosen.1.map (fun packet => packet.value? (ownNode who))) heq
  simp only [choice, Option.map_some, action, ownNode,
    ite_true, Option.some.injEq] at hvalues
  exact (Equiv.cast _).injective hvalues

def choiceEquiv (who : TestPlayer) : Bool ≃ program.information.Choice who (initialInfo who) :=
  Equiv.ofBijective (choice who) ⟨choice_injective who, fun chosen => by
    obtain ⟨bit, hbit⟩ := choice_exhaustive who chosen
    exact ⟨bit, hbit.symm⟩⟩

/-- The fair policy randomizes uniformly at the simultaneous initial frontier;
outside that information state it uses a legal total fallback. -/
def fairPolicy (who : TestPlayer) : program.information.BehavioralPolicy who := by
  classical
  exact Function.update ((program.defaultPureProfile who).toBehavioral)
    (initialInfo who) (FinDist.uniformOfFintype.map (choice who))

def joint (bits : TestPlayer → Bool) : ∀ who, Option (FrontierAction graph who) :=
  fun who => some (action who (bits who))

theorem joint_legal (bits : TestPlayer → Bool) :
    program.execution.Legal program.execution.init (joint bits) :=
  ⟨(matchingPenniesInitial_active 0).1,
    fun who => ⟨matchingPenniesInitial_active who, action_available who (bits who)⟩⟩

def after (bits : TestPlayer → Bool) : program.State :=
  applyFrontier graph program.graphWF program.execution.init (joint bits)

theorem after_val (bits : TestPlayer → Bool) :
    (after bits).1 = ((Config.initial graph).completeNode matchingPenniesNode0
      ⟨.bool, bits 0⟩).completeNode matchingPenniesNode1 ⟨.bool, bits 1⟩ := by
  unfold after
  rw [← EventGraph.applySerializedOrder_eq_applyFrontier graph program.graphWF program.guardLive
    program.execution.init (joint bits) (joint_legal bits) matchingPennies_zeroFirst_mem_schedules]
  rw [EventGraph.applySerializedOrder_val program.graphWF (joint bits) program.execution.init
    (fun who packet heq => by
      have hp : packet = action who (bits who) := (Option.some.inj heq).symm
      subst packet
      exact action_available who (bits who)) (by decide : ([0, 1] : List TestPlayer).Nodup)]
  rfl

def payoff (bits : TestPlayer → Bool) (who : TestPlayer) : ℝ :=
  if who = 0 then (if bits 0 = bits 1 then 1 else -1)
  else (if bits 0 = bits 1 then -1 else 1)

theorem terminal_payoff (bits : TestPlayer → Bool) (state : program.State)
    (hterminal : program.terminal state)
    (hleft : Store.getAs state.1.store 0 .bool = some (bits 0))
    (hright : Store.getAs state.1.store 1 .bool = some (bits 1)) (who : TestPlayer) :
    program.payoutUtility state who = payoff bits who := by
  have reveal_value (node : Fin graph.nodeCount) (source : Nat)
      (hsem : (graph.nodeRow node).sem = .reveal source) :
      Store.getAs state.1.store (graph.nodeTarget node) (graph.nodeRow node).ty =
        Store.getAs state.1.store source (graph.nodeRow node).ty := by
    obtain ⟨row, hrow, hvalid⟩ := reachable_validDoneValues program.graphWF state.2
      node (hterminal node)
    have heq : row = graph.nodeRow node :=
      Option.some.inj (hrow.symm.trans (graph.nodes_get?_nodeRow node))
    subst row
    rw [hsem] at hvalid
    obtain ⟨value, htarget, hsource⟩ := hvalid
    exact htarget.trans hsource.symm
  have hleftPublic : Store.getAs state.1.store 2 .bool = some (bits 0) :=
    (reveal_value matchingPenniesNode2 0 rfl).trans hleft
  have hrightPublic : Store.getAs state.1.store 3 .bool = some (bits 1) :=
    (reveal_value matchingPenniesNode3 1 rfl).trans hright
  let compiled := ToEventGraph.compile matchingPenniesProgram.core
  let available : ∀ {name ty} (binding : VHasVar compiled.terminalCtx name ty),
      ∃ value, Store.getAs state.1.store (compiled.terminalState.fieldOf binding) ty.base =
        some value := fun binding =>
    Machine.sourceBindingsAvailableAtTerminal compiled state hterminal binding
  let env := ToEventGraph.sourceEnvOfStore compiled.terminalState state.1.store available
  have henv : env = VEnv.cons (L := simpleExpr) (x := 3) (τ := .pub .bool) (bits 1)
      (VEnv.cons (L := simpleExpr) (x := 2) (τ := .pub .bool) (bits 0)
        (VEnv.cons (L := simpleExpr) (x := 1) (τ := .sealed 1 .bool) (bits 1)
          (VEnv.cons (L := simpleExpr) (x := 0) (τ := .sealed 0 .bool) (bits 0)
            (VEnv.empty simpleExpr)))) := by
    funext name ty binding
    have hget := ToEventGraph.sourceEnvOfStore_get compiled.terminalState
      state.1.store available binding
    cases binding with
    | here => exact Option.some.inj (hget.symm.trans hrightPublic)
    | there binding => cases binding with
      | here => exact Option.some.inj (hget.symm.trans hleftPublic)
      | there binding => cases binding with
        | here => exact Option.some.inj (hget.symm.trans hright)
        | there binding => cases binding with
          | here => exact Option.some.inj (hget.symm.trans hleft)
          | there binding => cases binding
  have heval := compiled.evalPayoffs_eq_sourceEnvOfStore state.1.store available
  change evalPayoffs? program.payoffs state.1.store = some (evalPayoffs compiled.sourcePayoffs env)
    at heval
  rw [henv] at heval
  rw [Machine.Program.payoutUtility, if_pos hterminal, heval]
  fin_cases who <;> simp [payoff, compiled, matchingPenniesProgram, matchingPenniesCore,
    ToEventGraph.compile, ToEventGraph.compileCore, evalPayoffs,
    matchingPenniesLeftPayoff, matchingPenniesRightPayoff, matchingPenniesSame,
    evalExpr, mkPayout, payoffAt, VEnv.erasePubEnv, VEnv.get, VEnv.cons,
    Env.get, Env.cons]

theorem continuation_payoff
    (profile : (who : TestPlayer) → program.information.BehavioralPolicy who)
    (bits : TestPlayer → Bool) (start : program.execution.History)
    (hstate : start.state = after bits) (who : TestPlayer) (observable : ℝ → ℝ) :
    (program.terminalStateLaw profile start).expect
      (fun state => observable (program.payoutUtility state who)) =
        observable (payoff bits who) := by
  rw [Machine.Program.terminalStateLaw, FinDist.expect_map]
  calc
    _ = (program.information.runBehavioralFrom profile graph.nodeCount start).expect
        (fun _ => observable (payoff bits who)) := by
      apply FinDist.expect_congr
      intro next hnext
      have hterminal := program.information.runBehavioralFrom_terminal_of_bound
        profile program.boundedHorizon start next hnext
      have hextends := program.runBehavioralFrom_extends profile graph.nodeCount start next hnext
      rw [hstate] at hextends
      apply congrArg observable
      apply terminal_payoff bits next.state hterminal
      all_goals
        rw [hextends.getAs _ .bool (by
          intro node hnot heq
          rw [nodeTarget_eq] at heq
          apply hnot
          rw [after_val]
          change node ∈ ({matchingPenniesNode1, matchingPenniesNode0} : Finset _)
          simp only [Finset.mem_insert, Finset.mem_singleton]
          first
          | exact Or.inr (Fin.ext heq.symm)
          | exact Or.inl (Fin.ext heq.symm))]
        rw [after_val]
        simp [Config.completeNode, Store.getAs, Store.set, TypedValue.as?,
          nodeTarget_eq, nodeCount_eq,
          matchingPenniesNode0, matchingPenniesNode1]
    _ = _ := FinDist.expect_const _ _

/-- Exact evaluation of the compiled behavioral game through its initial
choice laws. All automatic internal histories and all off-path policies are
accounted for by the continuation proof. -/
theorem expectedPayoffObservable_eq
    (profile : (who : TestPlayer) → program.information.BehavioralPolicy who)
    (who : TestPlayer) (observable : ℝ → ℝ) :
    (program.boundedGame.behavioral.form.play profile).expect
      (fun history => observable (program.boundedGame.behavioral.utility history who)) =
    (FinDist.pi fun player => (profile player (initialInfo player)).map
      (choiceEquiv player).symm).expect (fun bits => observable (payoff bits who)) := by
  have hterm : ¬ program.execution.terminal program.execution.init :=
    (matchingPenniesInitial_active 0).1
  change (program.information.runBehavioral profile graph.nodeCount).expect
    (fun history => observable (program.payoutUtility history.state who)) = _
  rw [← FinDist.expect_map ExecutionProtocol.History.state
    (program.information.runBehavioral profile graph.nodeCount)
    (fun state => observable (program.payoutUtility state who))]
  change (program.terminalStateLaw profile program.execution.initHistory).expect _ = _
  rw [program.terminalStateLaw_step profile _ hterm, FinDist.expect_bind,
    InformationModel.behavioralJoint, FinDist.expect_map, FinDist.pi_map, FinDist.expect_map]
  apply FinDist.expect_congr
  intro draws _
  let bits := fun player => (choiceEquiv player).symm (draws player)
  have hdraws : ∀ player, draws player = choice player (bits player) :=
    fun player => ((choiceEquiv player).apply_symm_apply (draws player)).symm
  have hcommand : (fun player => (draws player).1) = joint bits := by
    funext player
    rw [hdraws player]
    rfl
  have hlegal : program.execution.Legal program.execution.init
      (fun player => (draws player).1) := by
    rw [hcommand]
    exact joint_legal bits
  have hstep : (program.execution.step program.execution.init
      ⟨fun player => (draws player).1, hlegal⟩) = FinDist.pure (after bits) := by
    change (toExecutionProtocol graph program.graphWF program.guardLive).step _ _ = _
    rw [toExecutionProtocol_step_eq_pure_applyFrontier _ _ _ _ _
      (matchingPenniesInitial_active 0).2.1]
    change FinDist.pure (applyFrontier graph program.graphWF program.execution.init
      (fun player => (draws player).1)) = _
    rw [hcommand]
    rfl
  calc
    _ = ((program.execution.step program.execution.init
        ⟨fun player => (draws player).1, hlegal⟩).bindOnSupport
          (fun _ _ => FinDist.pure (observable (payoff bits who)))).expect id := by
      apply FinDist.expect_bindOnSupport_congr
      intro next hnext
      have hnextEq : next = after bits := by
        change next ∈ (program.execution.step program.execution.init
          ⟨fun player => (draws player).1, hlegal⟩).support at hnext
        simpa only [hstep, FinDist.mem_support_pure] using hnext
      rw [FinDist.expect_pure]
      exact continuation_payoff profile bits _ hnextEq who observable
    _ = _ := by rw [FinDist.bindOnSupport_eq_bind, FinDist.bind_const, FinDist.expect_pure]; rfl

theorem expectedUtility_eq
    (profile : (who : TestPlayer) → program.information.BehavioralPolicy who) (who : TestPlayer) :
    expectedUtility program.boundedGame.behavioral.utility who
      (program.boundedGame.behavioral.form.play profile) =
    (FinDist.pi fun player => (profile player (initialInfo player)).map
      (choiceEquiv player).symm).expect (fun bits => payoff bits who) :=
  expectedPayoffObservable_eq profile who id

theorem initialLaw_fair (who : TestPlayer) :
    (fairPolicy who (initialInfo who)).map (choiceEquiv who).symm =
      (FinDist.uniformOfFintype : FinDist Bool) := by
  classical
  simp only [fairPolicy, Function.update_self, FinDist.map_comp]
  have hinverse : (choiceEquiv who).symm ∘ choice who = id :=
    funext fun bit => (choiceEquiv who).symm_apply_apply bit
  rw [hinverse, FinDist.map_id]

theorem pi_two (laws : TestPlayer → FinDist Bool) :
    FinDist.pi laws = ((laws 0).product (laws 1)).map (finTwoArrowEquiv Bool).symm := by
  apply FinDist.ext_of_prob
  intro bits
  conv_rhs => rw [show bits = (finTwoArrowEquiv Bool).symm ((finTwoArrowEquiv Bool) bits)
    from ((finTwoArrowEquiv Bool).symm_apply_apply bits).symm]
  rw [FinDist.prob_map_of_injective _ (Equiv.injective _), FinDist.prob_product,
    FinDist.prob_pi]
  simp [Fin.prod_univ_two, finTwoArrowEquiv, piFinTwoEquiv]

/-- A fair opponent makes every behavioral policy worth exactly zero. -/
theorem expectedUtility_eq_zero_of_opponent_fair
    (profile : (who : TestPlayer) → program.information.BehavioralPolicy who)
    (who : TestPlayer)
    (hfair : ∀ other, other ≠ who →
      (profile other (initialInfo other)).map (choiceEquiv other).symm =
        (FinDist.uniformOfFintype : FinDist Bool)) :
    expectedUtility program.boundedGame.behavioral.utility who
      (program.boundedGame.behavioral.form.play profile) = 0 := by
  rw [expectedUtility_eq, pi_two, FinDist.expect_map, FinDist.expect_eq_sum]
  fin_cases who
  · simp only [hfair 1 (by decide), FinDist.prob_product]
    simp [Fintype.sum_prod_type, FinDist.prob_uniformOfFintype, payoff,
      finTwoArrowEquiv, piFinTwoEquiv]
  · simp only [hfair 0 (by decide), FinDist.prob_product]
    simp [Fintype.sum_prod_type, FinDist.prob_uniformOfFintype, payoff,
      finTwoArrowEquiv, piFinTwoEquiv]
    ring

/-- The actual compiled hidden-choice game has its fair-coin Nash equilibrium;
deviations range over complete legal behavioral policies, including off-path choices. -/
theorem fair_isNash :
    IsNash program.boundedGame.behavioral.form (euPreference program.boundedGame.behavioral.utility)
      fairPolicy := by
  rw [isNash_iff]
  intro who replacement
  have hbase := expectedUtility_eq_zero_of_opponent_fair fairPolicy who
    (fun other _ => initialLaw_fair other)
  have hdev := expectedUtility_eq_zero_of_opponent_fair
    (Profile.update (sig := program.boundedGame.behavioral.form.sig) fairPolicy who replacement) who
    (fun other hne => by simpa [Profile.update, hne] using initialLaw_fair other)
  change expectedUtility program.boundedGame.behavioral.utility who
    (program.boundedGame.behavioral.form.play (Profile.update fairPolicy who replacement)) ≤
      expectedUtility program.boundedGame.behavioral.utility who
        (program.boundedGame.behavioral.form.play fairPolicy)
  rw [hbase, hdev]

theorem expectedUtilities_sum
    (profile : (who : TestPlayer) → program.information.BehavioralPolicy who) :
    expectedUtility program.boundedGame.behavioral.utility 0
        (program.boundedGame.behavioral.form.play profile) +
      expectedUtility program.boundedGame.behavioral.utility 1
        (program.boundedGame.behavioral.form.play profile) = 0 := by
  rw [expectedUtility_eq, expectedUtility_eq, ← FinDist.expect_add]
  calc
    _ = (FinDist.pi fun player => (profile player (initialInfo player)).map
        (choiceEquiv player).symm).expect (fun _ => 0) := by
      apply FinDist.expect_congr
      intro bits _
      by_cases heq : bits 0 = bits 1 <;> simp [payoff, heq]
    _ = 0 := FinDist.expect_const _ _

/-- One arbitrary adversary cannot change either player's expected payoff when
the other uses the fair policy. This assumes no adversarial objective. -/
theorem fair_deviation_payoff (who victim : TestPlayer)
    (replacement : program.information.BehavioralPolicy who) :
    expectedUtility program.boundedGame.behavioral.utility victim
      (program.boundedGame.behavioral.form.play
        (Profile.update fairPolicy who replacement)) = 0 := by
  have hdev := expectedUtility_eq_zero_of_opponent_fair
    (Profile.update (sig := program.boundedGame.behavioral.form.sig) fairPolicy who replacement) who
    (fun other hne => by simpa [Profile.update, hne] using initialLaw_fair other)
  have hsum := expectedUtilities_sum
    (Profile.update (sig := program.boundedGame.behavioral.form.sig) fairPolicy who replacement)
  let utility : TestPlayer → ℝ := fun player =>
    expectedUtility program.boundedGame.behavioral.utility player
      (program.boundedGame.behavioral.form.play
        (Profile.update (sig := program.boundedGame.behavioral.form.sig)
          fairPolicy who replacement))
  change utility who = 0 at hdev
  change utility 0 + utility 1 = 0 at hsum
  change utility victim = 0
  fin_cases who <;> fin_cases victim <;> norm_num at hdev hsum ⊢ <;> linarith

/-- Every behavioral public-data scheduler preserves this equilibrium in the
actual order-revealing implementation, against all behavioral player deviations. -/
theorem fair_serialized_isPlayerNash
    (schedulerUtility : program.serializedExecution.History → ℝ)
    (scheduler : program.serializedInformation.BehavioralPolicy .scheduler) :
    Participant.IsPlayerNash (program.serializedBoundedGame schedulerUtility).behavioral
      (program.compileSerializedBehavioralProfile scheduler fairPolicy) :=
  program.isPlayerNash_compileSerialized_of_isNash schedulerUtility scheduler fairPolicy fair_isNash

/-- Honest-player protection in the actual serialized implementation. The
scheduler and the deviating player may use arbitrary behavioral policies. -/
theorem fair_serialized_deviation_payoff
    (scheduler : program.serializedInformation.BehavioralPolicy .scheduler)
    (who victim : TestPlayer)
    (replacement : program.serializedInformation.BehavioralPolicy (.player who)) :
    (program.serializedInformation.runBehavioral
      (Function.update (program.compileSerializedBehavioralProfile scheduler fairPolicy)
        (.player who) replacement) graph.nodeCount).expect
          (fun history => program.payoutUtility history.state.base victim) = 0 :=
  program.serializedDeviation_expect_eq scheduler fairPolicy who
    (fun state => program.payoutUtility state victim) 0
    (fun alternative => fair_deviation_payoff who victim alternative) replacement

/-- info: 'VegasTests.MatchingPenniesEquilibrium.fair_serialized_isPlayerNash' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms VegasTests.MatchingPenniesEquilibrium.fair_serialized_isPlayerNash

/-- info: 'VegasTests.MatchingPenniesEquilibrium.fair_serialized_deviation_payoff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms VegasTests.MatchingPenniesEquilibrium.fair_serialized_deviation_payoff

end VegasTests.MatchingPenniesEquilibrium

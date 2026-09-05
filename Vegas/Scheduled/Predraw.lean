/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import Vegas.Scheduled.Replay

/-! # Predrawing one participant's randomness

Only the selected participant is predrawn. All other participants retain their
behavioral policies and private randomness throughout the comparison.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace Vegas.Scheduled

open GameTheory.Protocol GameTheory.Math.Probability

theorem pi_update_bind {ι α : Type*} [Fintype ι] [DecidableEq ι]
    {A : ι → Type*} (laws : ∀ i, FinDist (A i)) (who : ι)
    (μ : FinDist α) (choices : α → FinDist (A who)) :
    FinDist.pi (Function.update laws who (μ.bind choices)) =
      μ.bind (fun a => FinDist.pi (Function.update laws who (choices a))) := by
  have hrest : ∀ law : FinDist (A who),
      (fun j : {j // j ≠ who} => Function.update laws who law j.1) =
        (fun j : {j // j ≠ who} => laws j.1) := by
    intro law
    funext j
    exact Function.update_of_ne j.2 law laws
  rw [FinDist.pi_eq_map_product who, hrest]
  simp only [Function.update_self]
  conv_rhs => arg 2; ext a; rw [FinDist.pi_eq_map_product who]
  simp only [Function.update_self, hrest]
  simp only [FinDist.product, FinDist.bind_bind, FinDist.map_bind]

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
  {E : ExecutionProtocol ι} (M : InformationModel E)

/-- A local policy mixture at one participant commutes with the simultaneous
joint draw. Other participants are neither fixed nor disclosed. -/
theorem behavioralJoint_update_bind {α : Type*}
    (profile : (i : ι) → M.BehavioralPolicy i) (who : ι)
    (μ : FinDist α) (policies : α → M.BehavioralPolicy who)
    {state : E.State} (trace : E.Trace state) (hterm : ¬ E.terminal state) :
    M.behavioralJoint (Function.update profile who (fun info =>
      μ.bind (fun a => policies a info))) trace hterm =
    μ.bind (fun a => M.behavioralJoint (Function.update profile who (policies a)) trace hterm) := by
  have hupdate : ∀ policy : M.BehavioralPolicy who,
      (fun i => Function.update profile who policy i (M.infoOf i trace)) =
        Function.update (fun i => profile i (M.infoOf i trace)) who
          (policy (M.infoOf who trace)) := by
    intro policy
    funext i
    by_cases heq : i = who
    · subst i; simp
    · simp [Function.update_of_ne heq]
  simp only [InformationModel.behavioralJoint, hupdate]
  rw [pi_update_bind, FinDist.map_bind]

/-- Predrawing one policy on finitely many sites is exact when its information
never repeats along a strict history extension. Other policies remain behavioral. -/
theorem runBehavioralFrom_predrawOneOn (who : ι) [DecidableEq (M.InfoState who)]
    (hfresh : ∀ first later : E.History, first.trace.length < later.trace.length →
      M.infoOf who later.trace ≠ M.infoOf who first.trace)
    (profile : (i : ι) → M.BehavioralPolicy i) :
    ∀ (fuel : Nat) (policy : M.BehavioralPolicy who)
      (sites : Finset (M.InfoState who)) (fallback : M.Policy who) (start : E.History),
      (∀ info, info ∉ sites → policy info = FinDist.pure (fallback info)) →
      ((policy.toMixedOn sites fallback).bind fun purePolicy =>
        M.runBehavioralFrom (Function.update profile who purePolicy.toBehavioral) fuel start) =
      M.runBehavioralFrom (Function.update profile who policy) fuel start := by
  classical
  intro fuel
  induction fuel with
  | zero => intros; exact FinDist.bind_const _ _
  | succ fuel ih =>
      intro policy sites fallback start hfinite
      by_cases hterm : E.terminal start.state
      · simp only [InformationModel.runBehavioralFrom_of_terminal _ _ _ hterm,
          FinDist.bind_const]
      · let info := M.infoOf who start.trace
        let assemble : M.Choice who info → M.Policy who → M.Policy who :=
          fun choice rest => FinDist.DependentAssignment.setOne rest ⟨info, choice⟩
        let restLaw := policy.toMixedOn (sites.erase info) fallback
        have hfactor : policy.toMixedOn sites fallback =
            (FinDist.product (policy info) restLaw).map
              (fun pair => assemble pair.1 pair.2) := by
          by_cases hinfo : info ∈ sites
          · exact FinDist.runDependent_factor_of_mem policy sites fallback info hinfo
          · exact FinDist.runDependent_factor_of_not_mem policy sites fallback info hinfo
              (hfinite info hinfo)
        have hhere : ∀ choice rest,
            M.behavioralJoint (Function.update profile who (assemble choice rest).toBehavioral)
                start.trace hterm =
            M.behavioralJoint (Function.update profile who (assemble choice fallback).toBehavioral)
                start.trace hterm := by
          intro choice rest
          apply InformationModel.behavioralJoint_congr
          intro i
          by_cases heq : i = who
          · subst i; simp [assemble, info, InformationModel.Policy.toBehavioral]
          · simp [Function.update_of_ne heq]
        have hdraw : M.behavioralJoint (Function.update profile who policy) start.trace hterm =
            (policy info).bind (fun choice => M.behavioralJoint
              (Function.update profile who (assemble choice fallback).toBehavioral)
                start.trace hterm) := by
          rw [← behavioralJoint_update_bind]
          apply InformationModel.behavioralJoint_congr
          intro i
          by_cases heq : i = who
          · subst i
            simp [assemble, info, InformationModel.Policy.toBehavioral]
          · simp [Function.update_of_ne heq]
        rw [hfactor, FinDist.bind_map, FinDist.product, FinDist.bind_bind,
          InformationModel.runBehavioralFrom_succ_of_not_terminal _ _ _ hterm,
          hdraw, FinDist.bind_bind]
        apply FinDist.bind_congr
        intro choice _
        rw [FinDist.bind_map]
        have hruns : ∀ rest,
            M.runBehavioralFrom (Function.update profile who (assemble choice rest).toBehavioral)
                (fuel + 1) start =
            (M.behavioralJoint
              (Function.update profile who (assemble choice fallback).toBehavioral)
                start.trace hterm).bind fun command =>
              (E.step start.state command).bindOnSupport fun _ realized =>
                M.runBehavioralFrom
                  (Function.update profile who (assemble choice rest).toBehavioral)
                  fuel (start.extend command.2 realized) := by
          intro rest
          rw [InformationModel.runBehavioralFrom_succ_of_not_terminal _ _ _ hterm, hhere]
        simp only [hruns]
        rw [FinDist.bind_comm]
        apply FinDist.bind_congr
        intro command _
        rw [FinDist.bind_bindOnSupport_comm]
        apply FinDist.bindOnSupport_congr
        intro next realized
        have hcommit : restLaw.map (assemble choice) =
            (policy.commit info choice).toMixedOn (sites.erase info)
              (assemble choice fallback) := by
          have hnot : info ∉ (sites.erase info).toList := by simp
          change (policy.toMixedOn _ fallback).map _ = _
          rw [InformationModel.BehavioralPolicy.toMixedOn,
            InformationModel.BehavioralPolicy.toMixedOn,
            ← FinDist.runDependent_setOne_of_not_mem policy _ fallback info choice hnot]
          apply FinDist.runDependent_congr_laws
          intro other hother
          apply (InformationModel.BehavioralPolicy.commit_of_ne _ _ _ ?_).symm
          intro heq
          subst other
          exact hnot hother
        have hfinite' : ∀ other, other ∉ sites.erase info →
            policy.commit info choice other = FinDist.pure (assemble choice fallback other) := by
          intro other hother
          by_cases heq : other = info
          · subst other
            simp [assemble]
          · rw [InformationModel.BehavioralPolicy.commit_of_ne _ _ _ heq]
            change policy other = FinDist.pure
              (FinDist.DependentAssignment.setOne fallback ⟨info, choice⟩ other)
            rw [FinDist.DependentAssignment.setOne_apply_of_ne _ _ heq]
            exact hfinite other (fun hmem => hother (Finset.mem_erase.mpr ⟨heq, hmem⟩))
        rw [← FinDist.bind_map (f := assemble choice)
          (g := fun purePolicy : M.Policy who => M.runBehavioralFrom
            (Function.update profile who purePolicy.toBehavioral) fuel
            (start.extend command.2 realized)), hcommit,
          ih (policy.commit info choice) (sites.erase info) (assemble choice fallback)
            (start.extend command.2 realized) hfinite']
        apply M.runBehavioralFrom_congr
        intro later hreach _ i
        by_cases heq : i = who
        · subst i
          simp only [Function.update_self]
          apply InformationModel.BehavioralPolicy.commit_of_ne
          apply hfresh start later
          have hlength := hreach.trace_length_le
          change start.trace.length + 1 ≤ later.trace.length at hlength
          omega
        · simp [Function.update_of_ne heq]

/-- Every finite behavioral run can predraw just one participant. The finite
table covers this run's support; no finiteness assumption on ambient information
or on other participants' strategy spaces is required. -/
theorem exists_predrawOne (who : ι)
    (hfresh : ∀ first later : E.History, first.trace.length < later.trace.length →
      M.infoOf who later.trace ≠ M.infoOf who first.trace)
    (profile : (i : ι) → M.BehavioralPolicy i) (fuel : Nat) (start : E.History) :
    ∃ policies : FinDist (M.Policy who),
      (policies.bind fun policy => M.runBehavioralFrom
        (Function.update profile who policy.toBehavioral) fuel start) =
      M.runBehavioralFrom profile fuel start := by
  classical
  let sites := M.behavioralSupportSitesFrom profile fuel start who
  let fallback := (profile who).supportFallback
  let finitePolicy : M.BehavioralPolicy who := fun info =>
    if info ∈ sites then profile who info else FinDist.pure (fallback info)
  refine ⟨finitePolicy.toMixedOn sites fallback, ?_⟩
  rw [runBehavioralFrom_predrawOneOn M who hfresh profile fuel finitePolicy sites fallback start
    (by intro info hinfo; simp [finitePolicy, hinfo])]
  symm
  apply M.runBehavioralFrom_congr_on_support
  intro elapsed helapsed later hlater _ i
  by_cases heq : i = who
  · subst i
    have hmem := M.mem_behavioralSupportSitesFrom profile fuel elapsed helapsed start later
      hlater who
    simp [finitePolicy, sites, hmem]
  · simp [Function.update_of_ne heq]

end Vegas.Scheduled

namespace Vegas.ScheduledSystem

open GameTheory.Protocol GameTheory.Math.Probability

variable {ι : Type} (sys : ScheduledSystem ι)

/-- Public order/view memory counts every executed round. -/
theorem revealingInfo_past_length (who : Participant ι)
    {state : sys.toExecutionProtocol.State} (trace : sys.toExecutionProtocol.Trace state) :
    (sys.revealingSignals.infoOf who trace).past.length = trace.length := by
  induction trace with
  | start => rfl
  | extend prior _ _ _ ih =>
      change (sys.revealingSignals.infoOf who prior).past.length + 1 = prior.length + 1
      rw [ih]

variable [Fintype ι]

/-- A behavioral scheduler is a mixture of actually executing deterministic
public-history schedulers, with every player's behavioral policy untouched.
The witness is local to the bounded run, which is sufficient for deviation
inequalities and does not assert a uniform finite table for all profiles. -/
theorem exists_predrawScheduler
    (profile : (who : Participant ι) → sys.revealingInformation.BehavioralPolicy who)
    (fuel : Nat) (start : sys.toExecutionProtocol.History) :
    ∃ schedulers : FinDist (sys.revealingInformation.Policy .scheduler),
      (schedulers.bind fun scheduler => sys.revealingInformation.runBehavioralFrom
        (sys.fixScheduler scheduler profile) fuel start) =
      sys.revealingInformation.runBehavioralFrom profile fuel start := by
  classical
  obtain ⟨schedulers, hlaw⟩ := Scheduled.exists_predrawOne sys.revealingInformation .scheduler
    (fun first later hlength heq => by
      have heqlength := congrArg (fun info => info.past.length) heq
      rw [sys.revealingInfo_past_length, sys.revealingInfo_past_length] at heqlength
      omega) profile fuel start
  refine ⟨schedulers, ?_⟩
  have hupdate : ∀ scheduler : sys.revealingInformation.Policy .scheduler,
      Function.update profile .scheduler scheduler.toBehavioral =
        sys.fixScheduler scheduler profile := by
    intro scheduler
    funext who
    cases who <;> simp [fixScheduler]
  simpa only [hupdate] using hlaw

end Vegas.ScheduledSystem

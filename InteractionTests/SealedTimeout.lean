import Interaction.SealedTimeoutPolicyLaws
import Interaction.SealedTimeoutHiding

/-! # Deadline boundaries and timed-policy trust checks -/

namespace InteractionTests.SealedTimeout

open Interaction

private def pending : Deadline := ⟨10, .pending⟩

#guard pending.expire 10 = none
#guard pending.expire 11 = some ⟨10, .expired⟩
#guard pending.complete = some ⟨10, .completed⟩
#guard (pending.complete.bind (Deadline.expire 11)) = none
#guard ((pending.expire 11).bind Deadline.complete) = none

end InteractionTests.SealedTimeout

/-- info: 'Interaction.SealedTimeout.handle_expire_success_iff' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Interaction.SealedTimeout.handle_expire_success_iff

/-- info: 'Interaction.SealedTimeout.handle_expire_updates_only_resolution' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms Interaction.SealedTimeout.handle_expire_updates_only_resolution

/-- info: 'Interaction.SealedTimeout.includePending_reject' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms Interaction.SealedTimeout.includePending_reject

/-- info: 'Interaction.SealedTimeout.includePending_preserves_inbox' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms Interaction.SealedTimeout.includePending_preserves_inbox

/-- info: 'Interaction.SealedTimeout.runPolicies_native_eq_run_trace' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Interaction.SealedTimeout.runPolicies_native_eq_run_trace

/-- info: 'Interaction.SealedTimeout.runPolicies_lookup_of_eq_some' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Interaction.SealedTimeout.runPolicies_lookup_of_eq_some

/-- info: 'Interaction.SealedProgram.validateMessage?_eq_of_serviceAgreement' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms Interaction.SealedProgram.validateMessage?_eq_of_serviceAgreement

/-- info: 'Interaction.SealedTimeout.HidingRelated.run' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms Interaction.SealedTimeout.HidingRelated.run

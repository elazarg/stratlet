/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import Interaction.MessagePool

/-! # Explicit endpoint routing for native messages

The endpoint is public payload data, independent of the sender-local message
identifier. Routing removes only that tag and preserves the original author and
serial. It introduces no authentication or cryptographic assumption.
-/

namespace Interaction.Message

universe uPrincipal uEndpoint uPayload uResult

variable {Principal : Type uPrincipal} {Endpoint : Type uEndpoint}
variable {Payload : Type uPayload} {Result : Type uResult}
variable [DecidableEq Endpoint]

/-- Select one explicitly addressed endpoint without changing the envelope's
sender-local identifier. Unknown or different endpoints are rejected. -/
def routeEndpoint? (endpoint : Endpoint)
    (message : Message Principal (Endpoint × Payload)) : Option (Message Principal Payload) :=
  if message.payload.1 = endpoint then some ⟨message.id, message.payload.2⟩ else none

@[simp]
theorem routeEndpoint?_addressed (endpoint : Endpoint) (id : MessageId Principal)
    (payload : Payload) :
    routeEndpoint? endpoint ⟨id, (endpoint, payload)⟩ = some ⟨id, payload⟩ := by
  simp [routeEndpoint?]

@[simp]
theorem routeEndpoint?_other (endpoint other : Endpoint) (id : MessageId Principal)
    (payload : Payload) (hne : other ≠ endpoint) :
    routeEndpoint? endpoint ⟨id, (other, payload)⟩ = none := by
  simp [routeEndpoint?, hne]

theorem routeEndpoint?_id (endpoint : Endpoint)
    (message : Message Principal (Endpoint × Payload)) (routed : Message Principal Payload)
    (hroute : routeEndpoint? endpoint message = some routed) : routed.id = message.id := by
  unfold routeEndpoint? at hroute
  split at hroute
  · cases hroute
    rfl
  · cases hroute

/-- Route an addressed message into an existing partial handler. The handler
receives the same author and serial, and no callback runs on a tag mismatch. -/
def dispatchEndpoint? (endpoint : Endpoint)
    (handler : Message Principal Payload → Option Result)
    (message : Message Principal (Endpoint × Payload)) : Option Result :=
  (routeEndpoint? endpoint message).bind handler

@[simp]
theorem dispatchEndpoint?_addressed (endpoint : Endpoint)
    (handler : Message Principal Payload → Option Result) (id : MessageId Principal)
    (payload : Payload) :
    dispatchEndpoint? endpoint handler ⟨id, (endpoint, payload)⟩ =
      handler ⟨id, payload⟩ := by
  simp [dispatchEndpoint?]

@[simp]
theorem dispatchEndpoint?_other (endpoint other : Endpoint)
    (handler : Message Principal Payload → Option Result) (id : MessageId Principal)
    (payload : Payload) (hne : other ≠ endpoint) :
    dispatchEndpoint? endpoint handler ⟨id, (other, payload)⟩ = none := by
  simp [dispatchEndpoint?, hne]

end Interaction.Message

/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import VegasEVM.Contract.EVMAssembly

/-!
# Local EVM labels and conditional control flow

Handler compilers should not calculate absolute jump destinations by hand.
This layer gives each handler a local label namespace, computes byte offsets
with fixed-width `PUSH4` destinations, and resolves labels after the four
handler base addresses are known. Resolution preserves the statically computed
byte length. A linked local-handler image therefore inherits the existing
32-bit whole-image bound and cannot truncate an internal destination.
-/

namespace Vegas.Machine.Contract.EVM

/-- Handler-local label identifier. -/
abbrev LocalLabel := Nat

/-- One symbolic handler item. Labels emit `JUMPDEST`; jumps emit a `PUSH4`
absolute destination followed by `JUMP` or `JUMPI`. -/
inductive LocalItem where
  | op (instruction : Instruction)
  | label (label : LocalLabel)
  | jump (target : LocalLabel)
  | jumpi (target : LocalLabel)

namespace LocalItem

/-- Encoded size before label resolution. Fixed-width destinations make this
independent of the final handler base address. -/
def byteLength : LocalItem → Nat
  | .op instruction => instruction.byteLength
  | .label _ => 1
  | .jump _ | .jumpi _ => 6

end LocalItem

/-- Symbolic assembly with one local label namespace. -/
abbrev LocalAssembly := List LocalItem

namespace LocalAssembly

/-- Static encoded byte length. -/
def byteLength (program : LocalAssembly) : Nat :=
  (program.map LocalItem.byteLength).sum

/-- Embed straight-line resolved assembly in a symbolic handler. -/
def ofAssembly (program : Assembly) : LocalAssembly :=
  program.map LocalItem.op

/-- Labels defined by a symbolic fragment, in source order. -/
def definedLabels : LocalAssembly → List LocalLabel
  | [] => []
  | .label label :: rest => label :: definedLabels rest
  | _ :: rest => definedLabels rest

/-- Every local label has at most one definition. -/
def LabelsUnique (program : LocalAssembly) : Prop :=
  program.definedLabels.Nodup

instance (program : LocalAssembly) : Decidable program.LabelsUnique := by
  unfold LabelsUnique
  infer_instance

@[simp] theorem ofAssembly_byteLength (program : Assembly) :
    (ofAssembly program).byteLength = program.byteLength := by
  induction program with
  | nil => rfl
  | cons instruction rest ih =>
      change instruction.byteLength + (ofAssembly rest).byteLength =
        instruction.byteLength + Assembly.byteLength rest
      rw [ih]

@[simp] theorem byteLength_append (left right : LocalAssembly) :
    (left ++ right).byteLength = left.byteLength + right.byteLength := by
  simp [byteLength]

/-- Locate the first matching label while accumulating a local byte offset. -/
def labelOffsetFrom : LocalAssembly → LocalLabel → Nat → Option Nat
  | [], _, _ => none
  | .label found :: rest, target, offset =>
      if found = target then some offset
      else labelOffsetFrom rest target (offset + 1)
  | item :: rest, target, offset =>
      labelOffsetFrom rest target (offset + item.byteLength)

/-- Local byte offset of the first matching label. -/
def labelOffset? (program : LocalAssembly) (target : LocalLabel) : Option Nat :=
  labelOffsetFrom program target 0

/-- Finding a label exposes the source prefix whose encoded length determines
the returned accumulated offset. -/
theorem labelOffsetFrom_eq_some
    (program : LocalAssembly) (target start offset : Nat)
    (hfind : labelOffsetFrom program target start = some offset) :
    ∃ pre suffix,
      program = pre ++ [LocalItem.label target] ++ suffix ∧
      start + LocalAssembly.byteLength pre = offset := by
  induction program generalizing start with
  | nil => simp [labelOffsetFrom] at hfind
  | cons item rest ih =>
      cases item with
      | label found =>
          by_cases heq : found = target
          · subst found
            have hoffset : start = offset := by
              simpa [labelOffsetFrom] using hfind
            subst offset
            exact ⟨[], rest, by simp, by simp [LocalAssembly.byteLength]⟩
          · have hrestFind :
                labelOffsetFrom rest target (start + 1) = some offset := by
              simpa [labelOffsetFrom, heq] using hfind
            rcases ih (start + 1) hrestFind with
              ⟨pre, suffix, hrest, hlength⟩
            refine ⟨LocalItem.label found :: pre, suffix, ?_, ?_⟩
            · simp [hrest]
            · change start + (1 + LocalAssembly.byteLength pre) = offset
              omega
      | op instruction =>
          simp only [labelOffsetFrom] at hfind
          rcases ih (start + LocalItem.byteLength
              (LocalItem.op instruction)) hfind with
            ⟨pre, suffix, hrest, hlength⟩
          refine ⟨LocalItem.op instruction :: pre, suffix, ?_, ?_⟩
          · simp [hrest]
          · change start + (instruction.byteLength +
                LocalAssembly.byteLength pre) = offset
            simp only [LocalItem.byteLength] at hlength
            omega
      | jump destination =>
          simp only [labelOffsetFrom] at hfind
          rcases ih (start + LocalItem.byteLength
              (LocalItem.jump destination)) hfind with
            ⟨pre, suffix, hrest, hlength⟩
          refine ⟨LocalItem.jump destination :: pre, suffix, ?_, ?_⟩
          · simp [hrest]
          · change start + (6 + LocalAssembly.byteLength pre) = offset
            simp only [LocalItem.byteLength] at hlength
            omega
      | jumpi destination =>
          simp only [labelOffsetFrom] at hfind
          rcases ih (start + LocalItem.byteLength
              (LocalItem.jumpi destination)) hfind with
            ⟨pre, suffix, hrest, hlength⟩
          refine ⟨LocalItem.jumpi destination :: pre, suffix, ?_, ?_⟩
          · simp [hrest]
          · change start + (6 + LocalAssembly.byteLength pre) = offset
            simp only [LocalItem.byteLength] at hlength
            omega

/-- A local label offset is exactly the encoded byte length of a prefix ending
immediately before the selected label. -/
theorem labelOffset?_eq_some
    (program : LocalAssembly) (target offset : Nat)
    (hfind : program.labelOffset? target = some offset) :
    ∃ pre suffix,
      program = pre ++ [LocalItem.label target] ++ suffix ∧
      LocalAssembly.byteLength pre = offset := by
  rcases labelOffsetFrom_eq_some program target 0 offset hfind with
    ⟨pre, suffix, hprogram, hlength⟩
  exact ⟨pre, suffix, hprogram, by simpa using hlength⟩

/-- A found label begins strictly inside its handler's encoded extent. -/
theorem labelOffset?_lt_byteLength
    (program : LocalAssembly) (target offset : Nat)
    (hfind : program.labelOffset? target = some offset) :
    offset < program.byteLength := by
  rcases labelOffset?_eq_some program target offset hfind with
    ⟨pre, suffix, hprogram, hlength⟩
  rw [hprogram, byteLength_append, byteLength_append, hlength]
  simp [LocalAssembly.byteLength, LocalItem.byteLength]
  omega

/-- Resolve one symbolic item against the complete local program. -/
def resolveItem? (whole : LocalAssembly) (base : Nat) :
    LocalItem → Option Assembly
  | .op instruction => some [instruction]
  | .label _ => some [.jumpdest]
  | .jump target =>
      (whole.labelOffset? target).map fun offset =>
        [.push (.nat32 (base + offset)), .jump]
  | .jumpi target =>
      (whole.labelOffset? target).map fun offset =>
        [.push (.nat32 (base + offset)), .jumpi]

/-- Resolve a suffix against the label namespace of its complete program. -/
def resolveFrom? (whole : LocalAssembly) (base : Nat) :
    LocalAssembly → Option Assembly
  | [] => some []
  | item :: rest =>
      match resolveItem? whole base item, resolveFrom? whole base rest with
      | some head, some tail => some (head ++ tail)
      | _, _ => none

@[simp] theorem resolveFrom?_ofAssembly (whole : LocalAssembly) (base : Nat)
    (program : Assembly) :
    resolveFrom? whole base (ofAssembly program) = some program := by
  induction program with
  | nil => rfl
  | cons instruction rest ih =>
      change
        (match some [instruction], resolveFrom? whole base (ofAssembly rest) with
        | some head, some tail => some (head ++ tail)
        | _, _ => none) = some (instruction :: rest)
      rw [ih]
      rfl

/-- Resolution distributes over symbolic-fragment concatenation. -/
theorem resolveFrom?_append (whole : LocalAssembly) (base : Nat)
    (left right : LocalAssembly) :
    resolveFrom? whole base (left ++ right) =
      match resolveFrom? whole base left, resolveFrom? whole base right with
      | some leftCode, some rightCode => some (leftCode ++ rightCode)
      | _, _ => none := by
  induction left with
  | nil =>
      cases hright : resolveFrom? whole base right <;>
        simp [resolveFrom?, hright]
  | cons item rest ih =>
      simp only [List.cons_append, resolveFrom?]
      rw [ih]
      cases resolveItem? whole base item <;>
        cases resolveFrom? whole base rest <;>
        cases resolveFrom? whole base right <;>
        simp [List.append_assoc]

/-- Resolve all labels to absolute byte destinations. Missing labels reject
the fragment. -/
def resolveAt (base : Nat) (whole : LocalAssembly) : Option Assembly :=
  resolveFrom? whole base whole

/-- Resolving one item never changes its encoded size. -/
theorem resolveItem?_byteLength {whole : LocalAssembly} {base : Nat}
    {item : LocalItem} {resolved : Assembly}
    (hresolve : resolveItem? whole base item = some resolved) :
    resolved.byteLength = item.byteLength := by
  cases item with
  | op instruction =>
      simp [resolveItem?] at hresolve
      subst resolved
      simp [LocalItem.byteLength, Assembly.byteLength]
  | label label =>
      simp [resolveItem?] at hresolve
      subst resolved
      simp [LocalItem.byteLength, Assembly.byteLength,
        Instruction.byteLength]
  | jump target =>
      unfold resolveItem? at hresolve
      cases hoffset : labelOffset? whole target with
      | none => simp [hoffset] at hresolve
      | some offset =>
          simp [hoffset] at hresolve
          subst resolved
          simp [LocalItem.byteLength, Assembly.byteLength,
            Instruction.byteLength]
  | jumpi target =>
      unfold resolveItem? at hresolve
      cases hoffset : labelOffset? whole target with
      | none => simp [hoffset] at hresolve
      | some offset =>
          simp [hoffset] at hresolve
          subst resolved
          simp [LocalItem.byteLength, Assembly.byteLength,
            Instruction.byteLength]

/-- Resolving any symbolic suffix preserves its encoded byte length. -/
theorem resolveFrom?_byteLength {whole rest : LocalAssembly} {base : Nat}
    {resolved : Assembly}
    (hresolve : resolveFrom? whole base rest = some resolved) :
    resolved.byteLength = rest.byteLength := by
  induction rest generalizing resolved with
  | nil =>
      simp [resolveFrom?] at hresolve
      subst resolved
      rfl
  | cons item tail ih =>
      cases hitem : resolveItem? whole base item with
      | none => simp [resolveFrom?, hitem] at hresolve
      | some head =>
          cases htail : resolveFrom? whole base tail with
          | none => simp [resolveFrom?, hitem, htail] at hresolve
          | some suffix =>
              simp only [resolveFrom?, hitem, htail,
                Option.some.injEq] at hresolve
              subst resolved
              rw [Assembly.byteLength_append,
                resolveItem?_byteLength hitem, ih htail]
              simp [LocalAssembly.byteLength]
/-- Successful whole-fragment resolution preserves byte length. -/
theorem resolveAt_byteLength {base : Nat} {program : LocalAssembly}
    {resolved : Assembly} (hresolve : resolveAt base program = some resolved) :
    resolved.byteLength = program.byteLength := by
  exact resolveFrom?_byteLength hresolve

/-- A straight-line assembly fragment embedded in a symbolic handler remains
the exact fragment after successful resolution. The resolved prefix has the
same byte length as its symbolic source. -/
theorem resolveAt_decomposition
    {base : Nat} {program pre suffix : LocalAssembly}
    {fragment resolved : Assembly}
    (hprogram : program = pre ++ ofAssembly fragment ++ suffix)
    (hresolve : resolveAt base program = some resolved) :
    ∃ preCode suffixCode,
      resolved = preCode ++ fragment ++ suffixCode ∧
      preCode.byteLength = pre.byteLength := by
  subst program
  rw [List.append_assoc] at hresolve
  unfold resolveAt at hresolve
  rw [resolveFrom?_append, resolveFrom?_append,
    resolveFrom?_ofAssembly] at hresolve
  cases hpre : resolveFrom? (pre ++ (ofAssembly fragment ++ suffix)) base pre with
  | none => simp [hpre] at hresolve
  | some preCode =>
      cases hsuffix : resolveFrom? (pre ++ (ofAssembly fragment ++ suffix)) base
          suffix with
      | none => simp [hpre, hsuffix] at hresolve
      | some suffixCode =>
          simp only [hpre, hsuffix, Option.some.injEq] at hresolve
          subst resolved
          refine ⟨preCode, suffixCode, ?_, ?_⟩
          · simp [List.append_assoc]
          · exact resolveFrom?_byteLength hpre

/-- Resolving a complete local handler preserves any selected symbolic
subfragment together with the subfragment's own resolved instruction code. -/
theorem resolveAt_resolved_decomposition
    {base : Nat} {program pre fragment suffix : LocalAssembly}
    {fragmentCode resolved : Assembly}
    (hprogram : program = pre ++ fragment ++ suffix)
    (hfragment : resolveFrom? program base fragment = some fragmentCode)
    (hresolve : resolveAt base program = some resolved) :
    ∃ preCode suffixCode,
      resolved = preCode ++ fragmentCode ++ suffixCode ∧
      preCode.byteLength = pre.byteLength := by
  subst program
  rw [List.append_assoc] at hresolve
  rw [List.append_assoc] at hfragment
  unfold resolveAt at hresolve
  rw [resolveFrom?_append, resolveFrom?_append, hfragment] at hresolve
  cases hpre : resolveFrom? (pre ++ (fragment ++ suffix)) base pre with
  | none => simp [hpre] at hresolve
  | some preCode =>
      cases hsuffix : resolveFrom? (pre ++ (fragment ++ suffix)) base suffix with
      | none => simp [hpre, hsuffix] at hresolve
      | some suffixCode =>
          simp only [hpre, hsuffix, Option.some.injEq] at hresolve
          subst resolved
          refine ⟨preCode, suffixCode, ?_, ?_⟩
          · simp [List.append_assoc]
          · exact resolveFrom?_byteLength hpre

end LocalAssembly

/-- Four symbolic classical handlers. -/
structure LocalClassicalHandlers where
  player : LocalAssembly
  reveal : LocalAssembly
  sampleRequest : LocalAssembly
  oracleCallback : LocalAssembly

namespace LocalClassicalHandlers

def get (handlers : LocalClassicalHandlers) : ClassicalEntry → LocalAssembly
  | .player => handlers.player
  | .reveal => handlers.reveal
  | .sampleRequest => handlers.sampleRequest
  | .oracleCallback => handlers.oracleCallback

/-- Local label definitions are unique independently in each handler
namespace. -/
def LabelsUnique (handlers : LocalClassicalHandlers) : Prop :=
  handlers.player.LabelsUnique ∧ handlers.reveal.LabelsUnique ∧
    handlers.sampleRequest.LabelsUnique ∧
    handlers.oracleCallback.LabelsUnique

instance (handlers : LocalClassicalHandlers) :
    Decidable handlers.LabelsUnique := by
  unfold LabelsUnique
  infer_instance

def blockSize (handlers : LocalClassicalHandlers)
    (entry : ClassicalEntry) : Nat :=
  2 + (handlers.get entry).byteLength

def runtimeSize (handlers : LocalClassicalHandlers) : Nat :=
  classicalDispatcherSize + handlers.blockSize .player +
    handlers.blockSize .reveal + handlers.blockSize .sampleRequest +
    handlers.blockSize .oracleCallback

def entryOffset (handlers : LocalClassicalHandlers) : ClassicalEntry → Nat
  | .player => classicalDispatcherSize
  | .reveal => classicalDispatcherSize + handlers.blockSize .player
  | .sampleRequest =>
      classicalDispatcherSize + handlers.blockSize .player +
        handlers.blockSize .reveal
  | .oracleCallback =>
      classicalDispatcherSize + handlers.blockSize .player +
        handlers.blockSize .reveal + handlers.blockSize .sampleRequest

/-- Every byte inside a selected handler lies inside the complete linked
runtime extent. -/
theorem internalOffset_lt_runtimeSize (handlers : LocalClassicalHandlers)
    (entry : ClassicalEntry) (offset : Nat)
    (hoffset : offset < (handlers.get entry).byteLength) :
    handlers.entryOffset entry + 2 + offset < handlers.runtimeSize := by
  cases entry <;>
    simp only [entryOffset, runtimeSize, blockSize, get] at hoffset ⊢ <;>
    omega

/-- Resolve every handler at the byte offset immediately after its linked
`JUMPDEST; POP` prefix. -/
def resolve? (handlers : LocalClassicalHandlers) : Option ClassicalHandlers :=
  match handlers.player.resolveAt (handlers.entryOffset .player + 2),
      handlers.reveal.resolveAt (handlers.entryOffset .reveal + 2),
      handlers.sampleRequest.resolveAt
        (handlers.entryOffset .sampleRequest + 2),
      handlers.oracleCallback.resolveAt
        (handlers.entryOffset .oracleCallback + 2) with
  | some player, some reveal, some sampleRequest, some oracleCallback =>
      some { player, reveal, sampleRequest, oracleCallback }
  | _, _, _, _ => none

/-- Successful handler resolution preserves the complete runtime size. -/
theorem resolve?_runtimeSize {handlers : LocalClassicalHandlers}
    {resolved : ClassicalHandlers}
    (hresolve : handlers.resolve? = some resolved) :
    classicalRuntimeSize resolved = handlers.runtimeSize := by
  cases hp : handlers.player.resolveAt (handlers.entryOffset .player + 2) with
  | none => simp [resolve?, hp] at hresolve
  | some player =>
      cases hr : handlers.reveal.resolveAt (handlers.entryOffset .reveal + 2) with
      | none => simp [resolve?, hp, hr] at hresolve
      | some reveal =>
          cases hs : handlers.sampleRequest.resolveAt
              (handlers.entryOffset .sampleRequest + 2) with
          | none => simp [resolve?, hp, hr, hs] at hresolve
          | some sampleRequest =>
              cases ho : handlers.oracleCallback.resolveAt
                  (handlers.entryOffset .oracleCallback + 2) with
              | none => simp [resolve?, hp, hr, hs, ho] at hresolve
              | some oracleCallback =>
                  unfold resolve? at hresolve
                  rw [hp, hr, hs, ho] at hresolve
                  cases hresolve
                  simp only [classicalRuntimeSize,
                    ClassicalHandlers.blockSize, ClassicalHandlers.get,
                    runtimeSize, blockSize, get]
                  rw [LocalAssembly.resolveAt_byteLength hp,
                    LocalAssembly.resolveAt_byteLength hr,
                    LocalAssembly.resolveAt_byteLength hs,
                    LocalAssembly.resolveAt_byteLength ho]

/-- Successful four-handler resolution exposes the exact resolution result of
each source handler. -/
theorem resolve?_components {handlers : LocalClassicalHandlers}
    {resolved : ClassicalHandlers}
    (hresolve : handlers.resolve? = some resolved) :
    handlers.player.resolveAt (handlers.entryOffset .player + 2) =
        some resolved.player ∧
      handlers.reveal.resolveAt (handlers.entryOffset .reveal + 2) =
        some resolved.reveal ∧
      handlers.sampleRequest.resolveAt
          (handlers.entryOffset .sampleRequest + 2) =
        some resolved.sampleRequest ∧
      handlers.oracleCallback.resolveAt
          (handlers.entryOffset .oracleCallback + 2) =
        some resolved.oracleCallback := by
  cases hp : handlers.player.resolveAt (handlers.entryOffset .player + 2) with
  | none => simp [resolve?, hp] at hresolve
  | some player =>
      cases hr : handlers.reveal.resolveAt
          (handlers.entryOffset .reveal + 2) with
      | none => simp [resolve?, hp, hr] at hresolve
      | some reveal =>
          cases hs : handlers.sampleRequest.resolveAt
              (handlers.entryOffset .sampleRequest + 2) with
          | none => simp [resolve?, hp, hr, hs] at hresolve
          | some sampleRequest =>
              cases ho : handlers.oracleCallback.resolveAt
                  (handlers.entryOffset .oracleCallback + 2) with
              | none => simp [resolve?, hp, hr, hs, ho] at hresolve
              | some oracleCallback =>
                  simp only [resolve?, hp, hr, hs, ho,
                    Option.some.injEq] at hresolve
                  subst resolved
                  constructor
                  · rfl
                  constructor
                  · rfl
                  constructor
                  · rfl
                  · rfl

/-- Every public entry retains the same byte offset when its local handlers
are resolved. -/
theorem resolve?_entryOffset {handlers : LocalClassicalHandlers}
    {resolved : ClassicalHandlers}
    (hresolve : handlers.resolve? = some resolved)
    (entry : ClassicalEntry) :
    classicalEntryOffset resolved entry = handlers.entryOffset entry := by
  rcases resolve?_components hresolve with ⟨hp, hr, hs, ho⟩
  cases entry <;>
    simp only [classicalEntryOffset, entryOffset, blockSize,
      ClassicalHandlers.blockSize, ClassicalHandlers.get, get] <;>
    rw [LocalAssembly.resolveAt_byteLength hp] <;>
    try rw [LocalAssembly.resolveAt_byteLength hr] <;>
    try rw [LocalAssembly.resolveAt_byteLength hs]

/-- Resolve any selected handler through the uniform entry-indexed API. -/
theorem resolve?_get {handlers : LocalClassicalHandlers}
    {resolved : ClassicalHandlers}
    (hresolve : handlers.resolve? = some resolved)
    (entry : ClassicalEntry) :
    (handlers.get entry).resolveAt (handlers.entryOffset entry + 2) =
      some (resolved.get entry) := by
  rcases resolve?_components hresolve with ⟨hp, hr, hs, ho⟩
  cases entry <;> assumption

end LocalClassicalHandlers

/-- Symbolic handlers whose complete resolved runtime fits `PUSH4` jump
destinations. -/
structure LinkableLocalHandlers where
  handlers : LocalClassicalHandlers
  size_fits : handlers.runtimeSize < 2 ^ 32
  labels_unique : handlers.LabelsUnique

namespace RuntimeImage

/-- Resolve and link local handler assembly to actual EVM bytes. -/
def linkLocal? (selectors : ClassicalSelectors)
    (linked : LinkableLocalHandlers) : Option (RuntimeImage selectors) :=
  match hresolve : linked.handlers.resolve? with
  | none => none
  | some resolved =>
      some <| RuntimeImage.link selectors
        { handlers := resolved
          size_fits := by
            rw [LocalClassicalHandlers.resolve?_runtimeSize hresolve]
            exact linked.size_fits }

/-- Check the whole-image bound and then resolve/link symbolic handlers. This
is the executable entry point used by partial concrete backends. -/
def linkLocalChecked? (selectors : ClassicalSelectors)
    (handlers : LocalClassicalHandlers) : Option (RuntimeImage selectors) :=
  if hunique : handlers.LabelsUnique then
    if hfits : handlers.runtimeSize < 2 ^ 32 then
      linkLocal? selectors
        { handlers := handlers
          size_fits := hfits
          labels_unique := hunique }
    else
      none
  else
    none

/-- A successfully linked checked image stores precisely the resolution of
the supplied local handlers. -/
theorem linkLocalChecked?_handlers_resolve
    {selectors : ClassicalSelectors} {handlers : LocalClassicalHandlers}
    {image : RuntimeImage selectors}
    (hlink : linkLocalChecked? selectors handlers = some image) :
    handlers.resolve? = some image.handlers.handlers := by
  unfold linkLocalChecked? at hlink
  split at hlink
  · split at hlink
    · unfold linkLocal? at hlink
      split at hlink
      · simp at hlink
      · rename_i resolved hresolve
        cases hlink
        exact hresolve
    · simp at hlink
  · simp at hlink

/-- Successful checked linking retains its source-level whole-image bound. -/
theorem linkLocalChecked?_source_size_fits
    {selectors : ClassicalSelectors} {handlers : LocalClassicalHandlers}
    {image : RuntimeImage selectors}
    (hlink : linkLocalChecked? selectors handlers = some image) :
    handlers.runtimeSize < 2 ^ 32 := by
  unfold linkLocalChecked? at hlink
  split at hlink
  · split at hlink
    · assumption
    · simp at hlink
  · simp at hlink

/-- Successful checked linking proves that no handler contains duplicate
label definitions. -/
theorem linkLocalChecked?_labels_unique
    {selectors : ClassicalSelectors} {handlers : LocalClassicalHandlers}
    {image : RuntimeImage selectors}
    (hlink : linkLocalChecked? selectors handlers = some image) :
    handlers.LabelsUnique := by
  unfold linkLocalChecked? at hlink
  split at hlink
  · assumption
  · simp at hlink

/-- Every local label destination in a checked linked image fits the `PUSH4`
address used by the resolver. -/
theorem linkLocalChecked?_labelDestination_fits
    {selectors : ClassicalSelectors} {handlers : LocalClassicalHandlers}
    {image : RuntimeImage selectors}
    (hlink : linkLocalChecked? selectors handlers = some image)
    (entry : ClassicalEntry) (target offset : Nat)
    (hlabel : (handlers.get entry).labelOffset? target = some offset) :
    handlers.entryOffset entry + 2 + offset < 2 ^ 32 := by
  exact (LocalClassicalHandlers.internalOffset_lt_runtimeSize handlers entry
    offset (LocalAssembly.labelOffset?_lt_byteLength _ _ _ hlabel)).trans
      (linkLocalChecked?_source_size_fits hlink)

/-- Checked linking preserves the locally computed offset of every public
entry point. -/
theorem linkLocalChecked?_entryOffset
    {selectors : ClassicalSelectors} {handlers : LocalClassicalHandlers}
    {image : RuntimeImage selectors}
    (hlink : linkLocalChecked? selectors handlers = some image)
    (entry : ClassicalEntry) :
    classicalEntryOffset image.handlers.handlers entry =
      handlers.entryOffset entry := by
  exact LocalClassicalHandlers.resolve?_entryOffset
    (linkLocalChecked?_handlers_resolve hlink) entry

end RuntimeImage

end Vegas.Machine.Contract.EVM

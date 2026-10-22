import InitECandidate.Solver.Input.MainStateInitRuntime
import InitECandidate.Solver.Input.MainRunAttemptConstructorPrefix

namespace InitECandidate.Solver.Input.Main.RunAttemptConstructors
open Flapjack PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString

/-- Real main startup/copy/decoder/hash provenance supplies the entire
physical/runtime context at the exact state_init caller, on every original
run_attempt body outcome that reaches it. No new workspace is assumed. -/
theorem state_init_boundary_of_actual (input : Guest.InputBlob)
    (before copiedSource origin hashed source post : PanSemStateFiniteExact 64 Guest.HostMemory) (root : BitVec 64) (counts : Nat→BitVec 64)
    (copied : InputCopied input before copiedSource)
    (actual : DecoderCall.DecoderReady input (DecoderSetup.entered copiedSource input) origin)
    (bounded : input.length%2^64≤Guest.maxInputBytes)
    (prepared : RequestRootHashData.Prepared input origin root counts) (returned : RequestHash.Returned input origin hashed root)
    (entryFrame : LocalEffects.erase source=LocalEffects.erase hashed)
    (siCell : source.locals.lookup (ofString "si")=some (.val (.word (RequestPrefix.cursor input))))
    (outcome : Option (PanSemResultExact 64)) (run : evaluateHOLFiniteState source RunAttempt.body=(outcome,post)) :
    source.clock-post.clock≤price input ∨ ∃ current inner,
      StateInitBoundary input current ∧ ConstructorRuntimeFrame source current ∧
      OriginalCode.Installed current.code ∧ OriginalScalarGlobals.Scalars current.globals ∧
      Rlp.Validation.Arena current 2713714688#64 2701135872#64 ∧
      Keccak256.Environment current 2713714976#64 2713715176#64 ∧
      current.clock≤source.clock ∧ source.clock-current.clock≤price input ∧ post.clock=inner.clock ∧
      evaluateHOLFiniteState current RunAttempt.afterCodes=(outcome,inner) ∧
      ∃ heap,current.globals.lookup (ofString "heap_ptr")=some (.val (.word heap)) ∧ 2713731432≤heap.toNat := by
  rcases prefix_of_actual input before copiedSource origin hashed source post root counts copied actual bounded prepared returned entryFrame siCell outcome run with stopped|reached
  · exact Or.inl stopped
  · obtain ⟨headerArray,context,payloadCell,pointerCell,countCell,scalars,siArena,siAligned⟩ :=
      RunAttemptData.entry_data input before copiedSource origin hashed source root counts copied actual bounded prepared returned entryFrame
    have code:=LocalEffects.code_of_erase hashed source entryFrame
    have installed : OriginalCode.Installed source.code := by rw [code]; exact returned.workspace.sha.installed
    have rootLower : 2713731432≤(initialHeap root).toNat:=by
      have lower:=prepared.layout.siLower
      have before:=prepared.layout.siBefore
      change 2713731432≤(RequestRootHashData.description input counts).si.toNat at lower
      have rounded:=prepared.before
      change 2713731432≤(PersistentAlloc.rounded root 32#64).toNat
      omega
    exact Or.inr (reached.state_init_runtime input source post root rootLower installed scalars outcome)

end InitECandidate.Solver.Input.Main.RunAttemptConstructors

#print axioms InitECandidate.Solver.Input.Main.RunAttemptConstructors.state_init_boundary_of_actual

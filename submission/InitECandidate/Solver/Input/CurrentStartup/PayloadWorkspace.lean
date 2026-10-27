import InitECandidate.Solver.Input.CurrentStartup.PayloadOffsetsLocals
import InitECandidate.Solver.Input.CurrentStartup.PayloadHeaderImage

namespace InitECandidate.Solver.Input.CurrentStartup.PayloadWorkspace
variable {decoderOrigin : DecoderOrigin}
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- Metadata and ownership geometry at a genuine payload stage. Memory
contents enter through the copied image; every other field is unchanged by
memory/clock-only effects. -/
structure Context (input : Guest.InputBlob) (current : PanSemStateFiniteExact 64 Guest.HostMemory)
    (pointer record : BitVec 64) (length : Nat) : Prop where
  code : OriginalCode.Installed current.code
  shapes : OriginalExceptions.Installed current.eshapes
  domain : current.memaddrs = InitE.ordinaryDomain
  endian : current.be = false
  image : Blob.HeapInput current input pointer
  heap : NormalHeapEffects.AtLeast (pointer.toNat + input.length % 2^64 + 8) current
  workspace : current.globals.lookup (ofString "ssz_offs") = some (.val (.word 2701132528#64))
  p : current.locals.lookup (ofString "p") = some (.val (.word (pointer + 62#64)))
  len : current.locals.lookup (ofString "len") = some (.val (.word (BitVec.ofNat 64 length)))
  pl : current.locals.lookup (ofString "pl") = some (.val (.word record))
  extra : current.locals.lookup (ofString "o_extra") = some (.val (.word (Payload.offsetWords input 0)))
  txs : current.locals.lookup (ofString "o_txs") = some (.val (.word (Payload.offsetWords input 1)))
  wd : current.locals.lookup (ofString "o_wd") = some (.val (.word (Payload.offsetWords input 2)))
  bal : current.locals.lookup (ofString "o_bal") = some (.val (.word (Payload.offsetWords input 3)))
  lengthBound : input.length % 2^64 ≤ Guest.maxInputBytes
  extent : 602 ≤ input.length % 2^64
  lower : 2701134640 ≤ pointer.toNat
  aligned : pointer.toNat % 8 = 0
  room : pointer.toNat + input.length % 2^64 + 8 ≤ 2952790016
  minimum : 540 ≤ length
  sliceUpper : length ≤ input.length % 2^64 - 62
  sliceEq : length = Guest.GasLimit.le32 input 22 - 44
  recordLower : pointer.toNat + input.length % 2^64 + 8 ≤ record.toNat
  recordAligned : record.toNat % 8 = 0
  recordRoom : record.toNat + 136 ≤ 2952790016
  recordHeap : NormalHeapEffects.AtLeast (record.toNat + 136) current

def Reached (input : Guest.InputBlob) : Prop :=
  ∃ current post, ∃ pointer record : BitVec 64, ∃ length : Nat, ∃ returned : ValueHOL 64,
    Context input current pointer record length ∧
    evaluateHOLFiniteState current Payload.offsetBody = (some (.returned returned), post) ∧
    PayloadEntry.Endpoint (decoderOrigin := decoderOrigin) input post pointer record length returned

/-- Transfer the retained context through real memory/clock-only effects;
the copied image must be established for the actual resulting memory. -/
theorem Context.memory_clock (input : Guest.InputBlob) (source : PanSemStateFiniteExact 64 Guest.HostMemory)
    (pointer record : BitVec 64) (length clock : Nat) (memory : BitVec 64 → HolWordLab 64)
    (context : Context input source pointer record length)
    (image : Blob.HeapInput {source with memory := memory, clock := clock} input pointer) :
    Context input {source with memory := memory, clock := clock} pointer record length :=
  ⟨context.code, context.shapes, context.domain, context.endian, image, context.heap, context.workspace,
    context.p, context.len, context.pl, context.extra, context.txs, context.wd, context.bal, context.lengthBound,
    context.extent, context.lower, context.aligned, context.room, context.minimum, context.sliceUpper, context.sliceEq,
    context.recordLower, context.recordAligned, context.recordRoom, context.recordHeap⟩

/-- Pure local-scope/clock changes retain context when the seven live payload
bindings agree. This keeps later call-return proofs independent of their bodies. -/
theorem Context.locals_clock (input : Guest.InputBlob) (source : PanSemStateFiniteExact 64 Guest.HostMemory)
    (pointer record : BitVec 64) (length clock : Nat) (locals : HolFiniteMapExact MlS (ValueHOL 64))
    (context : Context input source pointer record length)
    (kept : ∀ name : String, name ∈ ["p", "len", "pl", "o_extra", "o_txs", "o_wd", "o_bal"] →
      locals.lookup (ofString name) = source.locals.lookup (ofString name)) :
    Context input {source with locals := locals, clock := clock} pointer record length :=
  ⟨context.code, context.shapes, context.domain, context.endian, context.image, context.heap, context.workspace,
    (kept "p" (by simp)).trans context.p, (kept "len" (by simp)).trans context.len,
    (kept "pl" (by simp)).trans context.pl, (kept "o_extra" (by simp)).trans context.extra,
    (kept "o_txs" (by simp)).trans context.txs, (kept "o_wd" (by simp)).trans context.wd,
    (kept "o_bal" (by simp)).trans context.bal, context.lengthBound, context.extent, context.lower, context.aligned,
    context.room, context.minimum, context.sliceUpper, context.sliceEq, context.recordLower, context.recordAligned,
    context.recordRoom, context.recordHeap⟩

theorem offsets_frame (code) (installed : OriginalCode.Installed code) :
    GlobalEffects.Preserves (ofString "ssz_offs") code (CallPrefix.program PayloadCut.actions .skip) := by
  simp only [PayloadCut.actions, CallPrefix.program]
  refine GlobalEffects.scoped_body (ofString "ssz_offs") code _ _ (Code.name .alloc) _ _
    (Code.formals .alloc) (Code.body .alloc) (Code.shape .alloc)
    (Code.installed code installed .alloc) (OffsetsFrame.alloc code installed) ?_
  refine GlobalEffects.sequence (ofString "ssz_offs") code _ _ (GlobalEffects.store (ofString "ssz_offs") code _ _) ?_
  refine GlobalEffects.sequence (ofString "ssz_offs") code _ _ (GlobalEffects.store (ofString "ssz_offs") code _ _) ?_
  exact GlobalEffects.declared (ofString "ssz_offs") code _ _ _ _ (GlobalEffects.declared (ofString "ssz_offs") code _ _ _ _
    (GlobalEffects.declared (ofString "ssz_offs") code _ _ _ _ (GlobalEffects.declared (ofString "ssz_offs") code _ _ _ _ (GlobalEffects.skip (ofString "ssz_offs") code))))

theorem entry_reached (input : Guest.InputBlob) (actual : PayloadEntry.Reached (decoderOrigin := decoderOrigin) input) : Reached (decoderOrigin := decoderOrigin) input := by
  obtain ⟨source, post, pointer, length, returned, entryFacts⟩ := actual
  have originalEntry := entryFacts
  obtain ⟨lengthBound, installed, shapes, domain, endian, image, heap,
    workspace, lower, aligned, room, pCell, lenCell, extent, minimum, sliceUpper, sliceEq, actual, invocation⟩ := entryFacts
  obtain ⟨current, inner, execution, currentHeap, remaining, clock, frame⟩ :=
    PayloadCut.reached source post _ installed heap returned actual
  obtain ⟨record, originHeap, recordLower, recordAligned, recordRoom, recordCell, recordHeap⟩ := PayloadCut.record_pointer _ installed heap execution
  have endpoint : PayloadEntry.Endpoint (decoderOrigin := decoderOrigin) input post pointer record length returned := ⟨source, post, originalEntry, originHeap, rfl, rfl⟩
  have retained := PayloadCut.input_frame input pointer length installed heap image aligned room pCell lenCell execution
  have currentCode : OriginalCode.Installed current.code := by rw [execution.runtime.2.2.2.1]; exact installed
  have currentShapes : OriginalExceptions.Installed current.eshapes := by rw [execution.runtime.2.2.1]; exact shapes
  have currentWorkspace := (execution.globals (ofString "ssz_offs") (offsets_frame source.code installed)).trans workspace
  have currentP := (execution.keeps (ofString "p") (by
    intro action member
    exact List.all_eq_true.mp (show PayloadCut.actions.all (fun action => action.keeps (ofString "p")) = true from by decide) action member)).trans pCell
  have currentLen := (execution.keeps (ofString "len") (by
    intro action member
    exact List.all_eq_true.mp (show PayloadCut.actions.all (fun action => action.keeps (ofString "len")) = true from by decide) action member)).trans lenCell
  obtain ⟨extra, txs, wd, bal⟩ := PayloadOffsetsLocals.reached input pointer extent retained currentP execution
  exact ⟨current, inner, pointer, record, length, returned, ⟨currentCode, currentShapes,
    execution.runtime.1.trans domain, execution.runtime.2.1.trans endian, retained, currentHeap, currentWorkspace,
    currentP, currentLen, recordCell, extra, txs, wd, bal, lengthBound, extent, lower, aligned, room, minimum, sliceUpper, sliceEq,
    recordLower, recordAligned, recordRoom, recordHeap⟩, remaining,
    PayloadEntry.Endpoint.of_frame input post inner pointer record length returned endpoint frame clock⟩

theorem separated (input : Guest.InputBlob) (actual : MainSeparatedInput.RootRun input decoderOrigin) : Reached (decoderOrigin := decoderOrigin) input :=
  entry_reached input (PayloadEntry.separated input actual)

end InitECandidate.Solver.Input.CurrentStartup.PayloadWorkspace

#print axioms InitECandidate.Solver.Input.CurrentStartup.PayloadWorkspace.offsets_frame
#print axioms InitECandidate.Solver.Input.CurrentStartup.PayloadWorkspace.entry_reached
#print axioms InitECandidate.Solver.Input.CurrentStartup.PayloadWorkspace.separated

#print axioms InitECandidate.Solver.Input.CurrentStartup.PayloadWorkspace.Context.memory_clock

#print axioms InitECandidate.Solver.Input.CurrentStartup.PayloadWorkspace.Context.locals_clock

import InitECandidate.Solver.Input.CurrentStartup.RequestCut

namespace InitECandidate.Solver.Input.CurrentStartup.RecordEntry
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- A real request-length guard entry, retaining the copied image and its
fresh stateless record, derived from the whole-main stateless run. -/
def Reached (input : Guest.InputBlob) (word : BitVec 64) : Prop :=
  ∃ current inner, ∃ pointer record : BitVec 64,
    input.length % 2^64 ≤ Guest.maxInputBytes ∧
    OriginalCode.Installed current.code ∧ OriginalExceptions.Installed current.eshapes ∧
    current.memaddrs = InitE.ordinaryDomain ∧ current.be = false ∧
    Blob.HeapInput current input pointer ∧
    NormalHeapEffects.AtLeast (pointer.toNat + input.length % 2^64 + 8) current ∧
    current.globals.lookup (ofString "ssz_offs") = some (.val (.word 2701132528#64)) ∧
    2701134640 ≤ pointer.toNat ∧ pointer.toNat % 8 = 0 ∧
    pointer.toNat + input.length % 2^64 + 8 ≤ 2952790016 ∧
    pointer.toNat + input.length % 2^64 + 8 ≤ record.toNat ∧ record.toNat % 8 = 0 ∧
    record.toNat + 96 ≤ 2952790016 ∧ current.locals.lookup (ofString "si") = some (.val (.word record)) ∧
    evaluateHOLFiniteState current RequestCut.tail = (some (.returned (.val (.word word))), inner)

theorem offsets_frame (code) (installed : OriginalCode.Installed code) :
    GlobalEffects.Preserves (ofString "ssz_offs") code (CallPrefix.program RequestCut.actions .skip) := by
  simp only [RequestCut.actions, CallPrefix.program]
  refine GlobalEffects.declared (ofString "ssz_offs") code _ _ _ _ (GlobalEffects.declared (ofString "ssz_offs") code _ _ _ _ ?_)
  refine GlobalEffects.scoped_body (ofString "ssz_offs") code _ _ (Code.name .alloc) _ _
    (Code.formals .alloc) (Code.body .alloc) (Code.shape .alloc)
    (Code.installed code installed .alloc) (OffsetsFrame.alloc code installed) ?_
  exact GlobalEffects.sequence (ofString "ssz_offs") code _ _ (GlobalEffects.store (ofString "ssz_offs") code _ _)
    (GlobalEffects.declared (ofString "ssz_offs") code _ _ _ _
      (GlobalEffects.declared (ofString "ssz_offs") code _ _ _ _ (GlobalEffects.skip (ofString "ssz_offs") code)))

/-- The real main-derived input run reaches the request guard with its
original byte image intact. No record separation, room or helper success
hypothesis is added to that run. -/
theorem separated (input : Guest.InputBlob) (word : BitVec 64)
    (actual : MainSeparatedInput.StatelessRun input word) : Reached input word := by
  obtain ⟨source, target, pointer, lengthBound, initial, heap, bytes, pCell, lenCell, offsets, lower, aligned, room, separation, frontier, returned⟩ := actual
  obtain ⟨before, paid, price, funded, beforeEq, beforeBytes, continuation⟩ :=
    CanonicalHeader.outer_reached input source target pointer initial bytes pCell lenCell offsets lower aligned room (.val (.word word)) returned
  have beforeCode : OriginalCode.Installed before.code := by rw [beforeEq]; exact initial.arena.code
  have beforeShapes : OriginalExceptions.Installed before.eshapes := by rw [beforeEq]; exact initial.shapes
  have beforeDomain : before.memaddrs = InitE.ordinaryDomain := by rw [beforeEq]; exact initial.arena.domain
  have beforeEndian : before.be = false := by rw [beforeEq]; exact initial.little
  have beforeHeap : NormalHeapEffects.AtLeast (pointer.toNat + input.length % 2^64 + 8) before := by rw [beforeEq]; exact frontier
  have beforeOffsets : before.globals.lookup (ofString "ssz_offs") = some (.val (.word 2701132528#64)) := by rw [beforeEq]; exact offsets
  obtain ⟨current, inner, execution, currentHeap, remaining, clock, frame⟩ :=
    RequestCut.reached before target _ beforeCode beforeHeap (.val (.word word)) continuation
  obtain ⟨record, recordLower, recordAligned, recordRoom, binding⟩ := RequestCut.record_pointer _ beforeCode beforeHeap execution
  have currentBytes := RequestCut.input_frame input pointer beforeCode beforeHeap beforeBytes aligned room execution
  have currentCode : OriginalCode.Installed current.code := by rw [execution.runtime.2.2.2.1]; exact beforeCode
  have currentShapes : OriginalExceptions.Installed current.eshapes := by rw [execution.runtime.2.2.1]; exact beforeShapes
  have currentOffsets := (execution.globals (ofString "ssz_offs") (offsets_frame before.code beforeCode)).trans beforeOffsets
  exact ⟨current, inner, pointer, record, lengthBound, currentCode, currentShapes,
    execution.runtime.1.trans beforeDomain, execution.runtime.2.1.trans beforeEndian,
    currentBytes, currentHeap, currentOffsets, lower, aligned, room, recordLower, recordAligned, recordRoom, binding, remaining⟩

end InitECandidate.Solver.Input.CurrentStartup.RecordEntry

#print axioms InitECandidate.Solver.Input.CurrentStartup.RecordEntry.offsets_frame
#print axioms InitECandidate.Solver.Input.CurrentStartup.RecordEntry.separated

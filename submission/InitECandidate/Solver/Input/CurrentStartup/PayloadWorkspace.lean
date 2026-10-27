import InitECandidate.Solver.Input.CurrentStartup.PayloadHeaderImage

namespace InitECandidate.Solver.Input.CurrentStartup.PayloadWorkspace
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

def Reached (input : Guest.InputBlob) : Prop :=
  ∃ current post, ∃ pointer record : BitVec 64, ∃ length : Nat, ∃ returned : ValueHOL 64,
    OriginalCode.Installed current.code ∧ OriginalExceptions.Installed current.eshapes ∧
    current.memaddrs = InitE.ordinaryDomain ∧ current.be = false ∧
    Blob.HeapInput current input pointer ∧ NormalHeapEffects.AtLeast (pointer.toNat + input.length % 2^64 + 8) current ∧
    current.globals.lookup (ofString "ssz_offs") = some (.val (.word 2701132528#64)) ∧
    current.locals.lookup (ofString "p") = some (.val (.word (pointer + 62#64))) ∧
    current.locals.lookup (ofString "len") = some (.val (.word (BitVec.ofNat 64 length))) ∧
    current.locals.lookup (ofString "pl") = some (.val (.word record)) ∧
    input.length % 2^64 ≤ Guest.maxInputBytes ∧ 602 ≤ input.length % 2^64 ∧
    2701134640 ≤ pointer.toNat ∧ pointer.toNat % 8 = 0 ∧ pointer.toNat + input.length % 2^64 + 8 ≤ 2952790016 ∧
    540 ≤ length ∧ length ≤ input.length % 2^64 - 62 ∧ length = Guest.GasLimit.le32 input 22 - 44 ∧
    pointer.toNat + input.length % 2^64 + 8 ≤ record.toNat ∧ record.toNat % 8 = 0 ∧ record.toNat + 136 ≤ 2952790016 ∧
    evaluateHOLFiniteState current Payload.offsetBody = (some (.returned returned), post)

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

theorem entry_reached (input : Guest.InputBlob) (actual : PayloadEntry.Reached input) : Reached input := by
  obtain ⟨source, post, pointer, length, returned, lengthBound, installed, shapes, domain, endian, image, heap,
    workspace, lower, aligned, room, pCell, lenCell, extent, minimum, sliceUpper, sliceEq, actual⟩ := actual
  obtain ⟨current, inner, execution, currentHeap, remaining, clock, frame⟩ :=
    PayloadCut.reached source post _ installed heap returned actual
  obtain ⟨record, recordLower, recordAligned, recordRoom, recordCell⟩ := PayloadCut.record_pointer _ installed heap execution
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
  exact ⟨current, inner, pointer, record, length, returned, currentCode, currentShapes,
    execution.runtime.1.trans domain, execution.runtime.2.1.trans endian, retained, currentHeap, currentWorkspace,
    currentP, currentLen, recordCell, lengthBound, extent, lower, aligned, room, minimum, sliceUpper, sliceEq, recordLower, recordAligned, recordRoom, remaining⟩

theorem separated (input : Guest.InputBlob) (word : BitVec 64) (actual : MainSeparatedInput.StatelessRun input word) : Reached input :=
  entry_reached input (PayloadEntry.separated input word actual)

end InitECandidate.Solver.Input.CurrentStartup.PayloadWorkspace

#print axioms InitECandidate.Solver.Input.CurrentStartup.PayloadWorkspace.offsets_frame
#print axioms InitECandidate.Solver.Input.CurrentStartup.PayloadWorkspace.entry_reached
#print axioms InitECandidate.Solver.Input.CurrentStartup.PayloadWorkspace.separated

import InitECandidate.Solver.Input.CurrentStartup.OuterLocals
import InitECandidate.Solver.Input.CurrentStartup.RequestPositions
import InitECandidate.Solver.Input.GuardActual
import InitECandidate.Solver.Input.CurrentStartup.RequestCut

namespace InitECandidate.Solver.Input.CurrentStartup.RecordEntry
variable {decoderOrigin : DecoderOrigin}
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- A real request-length guard entry, retaining the copied image and its
fresh stateless record, derived from the whole-main stateless run.
The real request-length guard has passed. -/
def Reached (input : Guest.InputBlob) (word : BitVec 64) : Prop :=
  ∃ current inner, ∃ pointer record : BitVec 64,
    input.length % 2^64 ≤ Guest.maxInputBytes ∧
    OriginalCode.Installed current.code ∧ OriginalExceptions.Installed current.eshapes ∧
    current.memaddrs = InitE.ordinaryDomain ∧ current.be = false ∧
    Blob.HeapInput current input pointer ∧
    NormalHeapEffects.AtLeast (pointer.toNat + input.length % 2^64 + 8) current ∧
    current.globals.lookup (ofString "ssz_offs") = some (.val (.word 2701132528#64)) ∧
    2701134824 ≤ pointer.toNat ∧ pointer.toNat % 8 = 0 ∧
    pointer.toNat + input.length % 2^64 + 8 ≤ 2952790016 ∧
    pointer.toNat + input.length % 2^64 + 8 ≤ record.toNat ∧ record.toNat % 8 = 0 ∧
    record.toNat + 96 ≤ 2952790016 ∧ NormalHeapEffects.AtLeast (record.toNat + 96) current ∧ current.locals.lookup (ofString "si") = some (.val (.word record)) ∧
    current.locals.lookup (ofString "np") = some (.val (.word (pointer + 18#64))) ∧
    current.locals.lookup (ofString "nlen") = some (.val (.word (BitVec.ofNat 64 (Guest.GasLimit.le32 input 6 - 16)))) ∧
    62 ≤ input.length % 2^64 ∧ 44 ≤ Guest.GasLimit.le32 input 6 - 16 ∧
    Guest.GasLimit.le32 input 6 - 16 ≤ input.length % 2^64 - 18 ∧
    OuterLocals input current pointer ∧
    decoderOrigin.Frame inner pointer (.val (.word word)) ∧
    evaluateHOLFiniteState current Request.requestBody = (some (.returned (.val (.word word))), inner)

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
theorem separated (input : Guest.InputBlob)
    (actual : MainSeparatedInput.RootRun input decoderOrigin) : Reached (decoderOrigin := decoderOrigin) input decoderOrigin.word := by
  let source := decoderOrigin.entry
  let target := decoderOrigin.post
  let pointer := decoderOrigin.pointer
  obtain ⟨lengthBound, initial, heap, bytes, pCell, lenCell, offsets, lower, aligned, room, separation, frontier, returned⟩ := actual
  obtain ⟨extent, tag, version, firstOffset, witnessLower, witnessUpper⟩ :=
    CanonicalHeader.first_offset input source target pointer initial bytes pCell lenCell offsets lower aligned room (.val (.word decoderOrigin.word)) returned
  obtain ⟨before, paid, price, funded, beforeEq, beforeBytes, continuation⟩ :=
    CanonicalHeader.outer_reached input source target pointer initial bytes pCell lenCell offsets lower aligned room (.val (.word decoderOrigin.word)) returned
  have beforeCode : OriginalCode.Installed before.code := by rw [beforeEq]; exact initial.arena.code
  have beforeShapes : OriginalExceptions.Installed before.eshapes := by rw [beforeEq]; exact initial.shapes
  have beforeDomain : before.memaddrs = InitE.ordinaryDomain := by rw [beforeEq]; exact initial.arena.domain
  have beforeEndian : before.be = false := by rw [beforeEq]; exact initial.little
  have beforeHeap : NormalHeapEffects.AtLeast (pointer.toNat + input.length % 2^64 + 8) before := by rw [beforeEq]; exact frontier
  have beforeOffsets : before.globals.lookup (ofString "ssz_offs") = some (.val (.word 2701132528#64)) := by rw [beforeEq]; exact offsets
  have beforeP : before.locals.lookup (ofString "p") = some (.val (.word (pointer + 2#64))) := by
    rw [beforeEq]
    exact (WitnessRadix.QueryBranch.bind_lookup_other _ "len" "p" _ (by decide)).trans (WitnessRadix.QueryBranch.bind_lookup_same _ _ _)
  have firstMapped : before.memaddrs 2701132528#64 := by
    rw [beforeDomain]
    exact WitnessRadix.BackingLayout.ordinary_mapped _ (by decide) (by decide) (by decide)
  have secondMapped : before.memaddrs (2701132528#64 + 8#64) := by
    rw [beforeDomain]
    exact WitnessRadix.BackingLayout.ordinary_mapped _ (by decide) (by decide) (by decide)
  have firstCell : before.memory 2701132528#64 = .word 16#64 := by
    rw [beforeEq]
    simp [Header.pairState, Header.firstState, Header.firstWord, WitnessRadix.StoreWord.put, firstOffset,
      show (2701132528#64 : BitVec 64) ≠ 2701132528#64 + 8#64 from by decide]
  have secondCell : before.memory (2701132528#64 + 8#64) = .word (BitVec.ofNat 64 (Guest.GasLimit.le32 input 6)) := by
    rw [beforeEq]
    simp [Header.pairState, Header.secondWord, WitnessRadix.StoreWord.put]
  obtain ⟨current, inner, execution, currentHeap, remaining, clock, frame⟩ :=
    RequestCut.reached before target _ beforeCode beforeHeap (.val (.word decoderOrigin.word)) continuation
  obtain ⟨record, recordLower, recordAligned, recordRoom, binding, recordHeap⟩ := RequestCut.record_pointer _ beforeCode beforeHeap execution
  have currentBytes := RequestCut.input_frame input pointer beforeCode beforeHeap beforeBytes aligned room execution
  have currentCode : OriginalCode.Installed current.code := by rw [execution.runtime.2.2.2.1]; exact beforeCode
  have currentShapes : OriginalExceptions.Installed current.eshapes := by rw [execution.runtime.2.2.1]; exact beforeShapes
  have currentOffsets := (execution.globals (ofString "ssz_offs") (offsets_frame before.code beforeCode)).trans beforeOffsets
  obtain ⟨np, nlen, witnessCell⟩ := RequestPositions.bindings pointer 2701132528#64 (Guest.GasLimit.le32 input 6) witnessLower
    beforeP beforeOffsets firstMapped secondMapped firstCell secondCell execution
  have witnessSmall := Framing.le32_lt input 6
  have encoded : (BitVec.ofNat 64 (Guest.GasLimit.le32 input 6 - 16)).toNat = Guest.GasLimit.le32 input 6 - 16 := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have read : WitnessRadix.QueryBranch.eval current Request.lengthTest = some (.val (.word (if Guest.GasLimit.le32 input 6 - 16 < 44 then 1#64 else 0#64))) := by
    simp [WitnessRadix.QueryBranch.eval, Request.lengthTest, WitnessRadix.QueryBranch.localVar, evalHOLExact, toExact, nlen,
      Flapjack.Compiler.Encoders.Asm.wordCmpHOL, BitVec.lt_def, encoded]
  obtain ⟨large, requestRun⟩ := guard_actual current inner Request.lengthTest 81#64 (Guest.GasLimit.le32 input 6 - 16 < 44) read
    (CanonicalHeader.fail_code current.code currentCode) (currentShapes .SszErr) Request.requestBody (.val (.word decoderOrigin.word)) remaining
  have currentP := execution.keeps (ofString "p") (List.all_eq_true.mp
    (show RequestCut.actions.all (fun action => action.keeps (ofString "p")) = true by decide))
  have currentLen := execution.keeps (ofString "len") (List.all_eq_true.mp
    (show RequestCut.actions.all (fun action => action.keeps (ofString "len")) = true by decide))
  have beforeLen : before.locals.lookup (ofString "len") = some (.val (.word (BitVec.ofNat 64 (input.length % 2^64 - 2)))) := by
    rw [beforeEq]
    exact WitnessRadix.QueryBranch.bind_lookup_same _ _ _
  have outer : OuterLocals input current pointer :=
    ⟨currentP.trans beforeP, currentLen.trans beforeLen, witnessCell, witnessLower, witnessUpper⟩
  have rootFrame : decoderOrigin.Frame inner pointer (.val (.word decoderOrigin.word)) :=
    ⟨rfl, rfl, frame.symm, clock.symm⟩
  exact ⟨current, inner, pointer, record, lengthBound, currentCode, currentShapes,
    execution.runtime.1.trans beforeDomain, execution.runtime.2.1.trans beforeEndian,
    currentBytes, currentHeap, currentOffsets, lower, aligned, room, recordLower, recordAligned, recordRoom, recordHeap, binding, np, nlen, (by omega), (by omega), (by omega), outer, rootFrame, requestRun⟩

end InitECandidate.Solver.Input.CurrentStartup.RecordEntry

#print axioms InitECandidate.Solver.Input.CurrentStartup.RecordEntry.offsets_frame
#print axioms InitECandidate.Solver.Input.CurrentStartup.RecordEntry.separated

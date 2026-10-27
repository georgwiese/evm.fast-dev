import InitECandidate.Solver.Input.CurrentStartup.PayloadCut

namespace InitECandidate.Solver.Input.CurrentStartup.PayloadCut
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

/-- The real payload allocation, pointer/length stores and four offset
loads preserve copied bytes. The allocation's derived frontier separates both
written header words from input; store mapping follows from observed execution. -/
theorem input_frame {source target : PanSemStateFiniteExact 64 Guest.HostMemory}
    (input : Guest.InputBlob) (pointer : BitVec 64) (length : Nat) (installed : OriginalCode.Installed source.code)
    (heap : NormalHeapEffects.AtLeast (pointer.toNat + input.length % 2^64 + 8) source)
    (image : Blob.HeapInput source input pointer) (aligned : pointer.toNat % 8 = 0)
    (room : pointer.toNat + input.length % 2^64 + 8 ≤ 2952790016)
    (pCell : source.locals.lookup (ofString "p") = some (.val (.word (pointer + 62#64))))
    (lenCell : source.locals.lookup (ofString "len") = some (.val (.word (BitVec.ofNat 64 length))))
    (actual : CallPrefix.Execution source actions target) : Blob.HeapInput target input pointer := by
  cases actual with
  | @step _ allocatedState _ _ _ allocated rest =>
    obtain ⟨record, cell, low, recordAligned, recordRoom, stateEq⟩ := allocation_frontier (ofString "pl") 136#64 _ installed heap allocated
    have allocatedBytes : Blob.HeapInput allocatedState input pointer := Blob.HeapInput.of_fields source allocatedState input pointer
      (by rw [stateEq]; rfl) (by rw [stateEq]; rfl) (by rw [stateEq]; rfl) image
    have recordCell : allocatedState.locals.lookup (ofString "pl") = some (.val (.word record)) := by
      rw [stateEq]
      simp [setVarHOLFinite, HolFiniteMapExact.update, FUPDATE]
    have allocatedP : allocatedState.locals.lookup (ofString "p") = some (.val (.word (pointer + 62#64))) := by
      rw [stateEq]
      simpa [setVarHOLFinite, HolFiniteMapExact.update, FUPDATE, WitnessRadix.PersistentAlloc.post,
        show ofString "pl" ≠ ofString "p" from by decide] using pCell
    have allocatedLen : allocatedState.locals.lookup (ofString "len") = some (.val (.word (BitVec.ofNat 64 length))) := by
      rw [stateEq]
      simpa [setVarHOLFinite, HolFiniteMapExact.update, FUPDATE, WitnessRadix.PersistentAlloc.post,
        show ofString "pl" ≠ ofString "len" from by decide] using lenCell
    have readRecord : eval allocatedState (localVar "pl") = some (.val (.word record)) := by
      simpa [eval, localVar, evalHOLExact, toExact] using recordCell
    have readPointer : eval allocatedState (localVar "p") = some (.val (.word (pointer + 62#64))) := by
      simpa [eval, localVar, evalHOLExact, toExact] using allocatedP
    have readAddress : eval allocatedState (Scalar.plus (localVar "pl") 0) = some (.val (.word record)) := by
      simpa only [BitVec.add_zero] using Scalar.plus_read allocatedState (localVar "pl") record 0 readRecord
    cases rest with
    | @step _ pointerState _ _ _ pointerStore rest =>
      have pointerNormal : evaluateHOLFiniteState allocatedState Payload.pointerStore = (none, pointerState) := by cases pointerStore; assumption
      have pointerBytes : Blob.HeapInput pointerState input pointer := Blob.HeapInput.word_store_separate allocatedState pointerState input pointer
        record (pointer + 62#64) (Scalar.plus (localVar "pl") 0) (localVar "p") allocatedBytes aligned (by omega)
        (Or.inr (by omega)) readAddress readPointer pointerNormal
      obtain ⟨mapped, pointerEq⟩ := Input.word_store_normal allocatedState pointerState _ _ record (pointer + 62#64) readAddress readPointer pointerNormal
      have pointerRecord : pointerState.locals.lookup (ofString "pl") = some (.val (.word record)) := by rw [pointerEq]; exact recordCell
      have pointerLen : pointerState.locals.lookup (ofString "len") = some (.val (.word (BitVec.ofNat 64 length))) := by rw [pointerEq]; exact allocatedLen
      have readNextRecord : eval pointerState (localVar "pl") = some (.val (.word record)) := by
        simpa [eval, localVar, evalHOLExact, toExact] using pointerRecord
      have readLength : eval pointerState (localVar "len") = some (.val (.word (BitVec.ofNat 64 length))) := by
        simpa [eval, localVar, evalHOLExact, toExact] using pointerLen
      have readNextAddress := Scalar.plus_read pointerState (localVar "pl") record 8 readNextRecord
      have addressNumber : (record + 8#64).toNat = record.toNat + 8 := by
        rw [BitVec.toNat_add_of_lt (by change record.toNat + 8 < 2^64; change record.toNat + 136 ≤ 2952790016 at recordRoom; omega)]
        rfl
      cases rest with
      | @step _ headerState _ _ _ lengthStore remainder =>
        have lengthNormal : evaluateHOLFiniteState pointerState Payload.lengthStore = (none, headerState) := by cases lengthStore; assumption
        have headerBytes : Blob.HeapInput headerState input pointer := Blob.HeapInput.word_store_separate pointerState headerState input pointer
          (record + 8#64) (BitVec.ofNat 64 length) (Scalar.plus (localVar "pl") 8) (localVar "len") pointerBytes aligned (by omega)
          (Or.inr (by rw [addressNumber]; omega)) readNextAddress readLength lengthNormal
        cases remainder with
        | step extra rest =>
          cases rest with
          | step txs rest =>
            cases rest with
            | step wd rest =>
              cases rest with
              | step bal done =>
                cases done
                cases bal
                cases wd
                cases txs
                cases extra
                exact headerBytes

end InitECandidate.Solver.Input.CurrentStartup.PayloadCut

#print axioms InitECandidate.Solver.Input.CurrentStartup.PayloadCut.input_frame

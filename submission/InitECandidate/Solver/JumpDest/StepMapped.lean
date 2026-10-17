import InitECandidate.Solver.JumpDest.Step

namespace InitECandidate.Solver.JumpDest
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

/-- Derive all actual byte reads and the bitmap read/store from mapped
regions. Code contents may be arbitrary and need not survive bitmap writes:
strict progress and the protected earlier-memory frame hold for every byte. -/
theorem step_of_mapped (source : PanSemStateFiniteExact 64 Guest.HostMemory)
    (bitmap code index length : BitVec 64)
    (bmLocal : source.locals.lookup (ofString "bm") = some (.val (.word bitmap)))
    (codeLocal : source.locals.lookup (ofString "code") = some (.val (.word code)))
    (pcLocal : source.locals.lookup (ofString "pc") = some (.val (.word index)))
    (nLocal : source.locals.lookup (ofString "n") = some (.val (.word length)))
    (inside : index.toNat < length.toNat) (fits : length.toNat + 32 < 2 ^ 64)
    (codeMapped : ∀ offset < length.toNat,
      source.memaddrs (panByteAlignHOL (width := 64) (WitnessRadix.byteAddress code offset)))
    (bitmapMapped : ∀ offset, offset + 8 ≤ bitmapBytes length.toNat → offset % 8 = 0 →
      source.memaddrs (WitnessRadix.byteAddress bitmap offset)) :
    ∃ opcode next old : BitVec 64,
      evaluateHOLFiniteState source step = (none, stepState source bitmap opcode index length next old) ∧
      index.toNat < (index + selectedAdvance opcode index length next).toNat ∧
      (index + selectedAdvance opcode index length next).toNat ≤ length.toNat + 32 := by
  have opMapped : source.memaddrs (panByteAlignHOL (width := 64) (code + index)) := by
    simpa [WitnessRadix.byteAddress, BitVec.ofNat_toNat] using codeMapped index.toNat inside
  let opByte := WitnessRadix.ByteRegion.value source (code + index)
  have opAddress : eval source (.op .add [localVar "code", localVar "pc"]) = some (.val (.word (code + index))) := by
    simp [eval, localVar, evalHOLExact, evalListHOLExact, toExact, codeLocal, pcLocal,
      valueIsWord, valueWord, wordOpHOL, wordOp]
  have loaded := WitnessRadix.ByteRegion.load_expression source (.op .add [localVar "code", localVar "pc"])
    (code + index) opByte opAddress (WitnessRadix.ByteRegion.mapped_read source _ opMapped)
  let nextByteValue := WitnessRadix.ByteRegion.value source (code + index + 1#64)
  have oneNumber : (index + 1#64).toNat = index.toNat + 1 :=
    BitVec.toNat_add_of_lt (by change index.toNat + 1 < 2 ^ 64; omega)
  have loadedNext : index + 1#64 < length → eval source nextByte =
      some (.val (.word (BitVec.ofNat 64 nextByteValue.toNat))) := by
    intro following
    have nextInside : index.toNat + 1 < length.toNat := by
      change (index + 1#64).toNat < length.toNat at following
      omega
    have nextMapped : source.memaddrs (panByteAlignHOL (width := 64) (code + index + 1#64)) := by
      simpa [WitnessRadix.byteAddress, BitVec.ofNat_add, BitVec.ofNat_toNat, BitVec.add_assoc] using codeMapped (index.toNat + 1) nextInside
    have nextAddress : eval source (.op .add [localVar "code", localVar "pc", .const 1#64]) =
        some (.val (.word (code + index + 1#64))) := by
      simp [eval, localVar, evalHOLExact, evalListHOLExact, toExact, codeLocal, pcLocal,
        valueIsWord, valueWord, wordOpHOL, wordOp, BitVec.add_assoc]
    exact WitnessRadix.ByteRegion.load_expression source _ _ nextByteValue nextAddress
      (WitnessRadix.ByteRegion.mapped_read source _ nextMapped)
  have offset := word_offset_number index
  have selected := selected_word length.toNat index.toNat inside
  have wordMapped : source.memaddrs (bitmap + wordOffset index) := by
    have mapped := bitmapMapped (wordOffset index).toNat (by omega) (by rw [offset]; omega)
    simpa [WitnessRadix.byteAddress, BitVec.ofNat_toNat] using mapped
  cases cell : source.memory (bitmap + wordOffset index) with
  | word old =>
    have run := step_execute source bitmap (BitVec.ofNat 64 opByte.toNat) index length
      (BitVec.ofNat 64 nextByteValue.toNat) old bmLocal pcLocal nLocal loaded loadedNext wordMapped cell
    have progress := selected_progress (BitVec.ofNat 64 opByte.toNat) index length
      (BitVec.ofNat 64 nextByteValue.toNat) inside fits
    exact ⟨_, _, old, run, progress.2.1, progress.2.2⟩

end InitECandidate.Solver.JumpDest

#print axioms InitECandidate.Solver.JumpDest.step_of_mapped

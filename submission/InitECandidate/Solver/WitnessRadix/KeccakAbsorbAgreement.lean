import InitECandidate.Solver.WitnessRadix.KeccakAbsorbExecution
import InitECandidate.Solver.WitnessRadix.MemoryAgreement

namespace InitECandidate.Solver.WitnessRadix.KeccakAbsorb
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString QueryBranch
set_option maxRecDepth 10000

theorem input_eval_agrees {F : Type}
    (source : PanSemStateFiniteExact 64 F) (target : PanSemStateFiniteExact 64 F)
    (blk index : BitVec 64) (unaligned : Bool)
    (sourceBlk : source.locals.lookup (ofString "blk") = some (.val (.word blk)))
    (targetBlk : target.locals.lookup (ofString "blk") = some (.val (.word blk)))
    (sourceIndex : source.locals.lookup (ofString "i") = some (.val (.word index)))
    (targetIndex : target.locals.lookup (ofString "i") = some (.val (.word index)))
    (domain : source.memaddrs = target.memaddrs) (endian : source.be = target.be)
    (word : unaligned = false → source.memory (blk + index) = target.memory (blk + index))
    (bytes : ∀ offset : Fin 8,
      source.memory (panByteAlignHOL (width := 64) (blk + index + BitVec.ofNat 64 offset.val)) =
      target.memory (panByteAlignHOL (width := 64) (blk + index + BitVec.ofNat 64 offset.val))) :
    eval source (inputWord unaligned) = eval target (inputWord unaligned) := by
  classical
  cases unaligned with
  | false =>
    simp [eval, inputWord, address, localVar, evalHOLExact, evalListHOLExact, toExact,
      sourceBlk, targetBlk, sourceIndex, targetIndex, valueIsWord, valueWord,
      wordOpHOL, wordOp, memLoadHOLExact, domain, word rfl]
  | true =>
    have readByte (offset : Fin 8) := MemoryBytes.read_of_cell source target domain endian
      (blk + index + BitVec.ofNat 64 offset.val) (bytes offset)
    have r0 : @panMemLoadByteHOL 64 _ source.memory source.memaddrs
        (fun query => Classical.propDecidable (source.memaddrs query)) source.be (blk + index) =
      @panMemLoadByteHOL 64 _ target.memory target.memaddrs
        (fun query => Classical.propDecidable (target.memaddrs query)) target.be (blk + index) := by
      simpa using readByte ⟨0, by decide⟩
    have r1 := readByte ⟨1, by decide⟩
    have r2 := readByte ⟨2, by decide⟩
    have r3 := readByte ⟨3, by decide⟩
    have r4 := readByte ⟨4, by decide⟩
    have r5 := readByte ⟨5, by decide⟩
    have r6 := readByte ⟨6, by decide⟩
    have r7 := readByte ⟨7, by decide⟩
    simp only [BitVec.add_assoc] at r1 r2 r3 r4 r5 r6 r7
    simp [eval, inputWord, highWord, byte, shifted, address, localVar, evalHOLExact,
      evalListHOLExact, toExact, sourceBlk, targetBlk, sourceIndex, targetIndex,
      valueIsWord, valueWord, wordOpHOL, wordOp, wordShiftHOL, BitVec.add_assoc,
      r0, r1, r2, r3, r4, r5, r6, r7]

theorem input_value_agrees {F : Type}
    (source : PanSemStateFiniteExact 64 F) (target : PanSemStateFiniteExact 64 F)
    (blk index : BitVec 64) (unaligned : Bool)
    (sourceBlk : source.locals.lookup (ofString "blk") = some (.val (.word blk)))
    (targetBlk : target.locals.lookup (ofString "blk") = some (.val (.word blk)))
    (sourceIndex : source.locals.lookup (ofString "i") = some (.val (.word index)))
    (targetIndex : target.locals.lookup (ofString "i") = some (.val (.word index)))
    (domain : source.memaddrs = target.memaddrs) (endian : source.be = target.be)
    (word : unaligned = false → source.memory (blk + index) = target.memory (blk + index))
    (bytes : ∀ offset : Fin 8,
      source.memory (panByteAlignHOL (width := 64) (blk + index + BitVec.ofNat 64 offset.val)) =
      target.memory (panByteAlignHOL (width := 64) (blk + index + BitVec.ofNat 64 offset.val))) :
    inputValue source unaligned = inputValue target unaligned := by
  unfold inputValue
  rw [input_eval_agrees source target blk index unaligned sourceBlk targetBlk
    sourceIndex targetIndex domain endian word bytes]

theorem lane_memory_agrees {F : Type}
    (source : PanSemStateFiniteExact 64 F) (target : PanSemStateFiniteExact 64 F)
    (stp index : BitVec 64) (unaligned : Bool) (region : BitVec 64 → Prop)
    (same : ∀ query, region query → source.memory query = target.memory query)
    (stateCell : region (stp + index))
    (input : inputValue source unaligned = inputValue target unaligned) :
    ∀ query, region query →
      (lanePost source stp index unaligned).memory query =
      (lanePost target stp index unaligned).memory query := by
  intro query inside
  change StoreWord.put source.memory (stp + index) _ query =
    StoreWord.put target.memory (stp + index) _ query
  simp only [StoreWord.put, same _ stateCell, input]
  split
  · rfl
  · exact same query inside

end InitECandidate.Solver.WitnessRadix.KeccakAbsorb

#print axioms InitECandidate.Solver.WitnessRadix.KeccakAbsorb.input_eval_agrees
#print axioms InitECandidate.Solver.WitnessRadix.KeccakAbsorb.input_value_agrees
#print axioms InitECandidate.Solver.WitnessRadix.KeccakAbsorb.lane_memory_agrees

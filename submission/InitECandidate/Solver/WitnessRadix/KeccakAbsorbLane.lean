import InitECandidate.Solver.WitnessRadix.KeccakAbsorbProgram

namespace InitECandidate.Solver.WitnessRadix.KeccakAbsorb
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString QueryBranch

noncomputable def inputValue {F : Type} (source : PanSemStateFiniteExact 64 F) (unaligned : Bool) : BitVec 64 :=
  match eval source (inputWord unaligned) with | some (.val (.word value)) => value | _ => 0#64

theorem input_value_read {F : Type} (source : PanSemStateFiniteExact 64 F) (blk index : BitVec 64) (unaligned : Bool)
    (blkLocal : source.locals.lookup (ofString "blk") = some (.val (.word blk)))
    (indexLocal : source.locals.lookup (ofString "i") = some (.val (.word index)))
    (wordMapped : unaligned = false → source.memaddrs (blk + index))
    (byteMapped : ∀ offset : Fin 8, source.memaddrs (panByteAlignHOL (width := 64) (blk + index + BitVec.ofNat 64 offset.val))) :
    eval source (inputWord unaligned) = some (.val (.word (inputValue source unaligned))) := by
  obtain ⟨value, read⟩ := input_read source blk index unaligned blkLocal indexLocal wordMapped byteMapped
  simp only [inputValue, read]

noncomputable def lanePost {F : Type} (source : PanSemStateFiniteExact 64 F) (stp index : BitVec 64) (unaligned : Bool) : PanSemStateFiniteExact 64 F :=
  bind { source with memory := (StoreWord.put source.memory (stp + index)
    (MemoryBytes.wordBits (source.memory (stp + index)) ^^^ inputValue source unaligned)) } "i" (index + 8#64)

theorem lane_execute {F : Type} (source : PanSemStateFiniteExact 64 F) (stp blk index : BitVec 64) (unaligned : Bool)
    (stpLocal : source.locals.lookup (ofString "stp") = some (.val (.word stp)))
    (blkLocal : source.locals.lookup (ofString "blk") = some (.val (.word blk)))
    (indexLocal : source.locals.lookup (ofString "i") = some (.val (.word index)))
    (stateMapped : source.memaddrs (stp + index))
    (wordMapped : unaligned = false → source.memaddrs (blk + index))
    (byteMapped : ∀ offset : Fin 8, source.memaddrs (panByteAlignHOL (width := 64) (blk + index + BitVec.ofNat 64 offset.val))) :
    evaluateHOLFiniteState source (laneBody unaligned) = (none, lanePost source stp index unaligned) := by
  have addressRead : eval source (address "stp") = some (.val (.word (stp + index))) := by
    simp [eval, address, localVar, evalHOLExact, evalListHOLExact, toExact, stpLocal, indexLocal,
      valueIsWord, valueWord, wordOpHOL, wordOp]
  have stateRead : eval source (.load .one (address "stp")) =
      some (.val (.word (MemoryBytes.wordBits (source.memory (stp + index))))) := by
    simp only [eval] at addressRead ⊢
    cases cell : source.memory (stp + index) with
    | word value => simp [evalHOLExact, addressRead, memLoadHOLExact, stateMapped, cell, MemoryBytes.wordBits]
  have inputRead := input_value_read source blk index unaligned blkLocal indexLocal wordMapped byteMapped
  have xorRead : eval source (.op .xor [.load .one (address "stp"), inputWord unaligned]) =
      some (.val (.word (MemoryBytes.wordBits (source.memory (stp + index)) ^^^ inputValue source unaligned))) := by
    simp only [eval] at stateRead inputRead ⊢
    rw [evalHOLExact]
    simp [evalListHOLExact, stateRead, inputRead, valueIsWord, valueWord, wordOpHOL, wordOp]
  let written := { source with memory := (StoreWord.put source.memory (stp + index)
    (MemoryBytes.wordBits (source.memory (stp + index)) ^^^ inputValue source unaligned)) }
  have stored := StoreWord.execute source _ _ _ _ addressRead xorRead stateMapped
  have next := StateSteps.assign_execute written "i" (addConst (localVar "i") 8#64) index (index + 8#64)
    indexLocal (by simp [eval, localVar, addConst, evalHOLExact, evalListHOLExact, toExact, written, indexLocal,
      valueIsWord, valueWord, wordOpHOL, wordOp])
  rw [laneBody, StateSteps.next_sequence source written _ _ stored (Nat.le_refl _)]
  exact next

theorem lane_memory_away {F : Type} (source : PanSemStateFiniteExact 64 F) (stp index query : BitVec 64) (unaligned : Bool)
    (away : query ≠ stp + index) : (lanePost source stp index unaligned).memory query = source.memory query := if_neg away

theorem lane_other {F : Type} (source : PanSemStateFiniteExact 64 F) (stp index : BitVec 64) (unaligned : Bool)
    (name : MlS) (different : ofString "i" ≠ name) :
    (lanePost source stp index unaligned).locals.lookup name = source.locals.lookup name := by
  simp [lanePost, QueryBranch.bind, setVarHOLFinite, HolFiniteMapExact.update, FUPDATE, different]

end InitECandidate.Solver.WitnessRadix.KeccakAbsorb

#print axioms InitECandidate.Solver.WitnessRadix.KeccakAbsorb.input_value_read
#print axioms InitECandidate.Solver.WitnessRadix.KeccakAbsorb.lane_execute
#print axioms InitECandidate.Solver.WitnessRadix.KeccakAbsorb.lane_memory_away
#print axioms InitECandidate.Solver.WitnessRadix.KeccakAbsorb.lane_other

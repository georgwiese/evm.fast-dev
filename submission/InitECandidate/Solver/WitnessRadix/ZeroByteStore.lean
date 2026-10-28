import InitECandidate.Solver.WitnessRadix.ZeroTail

namespace InitECandidate.Solver.WitnessRadix.Zero
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString QueryBranch

def byteMemory (memory : WordWrites.Memory) (be : Bool) (address : BitVec 64) : WordWrites.Memory :=
  StoreWord.put memory (panByteAlignHOL (width := 64) address)
    (panSetByteHOL address 0#64 (MemoryBytes.wordBits (memory (panByteAlignHOL (width := 64) address))) be)

theorem zero_byte_execute {F : Type} (source : PanSemStateFiniteExact 64 F)
    (destination : ExpHOL 64) (address : BitVec 64)
    (read : eval source destination = some (.val (.word address)))
    (mapped : source.memaddrs (panByteAlignHOL (width := 64) address)) :
    evaluateHOLFiniteState source (.storeByte destination (.const 0#64)) =
      (none, { source with memory := byteMemory source.memory source.be address }) := by
  classical
  simp only [eval] at read
  rw [evaluateHOLFiniteState_storeByte, read]
  cases stored : source.memory (panByteAlignHOL (width := 64) address) with
  | word value =>
    simp [evalHOLExact, panMemStoreByteWord8HOL, mapped, stored, byteMemory, MemoryBytes.wordBits, StoreWord.put]
    rfl

theorem tail_body_shape : tailBody =
    .seq (.storeByte (.op .add [localVar "dst", localVar "i"]) (.const 0#64)) (increment 1#64) := by
  simp only [tailBody, loopTail, body, BuildProgram.loops, Guest.Software.guestFn_memzero,
    progToHOL, expToHOL, shapeToHOL, List.map_cons, List.map_nil, List.nil_append, List.cons_append,
    List.append_nil, List.getElem?_cons_zero, List.getElem?_cons_succ, Option.getD_some, increment, localVar, addConst]

def bytePost {F : Type} (source : PanSemStateFiniteExact 64 F) (dst index : BitVec 64) : PanSemStateFiniteExact 64 F :=
  bind { source with memory := byteMemory source.memory source.be (dst + index) } "i" (index + 1#64)

theorem tail_body_execute {F : Type} (source : PanSemStateFiniteExact 64 F) (dst index : BitVec 64)
    (dstLocal : source.locals.lookup (ofString "dst") = some (.val (.word dst)))
    (indexLocal : source.locals.lookup (ofString "i") = some (.val (.word index)))
    (mapped : source.memaddrs (panByteAlignHOL (width := 64) (dst + index))) :
    evaluateHOLFiniteState source tailBody = (none, bytePost source dst index) := by
  have addressRead : eval source (.op .add [localVar "dst", localVar "i"]) = some (.val (.word (dst + index))) := by
    simp [eval, localVar, evalHOLExact, evalListHOLExact, toExact, dstLocal, indexLocal,
      valueIsWord, valueWord, wordOpHOL, wordOp]
  have stored := zero_byte_execute source _ (dst + index) addressRead mapped
  let written := { source with memory := byteMemory source.memory source.be (dst + index) }
  have incremented := StateSteps.assign_execute written "i" (addConst (localVar "i") 1#64) index (index + 1#64)
    indexLocal (by simp [eval, localVar, addConst, evalHOLExact, evalListHOLExact, toExact, written, indexLocal,
      valueIsWord, valueWord, wordOpHOL, wordOp])
  rw [tail_body_shape, StateSteps.next_sequence source written _ _ stored (Nat.le_refl _)]
  exact incremented

end InitECandidate.Solver.WitnessRadix.Zero

#print axioms InitECandidate.Solver.WitnessRadix.Zero.zero_byte_execute
#print axioms InitECandidate.Solver.WitnessRadix.Zero.tail_body_execute

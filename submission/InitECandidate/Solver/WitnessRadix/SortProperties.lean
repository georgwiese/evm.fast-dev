import InitECandidate.Solver.WitnessRadix.SortCopy

namespace InitECandidate.Solver.WitnessRadix.SortProgram
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
open QueryBranch

def sortedMemory (memory : BitVec 64 → HolWordLab 64) (src dst : BitVec 64)
    (keyFor : BitVec 64 → ByteKeys.Key) (position start : Nat) (input : List (BitVec 64)) :
    BitVec 64 → HolWordLab 64 :=
  BuildCopy.copyMemory
    (BuildCopy.copyMemory memory dst (BitVec.ofNat 64 start) 0 (ScatterProgram.partition keyFor position input))
    src (BitVec.ofNat 64 start) 0 (ScatterProgram.partition keyFor position input)

theorem sorted_frame {F : Type} (source : PanSemStateFiniteExact 64 F) (src dst : BitVec 64)
    (keyFor : BitVec 64 → ByteKeys.Key) (position start limit : Nat) (input : List (BitVec 64))
    (fits : start + input.length ≤ limit) (allocation : dst.toNat + 8 * limit < 2 ^ 64) :
    emptyLocalsHOLFinite (sorted source src dst keyFor position start input) =
      emptyLocalsHOLFinite { source with
        memory := sortedMemory source.memory src dst keyFor position start input
        clock := source.clock - 2 * input.length } := by
  have scatterFrame := scattered_frame source dst keyFor position start input
  have memoryEq := scattered_memory source dst keyFor position start limit input fits allocation
  have rawMemory := congrArg (fun state : PanSemStateFiniteExact 64 F => state.memory) scatterFrame
  have heapEq : WordScatter.scatterWords (ScatterProgram.wordAddress dst) (ScatterProgram.keep keyFor position)
      input source.memory start (start + ScatterProgram.zeros keyFor position input) =
      BuildCopy.copyMemory source.memory dst (BitVec.ofNat 64 start) 0 (ScatterProgram.partition keyFor position input) :=
    rawMemory.symm.trans memoryEq
  have moved := congrArg (fun state : PanSemStateFiniteExact 64 F =>
    { state with
      memory := BuildCopy.copyMemory state.memory src (BitVec.ofNat 64 start) 0 (ScatterProgram.partition keyFor position input)
      clock := state.clock - (ScatterProgram.partition keyFor position input).length }) scatterFrame
  rw [sorted, BuildCopy.copyState_frame]
  have clockSub : source.clock - input.length - input.length = source.clock - 2 * input.length := by omega
  simpa only [second, QueryBranch.bind, setVarHOLFinite, emptyLocalsHOLFinite,
    heapEq, ScatterProgram.partition_length, clockSub, sortedMemory] using moved

theorem sorted_index {F : Type} (source : PanSemStateFiniteExact 64 F) (src dst : BitVec 64)
    (keyFor : BitVec 64 → ByteKeys.Key) (position start : Nat) (input : List (BitVec 64)) :
    (sorted source src dst keyFor position start input).locals.lookup (ofString "i") =
      some (.val (.word (BitVec.ofNat 64 input.length))) := by
  have initial := bind_lookup_same (scattered source dst keyFor position start input) "i" 0#64
  simpa only [sorted, Nat.zero_add, ScatterProgram.partition_length] using
    BuildCopy.copyState_index (second source dst keyFor position start input) src (BitVec.ofNat 64 start) 0
      (ScatterProgram.partition keyFor position input) initial

theorem sorted_other {F : Type} (source : PanSemStateFiniteExact 64 F) (src dst : BitVec 64)
    (keyFor : BitVec 64 → ByteKeys.Key) (position start : Nat) (input : List (BitVec 64)) (name : MlS)
    (notI : ofString "i" ≠ name) (notZero : ofString "zero_cursor" ≠ name) (notOne : ofString "one_cursor" ≠ name) :
    (sorted source src dst keyFor position start input).locals.lookup name = source.locals.lookup name := by
  unfold sorted
  rw [BuildCopy.copyState_other _ _ _ _ _ name notI]
  exact second_other source dst keyFor position start input name notI notZero notOne

theorem sorted_outside_cursors {F : Type} (source : PanSemStateFiniteExact 64 F) (src dst : BitVec 64)
    (keyFor : BitVec 64 → ByteKeys.Key) (position start : Nat) (input : List (BitVec 64))
    (initialIndex : source.locals.lookup (ofString "i") = some (.val (.word (BitVec.ofNat 64 input.length))))
    (name : MlS) (notZero : name ≠ ofString "zero_cursor") (notOne : name ≠ ofString "one_cursor") :
    (sorted source src dst keyFor position start input).locals.lookup name = source.locals.lookup name := by
  by_cases atI : name = ofString "i"
  · subst name
    rw [sorted_index]
    exact initialIndex.symm
  · exact sorted_other source src dst keyFor position start input name (Ne.symm atI) (Ne.symm notZero) (Ne.symm notOne)

end InitECandidate.Solver.WitnessRadix.SortProgram

#print axioms InitECandidate.Solver.WitnessRadix.SortProgram.sorted_frame
#print axioms InitECandidate.Solver.WitnessRadix.SortProgram.sorted_outside_cursors

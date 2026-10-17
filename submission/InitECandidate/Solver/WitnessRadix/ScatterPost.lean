import InitECandidate.Solver.WitnessRadix.ScatterBody
import InitECandidate.Solver.WitnessRadix.BuildRows

namespace InitECandidate.Solver.WitnessRadix.ScatterProgram
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
open QueryBranch

def destination (dst digit zeroCursor oneCursor : BitVec 64) : BitVec 64 :=
  dst + (if digit = 0#64 then zeroCursor else oneCursor) * 8#64

theorem post_frame {F : Type} (source : PanSemStateFiniteExact 64 F)
    (dst digit ordinal zeroCursor oneCursor index : BitVec 64) :
    emptyLocalsHOLFinite (post source dst digit ordinal zeroCursor oneCursor index) =
      emptyLocalsHOLFinite { source with
        memory := StoreWord.put source.memory (destination dst digit zeroCursor oneCursor) ordinal } := by
  by_cases zero : digit = 0#64
  all_goals simp only [post, destination, zero, ↓reduceIte]; rfl

theorem post_lookup {F : Type} (source : PanSemStateFiniteExact 64 F)
    (dst digit ordinal zeroCursor oneCursor index : BitVec 64) (name : MlS)
    (notI : ofString "i" ≠ name) (notZero : ofString "zero_cursor" ≠ name)
    (notOne : ofString "one_cursor" ≠ name) :
    (post source dst digit ordinal zeroCursor oneCursor index).locals.lookup name = source.locals.lookup name := by
  by_cases zero : digit = 0#64
  all_goals simp [post, zero, QueryBranch.bind, setVarHOLFinite,
    HolFiniteMapExact.update, FUPDATE, notI, notZero, notOne]

theorem post_index {F : Type} (source : PanSemStateFiniteExact 64 F)
    (dst digit ordinal zeroCursor oneCursor index : BitVec 64) :
    (post source dst digit ordinal zeroCursor oneCursor index).locals.lookup (ofString "i") =
      some (.val (.word (index + 1#64))) := by
  simp [post, QueryBranch.bind, setVarHOLFinite, HolFiniteMapExact.update, FUPDATE]

theorem post_zero {F : Type} (source : PanSemStateFiniteExact 64 F)
    (dst digit ordinal zeroCursor oneCursor index : BitVec 64)
    (initial : source.locals.lookup (ofString "zero_cursor") = some (.val (.word zeroCursor))) :
    (post source dst digit ordinal zeroCursor oneCursor index).locals.lookup (ofString "zero_cursor") =
      some (.val (.word (if digit = 0#64 then zeroCursor + 1#64 else zeroCursor))) := by
  have notI : ofString "i" ≠ ofString "zero_cursor" := by decide
  have notOne : ofString "one_cursor" ≠ ofString "zero_cursor" := by decide
  by_cases zero : digit = 0#64
  all_goals simp [post, zero, QueryBranch.bind, setVarHOLFinite,
    HolFiniteMapExact.update, FUPDATE, notI, notOne, initial]

theorem post_one {F : Type} (source : PanSemStateFiniteExact 64 F)
    (dst digit ordinal zeroCursor oneCursor index : BitVec 64)
    (initial : source.locals.lookup (ofString "one_cursor") = some (.val (.word oneCursor))) :
    (post source dst digit ordinal zeroCursor oneCursor index).locals.lookup (ofString "one_cursor") =
      some (.val (.word (if digit = 0#64 then oneCursor else oneCursor + 1#64))) := by
  have notI : ofString "i" ≠ ofString "one_cursor" := by decide
  have notZero : ofString "zero_cursor" ≠ ofString "one_cursor" := by decide
  by_cases zero : digit = 0#64
  all_goals simp [post, zero, QueryBranch.bind, setVarHOLFinite,
    HolFiniteMapExact.update, FUPDATE, notI, notZero, initial]

theorem post_byteView {F : Type} (source : PanSemStateFiniteExact 64 F)
    (dst digit ordinal zeroCursor oneCursor index pointer : BitVec 64) (key : ByteKeys.Key)
    (view : MemoryBytes.ByteView source pointer key)
    (away : ∀ byte : Fin 32, panByteAlignHOL (width := 64)
      (pointer + BitVec.ofNat 64 byte.val) ≠ destination dst digit zeroCursor oneCursor) :
    MemoryBytes.ByteView (post source dst digit ordinal zeroCursor oneCursor index) pointer key := by
  have written := StoreWord.byteView_away source (destination dst digit zeroCursor oneCursor)
    ordinal pointer key away view
  have frame := post_frame source dst digit ordinal zeroCursor oneCursor index
  apply MemoryBytes.byteView_of_fields _ _
    (congrArg (fun state => state.memory) frame).symm
    (congrArg (fun state => state.memaddrs) frame).symm
    (congrArg (fun state => state.be) frame).symm _ _ written

theorem post_rows {F : Type} (source : PanSemStateFiniteExact 64 F)
    (dst digit ordinal zeroCursor oneCursor index base start : BitVec 64)
    (offset : Nat) (input : List (BitVec 64))
    (rows : BuildCopy.Rows source.memory source.memaddrs base start offset input)
    (away : ∀ i < input.length, BuildCopy.row base start (BitVec.ofNat 64 (offset + i)) ≠
      destination dst digit zeroCursor oneCursor) :
    BuildCopy.Rows (post source dst digit ordinal zeroCursor oneCursor index).memory
      (post source dst digit ordinal zeroCursor oneCursor index).memaddrs base start offset input := by
  have frame := post_frame source dst digit ordinal zeroCursor oneCursor index
  have memoryEq : (post source dst digit ordinal zeroCursor oneCursor index).memory =
      StoreWord.put source.memory (destination dst digit zeroCursor oneCursor) ordinal :=
    congrArg (fun state => state.memory) frame
  have domainEq : (post source dst digit ordinal zeroCursor oneCursor index).memaddrs = source.memaddrs :=
    congrArg (fun state => state.memaddrs) frame
  rw [memoryEq, domainEq]
  exact BuildCopy.rows_store_away _ _ base start _ ordinal offset input rows away

end InitECandidate.Solver.WitnessRadix.ScatterProgram

#print axioms InitECandidate.Solver.WitnessRadix.ScatterProgram.post_frame
#print axioms InitECandidate.Solver.WitnessRadix.ScatterProgram.post_byteView
#print axioms InitECandidate.Solver.WitnessRadix.ScatterProgram.post_rows

import InitECandidate.Solver.Mpt.KeyToNibblesPair
import InitECandidate.Solver.WitnessRadix.ByteRegion
import InitECandidate.Solver.Input.ScalarScope

namespace InitECandidate.Solver.Mpt.KeyToNibbles
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch

theorem input_read {F : Type} (source : PanSemStateFiniteExact 64 F) (key index : BitVec 64) (offset : Nat)
    (keyCell : source.locals.lookup (ofString "key") = some (.val (.word key)))
    (indexCell : source.locals.lookup (ofString "i") = some (.val (.word index))) :
    eval source (inputAddress offset) = some (.val (.word (key + index + BitVec.ofNat 64 offset))) := by
  by_cases zero : offset = 0
  · subst offset
    simp [inputAddress, eval, evalHOLExact, evalListHOLExact, localVar, toExact, keyCell, indexCell,
      valueIsWord, valueWord, wordOpHOL, wordOp]
  · simp [inputAddress, zero, eval, evalHOLExact, evalListHOLExact, localVar, toExact, keyCell, indexCell,
      valueIsWord, valueWord, wordOpHOL, wordOp, BitVec.add_assoc]

def byteStep (name : String) (offset : Nat) (rest : ProgHOL 64) : ProgHOL 64 :=
  .dec (ofString name) .one (.loadByte (inputAddress offset)) (pair name offset rest)
def byteState {F : Type} (source : PanSemStateFiniteExact 64 F) (name : String) (offset : Nat)
    (out index : BitVec 64) (byte : BitVec 8) : PanSemStateFiniteExact 64 F :=
  pairState (bind source name (BitVec.ofNat 64 byte.toNat)) out index offset byte

/-- A literal input-byte declaration followed by its two stores, exposing
the real continuation and lexical restoration. -/
theorem byte_execute {F : Type} (source : PanSemStateFiniteExact 64 F) (name : String) (offset : Nat)
    (key out index : BitVec 64) (byte : BitVec 8) (rest : ProgHOL 64)
    (notOut : ofString "out" ≠ ofString name) (notIndex : ofString "i" ≠ ofString name)
    (keyCell : source.locals.lookup (ofString "key") = some (.val (.word key)))
    (outCell : source.locals.lookup (ofString "out") = some (.val (.word out)))
    (indexCell : source.locals.lookup (ofString "i") = some (.val (.word index)))
    (loaded : ByteRegion.read source (key + index + BitVec.ofNat 64 offset) = some byte)
    (firstMapped : source.memaddrs (panByteAlignHOL (width := 64) (firstAddress out index offset)))
    (secondMapped : source.memaddrs (panByteAlignHOL (width := 64) (secondAddress out index offset))) :
    evaluateHOLFiniteState source (byteStep name offset rest) =
      (let output := evaluateHOLFiniteState (byteState source name offset out index byte) rest
       (output.1, restore source name output.2)) := by
  have addressRead := input_read source key index offset keyCell indexCell
  have read := ByteRegion.load_expression source (inputAddress offset) _ byte addressRead loaded
  let entered := bind source name (BitVec.ofNat 64 byte.toNat)
  have currentOut : entered.locals.lookup (ofString "out") = some (.val (.word out)) :=
    (bind_lookup_other source name "out" _ (Ne.symm notOut)).trans outCell
  have currentIndex : entered.locals.lookup (ofString "i") = some (.val (.word index)) :=
    (bind_lookup_other source name "i" _ (Ne.symm notIndex)).trans indexCell
  have currentByte : entered.locals.lookup (ofString name) = some (.val (.word (BitVec.ofNat 64 byte.toNat))) := bind_lookup_same _ _ _
  have stores := pair_execute entered name offset out index byte rest currentOut currentIndex currentByte firstMapped secondMapped
  let output := evaluateHOLFiniteState (byteState source name offset out index byte) rest
  have actual := Input.ScalarScope.declare_execute source output.2 name (.loadByte (inputAddress offset))
    (BitVec.ofNat 64 byte.toNat) (pair name offset rest) output.1 read stores
  exact actual

theorem pair_other_byte {F : Type} (source : PanSemStateFiniteExact 64 F) (out index query : BitVec 64) (offset : Nat) (byte : BitVec 8)
    (little : source.be = false) (firstOther : firstAddress out index offset ≠ query) (secondOther : secondAddress out index offset ≠ query) :
    @panMemLoadByteHOL 64 _ (pairState source out index offset byte).memory source.memaddrs
      (fun address => Classical.propDecidable (source.memaddrs address)) false query =
      @panMemLoadByteHOL 64 _ source.memory source.memaddrs
      (fun address => Classical.propDecidable (source.memaddrs address)) false query := by
  simp only [pairState, little]
  rw [ByteStore.read_other _ _ _ _ _ secondOther, ByteStore.read_other _ _ _ _ _ firstOther]

end InitECandidate.Solver.Mpt.KeyToNibbles

#print axioms InitECandidate.Solver.Mpt.KeyToNibbles.input_read
#print axioms InitECandidate.Solver.Mpt.KeyToNibbles.byte_execute
#print axioms InitECandidate.Solver.Mpt.KeyToNibbles.pair_other_byte

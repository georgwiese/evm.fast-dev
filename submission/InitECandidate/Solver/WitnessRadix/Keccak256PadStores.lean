import InitECandidate.Solver.WitnessRadix.Keccak256AfterProgram

namespace InitECandidate.Solver.WitnessRadix.Keccak256
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString QueryBranch

def firstPadState {F : Type} (source : PanSemStateFiniteExact 64 F) (scratch rem : BitVec 64) : PanSemStateFiniteExact 64 F :=
  {source with memory := ByteStore.put source.memory source.be (scratch+rem) 1#8}

theorem pad_first_execute {F : Type} (source : PanSemStateFiniteExact 64 F) (scratch rem : BitVec 64)
    (scratchGlobal : source.globals.lookup (ofString "keccak_pad")=some (.val (.word scratch)))
    (remLocal : source.locals.lookup (ofString "rem")=some (.val (.word rem)))
    (mapped : source.memaddrs (panByteAlignHOL (width := 64) (scratch+rem))) :
    evaluateHOLFiniteState source padFirst=(none,firstPadState source scratch rem) := by
  have addressRead : eval source (.op .add [pad,localVar "rem"])=some (.val (.word (scratch+rem))) := by
    simp [eval,pad,localVar,evalHOLExact,evalListHOLExact,toExact,scratchGlobal,remLocal,valueIsWord,valueWord,wordOpHOL,wordOp]
  exact ByteStore.execute_word source _ _ _ 1#64 addressRead rfl mapped

def lastPadWord {F : Type} (source : PanSemStateFiniteExact 64 F) (scratch : BitVec 64) : BitVec 64 :=
  BitVec.ofNat 64 (ByteRegion.value source (scratch+135#64)).toNat ||| 128#64
def lastPadState {F : Type} (source : PanSemStateFiniteExact 64 F) (scratch : BitVec 64) : PanSemStateFiniteExact 64 F :=
  {source with memory := ByteStore.put source.memory source.be (scratch+135#64) (BitVec.ofNat 8 (lastPadWord source scratch).toNat)}

theorem pad_last_execute {F : Type} (source : PanSemStateFiniteExact 64 F) (scratch : BitVec 64)
    (scratchGlobal : source.globals.lookup (ofString "keccak_pad")=some (.val (.word scratch)))
    (mapped : source.memaddrs (panByteAlignHOL (width := 64) (scratch+135#64))) :
    evaluateHOLFiniteState source padLast=(none,lastPadState source scratch) := by
  have addressRead : eval source padLastAddress=some (.val (.word (scratch+135#64))) := by
    simp [eval,padLastAddress,pad,evalHOLExact,evalListHOLExact,toExact,scratchGlobal,valueIsWord,valueWord,wordOpHOL,wordOp]
  have byteRead := ByteRegion.mapped_read source (scratch+135#64) mapped
  have loaded := ByteRegion.load_expression source padLastAddress _ _ addressRead byteRead
  have orRead : eval source (.op .or [.loadByte padLastAddress,.const 128#64])=some (.val (.word (lastPadWord source scratch))) := by
    simp only [eval] at loaded ⊢
    rw [evalHOLExact]
    simp only [evalListHOLExact,loaded,show @evalHOLExact 64 F _ source.toExact
      (fun address => Classical.propDecidable (source.memaddrs address)) (.const 128#64)=some (.val (.word 128#64)) from rfl]
    simp [valueIsWord,valueWord,wordOpHOL,wordOp,lastPadWord,OrOp.or]
  exact ByteStore.execute_word source _ _ _ _ addressRead orRead mapped

end InitECandidate.Solver.WitnessRadix.Keccak256

#print axioms InitECandidate.Solver.WitnessRadix.Keccak256.pad_first_execute
#print axioms InitECandidate.Solver.WitnessRadix.Keccak256.pad_last_execute

import InitECandidate.Solver.Input.PayloadHeaderFrame
import InitECandidate.Solver.Input.RlpWrite.U256Store

namespace InitECandidate.Solver.Input.PayloadHeader
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

def wideStored (source : PanSemStateFiniteExact 64 Guest.HostMemory) (heap : BitVec 64) (offset : Nat) (words : RlpWrite.U256Value.Words):=
  storedField (storedField (storedField (storedField source heap offset (words 0))
    heap (offset+8) (words 1)) heap (offset+16) (words 2)) heap (offset+24) (words 3)

theorem store_wide_execute (source : PanSemStateFiniteExact 64 Guest.HostMemory) (heap : BitVec 64)
    (offset : Nat) (words : RlpWrite.U256Value.Words) (expression : ExpHOL 64)
    (domain : source.memaddrs=InitE.ordinaryDomain) (arena : AllocatedBytes.Arena heap 248) (aligned : heap.toNat%8=0)
    (inside : offset+32≤248) (offsetAligned : offset%8=0)
    (hCell : source.locals.lookup (ofString "h")=some (.val (.word heap)))
    (readValue : eval source expression=some (RlpWrite.U256Value.tuple words)) :
    evaluateHOLFiniteState source (.store (headerAddress offset) expression)=(none,wideStored source heap offset words) := by
  have address : eval source (headerAddress offset)=some (.val (.word (heap+BitVec.ofNat 64 offset))):=by
    simp [eval,evalHOLExact,evalListHOLExact,toExact,headerAddress,localVar,hCell,valueIsWord,valueWord,wordOpHOL,wordOp]
  have mapped (index : Fin 4) : source.memaddrs (heap+BitVec.ofNat 64 offset+BitVec.ofNat 64 (8*index.val)):=by
    have cell:=AllocatedBytes.word_mapped source heap 248 (offset+8*index.val) domain arena
      (by have h:=index.isLt; omega) aligned (by omega)
    simpa only [byteAddress,BitVec.ofNat_add,BitVec.add_assoc] using cell
  have run:=RlpWrite.U256Value.store_execute source (headerAddress offset) expression _ words address readValue mapped
  simpa only [wideStored,storedField,RlpWrite.U256Value.wordWrites,WordWrites.write,BitVec.ofNat_add,BitVec.add_assoc] using run

theorem HeaderFrame.wide_stored (input : Guest.InputBlob) (source current : PanSemStateFiniteExact 64 Guest.HostMemory)
    (heap : BitVec 64) (frame : HeaderFrame input source heap current) (offset : Nat) (words : RlpWrite.U256Value.Words)
    (arena : AllocatedBytes.Arena heap 248) (inside : offset+32≤248) :
    HeaderFrame input source heap (wideStored current heap offset words) := by
  have first:=frame.stored input source current heap offset (words 0) arena (by omega)
  have second:=first.stored input source _ heap (offset+8) (words 1) arena (by omega)
  have third:=second.stored input source _ heap (offset+16) (words 2) arena (by omega)
  exact third.stored input source _ heap (offset+24) (words 3) arena (by omega)

end InitECandidate.Solver.Input.PayloadHeader

#print axioms InitECandidate.Solver.Input.PayloadHeader.store_wide_execute
#print axioms InitECandidate.Solver.Input.PayloadHeader.HeaderFrame.wide_stored

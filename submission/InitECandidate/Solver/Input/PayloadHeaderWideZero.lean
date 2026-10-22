import InitECandidate.Solver.Input.PayloadHeaderFrame
import InitECandidate.Solver.Input.RlpWrite.U256Store

namespace InitECandidate.Solver.Input.PayloadHeader
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

def wideZeroExpression : ExpHOL 64:=.rstruct [.const 0#64,.const 0#64,.const 0#64,.const 0#64]
def storeWideZero : ProgHOL 64:=.store (headerAddress 64) wideZeroExpression
def wideZeroStored (source : PanSemStateFiniteExact 64 Guest.HostMemory) (heap : BitVec 64):=
  storedField (storedField (storedField (storedField source heap 64 0#64) heap 72 0#64) heap 80 0#64) heap 88 0#64

theorem wide_zero_execute (source : PanSemStateFiniteExact 64 Guest.HostMemory) (heap : BitVec 64)
    (domain : source.memaddrs=InitE.ordinaryDomain) (arena : AllocatedBytes.Arena heap 248) (aligned : heap.toNat%8=0)
    (hCell : source.locals.lookup (ofString "h")=some (.val (.word heap))) :
    evaluateHOLFiniteState source storeWideZero=(none,wideZeroStored source heap) := by
  have address : eval source (headerAddress 64)=some (.val (.word (heap+64#64))):=by
    simp [eval,evalHOLExact,evalListHOLExact,toExact,headerAddress,localVar,hCell,valueIsWord,valueWord,wordOpHOL,wordOp]
  have mapped (index : Fin 4) : source.memaddrs (heap+64#64+BitVec.ofNat 64 (8*index.val)):=by
    have cell:=AllocatedBytes.word_mapped source heap 248 (64+8*index.val) domain arena
      (by have h:=index.isLt; omega) aligned (by omega)
    simpa only [byteAddress,BitVec.ofNat_add,BitVec.add_assoc] using cell
  have run:=RlpWrite.U256Value.store_execute source (headerAddress 64) wideZeroExpression (heap+64#64) (fun _=>0#64) address rfl mapped
  simpa only [storeWideZero,wideZeroStored,storedField,RlpWrite.U256Value.wordWrites,WordWrites.write,BitVec.add_assoc,
    show 64#64+8#64=72#64 from by decide,show 64#64+16#64=80#64 from by decide,show 64#64+24#64=88#64 from by decide] using run

theorem HeaderFrame.wide_zero (input : Guest.InputBlob) (source current : PanSemStateFiniteExact 64 Guest.HostMemory)
    (heap : BitVec 64) (frame : HeaderFrame input source heap current) (arena : AllocatedBytes.Arena heap 248) :
    HeaderFrame input source heap (wideZeroStored current heap) := by
  have first:=frame.stored input source current heap 64 0#64 arena (by decide)
  have second:=first.stored input source _ heap 72 0#64 arena (by decide)
  have third:=second.stored input source _ heap 80 0#64 arena (by decide)
  exact third.stored input source _ heap 88 0#64 arena (by decide)

end InitECandidate.Solver.Input.PayloadHeader

#print axioms InitECandidate.Solver.Input.PayloadHeader.wide_zero_execute
#print axioms InitECandidate.Solver.Input.PayloadHeader.HeaderFrame.wide_zero

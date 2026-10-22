import InitECandidate.Solver.Input.PayloadHeaderOmmerFields

namespace InitECandidate.Solver.Input.PayloadHeader
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

def storeField (offset : Nat) (value : ExpHOL 64) : ProgHOL 64:=.store (headerAddress offset) value
def storedField (source : PanSemStateFiniteExact 64 Guest.HostMemory) (heap : BitVec 64) (offset : Nat) (value : BitVec 64):=
  {source with memory:=StoreWord.put source.memory (heap+BitVec.ofNat 64 offset) value}

theorem store_field_execute (source : PanSemStateFiniteExact 64 Guest.HostMemory) (heap : BitVec 64)
    (offset : Nat) (value : BitVec 64) (expression : ExpHOL 64)
    (domain : source.memaddrs=InitE.ordinaryDomain) (arena : AllocatedBytes.Arena heap 248) (aligned : heap.toNat%8=0)
    (inside : offset<248) (offsetAligned : offset%8=0)
    (hCell : source.locals.lookup (ofString "h")=some (.val (.word heap)))
    (readValue : eval source expression=some (.val (.word value))) :
    evaluateHOLFiniteState source (storeField offset expression)=(none,storedField source heap offset value) := by
  have address : eval source (headerAddress offset)=some (.val (.word (heap+BitVec.ofNat 64 offset))):=by
    simp [eval,evalHOLExact,evalListHOLExact,toExact,headerAddress,localVar,hCell,valueIsWord,valueWord,wordOpHOL,wordOp]
  exact StoreWord.execute source (headerAddress offset) expression _ value address readValue
    (AllocatedBytes.word_mapped source heap 248 offset domain arena inside aligned offsetAligned)

theorem stored_field_older (source : PanSemStateFiniteExact 64 Guest.HostMemory) (heap query : BitVec 64)
    (offset : Nat) (value : BitVec 64) (arena : AllocatedBytes.Arena heap 248) (inside : offset<248)
    (before : query.toNat<heap.toNat) : (storedField source heap offset value).memory query=source.memory query := by
  apply if_neg
  intro same
  have number:=byteAddress_toNat heap offset (by have h:=arena.upper; omega)
  change (heap+BitVec.ofNat 64 offset).toNat=heap.toNat+offset at number
  have numeric:=congrArg BitVec.toNat same
  omega

end InitECandidate.Solver.Input.PayloadHeader

#print axioms InitECandidate.Solver.Input.PayloadHeader.store_field_execute
#print axioms InitECandidate.Solver.Input.PayloadHeader.stored_field_older

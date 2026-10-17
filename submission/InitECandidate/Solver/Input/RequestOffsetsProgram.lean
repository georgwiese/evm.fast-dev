import InitECandidate.Solver.Input.RequestFromHeader

namespace InitECandidate.Solver.Input.Request
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch
open WitnessRadix.ProgramPrefix

def requestWords (input : Guest.InputBlob) (position : Nat) : BitVec 64 :=
  BitVec.ofNat 64 (Guest.GasLimit.le32 input (if position=0 then 18 else if position=1 then 22 else 58))
def offsetFirst (source : PanSemStateFiniteExact 64 Guest.HostMemory) (input : Guest.InputBlob) :=
  bind source "o_pl" (requestWords input 0)
def offsetSecond (source : PanSemStateFiniteExact 64 Guest.HostMemory) (input : Guest.InputBlob) :=
  bind (offsetFirst source input) "o_vh" (requestWords input 1)
def offsetLoaded (source : PanSemStateFiniteExact 64 Guest.HostMemory) (input : Guest.InputBlob) :=
  bind (offsetSecond source input) "o_rq" (requestWords input 2)
def payloadStored (source : PanSemStateFiniteExact 64 Guest.HostMemory) (input : Guest.InputBlob) (array : BitVec 64) :=
  {offsetLoaded source input with memory:=WitnessRadix.StoreWord.put source.memory array (requestWords input 0)}
def hashesStored (source : PanSemStateFiniteExact 64 Guest.HostMemory) (input : Guest.InputBlob) (array : BitVec 64) :=
  {payloadStored source input array with memory:=WitnessRadix.StoreWord.put (payloadStored source input array).memory (array+8#64) (requestWords input 1)}
def offsetsStored (source : PanSemStateFiniteExact 64 Guest.HostMemory) (input : Guest.InputBlob) (array : BitVec 64) :=
  {hashesStored source input array with memory:=WitnessRadix.StoreWord.put (hashesStored source input array).memory (array+16#64) (requestWords input 2)}
def offsetActions : List Action := [
  .declare "o_pl" (Scalar.flat32 (localVar "np") []),
  .declare "o_vh" (Scalar.flat32 (localVar "np") [4]),
  .declare "o_rq" (Scalar.flat32 (localVar "np") [40]),
  .command storePayload,.command storeHashes,.command storeRequests]
def restoreOffsets (source : PanSemStateFiniteExact 64 Guest.HostMemory) (input : Guest.InputBlob)
    (target : PanSemStateFiniteExact 64 Guest.HostMemory) :=
  restore source "o_pl" (restore (offsetFirst source input) "o_vh" (restore (offsetSecond source input) "o_rq" target))

theorem offset_actions_shape : requestBody=program offsetActions (.seq guardCall continuation) := by
  rw [request_shape]
  rfl

/-- The three request offset reads use the copied extent, with no assumption
about the mathematical input list length or its decoded shape. -/
theorem request_read (source : PanSemStateFiniteExact 64 Guest.HostMemory) (input : Guest.InputBlob)
    (pointer : BitVec 64) (extras : List Nat) (start : Nat)
    (heap : Blob.HeapInput source input pointer) (inside : start+4≤input.length%2^64)
    (np : source.locals.lookup (ofString "np")=some (.val (.word (pointer+18#64))))
    (offset : 18+extras.sum=start) :
    eval source (Scalar.flat32 (localVar "np") extras)=some (.val (.word (BitVec.ofNat 64 (Guest.GasLimit.le32 input start)))) := by
  have base : eval source (localVar "np")=some (.val (.word (pointer+18#64))) := by
    simpa [eval,localVar,evalHOLExact,toExact] using np
  have address:=Scalar.flat_read source (localVar "np") (pointer+18#64) extras base
  have field : pointer+18#64+BitVec.ofNat 64 extras.sum=pointer+BitVec.ofNat 64 start := by
    rw [BitVec.add_assoc,←BitVec.ofNat_add]
    exact congrArg (fun n=>pointer+BitVec.ofNat 64 n) offset
  rw [field] at address
  exact (Scalar.flat32_equiv source (localVar "np") (pointer+18#64) extras base).trans
    (Scalar.heap_le32 source input pointer start _ heap inside address)

end InitECandidate.Solver.Input.Request

#print axioms InitECandidate.Solver.Input.Request.offset_actions_shape
#print axioms InitECandidate.Solver.Input.Request.request_read

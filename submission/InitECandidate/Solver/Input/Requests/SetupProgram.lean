import InitECandidate.Solver.Input.Requests.OffsetsTrace
import InitECandidate.Solver.WitnessRadix.ProgramPrefix

namespace InitECandidate.Solver.Input.Requests
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString QueryBranch ProgramPrefix

def afterAllocation : ProgHOL 64 := match afterOffsets with | .decCall _ _ _ _ rest => rest | _ => .skip
def countCalls : ProgHOL 64 := Payload.dropLeading 5 afterAllocation
def loadOffset (position : Nat) : ExpHOL 64 := .load .one (if position = 0 then Header.offsets else Scalar.plus Header.offsets (8*position))
def setupActions : List Action := [.allocate "rq" (.const 80#64),
  .declare "o0" (loadOffset 0),.declare "o1" (loadOffset 1),.declare "o2" (loadOffset 2),.declare "o3" (loadOffset 3),.declare "o4" (loadOffset 4)]

theorem setup_shape : afterOffsets = program setupActions countCalls := by
  simp only [afterOffsets,offsetTail,body,Guest.guestFn_decode_requests,progToHOL,expToHOL,shapeToHOL,List.map_cons,List.map_nil,Option.map_none,
    program,setupActions,countCalls,afterAllocation,Payload.dropLeading,loadOffset,Header.offsets,Scalar.plus]
  rfl

def allocated (source : PanSemStateFiniteExact 64 Guest.HostMemory) (cursor : BitVec 64) :=
  bind (PersistentAlloc.post {source with clock := source.clock - 1} cursor 80#64) "rq" cursor

def loaded0 (source : PanSemStateFiniteExact 64 Guest.HostMemory) (input : Guest.InputBlob) (cursor : BitVec 64) (start : Nat) :=
  bind (allocated source cursor) "o0" (offsetWord input start 0)
def loaded1 (source : PanSemStateFiniteExact 64 Guest.HostMemory) (input : Guest.InputBlob) (cursor : BitVec 64) (start : Nat) :=
  bind (loaded0 source input cursor start) "o1" (offsetWord input start 1)
def loaded2 (source : PanSemStateFiniteExact 64 Guest.HostMemory) (input : Guest.InputBlob) (cursor : BitVec 64) (start : Nat) :=
  bind (loaded1 source input cursor start) "o2" (offsetWord input start 2)
def loaded3 (source : PanSemStateFiniteExact 64 Guest.HostMemory) (input : Guest.InputBlob) (cursor : BitVec 64) (start : Nat) :=
  bind (loaded2 source input cursor start) "o3" (offsetWord input start 3)
def prepared (source : PanSemStateFiniteExact 64 Guest.HostMemory) (input : Guest.InputBlob) (cursor : BitVec 64) (start : Nat) :=
  bind (loaded3 source input cursor start) "o4" (offsetWord input start 4)

def restoreSetup (source : PanSemStateFiniteExact 64 Guest.HostMemory) (input : Guest.InputBlob) (cursor : BitVec 64) (start : Nat)
    (target : PanSemStateFiniteExact 64 Guest.HostMemory) :=
  restore source "rq" (restore (allocated source cursor) "o0" (restore (loaded0 source input cursor start) "o1"
    (restore (loaded1 source input cursor start) "o2" (restore (loaded2 source input cursor start) "o3" (restore (loaded3 source input cursor start) "o4" target)))))

end InitECandidate.Solver.Input.Requests

#print axioms InitECandidate.Solver.Input.Requests.setup_shape

import InitECandidate.Solver.Input.Requests.OffsetsTrace
import InitECandidate.Solver.Input.DropLeading

namespace InitECandidate.Solver.Input.Requests
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

def afterAllocation : ProgHOL 64 := match afterOffsets with | .decCall _ _ _ _ rest => rest | _ => .skip
def countCalls : ProgHOL 64 := Payload.dropLeading 5 afterAllocation
def loadOffset (position : Nat) : ExpHOL 64 := .load .one (if position = 0 then Header.offsets else Scalar.plus Header.offsets (8 * position))

theorem allocation_shape : afterOffsets = .decCall (ofString "rq") .one (ofString "alloc") [.const 80#64] afterAllocation := by
  simp only [afterOffsets, offsetTail, afterAllocation, body, Guest.Software.guestFn_decode_requests,
    progToHOL, expToHOL, shapeToHOL, List.map_cons, List.map_nil, Option.map_none]

theorem loads_shape : afterAllocation = .dec (ofString "o0") .one (loadOffset 0)
    (.dec (ofString "o1") .one (loadOffset 1) (.dec (ofString "o2") .one (loadOffset 2)
      (.dec (ofString "o3") .one (loadOffset 3) (.dec (ofString "o4") .one (loadOffset 4) countCalls)))) := by
  simp only [afterAllocation, afterOffsets, offsetTail, countCalls, Payload.dropLeading, body,
    Guest.Software.guestFn_decode_requests, progToHOL, expToHOL, shapeToHOL, List.map_cons, List.map_nil,
    Option.map_none, loadOffset, Header.offsets, Scalar.plus]
  simp

end InitECandidate.Solver.Input.Requests

#print axioms InitECandidate.Solver.Input.Requests.allocation_shape
#print axioms InitECandidate.Solver.Input.Requests.loads_shape

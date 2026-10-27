import InitECandidate.Solver.Input.RequestOffsetValues
import InitECandidate.Solver.Input.FixedList.Environment

namespace InitECandidate.Solver.Input.Request
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

def hashCountArguments : List (ExpHOL 64) :=
  [.op .sub [localVar "o_rq", localVar "o_vh"], .const 32#64, .const 9223372036854775807#64]
def payloadPointerStore : ProgHOL 64 := .store (Scalar.plus (localVar "si") 0) (localVar "pl")
def hashCountCall : ProgHOL 64 := match afterPayload with | .seq _ rest => rest | _ => .skip
def afterHashCount : ProgHOL 64 := match hashCountCall with | .decCall _ _ _ _ rest => rest | _ => .skip

theorem hash_count_shape : afterPayload = .seq payloadPointerStore hashCountCall ∧
    hashCountCall = .decCall (ofString "nvh") .one (ofString "ssz_fixed_list_count") hashCountArguments afterHashCount := by
  simp only [afterHashCount, hashCountCall, payloadPointerStore, Scalar.plus, afterPayload, continuation, requestBody, prefixBody, Header.continuation,
    Header.afterHeader, Header.body, Guest.Software.guestFn_decode_stateless_input, progToHOL, expToHOL, shapeToHOL,
    List.map_cons, List.map_nil, Option.map_none, hashCountArguments, localVar]
  simp

theorem hash_count_arguments (source : PanSemStateFiniteExact 64 Guest.HostMemory) (input : Guest.InputBlob)
    (vh : source.locals.lookup (ofString "o_vh") = some (.val (.word (requestWords input 1))))
    (rq : source.locals.lookup (ofString "o_rq") = some (.val (.word (requestWords input 2)))) :
    evalListHOLFinite source (h := fun address => Classical.propDecidable (source.memaddrs address)) hashCountArguments =
      some (FixedList.values (requestWords input 2 - requestWords input 1) 32#64 9223372036854775807#64) := by
  classical
  simp [evalListHOLFinite, evalListHOLExact, evalHOLExact, toExact, hashCountArguments, FixedList.values,
    localVar, vh, rq, valueIsWord, valueWord, wordOpHOL, wordOp]

end InitECandidate.Solver.Input.Request

#print axioms InitECandidate.Solver.Input.Request.hash_count_shape
#print axioms InitECandidate.Solver.Input.Request.hash_count_arguments

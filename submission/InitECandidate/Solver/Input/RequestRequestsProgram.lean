import InitECandidate.Solver.Input.RequestHashesProgram
import InitECandidate.Solver.Input.DropLeading
import InitECandidate.Solver.Input.Requests.Entry

namespace InitECandidate.Solver.Input.Request
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

def hashPointerStore : ProgHOL 64 := .store (Scalar.plus (localVar "si") 8) (.op .add [localVar "np", localVar "o_vh"])
def hashCountStore : ProgHOL 64 := .store (Scalar.plus (localVar "si") 16) (localVar "nvh")
def requestHeaderStore : ProgHOL 64 := .store (Scalar.plus (localVar "si") 24) (Scalar.plus (localVar "np") 8)
def requestsArguments : List (ExpHOL 64) := [.op .add [localVar "np", localVar "o_rq"], .op .sub [localVar "nlen", localVar "o_rq"]]
def requestsCall : ProgHOL 64 := Payload.dropLeading 3 afterHashCount
def afterRequests : ProgHOL 64 := match requestsCall with | .decCall _ _ _ _ rest => rest | _ => .skip

theorem requests_shape : afterHashCount = .seq hashPointerStore (.seq hashCountStore (.seq requestHeaderStore requestsCall)) ∧
    requestsCall = .decCall (ofString "rq") .one (ofString "decode_requests") requestsArguments afterRequests := by
  simp only [afterRequests, requestsCall, Payload.dropLeading, afterHashCount, hashCountCall, afterPayload,
    continuation, requestBody, prefixBody, Header.continuation, Header.afterHeader, Header.body,
    Guest.Software.guestFn_decode_stateless_input, progToHOL, expToHOL, shapeToHOL, List.map_cons, List.map_nil,
    Option.map_none, hashPointerStore, hashCountStore, requestHeaderStore, requestsArguments, Scalar.plus, localVar]
  simp

end InitECandidate.Solver.Input.Request

#print axioms InitECandidate.Solver.Input.Request.requests_shape

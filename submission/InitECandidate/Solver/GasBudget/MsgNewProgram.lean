import InitECandidate.Solver.WitnessRadix.ZeroNormal
import InitECandidate.Solver.WitnessRadix.AllocationNormalExpected
import InitECandidate.Solver.Input.NormalCallClock
import InitECandidate.Solver.Input.CallResume
import InitECandidate.Solver.Input.LocalPrefix
import InitECandidate.Solver.MutableTable.MemoryRegionWord

namespace InitECandidate.Solver.GasBudget.MsgNew
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch WitnessRadix

def body : ProgHOL 64 := match Guest.guestFn_msg_new with | .function fn => progToHOL fn.body | _ => .skip
def formals : List (MlS × ShapeHOL) := []
def clearCall : ProgHOL 64 := .call (some (none, none)) (ofString "memzero") [localVar "m", .const 176#64]
def returnMessage : ProgHOL 64 := .return (localVar "m")

theorem body_shape : body = .decCall (ofString "m") .one (ofString "alloc") [.const 176#64] (.seq clearCall returnMessage) := by
  simp only [body, Guest.guestFn_msg_new, progToHOL, expToHOL, shapeToHOL, List.map_cons, List.map_nil, Option.map_none,
    clearCall, returnMessage, localVar]

theorem environment (codeFn : MlS → Option (List (MlS × ShapeHOL) × ProgHOL 64 × ShapeHOL))
    (code : codeFn (ofString "msg_new") = some (formals, body, .one)) :
    ∃ callee : HolFiniteMapExact MlS (ValueHOL 64), lookupCodeHOLFinite codeFn (ofString "msg_new") [] = some (body, callee, .one) := by
  have raw : lookupCodeHOLExact codeFn (ofString "msg_new") [] = some (body, (fun _ => none), .one) := by
    simp [lookupCodeHOLExact, code, formals]
  obtain ⟨callee, called, _⟩ := CodeEnvironment.finite_lookup codeFn (ofString "msg_new") [] body (fun _ => none) .one raw
  exact ⟨callee, called⟩

end InitECandidate.Solver.GasBudget.MsgNew

#print axioms InitECandidate.Solver.GasBudget.MsgNew.body_shape
#print axioms InitECandidate.Solver.GasBudget.MsgNew.environment

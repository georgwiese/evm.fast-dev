import InitECandidate.Solver.GasBudget.CallFirstFeeSites
import InitECandidate.Solver.GasBudget.StackPopsTyped
import InitECandidate.Solver.GasBudget.AddressMaskedCall
import InitECandidate.Solver.GasBudget.AddressMaskedFooter

namespace InitECandidate.Solver.GasBudget.CallOpcode
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

def body : ProgHOL 64 := match Guest.guestFn_op_call with | .function fn => progToHOL fn.body | _ => .skip
def firstNames : List String := ["gasv", "tov"]
def remainingNames : List String := ["value", "in_start", "in_size", "out_start", "out_size"]
def afterPops : ProgHOL 64 := OpcodeChargeSites.stripPops 8 body
def afterAddress : ProgHOL 64 := StackPop.pops remainingNames afterPops
def addressProgram : ProgHOL 64 := .decCall (ofString "to") .one (ofString "to_address_masked") [localVar "tov"] afterAddress

set_option maxRecDepth 10000 in
theorem body_shape : body = StackPop.pops firstNames addressProgram := by
  simp only [body, Guest.guestFn_op_call, firstNames, remainingNames, addressProgram, afterAddress, afterPops,
    OpcodeChargeSites.stripPops, StackPop.pops, StackPop.shape, progToHOL, expToHOL, shapeToHOL, List.map_cons,
    List.map_nil, Option.map_none, localVar]

set_option maxRecDepth 100000 in
theorem original_code (code) (installed : Input.OriginalCode.Installed code) :
    code.lookup (ofString "op_call") = some ([], body, .one) := by
  have checked := Input.OriginalCode.indexed code installed 557 (OriginalCodeEnvironment.originalEntry Guest.guestFn_op_call) (by rfl)
  simpa only [OriginalCodeEnvironment.originalEntry, declToHOL, funDeclToHOL, body, Guest.guestFn_op_call, shapeToHOL, List.map_nil] using checked

theorem remaining_away (key : String) (member : key ∈ (["gasv", "tov", "to"] : List String)) :
    ∀ name ∈ remainingNames, ofString name ≠ ofString key := by
  intro name inside
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  simp only [remainingNames, List.mem_cons, List.not_mem_nil, or_false] at inside
  rcases member with rfl | rfl | rfl <;> rcases inside with rfl | rfl | rfl | rfl | rfl <;> decide

end InitECandidate.Solver.GasBudget.CallOpcode

#print axioms InitECandidate.Solver.GasBudget.CallOpcode.body_shape
#print axioms InitECandidate.Solver.GasBudget.CallOpcode.original_code
#print axioms InitECandidate.Solver.GasBudget.CallOpcode.remaining_away

import InitECandidate.Solver.Mpt.WitnessMaterializeProgram
import InitECandidate.Solver.Arenas.ScratchScope

namespace InitECandidate.Solver.Mpt.WitnessMaterialize
open Flapjack Flapjack.Pancake.PanLang
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

def release : ProgHOL 64 := .call (some (none,none)) (ofString "scratch_release") [localVar "mark"]
def handler : ProgHOL 64 := .seq release (.raise (ofString "RlpErr") (localVar "e"))
def childArguments : List (ExpHOL 64) := [localVar "db",localVar "p",localVar "n",localVar "mark"]
def caught : ProgHOL 64 := .call (some (some (.local,ofString "nd"),some (ofString "RlpErr",ofString "e",handler))) (ofString "_decode_witness_node_mpt") childArguments
def footer : ProgHOL 64 := .seq release (.return (localVar "nd"))
def afterResult : ProgHOL 64 := .seq caught footer
def afterError : ProgHOL 64 := .dec (ofString "nd") .one (.const 0#64) afterResult
def afterMark : ProgHOL 64 := .dec (ofString "e") .one (.const 0#64) afterError

set_option maxRecDepth 100000 in
/-- Original240's actual mark, locals, caught child, release and return. -/
theorem wrapper_shape : body=.decCall (ofString "mark") .one (ofString "scratch_mark") [] afterMark := by
  simp only [body,Guest.guestFn__decode_witness_node,progToHOL,expToHOL,shapeToHOL,List.map_cons,List.map_nil,Option.map_some,Option.map_none,
    afterMark,afterError,afterResult,caught,footer,handler,release,childArguments,localVar]

theorem handler_price (code) (installed : Input.OriginalCode.Installed code) : Input.ClockCost.Bound code handler 1 :=
  Input.ClockCost.sequence code _ _ 1 0 (Arenas.Scratch.release_call_price code installed _) (Input.ClockCost.raised code _ _)

theorem footer_price (code) (installed : Input.OriginalCode.Installed code) : Input.ClockCost.Bound code footer 1 :=
  Input.ClockCost.sequence code _ _ 1 0 (Arenas.Scratch.release_call_price code installed _) (Input.ClockCost.returned code _)

end InitECandidate.Solver.Mpt.WitnessMaterialize

namespace InitECandidate.Solver.Mpt.WitnessMaterializeMpt
open Flapjack Flapjack.Pancake.PanLang
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

def body : ProgHOL 64 := match Guest.guestFn__decode_witness_node_mpt with | .function fn=>progToHOL fn.body | _=>.skip
def formals : List (MlS×ShapeHOL) := [(ofString "db",.one),(ofString "p",.one),(ofString "n",.one),(ofString "mark",.one)]
def handler : ProgHOL 64 := .seq WitnessMaterialize.release (.raise (ofString "MptErr") (localVar "e"))
def childArguments : List (ExpHOL 64) := [localVar "db",localVar "p",localVar "n"]
def caught : ProgHOL 64 := .call (some (some (.local,ofString "nd"),some (ofString "MptErr",ofString "e",handler))) (ofString "_decode_witness_node_body") childArguments
def footer : ProgHOL 64 := .return (localVar "nd")
def afterResult : ProgHOL 64 := .seq caught footer
def afterError : ProgHOL 64 := .dec (ofString "nd") .one (.const 0#64) afterResult

set_option maxRecDepth 100000 in
theorem wrapper_shape : body=.dec (ofString "e") .one (.const 0#64) afterError := by
  simp only [body,Guest.guestFn__decode_witness_node_mpt,progToHOL,expToHOL,shapeToHOL,List.map_cons,List.map_nil,Option.map_some,Option.map_none,
    afterError,afterResult,caught,footer,handler,WitnessMaterialize.release,childArguments,localVar]

set_option maxRecDepth 100000 in
theorem original_code (code) (installed : Input.OriginalCode.Installed code) :
    code.lookup (ofString "_decode_witness_node_mpt")=some (formals,body,.one) := by
  have checked:=Input.OriginalCode.indexed code installed 239 (GasBudget.OriginalCodeEnvironment.originalEntry Guest.guestFn__decode_witness_node_mpt) (by rfl)
  simpa only [GasBudget.OriginalCodeEnvironment.originalEntry,declToHOL,funDeclToHOL,formals,body,Guest.guestFn__decode_witness_node_mpt,
    shapeToHOL,paramToHOL,List.map_cons,List.map_nil] using checked

theorem handler_price (code) (installed : Input.OriginalCode.Installed code) : Input.ClockCost.Bound code handler 1 :=
  Input.ClockCost.sequence code _ _ 1 0 (Arenas.Scratch.release_call_price code installed _) (Input.ClockCost.raised code _ _)

end InitECandidate.Solver.Mpt.WitnessMaterializeMpt

#print axioms InitECandidate.Solver.Mpt.WitnessMaterialize.wrapper_shape
#print axioms InitECandidate.Solver.Mpt.WitnessMaterialize.handler_price
#print axioms InitECandidate.Solver.Mpt.WitnessMaterialize.footer_price
#print axioms InitECandidate.Solver.Mpt.WitnessMaterializeMpt.wrapper_shape
#print axioms InitECandidate.Solver.Mpt.WitnessMaterializeMpt.original_code
#print axioms InitECandidate.Solver.Mpt.WitnessMaterializeMpt.handler_price

import InitECandidate.Solver.Rlp.HeaderValue
import InitECandidate.Solver.Rlp.HeaderCall

namespace InitECandidate.Solver.Rlp.ItemTotal
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

def body : ProgHOL 64 := match Guest.Software.guestFn_rlp_item_total with | .function fn=>progToHOL fn.body | _=>.skip
def arguments : List (ExpHOL 64) := [localVar "p",localVar "len"]
def payloadArguments : List (ExpHOL 64) := [.op .add [localVar "p",.rfield 0 (localVar "h")],.rfield 1 (localVar "h")]
def validate : ProgHOL 64 := .call (some (none,none)) (ofString "rlp_validate_items") payloadArguments
def check : ProgHOL 64 := .ite (.cmp .notEqual (.rfield 2 (localVar "h")) (.const 0#64)) validate .skip
def total : ExpHOL 64 := .op .add [.rfield 0 (localVar "h"),.rfield 1 (localVar "h")]
def afterHeader : ProgHOL 64 := .seq check (.return total)

theorem body_shape : body=.decCall (ofString "h") Header.resultShape (ofString "rlp_item_header") arguments afterHeader := by
  simp only [body,arguments,afterHeader,check,validate,payloadArguments,total,Header.resultShape,localVar,
    Guest.Software.guestFn_rlp_item_total,progToHOL,expToHOL,shapeToHOL,List.map_cons,List.map_nil,Option.map_some,Option.map_none]

set_option maxRecDepth 100000 in
theorem original_code (code) (installed : Input.OriginalCode.Installed code) :
    code.lookup (ofString "rlp_item_total")=some (Header.formals,body,.one) := by
  have checked := Input.OriginalCode.indexed code installed 100 (GasBudget.OriginalCodeEnvironment.originalEntry Guest.Software.guestFn_rlp_item_total) (by rfl)
  simpa only [GasBudget.OriginalCodeEnvironment.originalEntry,declToHOL,funDeclToHOL,body,Header.formals,
    Guest.Software.guestFn_rlp_item_total,shapeToHOL,paramToHOL,List.map_cons,List.map_nil] using checked

theorem payload_arguments (source : PanSemStateFiniteExact 64 Guest.HostMemory) (pointer header payload flag : BitVec 64)
    (pointerCell : source.locals.lookup (ofString "p")=some (.val (.word pointer)))
    (headerCell : source.locals.lookup (ofString "h")=some (Header.result header payload flag)) :
    evalListHOLFinite source (h:=fun address=>Classical.propDecidable (source.memaddrs address)) payloadArguments=some (Header.values (pointer+header) payload) := by
  simp [payloadArguments,Header.values,evalListHOLFinite,evalListHOLExact,evalHOLExact,localVar,toExact,pointerCell,headerCell,
    Header.result,valueIsWord,valueWord,wordOpHOL,wordOp]

theorem check_evaluate (source : PanSemStateFiniteExact 64 Guest.HostMemory) (header payload flag : BitVec 64)
    (cell : source.locals.lookup (ofString "h")=some (Header.result header payload flag)) :
    evaluateHOLFiniteState source check=if flag≠0#64 then evaluateHOLFiniteState source validate else evaluateHOLFiniteState source .skip := by
  simp [check,evaluateHOLFiniteState_ite,evalHOLExact,localVar,toExact,cell,Header.result,Flapjack.Compiler.Encoders.Asm.wordCmpHOL]

end InitECandidate.Solver.Rlp.ItemTotal

#print axioms InitECandidate.Solver.Rlp.ItemTotal.body_shape
#print axioms InitECandidate.Solver.Rlp.ItemTotal.original_code
#print axioms InitECandidate.Solver.Rlp.ItemTotal.payload_arguments
#print axioms InitECandidate.Solver.Rlp.ItemTotal.check_evaluate

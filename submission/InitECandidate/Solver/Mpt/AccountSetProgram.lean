import InitECandidate.Solver.GasBudget.AccountRequiredProgram
import InitECandidate.Solver.GasBudget.JournalAppendProgram
import InitECandidate.Solver.MutableTable.GetNoException

namespace InitECandidate.Solver.Mpt.AccountSet
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch MutableTable

def body : ProgHOL 64 := match Guest.guestFn_set_account with | .function fn=>progToHOL fn.body | _=>.skip
def formals : List (MlS×ShapeHOL) := [(ofString "addr",.one),(ofString "a",.one)]
def values (address account : BitVec 64) : List (ValueHOL 64) := [.val (.word address),.val (.word account)]
def table : ExpHOL 64 := .load .one (.op .add [.var .global (ofString "ts"),.const 16#64])
def mutation : ProgHOL 64 := .call (some (none,none)) (ofString "jset") [table,localVar "addr",localVar "a"]

theorem body_shape : body=.seq mutation (.return (.const 0#64)) := by
  simp only [body,mutation,table,localVar,Guest.guestFn_set_account,progToHOL,expToHOL,shapeToHOL,List.map_cons,List.map_nil,Option.map_some,Option.map_none]

set_option maxRecDepth 100000 in
theorem original_code (code) (installed : Input.OriginalCode.Installed code) :
    code.lookup (ofString "set_account")=some (formals,body,.one) := by
  have checked := Input.OriginalCode.indexed code installed 355 (GasBudget.OriginalCodeEnvironment.originalEntry Guest.guestFn_set_account) (by rfl)
  simpa only [GasBudget.OriginalCodeEnvironment.originalEntry,declToHOL,funDeclToHOL,body,formals,Guest.guestFn_set_account,shapeToHOL,paramToHOL,List.map_cons,List.map_nil] using checked

set_option maxRecDepth 100000 in
theorem journal_code (code) (installed : Input.OriginalCode.Installed code) :
    code.lookup (ofString "jset")=some (TableCall.formals,GasBudget.Journal.Append.setBody,.one) := by
  have checked := Input.OriginalCode.indexed code installed 324 (GasBudget.OriginalCodeEnvironment.originalEntry Guest.guestFn_jset) (by rfl)
  simpa only [GasBudget.OriginalCodeEnvironment.originalEntry,declToHOL,funDeclToHOL,GasBudget.Journal.Append.setBody,TableCall.formals,Guest.guestFn_jset,
    shapeToHOL,paramToHOL,List.map_cons,List.map_nil] using checked

theorem arguments (source : PanSemStateFiniteExact 64 Guest.HostMemory) (transaction pointer address account : BitVec 64)
    (transactionGlobal : source.globals.lookup (ofString "ts")=some (.val (.word transaction)))
    (mapped : source.memaddrs (transaction+16#64)) (stored : source.memory (transaction+16#64)=.word pointer)
    (addressCell : source.locals.lookup (ofString "addr")=some (.val (.word address)))
    (accountCell : source.locals.lookup (ofString "a")=some (.val (.word account))) :
    evalListHOLFinite source (h:=fun query=>Classical.propDecidable (source.memaddrs query)) [table,localVar "addr",localVar "a"]=some (TableCall.values pointer address account) := by
  simp [evalListHOLFinite,evalListHOLExact,evalHOLExact,table,localVar,toExact,transactionGlobal,addressCell,accountCell,
    valueIsWord,valueWord,wordOpHOL,wordOp,memLoadHOLExact,isWfShapeExactHOL,mapped,stored,TableCall.values]

end InitECandidate.Solver.Mpt.AccountSet

#print axioms InitECandidate.Solver.Mpt.AccountSet.body_shape
#print axioms InitECandidate.Solver.Mpt.AccountSet.original_code
#print axioms InitECandidate.Solver.Mpt.AccountSet.journal_code
#print axioms InitECandidate.Solver.Mpt.AccountSet.arguments

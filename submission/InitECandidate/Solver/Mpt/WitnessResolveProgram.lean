import InitECandidate.Solver.Mpt.WitnessStepProgram
import InitECandidate.Solver.MutableTable.NodeDbEnvironment

namespace InitECandidate.Solver.Mpt.WitnessResolve
open Flapjack Flapjack.Pancake.PanLang
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

def field (variableName : String) (index : Nat) : ExpHOL 64 := .rfield index (localVar variableName)
def emptyReturn : ProgHOL 64 := .return (.rstruct [.const 0#64,.const 0#64,.const 0#64,.const 0#64])
def hashReturn : ProgHOL 64 := .return (.rstruct [.const 0#64,localVar "hn",.const 0#64,.const 0#64])
def hitReturn : ProgHOL 64 := .return (.rstruct [.const 1#64,field "r" 1,field "r" 2,field "it" 1])
def listReturn : ProgHOL 64 := .return (.rstruct [.const 1#64,localVar "p",localVar "n",.const 0#64])
def hashCall : ProgHOL 64 := .decCall (ofString "hn") .one (ofString "node_new_hashed") [field "it" 1] hashReturn
def afterLookup : ProgHOL 64 := .seq (.ite (.cmp .equal (field "r" 0) (.const 0#64)) hashCall .skip) hitReturn
def queryArguments : List (ExpHOL 64) := [localVar "db",field "it" 1]
def lookupCall : ProgHOL 64 := .decCall (ofString "r") MutableTable.NodeDb.resultShape (ofString "nodedb_lookup") queryArguments afterLookup
def wrongSize : ProgHOL 64 := .call (some (none,none)) (ofString "mpt_fail") [.const 10#64]
def sizeTest : ExpHOL 64 := .cmp .notEqual (field "it" 2) (.const 32#64)
def emptyTest : ExpHOL 64 := .cmp .equal (field "it" 2) (.const 0#64)
def afterEmpty : ProgHOL 64 := .seq (.ite sizeTest wrongSize .skip) lookupCall
def stringBranch : ProgHOL 64 := .seq (.ite emptyTest emptyReturn .skip) afterEmpty
def stringTest : ExpHOL 64 := .cmp .equal (field "it" 0) (.const 0#64)

set_option maxRecDepth 100000 in
/-- The real original resolver's complete suffix after the caught item
parser, including its two early guards and actual table/hash constructor. -/
theorem suffix_shape : WitnessStep.afterRlp .resolve=.seq (.ite stringTest stringBranch .skip) listReturn := by
  simp only [WitnessStep.afterRlp,WitnessStep.body,WitnessStep.original,field,emptyReturn,hashReturn,hitReturn,listReturn,hashCall,
    afterLookup,queryArguments,lookupCall,wrongSize,sizeTest,emptyTest,afterEmpty,stringBranch,stringTest,MutableTable.NodeDb.resultShape,localVar,
    Guest.guestFn__resolve_step,progToHOL,expToHOL,shapeToHOL,List.map_cons,List.map_nil,Option.map_some,Option.map_none]

end InitECandidate.Solver.Mpt.WitnessResolve

#print axioms InitECandidate.Solver.Mpt.WitnessResolve.suffix_shape

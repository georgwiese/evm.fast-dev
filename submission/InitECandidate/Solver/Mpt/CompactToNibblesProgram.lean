import InitECandidate.Solver.Mpt.KeyToNibblesAnyCall
import InitECandidate.Solver.Mpt.Fail

namespace InitECandidate.Solver.Mpt.CompactToNibbles
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

private def decRest : ProgHOL 64→ProgHOL 64 | .dec _ _ _ rest=>rest | _=>.skip
private def callRest : ProgHOL 64→ProgHOL 64 | .decCall _ _ _ _ rest=>rest | _=>.skip
private def seqRest : ProgHOL 64→ProgHOL 64 | .seq _ rest=>rest | _=>.skip
def body : ProgHOL 64:=match Guest.guestFn_compact_to_nibbles with | .function fn=>progToHOL fn.body | _=>.skip
def formals : List (MlS×ShapeHOL):=[(ofString "p",.one),(ofString "n",.one)]
def resultShape : ShapeHOL:=.comb [.one,.one,.one]
def fail : ProgHOL 64:=.call (some (none,none)) (ofString "mpt_fail") [.const 5#64]
def zeroTest : ExpHOL 64:=.cmp .equal (localVar "n") (.const 0#64)
def afterGuard : ProgHOL 64:=seqRest body
def afterByte : ProgHOL 64:=decRest afterGuard
def allocationCall : ProgHOL 64:=decRest (decRest (decRest afterByte))
def afterAllocation : ProgHOL 64:=callRest allocationCall
def firstExpression : ExpHOL 64:=.shift .lsr (localVar "c0") (.const 4#64)
def leafExpression : ExpHOL 64:=.op .and [.shift .lsr (localVar "first") (.const 1#64),.const 1#64]
def oddExpression : ExpHOL 64:=.op .and [localVar "first",.const 1#64]
def initialActions : List ProgramPrefix.Action:=[.declare "first" firstExpression,.declare "is_leaf" leafExpression,.declare "odd" oddExpression]
def amount : ExpHOL 64:=.panop .mul [.const 2#64,localVar "n"]
def oddTest : ExpHOL 64:=.cmp .notEqual (localVar "odd") (.const 0#64)
def oddWrite : ProgHOL 64:=.seq (.storeByte (localVar "out") (.op .and [localVar "c0",.const 15#64]))
  (.assign .local (ofString "k") (.const 1#64))
def oddGuard : ProgHOL 64:=.ite oddTest oddWrite .skip
def keyArguments : List (ExpHOL 64):=[.op .add [localVar "p",.const 1#64],.op .sub [localVar "n",.const 1#64],.op .add [localVar "out",localVar "k"]]
def keyCall : ProgHOL 64:=.call (some (none,none)) (ofString "key_to_nibbles") keyArguments
def resultExpression : ExpHOL 64:=.rstruct [localVar "out",.op .add [localVar "k",.panop .mul [.const 2#64,.op .sub [localVar "n",.const 1#64]]],localVar "is_leaf"]
def footer : ProgHOL 64:=.return resultExpression
def afterOdd : ProgHOL 64:=.seq keyCall footer

set_option maxRecDepth 100000
theorem body_shape : body=.seq (.ite zeroTest fail .skip) afterGuard := by
  simp only [body,afterGuard,seqRest,zeroTest,fail,localVar,Guest.guestFn_compact_to_nibbles,progToHOL,expToHOL,shapeToHOL,List.map_cons,List.map_nil,Option.map_none]
theorem byte_shape : afterGuard=.dec (ofString "c0") .one (.loadByte (localVar "p")) afterByte := by
  simp only [body,afterGuard,afterByte,seqRest,decRest,localVar,Guest.guestFn_compact_to_nibbles,progToHOL,expToHOL,shapeToHOL,List.map_cons,List.map_nil,Option.map_none]
theorem initial_shape : afterByte=ProgramPrefix.program initialActions allocationCall := by
  simp only [body,afterGuard,afterByte,allocationCall,seqRest,decRest,initialActions,firstExpression,leafExpression,oddExpression,
    ProgramPrefix.program,localVar,Guest.guestFn_compact_to_nibbles,progToHOL,expToHOL,shapeToHOL,List.map_cons,List.map_nil,Option.map_none]
theorem allocation_shape : allocationCall=.decCall (ofString "out") .one (ofString "alloc") [amount] afterAllocation := by
  simp only [body,afterGuard,afterByte,allocationCall,afterAllocation,seqRest,decRest,callRest,amount,localVar,
    Guest.guestFn_compact_to_nibbles,progToHOL,expToHOL,shapeToHOL,List.map_cons,List.map_nil,Option.map_none]
theorem after_allocation_shape : afterAllocation=.dec (ofString "k") .one (.const 0#64) (.seq oddGuard afterOdd) := by
  simp only [body,afterGuard,afterByte,allocationCall,afterAllocation,seqRest,decRest,callRest,oddGuard,oddTest,oddWrite,afterOdd,keyCall,keyArguments,footer,resultExpression,localVar,
    Guest.guestFn_compact_to_nibbles,progToHOL,expToHOL,shapeToHOL,List.map_cons,List.map_nil,Option.map_none]

theorem original_code (code) (installed : Input.OriginalCode.Installed code) :
    code.lookup (ofString "compact_to_nibbles")=some (formals,body,resultShape) := by
  have checked:=Input.OriginalCode.indexed code installed 225 (GasBudget.OriginalCodeEnvironment.originalEntry Guest.guestFn_compact_to_nibbles) (by rfl)
  simpa only [GasBudget.OriginalCodeEnvironment.originalEntry,declToHOL,funDeclToHOL,formals,body,resultShape,
    Guest.guestFn_compact_to_nibbles,shapeToHOL,paramToHOL,List.map_cons,List.map_nil] using checked

end InitECandidate.Solver.Mpt.CompactToNibbles

#print axioms InitECandidate.Solver.Mpt.CompactToNibbles.body_shape
#print axioms InitECandidate.Solver.Mpt.CompactToNibbles.byte_shape
#print axioms InitECandidate.Solver.Mpt.CompactToNibbles.initial_shape
#print axioms InitECandidate.Solver.Mpt.CompactToNibbles.allocation_shape
#print axioms InitECandidate.Solver.Mpt.CompactToNibbles.after_allocation_shape
#print axioms InitECandidate.Solver.Mpt.CompactToNibbles.original_code

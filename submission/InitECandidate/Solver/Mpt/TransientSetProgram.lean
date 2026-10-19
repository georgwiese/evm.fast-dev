import InitECandidate.Solver.Mpt.StorageKeyProgram
import InitECandidate.Solver.GasBudget.U256MemoryValues

namespace InitECandidate.Solver.Mpt.TransientSet
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch

def body : ProgHOL 64 := match Guest.guestFn_set_transient_storage with | .function fn => progToHOL fn.body | _ => .skip
def formals : List (MlS × ShapeHOL) := [(ofString "addr",.one),(ofString "key",.one),(ofString "value",Input.RlpWrite.U256Value.tupleShape)]
def table : ExpHOL 64 := .load .one (.op .add [.var .global (ofString "ts"),.const 64#64])
def deleteCall : ProgHOL 64 := .call (some (none,none)) (ofString "jdel") [table,localVar "k"]
def setCall : ProgHOL 64 := .call (some (none,none)) (ofString "jset") [table,localVar "k",localVar "v"]
def afterAlloc : ProgHOL 64 := .seq (.store (localVar "v") (localVar "value")) (.seq setCall (.return (.const 0#64)))
def allocate : ProgHOL 64 := .decCall (ofString "v") .one (ofString "alloc") [.const 32#64] afterAlloc
def afterZero : ProgHOL 64 := .seq (.ite (.cmp .notEqual (localVar "z") (.const 0#64)) (.seq deleteCall (.return (.const 0#64))) .skip) allocate
def afterKey : ProgHOL 64 := .decCall (ofString "z") .one (ofString "u256_is_zero") [localVar "value"] afterZero

theorem body_shape : body = .decCall (ofString "k") .one (ofString "sk_make") [localVar "addr",localVar "key"] afterKey := by
  simp only [body,afterKey,afterZero,allocate,afterAlloc,deleteCall,setCall,table,localVar,Guest.guestFn_set_transient_storage,progToHOL,expToHOL,
    shapeToHOL,List.map_cons,List.map_nil,Option.map_some,Option.map_none]

set_option maxRecDepth 100000 in
theorem original_code (code) (installed : Input.OriginalCode.Installed code) :
    code.lookup (ofString "set_transient_storage") = some (formals,body,.one) := by
  have checked := Input.OriginalCode.indexed code installed 362 (GasBudget.OriginalCodeEnvironment.originalEntry Guest.guestFn_set_transient_storage) (by rfl)
  simpa only [GasBudget.OriginalCodeEnvironment.originalEntry,declToHOL,funDeclToHOL,body,formals,Input.RlpWrite.U256Value.tupleShape,Guest.guestFn_set_transient_storage,
    shapeToHOL,paramToHOL,List.map_cons,List.map_nil] using checked

theorem zero_dispatch (source : PanSemStateFiniteExact 64 Guest.HostMemory) (zero : BitVec 64)
    (zeroLocal : source.locals.lookup (ofString "z") = some (.val (.word zero))) :
    evaluateHOLFiniteState source afterZero = if zero = 0#64 then evaluateHOLFiniteState source allocate
      else evaluateHOLFiniteState source (.seq deleteCall (.return (.const 0#64))) := by
  classical
  by_cases absent : zero = 0#64
  · simp [afterZero,evaluateHOLFiniteState_seq_line780,evaluateHOLFiniteState_ite,evaluateHOLFiniteState_skip,evalHOLExact,localVar,toExact,zeroLocal,
      Flapjack.Compiler.Encoders.Asm.wordCmpHOL,absent]
  · cases output : evaluateHOLFiniteState source deleteCall with
    | mk result next =>
      cases result <;> simp [afterZero,evaluateHOLFiniteState_seq_line780,evaluateHOLFiniteState_ite,evaluateHOLFiniteState_return,evalHOLExact,localVar,toExact,zeroLocal,
        Flapjack.Compiler.Encoders.Asm.wordCmpHOL,absent,output,shapeOfHOLExact,sizeOfShapeWithContextHOL]

end InitECandidate.Solver.Mpt.TransientSet

#print axioms InitECandidate.Solver.Mpt.TransientSet.body_shape
#print axioms InitECandidate.Solver.Mpt.TransientSet.original_code
#print axioms InitECandidate.Solver.Mpt.TransientSet.zero_dispatch

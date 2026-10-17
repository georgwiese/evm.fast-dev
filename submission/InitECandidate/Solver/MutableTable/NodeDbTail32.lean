import InitECandidate.Solver.MutableTable.GetCall32

namespace InitECandidate.Solver.MutableTable.NodeDb
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

abbrev Slice:=BitVec 64×BitVec 64
def body : ProgHOL 64:=match Guest.guestFn_nodedb_lookup with | .function fn=>progToHOL fn.body | _=>.skip
def formals : List (MlS×ShapeHOL):=[(ofString "db",.one),(ofString "hash",.one)]
def triple (flag pointer length : BitVec 64) : ValueHOL 64:=.rStruct [.val (.word flag),.val (.word pointer),.val (.word length)]
def output : Option Slice→ValueHOL 64
  | none=>triple 0#64 0#64 0#64
  | some slice=>triple 1#64 slice.1 slice.2

def recordExpression : ExpHOL 64:=.rfield 1 (localVar "r")
def condition : ExpHOL 64:=.cmp .equal (.rfield 0 (localVar "r")) (.const 0#64)
def absent : ProgHOL 64:=.return (.rstruct [.const 0#64,.const 0#64,.const 0#64])
def present : ProgHOL 64:=.return (.rstruct [.const 1#64,.load .one recordExpression,.load .one (.op .add [recordExpression,.const 8#64])])
def afterGet : ProgHOL 64:=.seq (.ite condition absent .skip) present

theorem body_shape : body=.decCall (ofString "r") Get.pairShape (ofString "htab_get") [localVar "db",localVar "hash"] afterGet := by
  simp only [body,Guest.guestFn_nodedb_lookup,progToHOL,expToHOL,shapeToHOL,List.map_cons,List.map_nil,
    afterGet,condition,absent,present,recordExpression,localVar,Get.pairShape]

/-- Actual original nodedb_lookup suffix, including both real record-cell loads
and its exact absent triple. Record correspondence stays an entry premise. -/
theorem tail32_execute (source : PanSemStateFiniteExact 64 Guest.HostMemory) (result : Option (BitVec 64)) (slices : BitVec 64→Slice)
    (rLocal : source.locals.lookup (ofString "r")=some (Get.output result))
    (records : ∀ record,result=some record→source.memaddrs record ∧ source.memaddrs (record+8#64) ∧
      source.memory record=.word (slices record).1 ∧ source.memory (record+8#64)=.word (slices record).2) :
    evaluateHOLFiniteState source afterGet=(some (.returned (output (result.map slices))),emptyLocalsHOLFinite source) := by
  classical
  cases selected : result with
  | none=>
    rw [selected] at rLocal
    have stopped : evaluateHOLFiniteState source (.ite condition absent .skip)=
        (some (.returned (output none)),emptyLocalsHOLFinite source) := by
      simp [condition,evaluateHOLFiniteState_ite,evalHOLExact,toExact,localVar,rLocal,Get.output,Get.pair,
        Flapjack.Compiler.Encoders.Asm.wordCmpHOL,absent,triple,output,evaluateHOLFiniteState_return,evalListHOLExact,shapeOfHOLExact,sizeOfShapeWithContextHOL]
    rw [afterGet,WitnessRadix.StateSteps.stopped_sequence source (emptyLocalsHOLFinite source) _ _ _ stopped (Nat.le_refl _)]
    rfl
  | some record=>
    rw [selected] at rLocal
    obtain ⟨mapped,plusMapped,stored,plusStored⟩:=records record selected
    have skipped : evaluateHOLFiniteState source (.ite condition absent .skip)=(none,source) := by
      simp [condition,evaluateHOLFiniteState_ite,evalHOLExact,toExact,localVar,rLocal,Get.output,Get.pair,
        Flapjack.Compiler.Encoders.Asm.wordCmpHOL]
    have returned : evaluateHOLFiniteState source present=(some (.returned (output (some (slices record)))),emptyLocalsHOLFinite source) := by
      simp [present,recordExpression,triple,output,evaluateHOLFiniteState_return,evalHOLExact,evalListHOLExact,toExact,localVar,rLocal,Get.output,Get.pair,
        valueIsWord,valueWord,wordOpHOL,wordOp,memLoadHOLExact,isWfShapeExactHOL,mapped,plusMapped,stored,plusStored,shapeOfHOLExact,sizeOfShapeWithContextHOL]
    rw [afterGet,WitnessRadix.StateSteps.next_sequence source source _ _ skipped (Nat.le_refl _)]
    exact returned

end InitECandidate.Solver.MutableTable.NodeDb

#print axioms InitECandidate.Solver.MutableTable.NodeDb.body_shape
#print axioms InitECandidate.Solver.MutableTable.NodeDb.tail32_execute

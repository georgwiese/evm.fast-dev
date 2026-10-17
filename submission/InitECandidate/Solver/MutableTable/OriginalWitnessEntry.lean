import InitECandidate.Solver.MutableTable.WitnessBuildExecution
import InitECandidate.Solver.Input.PayloadPrefixProgram

namespace InitECandidate.Solver.MutableTable.WitnessRunAttempt
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString QueryBranch
set_option maxRecDepth 10000

def body : ProgHOL 64:=match Guest.guestFn_run_attempt with | .function fn=>progToHOL fn.body | _=>.skip
/-- The actual initialization suffix after header validation and block-hash globals. -/
def initialization : ProgHOL 64:=Input.Payload.dropLeading 9 body
def codeCall : ProgHOL 64:=match initialization with | .decCall _ _ _ _ rest=>rest | _=>.skip
def runtime : ProgHOL 64:=match codeCall with | .decCall _ _ _ _ rest=>rest | _=>.skip
def inputField (offset : Nat) : ExpHOL 64:=.load .one (.op .add [localVar "si",.const (BitVec.ofNat 64 offset)])
def arguments (offset : Nat) : List (ExpHOL 64):=[inputField offset,inputField (offset+8)]

theorem initialization_shape : initialization=.decCall (ofString "nodedb") .one (ofString "nodedb_build") (arguments 40)
    (.decCall (ofString "codedb") .one (ofString "nodedb_build") (arguments 56) runtime) := by
  simp only [initialization,codeCall,runtime,body,Guest.guestFn_run_attempt,Input.Payload.dropLeading,
    progToHOL,expToHOL,shapeToHOL,List.map_cons,List.map_nil,Option.map_none,arguments,inputField,localVar,
    List.nil_append,List.cons_append,List.append_nil]

/-- The real two constructor calls load their array/count pairs from the
stateless input structure, including the zero pair for an empty list. -/
theorem input_arguments (source : PanSemStateFiniteExact 64 Guest.HostMemory) (si : BitVec 64) (offset records count : Nat)
    (siLocal : source.locals.lookup (ofString "si")=some (.val (.word si)))
    (pointerMapped : source.memaddrs (byteAddress si offset))
    (countMapped : source.memaddrs (byteAddress si (offset+8)))
    (pointerWord : source.memory (byteAddress si offset)=.word (BitVec.ofNat 64 records))
    (countWord : source.memory (byteAddress si (offset+8))=.word (BitVec.ofNat 64 count)) :
    evalListHOLFinite source (h:=fun q=>Classical.propDecidable (source.memaddrs q)) (arguments offset)=some ([.val (.word (BitVec.ofNat 64 records)), .val (.word (BitVec.ofNat 64 count))]) := by
  classical
  change source.memaddrs (si+BitVec.ofNat 64 offset) at pointerMapped
  change source.memaddrs (si+BitVec.ofNat 64 (offset+8)) at countMapped
  change source.memory (si+BitVec.ofNat 64 offset)=_ at pointerWord
  change source.memory (si+BitVec.ofNat 64 (offset+8))=_ at countWord
  simp [arguments,inputField,evalListHOLFinite,evalListHOLExact,evalHOLExact,toExact,localVar,siLocal,
    valueIsWord,valueWord,wordOpHOL,wordOp,panOpHOL,isWfShapeExactHOL,memLoadHOLExact,byteAddress,pointerMapped,countMapped,pointerWord,countWord]

end InitECandidate.Solver.MutableTable.WitnessRunAttempt

#print axioms InitECandidate.Solver.MutableTable.WitnessRunAttempt.initialization_shape
#print axioms InitECandidate.Solver.MutableTable.WitnessRunAttempt.input_arguments

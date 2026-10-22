import InitECandidate.Solver.Input.CallPrefixNormalTrace
import InitECandidate.Solver.Input.CallPrefixDeclaration
import InitECandidate.Solver.GasBudget.OriginalCodeEnvironment
import InitECandidate.Solver.Input.OriginalCode

namespace InitECandidate.Solver.Mpt.Insert
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

def body : ProgHOL 64:=match Guest.guestFn__mpt_insert_node with | .function fn=>progToHOL fn.body | _=>.skip
def formals : List (MlS×ShapeHOL):=[(ofString "node",.one),(ofString "key",.one),(ofString "klen",.one),
  (ofString "level",.one),(ofString "vptr",.one),(ofString "vlen",.one)]
def afterResult : ProgHOL 64:=match body with | .dec _ _ _ rest=>rest | _=>.skip
def afterSlot : ProgHOL 64:=match afterResult with | .dec _ _ _ rest=>rest | _=>.skip
def loopAndAfter : ProgHOL 64:=match afterSlot with | .dec _ _ _ rest=>rest | _=>.skip
def loop : ProgHOL 64:=match loopAndAfter with | .seq first _=>first | _=>.skip
def afterLoop : ProgHOL 64:=match loopAndAfter with | .seq _ rest=>rest | _=>.skip
def loopBody : ProgHOL 64:=match loop with | .while _ rest=>rest | _=>.skip
def test : ExpHOL 64:=.cmp .notEqual (localVar "go") (.const 0#64)
def actions : List Input.CallPrefix.Action:=[.declare (ofString "result") .one (.const 0#64),
  .declare (ofString "slot") .one (.const 0#64),.declare (ofString "go") .one (.const 1#64)]
def setup (source : PanSemStateFiniteExact 64 Guest.HostMemory):=
  bind (bind (bind source "result" 0#64) "slot" 0#64) "go" 1#64

set_option maxRecDepth 100000 in
theorem body_shape : body=Input.CallPrefix.program actions loopAndAfter := by
  simp only [body,Guest.guestFn__mpt_insert_node,progToHOL,expToHOL,shapeToHOL,List.map_cons,List.map_nil,
    Option.map_none,Option.map_some,actions,Input.CallPrefix.program,loopAndAfter,afterResult,afterSlot]

set_option maxRecDepth 100000 in
theorem loop_shape : loopAndAfter=.seq (.while test loopBody) (.return (localVar "result")) := by
  simp only [loopAndAfter,afterResult,afterSlot,body,Guest.guestFn__mpt_insert_node,progToHOL,expToHOL,shapeToHOL,
    List.map_cons,List.map_nil,Option.map_none,Option.map_some,loop,loopBody,test,localVar]

set_option maxRecDepth 100000 in
theorem original_code (code) (installed : Input.OriginalCode.Installed code) :
    code.lookup (ofString "_mpt_insert_node")=some (formals,body,.one) := by
  have checked:=Input.OriginalCode.indexed code installed 251 (GasBudget.OriginalCodeEnvironment.originalEntry Guest.guestFn__mpt_insert_node) (by rfl)
  simpa only [GasBudget.OriginalCodeEnvironment.originalEntry,declToHOL,funDeclToHOL,formals,body,Guest.guestFn__mpt_insert_node,
    shapeToHOL,paramToHOL,List.map_cons,List.map_nil] using checked

set_option maxRecDepth 100000 in
/-- The original traversal body cannot return from its enclosing insertion;
actual helper calls restore its key-length local before continuing. -/
theorem loop_body_safe : Input.LocalPrefix (ofString "klen") loopBody := by
  simp only [loopBody,loop,loopAndAfter,afterResult,afterSlot,body,Guest.guestFn__mpt_insert_node,progToHOL,expToHOL,
    shapeToHOL,List.map_cons,List.map_nil,Option.map_none,Option.map_some]
  repeat first
    | apply Input.LocalPrefix.dec <;> (try decide)
    | apply Input.LocalPrefix.decCall <;> (try decide)
    | apply Input.LocalPrefix.seq
    | apply Input.LocalPrefix.ite
    | exact Input.LocalPrefix.assign _ _ (by decide)
    | exact Input.LocalPrefix.store _ _
    | exact Input.LocalPrefix.skip
    | exact Input.LocalPrefix.call (some (ofString "r")) _ _ (by intro name same; have equal:=Option.some.inj same; subst name; decide)
    | exact Input.LocalPrefix.call none _ _ (by intro name impossible; cases impossible)

/-- The genuine insertion initializes its loop locals without touching
memory or globals. The real loop remainder retains its exact nonlocal state. -/
theorem normal_setup (source target : PanSemStateFiniteExact 64 Guest.HostMemory) (value : ValueHOL 64)
    (normal : evaluateHOLFiniteState source body=(some (.returned value),target)) :
    ∃ inner,target.clock=inner.clock ∧ Input.LocalEffects.erase target=Input.LocalEffects.erase inner ∧
      evaluateHOLFiniteState (setup source) loopAndAfter=(some (.returned value),inner) := by
  have never : Input.NoReturn.Never (Input.CallPrefix.program actions .skip):=
    Input.NoReturn.declared _ _ _ _ (Input.NoReturn.declared _ _ _ _ (Input.NoReturn.declared _ _ _ _ Input.NoReturn.skip))
  rw [body_shape] at normal
  obtain ⟨current,inner,trace,clock,continued⟩:=Input.CallPrefix.normal_trace source target actions loopAndAfter value never normal
  have first:=trace.declare_next (.val (.word 0#64)) rfl
  have second:=first.declare_next (.val (.word 0#64)) rfl
  have last:=second.declare_next (.val (.word 1#64)) rfl
  have same : current=setup source:=by cases last; rfl
  have frame:=trace.erase loopAndAfter
  rw [normal,continued] at frame
  exact ⟨inner,clock,frame,by simpa only [same] using continued⟩

end InitECandidate.Solver.Mpt.Insert

#print axioms InitECandidate.Solver.Mpt.Insert.body_shape
#print axioms InitECandidate.Solver.Mpt.Insert.loop_shape
#print axioms InitECandidate.Solver.Mpt.Insert.original_code
#print axioms InitECandidate.Solver.Mpt.Insert.loop_body_safe
#print axioms InitECandidate.Solver.Mpt.Insert.normal_setup

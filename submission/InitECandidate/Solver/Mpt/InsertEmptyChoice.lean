import InitECandidate.Solver.Mpt.InsertSetup
import InitECandidate.Solver.Input.CallPrefixCommand

namespace InitECandidate.Solver.Mpt.Insert
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

def afterR : ProgHOL 64:=match loopBody with | .dec _ _ _ rest=>rest | _=>.skip
def afterNextNode : ProgHOL 64:=match afterR with | .dec _ _ _ rest=>rest | _=>.skip
def afterNextSlot : ProgHOL 64:=match afterNextNode with | .dec _ _ _ rest=>rest | _=>.skip
def afterNextLevel : ProgHOL 64:=match afterNextSlot with | .dec _ _ _ rest=>rest | _=>.skip
def afterGo : ProgHOL 64:=match afterNextLevel with | .seq _ rest=>rest | _=>.skip
def nodeChoice : ProgHOL 64:=match afterGo with | .seq first _=>first | _=>.skip
def afterChoice : ProgHOL 64:=match afterGo with | .seq _ rest=>rest | _=>.skip
def nonemptyChoice : ProgHOL 64:=match nodeChoice with | .ite _ _ no=>no | _=>.skip
def nodeTest : ExpHOL 64:=.cmp .equal (localVar "node") (.const 0#64)
def clearGo : ProgHOL 64:=.assign .local (ofString "go") (.const 0#64)
def leafArguments : List (ExpHOL 64):=[.op .add [localVar "key",localVar "level"],
  .op .sub [localVar "klen",localVar "level"],localVar "vptr",localVar "vlen"]
def leafCall : ProgHOL 64:=.call (some (some (.local,ofString "r"),none)) (ofString "node_new_leaf") leafArguments
def iterationActions : List Input.CallPrefix.Action:=[
  .declare (ofString "r") .one (.const 0#64),.declare (ofString "next_node") .one (.const 0#64),
  .declare (ofString "next_slot") .one (.const 0#64),.declare (ofString "next_level") .one (.const 0#64),.command clearGo]
def prepared (source : PanSemStateFiniteExact 64 Guest.HostMemory):=
  bind (bind (bind (bind source "r" 0#64) "next_node" 0#64) "next_slot" 0#64) "next_level" 0#64
def dispatchEntry (source : PanSemStateFiniteExact 64 Guest.HostMemory):=bind (prepared source) "go" 0#64

set_option maxRecDepth 100000 in
theorem iteration_shape : loopBody=Input.CallPrefix.program iterationActions (.seq nodeChoice afterChoice) := by
  simp only [loopBody,loop,loopAndAfter,afterResult,afterSlot,body,Guest.guestFn__mpt_insert_node,progToHOL,expToHOL,shapeToHOL,
    List.map_cons,List.map_nil,Option.map_none,Option.map_some,iterationActions,Input.CallPrefix.program,clearGo,
    nodeChoice,afterChoice,afterGo,afterNextLevel,afterNextSlot,afterNextNode,afterR]

set_option maxRecDepth 100000 in
theorem node_choice_shape : nodeChoice=.ite nodeTest leafCall nonemptyChoice := by
  simp only [nodeChoice,nonemptyChoice,afterGo,afterNextLevel,afterNextSlot,afterNextNode,afterR,loopBody,loop,loopAndAfter,afterResult,afterSlot,
    body,Guest.guestFn__mpt_insert_node,progToHOL,expToHOL,shapeToHOL,List.map_cons,List.map_nil,Option.map_none,Option.map_some,
    nodeTest,leafCall,leafArguments,localVar]

theorem prefix_execution (source : PanSemStateFiniteExact 64 Guest.HostMemory) (go : BitVec 64)
    (goCell : source.locals.lookup (ofString "go")=some (.val (.word go))) :
    Input.CallPrefix.Execution source iterationActions (dispatchEntry source) := by
  have currentGo : (prepared source).locals.lookup (ofString "go")=some (.val (.word go)):=by
    simpa [prepared,QueryBranch.bind,setVarHOLFinite,HolFiniteMapExact.update,FUPDATE,
      show ofString "r"≠ofString "go" from by decide,show ofString "next_node"≠ofString "go" from by decide,
      show ofString "next_slot"≠ofString "go" from by decide,show ofString "next_level"≠ofString "go" from by decide] using goCell
  have cleared : evaluateHOLFiniteState (prepared source) clearGo=(none,dispatchEntry source):=
    StateSteps.assign_execute (prepared source) "go" (.const 0#64) go 0#64 currentGo rfl
  refine .step (.declare source _ .one (.const 0#64) (.val (.word 0#64)) rfl (by simp [shapeEqHOL,shapeOfHOLExact])) ?_
  refine .step (.declare _ _ .one (.const 0#64) (.val (.word 0#64)) rfl (by simp [shapeEqHOL,shapeOfHOLExact])) ?_
  refine .step (.declare _ _ .one (.const 0#64) (.val (.word 0#64)) rfl (by simp [shapeEqHOL,shapeOfHOLExact])) ?_
  refine .step (.declare _ _ .one (.const 0#64) (.val (.word 0#64)) rfl (by simp [shapeEqHOL,shapeOfHOLExact])) ?_
  exact .step (.command _ _ clearGo cleared) (.done _)

theorem empty_choice (source : PanSemStateFiniteExact 64 Guest.HostMemory)
    (nodeCell : source.locals.lookup (ofString "node")=some (.val (.word 0#64))) :
    evaluateHOLFiniteState source nodeChoice=evaluateHOLFiniteState source leafCall := by
  have read : eval source nodeTest=some (.val (.word 1#64)):=by
    simp [eval,nodeTest,localVar,evalHOLExact,toExact,nodeCell,Flapjack.Compiler.Encoders.Asm.wordCmpHOL]
  rw [node_choice_shape,evaluateHOLFiniteState_ite]
  simp only [eval] at read
  rw [read]
  simp

end InitECandidate.Solver.Mpt.Insert

#print axioms InitECandidate.Solver.Mpt.Insert.iteration_shape
#print axioms InitECandidate.Solver.Mpt.Insert.node_choice_shape
#print axioms InitECandidate.Solver.Mpt.Insert.prefix_execution
#print axioms InitECandidate.Solver.Mpt.Insert.empty_choice
